module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModelPolynomial
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmRealProd
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SupremumKeepingLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLevelReductionCriterion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankDiffLeHalfRank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSecondOfPrints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFinCombOfIsThetaAt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingEvaluation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SquareAgree.StabLieAdelic

theorem conjU_one {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E)
    (h : J = c • V.gram) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h 1 = 1 := by
  apply Subtype.ext
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU]

theorem exists_sum_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) {Φ : (Fin n × Fin d → AF F) → ℂ}
    (hΦ : Φ ∈ algD M ψ emb) :
    ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) ∧
      Φ = ∑ i, pure (f i) (φ i) := by
  obtain ⟨m, c, g, hg⟩ := Submodule.mem_span_set'.mp hΦ
  have hg' : ∀ i, ∃ f φ, f ∈ M.Pol ψ emb ∧ (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) ∧
      (∀ᶠ v in Filter.cofinite, φ v = M.vac v) ∧ (g i : (Fin n × Fin d → AF F) → ℂ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ :=
    fun i => (g i).2
  choose f φ hf hSB hvac hpure using hg'
  refine ⟨m, fun i => c i • f i, φ, fun i => ⟨(M.Pol ψ emb).smul_mem _ (hf i), hSB i, hvac i⟩, ?_⟩
  rw [← hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hpure i]
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, SchwartzMap.smul_apply, smul_eq_mul, mul_assoc]

end GlobalTheory.SquareAgree.StabLieAdelic


end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseRatAtOfPhaseOne
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.IndefR.Arith Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftRatObj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem phiC_congr (T : CoreJ D) {j : ℕ} {σ σ' : T.Q.c.F →+* ℂ} (e : σ = σ') {W : HSp D} (hV : T.V j σ = W)
    (hV' : T.V j σ' = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) : phiC T hV a f = phiC T hV' a f := by
  subst e
  rfl

section General
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (ph : Fin D.R.m → ℂ)

end General

section Obj

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ)

end Obj

end GlobalTheory.LiftRatObj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumInfPartIntegralOneSubMem
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumInfPartIntegralOneSubMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.IdemSumIdeal

section Generic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem one_sub_mem_idS_prod [StarRing E] (P : Finset (Pl E)) (d : Pl E → ℕ) {ε : E ⊗[F] Formalism.L2.Herm.Af F}
    (hε : ε ∈ Formalism.L2.Herm.intAf F E)
    (h : ∀ w ∈ P, ∃ a : E ⊗[F] Formalism.L2.Herm.Af F, GlobalTheory.InertNbr.IdemOf F w a ∧ a * ε = a) :
    ∃ t ∈ Formalism.L2.DIV.idS F (∏ w ∈ P, w.asIdeal ^ d w), (t : E ⊗[F] Formalism.L2.Herm.Af F) = 1 - ε := by
  classical
  choose! a ha hae using h
  have hone : (1 : E ⊗[F] Formalism.L2.Herm.Af F) - ε ∈ Formalism.L2.Herm.intAf F E := sub_mem (one_mem _) hε
  set t : Formalism.L2.Herm.intAf F E := ⟨1 - ε, hone⟩ with ht
  set b : Pl E → Formalism.L2.Herm.intAf F E := fun w =>
    if hw : w ∈ P then ⟨1 - a w, (ha w hw).one_sub_mem⟩ else 1 with hb
  have hbm : ∀ w ∈ P, b w ∈ Formalism.L2.DIV.idS F (w.asIdeal ^ d w) := by
    intro w hw
    have := (ha w hw).one_sub_mem_idS (d w)
    simpa [hb, hw] using this
  have hprod : ∏ w ∈ P, b w ∈ ∏ w ∈ P, Formalism.L2.DIV.idS F (w.asIdeal ^ d w) := Ideal.prod_mem_prod hbm
  have hmap : ∏ w ∈ P, Formalism.L2.DIV.idS F (w.asIdeal ^ d w) = Formalism.L2.DIV.idS F (∏ w ∈ P, w.asIdeal ^ d w) := by
    unfold Formalism.L2.DIV.idS
    exact (map_prod (Ideal.mapHom (Formalism.L2.DIV.oToS F E)) _ P).symm
  have hfix : t * ∏ w ∈ P, b w = t := by
    refine Finset.prod_induction b (fun x => t * x = t) (fun x y hx hy => by rw [← mul_assoc, hx, hy]) (mul_one t) ?_
    intro w hw
    apply Subtype.ext
    simp only [hb, hw, dif_pos, ht, Subring.coe_mul]
    linear_combination (hae w hw)
  refine ⟨t, ?_, rfl⟩
  rw [← hfix, ← hmap]
  exact Ideal.mul_mem_left _ _ hprod

end Generic

end GlobalTheory.IdemSumIdeal

namespace GlobalTheory.IdemSumIdeal

theorem idemOf_toEAf {D : D7} {a : AE D} {w : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt a w) :
    GlobalTheory.InertNbr.IdemOf D.host.F w (toEAf D a) := by
  refine ⟨by rw [← map_mul, h.1.1], fun x hx => ?_⟩
  rw [h.2 x hx]
  have e : toEAf D (a * incA D ((x : D.host.E)⁻¹)) = toEAf D a * Formalism.L2.Col.iA D.host.F D.host.E ((x : D.host.E)⁻¹) := by
    rw [map_mul]; rfl
  rw [← e]
  exact not_congr ⟨GlobalTheory.IdemIntegral.toEAf_mem_of_finPart_mem, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf⟩

theorem isIdemSum_props : ∀ {D : D7} (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (d : Formalism.L2.DIV.Pl D.host.E → ℕ),
    IsIdemSum e P → infPart D e = 0 ∧ toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧
      ∃ t ∈ Formalism.L2.DIV.idS D.host.F (∏ w ∈ P, w.asIdeal ^ d w), (t : EAf D) = 1 - toEAf D e := by
  intro D e P d h
  obtain ⟨⟨es, hes, he⟩, -⟩ := id h
  have hint : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [he, map_sum]
    exact sum_mem fun w hw => (idemOf_toEAf (hes w hw)).mem
  refine ⟨?_, hint, ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [he, map_sum]
    exact Finset.sum_eq_zero fun w hw =>
      GlobalTheory.ExportSeries.SpecGood.infPart_eq_zero_of_isIdemAt D w (es w) (hes w hw)
  · refine one_sub_mem_idS_prod P d hint fun w hw => ?_
    obtain ⟨a, ha, hae⟩ := GlobalTheory.OffIdem.idemSum_mul_idemAt h hw
    exact ⟨toEAf D a, idemOf_toEAf ha, by rw [← map_mul, hae]⟩

end GlobalTheory.IdemSumIdeal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumInfPartIntegralOneSubMemStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentSum_infPart_integral_one_sub_mem : ∀ {D : D7} (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (d : Formalism.L2.DIV.Pl D.host.E → ℕ), IsIdemSum e P → infPart D e = 0 ∧ toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ ∃ t ∈ Formalism.L2.DIV.idS D.host.F (∏ w ∈ P, w.asIdeal ^ d w), (t : EAf D) = 1 - toEAf D e := by
  first | exact @GlobalTheory.IdemSumIdeal.isIdemSum_props | exact GlobalTheory.IdemSumIdeal.isIdemSum_props | (intros; apply GlobalTheory.IdemSumIdeal.isIdemSum_props <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasCtpId
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

noncomputable section

namespace GlobalTheory.PlaceDecomp

variable {D : D7}

def TyOf (θ : InfFam D) (N : GlobalTheory.Grid.Node D) {W : D.what₂.Tau → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)]
    (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)) : D.what₂.Tau → (GA D N.V → ℂ) → Prop :=
  fun τ f => GlobalTheory.Published.AutFin.HasTypeAt θ N.V τ (N.M.ε τ) (N.M.fr τ) (ρ τ) f

def HasCtp (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (Ty : D.what₂.Tau → (GA D N.V → ℂ) → Prop)
    (τ : D.what₂.Tau) (T : N.M.H τ → N.M.H τ) : Prop :=
  ∃ A : (GA D N.V → ℂ) → (GA D N.V → ℂ), GlobalTheory.KFinDecomp.IsOpAt θ N (GlobalTheory.KFinDecomp.Cls θ N U) Ty τ A ∧
    ∀ φ ∈ GlobalTheory.KFinDecomp.Cls θ N U, GlobalTheory.SeriesToClosure.Moves θ N.V τ (N.M.ε τ) (N.M.σ τ) (N.M.fr τ) T φ (A φ)

theorem hasCtp_id (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (Ty : D.what₂.Tau → (GA D N.V → ℂ) → Prop)
    (τ : D.what₂.Tau) : HasCtp θ N U Ty τ id :=
  ⟨id, GlobalTheory.KFinDecomp.isOpAt_id θ N _ Ty τ, fun _ _ _ _ _ _ _ _ _ h => h⟩

end GlobalTheory.PlaceDecomp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanMatricesTriple
noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.RealLift.FockFirst

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_map_piInf {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j

  change infEmb τ (compInf F E w ((1 : AF F) ⊗ₜ[F] J i j)) = τ.1 (J i j)
  simp [compInf, infEmb_tmul]

theorem hasExp_div (τ : ∀ w : InfinitePlace F, EmbOver E w) {χ χ' : Chr F E} {m m' : InfinitePlace F → ℤ}
    (h : HasExp τ χ m) (h' : HasExp τ χ' m') : HasExp τ (χ / χ') (fun w => m w - m' w) := by
  intro z hz
  rw [MonoidHom.div_apply, Circle.coe_div, h z hz, h' z hz, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_

  have h0 : piInf (τ w) (z : AE F E) ≠ 0 := (z.isUnit.map (piInf (τ w))).ne_zero
  have hne : piInf (τ w) (z : AE F E) / (‖piInf (τ w) (z : AE F E)‖ : ℂ) ≠ 0 :=
    div_ne_zero h0 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h0))
  rw [zpow_sub₀ hne]

end SlopeTestRemainingChoices

end GlobalTheory.RealLift.FockFirst

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainLiftsSurjectiveOfEvenRank
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainLiftsSurjectiveOfEvenRank
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoreOnto

theorem coreOnto_of_chain (hO : ∀ D : D7, GlobalTheory.EvenOnto.OntoAll D) (hC : ComOK) (hS : StageOK) (hE : ChainEx) (hT : TopCols) :
    CoreOnto := by
  intro D hq hsz T L μ0 hL sc hgap G W M hM v MP _hcart y hy x hx
  have hRL := GlobalTheory.T.selfDualLattice_changeOfLattice_laws D
  obtain ⟨⟨r₀, hr₀⟩, hst₀⟩ := hS D hq T L μ0 hL sc G W M hM 0 (Nat.zero_le _)
  obtain ⟨r, Mm, _hr, Θ, hR, hB⟩ := hE D hq hsz T L μ0 hL sc hgap G W M hM v r₀ MP hr₀ D.R.m le_rfl
  have hcom : (gridCom W).Is := hC D hq hsz T L μ0 hL sc hgap G W M hM
  have hs0 : (gridStage G v 0 r₀ MP).Is (gridCom W) 0 := hst₀ r₀ hr₀ v MP
  have hsurj := hO D (gridCom W) hcom (gridStage G v 0 r₀ MP) hs0 D.R.m le_rfl _ Θ hR
  have hyCC : y ∈ (gridStage G v 0 r₀ MP).CC (gridCom W) := by
    have h := (hRL.2.1 (G.V (.core 0)) r₀ W.θ _ MP (lev G (.core 0) : Set _)).1
    exact (SetLike.ext_iff.mp h y).mpr hy
  obtain ⟨y', hy'⟩ := hsurj ⟨y, hyCC⟩
  have hx' : x ∈ (gridStage G v 0 r₀ MP).KF := by
    have h := (hRL.2.1 (G.V (.core 0)) r₀ W.θ _ MP (lev G (.core 0) : Set _)).2.1
    rw [← h] at hx
    exact hx
  have key := hB y' x hx'
  rw [hy'] at key
  refine Submodule.span_mono ?_ key
  rintro F₀ ⟨w, Ψ, hrap, hstep, h0, hm⟩
  refine ⟨Ψ, ⟨hrap, hstep⟩, h0, ?_⟩
  have htop : y'.1 ∈ CoreForms G W.θ D.R.m Mm := by
    have h := (hRL.2.1 (G.V (.core D.R.m)) r W.θ _ Mm (lev G (.core D.R.m) : Set _)).1
    exact (SetLike.ext_iff.mp h y'.1).mp y'.2
  obtain ⟨c, hc, ξ, hξ⟩ := hT D hq T L μ0 hL sc G W M hM Mm _ htop w
  exact ⟨c, hc, ξ, hm.trans hξ⟩

end GlobalTheory.CoreOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainLiftsSurjectiveOfEvenRankStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coreChain_lifts_surjective_of_evenRank : (∀ D : D7, GlobalTheory.EvenOnto.OntoAll D) → ComOK → StageOK → ChainEx → TopCols → CoreOnto := by
  first | exact @GlobalTheory.CoreOnto.coreOnto_of_chain | exact GlobalTheory.CoreOnto.coreOnto_of_chain | (intros; apply GlobalTheory.CoreOnto.coreOnto_of_chain <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActOChiRight
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

open GlobalTheory.StdFrames
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
namespace GlobalTheory.RowMoveAt
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem notOff (S : GridChoice W U) {t : T} (ht : t ∈ U) {w : Pl D.host.E} (hw : w ∈ locPl G t) : ¬ Off S.N.S w := by
  classical
  intro h0
  have h3 := S.N.off w h0
  rcases Finset.mem_union.1 hw with h | h
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
    exact h3.1 (by rw [G.pl.under_w hv]; exact hv)
  · exact h3.2.1 t ht w h rfl

theorem cpt_supp_zero {S : Finset ℕ} {w : Pl D.host.E} (hw : ¬ Off S w) {P : Finset (Pl D.host.E)} {e : AE D}
    (he : IsIdemSum e P) (hoff : ∀ w' ∈ P, Off S w') : cpt w (toEAf D (e + cA D e)) = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← Finset.sum_add_distrib, map_sum, map_sum]
  refine Finset.sum_eq_zero fun w' hw' => ?_
  obtain ⟨hne, hnc⟩ := GlobalTheory.StdHalfLat.ne_and_not_conj hw (hoff w' hw')
  rw [map_add (f := _), map_add (f := _), (cpt_of_isIdemAt (hes w' hw')).2 w hne,
    (cpt_of_isIdemAt (GlobalTheory.MovedIdem.isIdemAt_conj (hes w' hw') (GlobalTheory.IdemSupport.mem_cP w'))).2 w ?_, add_zero]
  rintro rfl
  apply hnc
  intro c hc
  exact ⟨GlobalTheory.IdemSupport.cO D c, (GlobalTheory.IdemSupport.mem_cP w' c).1 hc, by simp [GlobalTheory.IdemSupport.cO]⟩

theorem map_mt_eq_one {S : Finset ℕ} {w : Pl D.host.E} (hw : ¬ Off S w) {P : Finset (Pl D.host.E)} {e : AE D}
    (he : IsIdemSum e P) (hoff : ∀ w' ∈ P, Off S w') {V : HSp D} {g : GA D V} (hg : SuppAt e V g) :
    (mt V g).map ((cpt w).comp (toEAf D)) = 1 := by
  have h0 := cpt_supp_zero hw he hoff
  have h1 : (mt V g - 1).map ((cpt w).comp (toEAf D)) = 0 := by
    ext i j
    rw [Matrix.map_apply, ← hg i j, RingHom.comp_apply, map_mul, map_mul, h0, zero_mul, Matrix.zero_apply]
  have h2 : (mt V g).map ((cpt w).comp (toEAf D)) =
      (mt V g - 1).map ((cpt w).comp (toEAf D)) + (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map ((cpt w).comp (toEAf D)) := by
    rw [← Matrix.map_add _ (map_add _), sub_add_cancel]
  rw [h2, h1, zero_add, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.RowMoveAt

namespace GlobalTheory.RowMoveAt
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem actO_chi_right (j : ℕ) (M : GA D (G.V (.grid (j + 1) D.R.m)))
    (x : WO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T))) :
    actO _ _ (G.toPair (.chi j D.R.m) 1 M)⁻¹.1 (G.toPair (.chi j D.R.m) 1 M)⁻¹.2 x =
      (x : Matrix _ _ (AE D)) * mt (G.V (.grid (j + 1) D.R.m)) M := by
  simp only [actO, GridData.toPair, Prod.fst_inv, Prod.snd_inv, inv_inv, inv_one]
  rw [show mt (G.pT (.chi j D.R.m : Pair T)) 1 = 1 from rfl, Matrix.one_mul]
  rfl

theorem actO_chi_left (j : ℕ) (M : GA D (G.V (.grid (j + 1) D.R.m)))
    (x : WO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T))) :
    actO _ _ (G.toPair (.chi (j + 1) D.R.m) M 1)⁻¹.1 (G.toPair (.chi (j + 1) D.R.m) M 1)⁻¹.2 x =
      mt (G.V (.grid (j + 1) D.R.m)) M⁻¹ * (x : Matrix _ _ (AE D)) := by
  simp only [actO, GridData.toPair, Prod.fst_inv, Prod.snd_inv, inv_inv, map_one, inv_one]
  rw [show mt (G.pS (.chi (j + 1) D.R.m : Pair T)) 1 = 1 from rfl, Matrix.mul_one]

theorem sub_mul_cast {K : Type} [Field K] {a b a' b' : ℕ} (ha : a' = a) (hb : b' = b) (P : GL (Fin a) K) (Q : GL (Fin b) K)
    (Y : Matrix (Fin a) (Fin b) K) (X : Matrix (Fin b) (Fin b) K) :
    ((P⁻¹).val * (Y * X) * Q.val).submatrix (Fin.cast ha) (Fin.cast hb) =
      ((P⁻¹).val * Y * Q.val).submatrix (Fin.cast ha) (Fin.cast hb) * ((Q⁻¹).val * X * Q.val).submatrix (Fin.cast hb) (Fin.cast hb) := by
  rw [← Matrix.submatrix_mul _ _ (Fin.cast ha) (Fin.cast hb) (Fin.cast hb) (finCongr hb).bijective]
  congr 1
  simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]

theorem mul_sub_cast {K : Type} [Field K] {a b a' b' : ℕ} (ha : a' = a) (hb : b' = b) (P : GL (Fin a) K) (Q : GL (Fin b) K)
    (Y : Matrix (Fin a) (Fin b) K) (X : Matrix (Fin a) (Fin a) K) :
    ((P⁻¹).val * (X * Y) * Q.val).submatrix (Fin.cast ha) (Fin.cast hb) =
      ((P⁻¹).val * X * P.val).submatrix (Fin.cast ha) (Fin.cast ha) * ((P⁻¹).val * Y * Q.val).submatrix (Fin.cast ha) (Fin.cast hb) := by
  rw [← Matrix.submatrix_mul _ _ (Fin.cast ha) (Fin.cast ha) (Fin.cast hb) (finCongr ha).bijective]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (P.val), Units.mul_inv, Matrix.one_mul]

theorem inBasis_val {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) :
    (inBasis h β w x).val = (((loc w β)⁻¹).val * (loc w x).val * (loc w β).val).submatrix (Fin.cast h) (Fin.cast h) := by
  ext i j
  rw [GlobalTheory.FunObj.ProdOpen.inBasis_apply, ← map_inv, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]
  rfl

end GlobalTheory.RowMoveAt

namespace GlobalTheory.RowMoveAt

theorem rowAt_move : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)) (w : Pl D.host.E), w ∈ locPl G t →
    ∀ (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
    S.rowAt t w (Function.update (Function.update y ⟨j, by omega⟩
        (actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1 (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2
          (y ⟨j, by omega⟩) : WO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T))))
      ⟨j + 1, hj⟩ (actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1
          (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 (y ⟨j + 1, hj⟩) :
          WO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T)))) =
    Function.update (Function.update (S.rowAt t w y) j
        (S.rowAt t w y j * @id (Matrix (Fin ((locGrid G t w).rank (j + 1, (locGrid G t w).m)))
            (Fin ((locGrid G t w).rank (j + 1, (locGrid G t w).m))) (Kw w)) (inBasis (rank_vertex G t w (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w
          (finG (G.V (.grid (j + 1) D.R.m)) k)).val))
      (j + 1) (@id (Matrix (Fin ((locGrid G t w).rank (j + 1, (locGrid G t w).m)))
            (Fin ((locGrid G t w).rank (j + 1, (locGrid G t w).m))) (Kw w)) (inBasis (rank_vertex G t w (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w
          (finG (G.V (.grid (j + 1) D.R.m)) k))⁻¹.val * S.rowAt t w y (j + 1)) := by
  intro D T L sc G W U S t ht j hj k w hw y
  have hX : DefNode D.R.m (.grid (j + 1) D.R.m) := ⟨by omega, rfl⟩
  obtain ⟨P, e, he, hsupp, hoff⟩ := S.N.u_supp _ hX
  have hn := notOff S ht hw
  have hu := map_mt_eq_one hn he hoff hsupp
  have hu' := map_mt_eq_one hn he hoff (GlobalTheory.StdHalfLat.suppAt_inv' hsupp)
  have hM : (mt _ (moved S j k)).map ((cpt w).comp (toEAf D)) = (loc w (finG (G.V (.grid (j + 1) D.R.m)) k)).val := by
    rw [show mt _ (moved S j k) = mt _ (S.N.u (.grid (j + 1) D.R.m)).1⁻¹ * mt _ k.1 * mt _ (S.N.u (.grid (j + 1) D.R.m)).1 from rfl,
      Matrix.map_mul, Matrix.map_mul, hu, hu', Matrix.one_mul, Matrix.mul_one]
    rfl
  have hM' : (mt _ (moved S j k)⁻¹).map ((cpt w).comp (toEAf D)) = (loc w (finG (G.V (.grid (j + 1) D.R.m)) k⁻¹)).val := by
    rw [show mt _ (moved S j k)⁻¹ = mt _ (S.N.u (.grid (j + 1) D.R.m)).1⁻¹ * mt _ k.1⁻¹ * mt _ (S.N.u (.grid (j + 1) D.R.m)).1 from by
      rw [RowVertexInv.moved]; simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc]; rfl,
      Matrix.map_mul, Matrix.map_mul, hu, hu', Matrix.one_mul, Matrix.mul_one]
    rfl
  funext i

  by_cases h1 : i = j + 1
  · subst h1
    rw [Function.update_self]
    simp only [GridChoice.rowAt, dif_pos hj, Function.update_self, Frames.coord]
    rw [actO_chi_left, Matrix.map_mul, hM']
    erw [Matrix.transpose_transpose, Matrix.transpose_transpose, id_eq]
    rw [← map_inv (inBasis _ (S.B.β (j + 1) D.R.m) w), map_inv (finG (G.V (Node.grid (j + 1) D.R.m))) k, inBasis_val, mul_sub_cast]
    rfl
  by_cases h2 : i = j
  · subst h2
    rw [Function.update_of_ne (by omega), Function.update_self]
    have hj' : i < D.R.m := by omega
    simp only [GridChoice.rowAt, dif_pos hj', Frames.coord]
    rw [Function.update_of_ne (fun h => by simp [Fin.ext_iff] at h), Function.update_self, actO_chi_right, Matrix.map_mul, hM]
    erw [Matrix.transpose_transpose, Matrix.transpose_transpose, id_eq]
    rw [inBasis_val, sub_mul_cast]
    rfl
  · rw [Function.update_of_ne h1, Function.update_of_ne h2]
    simp only [GridChoice.rowAt]
    by_cases hi : i < D.R.m
    · rw [dif_pos hi, dif_pos hi, Function.update_of_ne (fun h => h1 (by simpa [Fin.ext_iff] using h)),
        Function.update_of_ne (fun h => h2 (by simpa [Fin.ext_iff] using h))]
    · rw [dite_eq_right hi, dite_eq_right hi]
end GlobalTheory.RowMoveAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRealPointFockVectorPositiveDefiniteDet
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRealPointFockVectorPositiveDefiniteDet
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealFockPos

variable {D : D7}

theorem det_ne_zero_of_frame {n : ℕ} {G B : Matrix (Fin n) (Fin n) ℂ} (h : Bᴴ * G * B = 1) :
    G.det ≠ 0 ∧ B.det ≠ 0 := by
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one] at h2
  exact ⟨right_ne_zero_of_mul (left_ne_zero_of_mul_eq_one h2), right_ne_zero_of_mul_eq_one h2⟩

theorem mul_eq_mul_conj {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hB : B.det ≠ 0) :
    A * B = B * (B⁻¹ * A * B) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit hB), Matrix.one_mul]

theorem scalar_identity (G H : ℂ) (hG : G ≠ 0) (hH : H ≠ 0) (e₁ e₂ : ℤ) (nS nT : ℕ) :
    (G ^ (-e₂ - (nT : ℤ)))⁻¹ * H ^ (e₁ - (nS : ℤ)) * (H ^ nS * G⁻¹ ^ nT) = G ^ e₂ * H ^ e₁ := by
  rw [inv_pow, ← zpow_natCast H, ← zpow_natCast G, ← zpow_neg G, ← zpow_neg G]
  calc G ^ (-(-e₂ - (nT : ℤ))) * H ^ (e₁ - (nS : ℤ)) * (H ^ (nS : ℤ) * G ^ (-(nT : ℤ)))
      = G ^ (-(-e₂ - (nT : ℤ))) * G ^ (-(nT : ℤ)) * (H ^ (e₁ - (nS : ℤ)) * H ^ (nS : ℤ)) := by ring
    _ = G ^ (-(-e₂ - (nT : ℤ)) + -(nT : ℤ)) * H ^ (e₁ - (nS : ℤ) + (nS : ℤ)) := by
      rw [← zpow_add₀ hG, ← zpow_add₀ hH]
    _ = G ^ e₂ * H ^ e₁ := by congr 2 <;> ring

theorem om_pureTensorO_pos : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) → (∀ τ, (BT τ)ᴴ * gramAt D T τ * BT τ = 1) → ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D χS τ (a τ)) → (∀ τ, HasInfExp D χT τ (b τ)) → ∀ (e₁ e₂ : D.what₂.Tau → ℤ), (∀ τ, (e₁ τ : ℚ) = a τ + (S.rank : ℚ) / 2) → (∀ τ, (e₂ τ : ℚ) = -(b τ + (T.rank : ℚ) / 2)) → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, om (g, h) (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT f P) = (∏ τ, (compAt θ τ (Formalism.L2.Theta.mt S g)).det ^ e₂ τ * (compAt θ τ (Formalism.L2.Theta.mt T h)).det ^ e₁ τ) • pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT f (GlobalTheory.CompactHowe.substF (fun τ => (BT τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ) (fun τ => (((BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ)⁻¹)ᵀ) P) := by
  intro D ψ θ S T χS χT om hom hθ BS BT hBS hBT a b ha hb e₁ e₂ he₁ he₂ f hf hv g hg h hh P
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have hψ := hom.std
  have dS : ∀ τ, (gramAt D S τ).det ≠ 0 ∧ (BS τ).det ≠ 0 := fun τ => det_ne_zero_of_frame (hBS τ)
  have dT : ∀ τ, (gramAt D T τ).det ≠ 0 ∧ (BT τ).det ≠ 0 := fun τ => det_ne_zero_of_frame (hBT τ)
  have cS : ∀ τ, IsCartanInv (gramAt D S τ) 1 := fun τ => GlobalTheory.FockCompactAction.isCartanInv_one (hBS τ)
  have cT : ∀ τ, IsCartanInv (gramAt D T τ) 1 := fun τ => GlobalTheory.FockCompactAction.isCartanInv_one (hBT τ)
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ S (fun τ => (dS τ).1) g hg
  obtain ⟨y, hy, hyv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ T (fun τ => (dT τ).1) h hh
  have hvac := GlobalTheory.WeilVacChar.vacuum_character D ψ hψ S T θ hθ χS χT om η hη hom (fun _ => 1) (fun _ => 1)
    cS cT g hg h hh (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) x y hx hy f hf hv
  have expT : ∀ τ, HasInfExp D (χT * (η ^ T.rank)⁻¹) τ ((-e₂ τ - T.rank : ℤ) : ℚ) := fun τ => by
    have h1 := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist (hb τ) (hη.2.2.2 τ) T.rank
    convert h1 using 1
    push_cast; rw [he₂]; ring
  have expS : ∀ τ, HasInfExp D (χS * (η ^ S.rank)⁻¹) τ ((e₁ τ - S.rank : ℤ) : ℚ) := fun τ => by
    have h1 := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist (ha τ) (hη.2.2.2 τ) S.rank
    convert h1 using 1
    push_cast; rw [he₁]; ring
  have vx := hxv _ (fun τ => -e₂ τ - T.rank) expT
  have vy := hyv _ (fun τ => e₁ τ - S.rank) expS
  have hmain := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hom hθ (fun _ => 1) (fun _ => 1) BS
    (fun τ => compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ) (fun _ => 1) (fun _ => 1) BT
    (fun τ => compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ) g h (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => rfl) (fun τ => rfl) f hf P).2
  have fS : (fun τ => compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ) =
      fun τ => BS τ * ((BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ) :=
    funext fun τ => mul_eq_mul_conj _ _ (dS τ).2
  have fT : (fun τ => compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ) =
      fun τ => BT τ * ((BT τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ) :=
    funext fun τ => mul_eq_mul_conj _ _ (dT τ).2
  rw [hmain, hvac, GlobalTheory.FiniteFock.pureTensorO_smul, fS, fT,
    GlobalTheory.FockBaseChange.pureTensorO_subst D ψ θ S T hψ hθ BS _ BT _ f hf P]
  congr 1
  rw [Circle.coe_mul, Circle.coe_inv, vx, vy, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have inv := congrArg Matrix.det (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ g)
  rw [Matrix.det_mul, Matrix.det_one] at inv
  have g0 := left_ne_zero_of_mul_eq_one inv
  have inv' := congrArg Matrix.det (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ h)
  rw [Matrix.det_mul, Matrix.det_one] at inv'
  have h0 := left_ne_zero_of_mul_eq_one inv'
  rw [GlobalTheory.KJReal.detPlus_one_one, eq_inv_of_mul_eq_one_right inv]
  exact scalar_identity _ _ g0 h0 (e₁ τ) (e₂ τ) S.rank T.rank

end GlobalTheory.RealFockPos

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRealPointFockVectorPositiveDefiniteDetStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_realPoint_fockVector_positiveDefinite_det : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) → (∀ τ, (BT τ)ᴴ * gramAt D T τ * BT τ = 1) → ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D χS τ (a τ)) → (∀ τ, HasInfExp D χT τ (b τ)) → ∀ (e₁ e₂ : D.what₂.Tau → ℤ), (∀ τ, (e₁ τ : ℚ) = a τ + (S.rank : ℚ) / 2) → (∀ τ, (e₂ τ : ℚ) = -(b τ + (T.rank : ℚ) / 2)) → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, om (g, h) (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT f P) = (∏ τ, (compAt θ τ (Formalism.L2.Theta.mt S g)).det ^ e₂ τ * (compAt θ τ (Formalism.L2.Theta.mt T h)).det ^ e₁ τ) • pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT f (GlobalTheory.CompactHowe.substF (fun τ => (BT τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ) (fun τ => (((BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ)⁻¹)ᵀ) P) := by
  first | exact @GlobalTheory.RealFockPos.om_pureTensorO_pos | exact GlobalTheory.RealFockPos.om_pureTensorO_pos | (intros; apply GlobalTheory.RealFockPos.om_pureTensorO_pos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexDerivativeAdjointOfSkewFormStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexDerivativeAdjointOfSkewForm
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

namespace GlobalTheory.RderCAdjoint

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

theorem Rder_neg_dir (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    Rder θ V τ (-X) φ = -Rder θ V τ X φ := by
  funext g
  have := deriv_comp_neg (fun t : ℝ => φ (g * oneP θ V τ X t)) 0
  simpa only [Rder, oneP, smul_neg, neg_smul, neg_zero, Pi.neg_apply] using this

theorem conjAt_adjoint (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    conjAt V τ ((gramAt D V τ)⁻¹ * Zᴴ * gramAt D V τ) = -Z := by
  have hu := GlobalTheory.SmoothAutCheck.gramAt_unit V τ
  have hH := GlobalTheory.SmoothAutCheck.gramAt_herm V τ
  unfold conjAt
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hH,
    ← mul_assoc, nonsing_inv_mul _ hu, one_mul, mul_assoc, nonsing_inv_mul _ hu, mul_one]

theorem RderC_adjoint_eq (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    RderC θ V τ ((gramAt D V τ)⁻¹ * Zᴴ * gramAt D V τ) φ =
      -Rder θ V τ ((1 / 2 : ℂ) • (Z + conjAt V τ Z)) φ +
        Complex.I • Rder θ V τ ((1 / (2 * Complex.I)) • (Z - conjAt V τ Z)) φ := by
  unfold RderC
  rw [conjAt_adjoint]
  have hW : (gramAt D V τ)⁻¹ * Zᴴ * gramAt D V τ = -conjAt V τ Z := by simp [conjAt]
  rw [hW, ← Rder_neg_dir, ← smul_neg, neg_add, add_comm (-Z), neg_sub_neg]

theorem rderC_adjoint : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau)
    (A : Submodule ℂ (GA D V → ℂ)) (b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ),
    (∀ X ∈ lieAt V τ, ∀ x ∈ A, ∀ y ∈ A, b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) →
    ∀ (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ), ∀ x ∈ A, ∀ y ∈ A,
      b x (RderC θ V τ Z y) = b (RderC θ V τ ((gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ) x) y := by
  intro D θ V τ A b hb Z x hx y hy
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  rw [RderC_adjoint_eq]
  unfold RderC
  rw [map_add (f := _), map_smul, hb _ h1 x hx y hy, hb _ h2 x hx y hy, map_add (f := _), map_neg, map_smulₛₗ]
  simp

end GlobalTheory.RderCAdjoint

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexDerivative_adjoint_of_skew_form : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau)
    (A : Submodule ℂ (GA D V → ℂ)) (b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ),
    (∀ X ∈ lieAt V τ, ∀ x ∈ A, ∀ y ∈ A, b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) →
    ∀ (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ), ∀ x ∈ A, ∀ y ∈ A,
      b x (RderC θ V τ Z y) = b (RderC θ V τ ((gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ) x) y := by
  first | exact @GlobalTheory.RderCAdjoint.rderC_adjoint | exact GlobalTheory.RderCAdjoint.rderC_adjoint | (intros; apply GlobalTheory.RderCAdjoint.rderC_adjoint <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsJointEigenDecompositionCommutingSymmetricO
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsJointEigenDecompositionCommutingSymmetricO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory.JointSpectral

theorem exists_finset_joint_eigen : ∀ {E ι : Type} [AddCommGroup E] [Module ℂ E] (F : ι → E → E) (Z : Submodule ℂ E), FiniteDimensional ℂ Z →
    (∀ i, ∀ x ∈ Z, F i x ∈ Z) → (∀ i, ∀ x ∈ Z, ∀ y ∈ Z, F i (x + y) = F i x + F i y) →
    (∀ i (a : ℂ), ∀ x ∈ Z, F i (a • x) = a • F i x) → (∀ i j, ∀ x ∈ Z, F i (F j x) = F j (F i x)) →
    ∀ b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ, (∀ x ∈ Z, x ≠ 0 → 0 < (b x x).re) → (∀ x ∈ Z, ∀ y ∈ Z, star (b x y) = b y x) →
    (∀ i, ∀ x ∈ Z, ∀ y ∈ Z, b x (F i y) = b (F i x) y) →
    ∃ C : Finset (ι → ℂ), ∀ x ∈ Z, x ∈ ⨆ c ∈ C, Submodule.span ℂ {h | h ∈ Z ∧ ∀ i, F i h = c i • h} := by
  intro E ι _ _ F Z hfd hmap hadd hsmul hcomm b hpos hsymm hadj
  let T : ι → Module.End ℂ Z := fun i =>
    { toFun := fun x => ⟨F i x, hmap i x x.2⟩
      map_add' := fun x y => Subtype.ext (hadd i x x.2 y y.2)
      map_smul' := fun a x => Subtype.ext (hsmul i a x x.2) }
  let core : InnerProductSpace.Core ℂ Z :=
    { inner := fun x y => b x y
      conj_inner_symm := fun x y => by
        show star (b (y : E) x) = b x y
        exact hsymm y y.2 x x.2
      re_inner_nonneg := fun x => by
        show 0 ≤ (b (x : E) x).re
        by_cases hx : (x : E) = 0
        · rw [hx]; simp
        · exact (hpos x x.2 hx).le
      add_left := fun x y z => by
        show b ((x : E) + y) z = b x z + b y z
        rw [map_add (f := _), LinearMap.add_apply]
      smul_left := fun x y r => by
        show b (r • (x : E)) y = starRingEnd ℂ r * b x y
        rw [LinearMap.map_smulₛₗ₂, smul_eq_mul]
      definite := fun x hx => by
        by_contra h0
        have h1 := hpos x x.2 (fun e => h0 (Subtype.ext e))
        have h2 : b (x : E) x = 0 := hx
        rw [h2] at h1
        simp at h1 }
  letI : NormedAddCommGroup Z := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (cd := core)
  letI : InnerProductSpace ℂ Z := InnerProductSpace.ofCore core.toCore
  have hT : ∀ i, (T i).IsSymmetric := fun i x y => (hadj i x x.2 y y.2).symm
  have hC : Pairwise (Function.onFun Commute T) := fun i j _ =>
    LinearMap.ext fun x => Subtype.ext (hcomm i j x x.2)
  have key := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hT hC
  have htop : IsCompactElement (⊤ : Submodule ℂ Z) :=
    (Submodule.fg_iff_compact _).1 (Module.finite_def.1 hfd)
  obtain ⟨s, hs⟩ := htop.exists_finset_of_le_iSup
    (fun χ : ι → ℂ => ⨅ i, Module.End.eigenspace (T i) (χ i)) key.ge
  have hle : (⊤ : Submodule ℂ Z) ≤
      (⨆ c ∈ s, Submodule.span ℂ {h | h ∈ Z ∧ ∀ i, F i h = c i • h}).comap Z.subtype := by
    refine hs.trans (iSup₂_le fun c hc y hy => ?_)
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hy
    refine Submodule.mem_comap.2 ((le_iSup₂ (f := fun c (_ : c ∈ s) =>
      Submodule.span ℂ {h | h ∈ Z ∧ ∀ i, F i h = c i • h}) c hc) (Submodule.subset_span ⟨y.2, fun i => ?_⟩))
    exact congrArg Subtype.val (hy i)
  exact ⟨s, fun x hx => hle (x := ⟨x, hx⟩) Submodule.mem_top⟩

end GlobalTheory.JointSpectral
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsJointEigenDecompositionCommutingSymmetricOStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_jointEigenDecomposition_commuting_symmetricOps : ∀ {E ι : Type} [AddCommGroup E] [Module ℂ E] (F : ι → E → E) (Z : Submodule ℂ E), FiniteDimensional ℂ Z →
    (∀ i, ∀ x ∈ Z, F i x ∈ Z) → (∀ i, ∀ x ∈ Z, ∀ y ∈ Z, F i (x + y) = F i x + F i y) →
    (∀ i (a : ℂ), ∀ x ∈ Z, F i (a • x) = a • F i x) → (∀ i j, ∀ x ∈ Z, F i (F j x) = F j (F i x)) →
    ∀ b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ, (∀ x ∈ Z, x ≠ 0 → 0 < (b x x).re) → (∀ x ∈ Z, ∀ y ∈ Z, star (b x y) = b y x) →
    (∀ i, ∀ x ∈ Z, ∀ y ∈ Z, b x (F i y) = b (F i x) y) →
    ∃ C : Finset (ι → ℂ), ∀ x ∈ Z, x ∈ ⨆ c ∈ C, Submodule.span ℂ {h | h ∈ Z ∧ ∀ i, F i h = c i • h} := by
  first | exact @GlobalTheory.JointSpectral.exists_finset_joint_eigen | exact GlobalTheory.JointSpectral.exists_finset_joint_eigen | (intros; apply GlobalTheory.JointSpectral.exists_finset_joint_eigen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandInvariantMemIntertwinedTypeSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandInvariantMemIntertwinedTypeSpan
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory.KTypeGelf

theorem gelf_mem_typeSpan : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ → ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ →
    ∀ (Y₀ : Submodule ℂ (GA D V → ℂ)) (τ : D.what₂.Tau) (k : ℕ),
    ∀ f ∈ GlobalTheory.KTypeProj.typeSpan (GlobalTheory.KTypeProj.rhoK θ M) Y₀ (GlobalTheory.CuspGK.gkGen θ M ψ),
      gelf θ V τ k f ∈ GlobalTheory.KTypeProj.typeSpan (GlobalTheory.KTypeProj.rhoK θ M) Y₀ (GlobalTheory.CuspGK.gkGen θ M ψ) := by
  intro D θ V S M hθ ψ hψ Y₀ τ k
  set G := GlobalTheory.CuspGK.gkGen θ M ψ with hGdef
  set ρ := GlobalTheory.KTypeProj.rhoK θ M with hρ
  have hGsm : ∀ f ∈ G, f ∈ GlobalTheory.Mem.AutSpace.SmFun θ V := fun f hf =>
    fun k τs Xs h g => (GlobalTheory.KTypeAdm.isAutFunSm_of_mem_gkGen θ M hθ hψ f hf).smooth k τs Xs h g
  have hL := GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) τ k

  let g0 : GlobalTheory.Mem.AutSpace.SmFun θ V →ₗ[ℂ] (GA D V → ℂ) :=
    { toFun := fun φ => gelf θ V τ k φ
      map_add' := fun φ ψ' => hL.add _ φ.2 _ ψ'.2
      map_smul' := fun c φ => hL.smul c φ }
  obtain ⟨L, hLe⟩ := LinearMap.exists_extend g0
  have hLa : ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, L φ = gelf θ V τ k φ := fun φ hφ => by
    have := congrArg (fun F => F ⟨φ, hφ⟩) hLe
    simpa [g0] using this
  have hgel0 : gelf θ V τ k 0 = 0 := by
    have := hL.smul 0 0
    simpa using this
  let Q : Submodule ℂ (GA D V → ℂ) :=
    { carrier := {f | f ∈ G ∧ gelf θ V τ k f ∈ GlobalTheory.KTypeProj.typeSpan ρ Y₀ G}
      add_mem' := fun {a b} ha hb => by
        refine ⟨G.add_mem ha.1 hb.1, ?_⟩
        rw [hL.add a (hGsm a ha.1) b (hGsm b hb.1)]
        exact Submodule.add_mem _ ha.2 hb.2
      zero_mem' := ⟨G.zero_mem, by rw [hgel0]; exact Submodule.zero_mem _⟩
      smul_mem' := fun c f hf => by
        refine ⟨G.smul_mem c hf.1, ?_⟩
        rw [hL.smul c f]
        exact Submodule.smul_mem _ c hf.2 }
  have hle : GlobalTheory.KTypeProj.typeSpan ρ Y₀ G ≤ Q := by
    refine iSup₂_le fun T hT => ?_
    rintro _ ⟨w, hw, rfl⟩
    have hTw : T w ∈ G := hT.1 ⟨w, hw, rfl⟩
    refine ⟨hTw, ?_⟩
    have hmap : Y₀.map (L ∘ₗ T) ≤ G := by
      rintro _ ⟨v, hv, rfl⟩
      have hTv : T v ∈ G := hT.1 ⟨v, hv, rfl⟩
      show L (T v) ∈ G
      rw [hLa _ (hGsm _ hTv)]
      exact GlobalTheory.KTypeAdm.gelf_mem_of_isGKSub θ M (GlobalTheory.CuspGK.isGKSub_gkGen θ M ψ) τ k _ hTv
    have hcomm : ∀ i, ∀ v ∈ Y₀, (L ∘ₗ T) (ρ i v) = ρ i ((L ∘ₗ T) v) := by
      intro i v hv
      have hTv : T v ∈ G := hT.1 ⟨v, hv, rfl⟩
      have hs := hGsm _ hTv
      simp only [LinearMap.comp_apply]
      rw [hT.2 i v hv, hLa _ (hs), hρ, GlobalTheory.KTypeProj.rhoK, GlobalTheory.KTypeProj.rTrL_apply, GlobalTheory.KTypeProj.rTrL_apply,
        hLa _ (GlobalTheory.RegSch.CentreRight.rTr_mem_all hθ _ hs), GlobalTheory.RegSch.CentreRight.gelf_rTr_all hθ _ τ k hs]
    have := GlobalTheory.KTypeProj.map_le_typeSpan ρ (L ∘ₗ T) hmap hcomm ⟨w, hw, rfl⟩
    simpa [hLa _ (hGsm _ hTw)] using this
  intro f hf
  exact (hle hf).2

end GlobalTheory.KTypeGelf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandInvariantMemIntertwinedTypeSpanStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfandInvariant_mem_intertwinedTypeSpan : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ → ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ →
    ∀ (Y₀ : Submodule ℂ (GA D V → ℂ)) (τ : D.what₂.Tau) (k : ℕ),
    ∀ f ∈ GlobalTheory.KTypeProj.typeSpan (GlobalTheory.KTypeProj.rhoK θ M) Y₀ (GlobalTheory.CuspGK.gkGen θ M ψ),
      gelf θ V τ k f ∈ GlobalTheory.KTypeProj.typeSpan (GlobalTheory.KTypeProj.rhoK θ M) Y₀ (GlobalTheory.CuspGK.gkGen θ M ψ) := by
  first | exact @GlobalTheory.KTypeGelf.gelf_mem_typeSpan | exact GlobalTheory.KTypeGelf.gelf_mem_typeSpan | (intros; apply GlobalTheory.KTypeGelf.gelf_mem_typeSpan <;> assumption)
end
end
