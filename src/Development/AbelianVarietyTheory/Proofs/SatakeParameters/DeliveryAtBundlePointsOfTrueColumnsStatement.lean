module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivRows3GIff
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimePeriodRowOfConstructedPointChains
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RamifiedColumnsTrueColumnsEqConcrete
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsTrueColsRowInt
public import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.NumbersP
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointsEqualEigenMatch

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DisjointReferenceTwistPrimes
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Core.Rk
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Rk.RowRead

theorem map_mem_span_range {K L M N J : Type*} [Semiring K] [Semiring L] [AddCommMonoid M] [AddCommMonoid N] [Module K M]
    [Module L N] {σ : K →+* L} (f : M →ₛₗ[σ] N) {φ : J → M} (h : Submodule.span K (Set.range φ) = ⊤) (z : M) :
    f z ∈ Submodule.span L (Set.range fun a => f (φ a)) := by
  have hz : z ∈ Submodule.span K (Set.range φ) := h ▸ Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact Submodule.subset_span ⟨a, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

section G
open GlobalTheory.PeriodOnStep
variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) {I : ChainIn X.E X.K X.Tau R} (b0 : (I.S R.m).β)
  (til : ∀ b, (stepX Ch sel mu P).D b → (I.S R.m).D b0) (ext : ∀ b, (stepX Ch sel mu P).G b →* (I.S R.m).G b0)
  (tz : X.E) (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K))) (σ : X.K →+* ℂ)

def valMt (H : ∀ b, Subgroup ((stepX Ch sel mu P).G b)) :
    (perOn W Ch sel mu P b0 til ext tz H).Mt X.emb σ →ₗ[ℂ] ((stepX Ch sel mu P).D () → Pol ℂ X.Tau (R.N R.m - 1)) where
  toFun F p := F.1 () p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def valMtP : MtP W Ch sel mu P σ →ₗ[ℂ] ((stepX Ch sel mu P).D () → Pol ℂ X.Tau (R.N R.m - 1)) where
  toFun G p := G.1 (toRow sel mu p.1.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem valMtP_injective : Function.Injective (valMtP W Ch sel mu P σ) := by
  intro G G' h
  refine Subtype.ext (funext fun d => ?_)
  obtain ⟨p, rfl⟩ := toRow_surjective sel mu d
  exact congrFun h (trivPt X _ _ _ _ p)

theorem rowEmb_linearIndependent (H : ∀ b, Subgroup ((stepX Ch sel mu P).G b)) {J : Type} {φ : J → MtildeV W Ch sel mu P}
    (h : LinearIndependent X.K φ) :
    LinearIndependent ℂ fun a => rowEmb W Ch sel mu P b0 til ext tz H hd σ (φ a) :=
  LinearIndependent.of_comp (valMt W Ch sel mu P b0 til ext tz σ H)
    ((toMtilde_linearIndependent W Ch sel mu P σ h).map' (valMtP W Ch sel mu P σ)
      (LinearMap.ker_eq_bot.2 (valMtP_injective W Ch sel mu P σ)))

theorem rowEmb_span (hX : X.Ok) {J : Type} {φ : J → MtildeV W Ch sel mu P} (h : Submodule.span X.K (Set.range φ) = ⊤) :
    Submodule.span ℂ (Set.range fun a => rowEmb W Ch sel mu P b0 til ext tz (fun _ => ⊤) hd σ (φ a)) = ⊤ :=
  GlobalTheory.PerQ.RowIntModel.eq_top_of_rowEmb_mem W Ch sel mu P b0 til ext tz hd σ hX _ fun z _ =>
    map_mem_span_range (rowEmb W Ch sel mu P b0 til ext tz (fun _ => ⊤) hd σ) h z

end G

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

end GlobalTheory.Core.Rk.RowRead

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConstructionAtBundlePointsOfTrueColumns
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodValuationsTypePrimesOfJetTableSplitPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConcreteChainAgreesAtTupleOfNormalisedRows
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodRelationsTrueColumnsAtTuple
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowFormsCoefficientFieldFormComplexPeriodRows
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowFormsCoefficientFieldFormComplexPeriodRows
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG

namespace GlobalTheory.Mem.Col2.KerRat

theorem rowForm_baseChange : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : GlobalTheory.Mem.Col2.TC B X) (h : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι), (∀ s : Finset (Formalism.L2.Col.MtildeV (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps), LinearIndependent B.LL (fun x : s => x.1) → LinearIndependent ℂ (fun x : s => GlobalTheory.Mem.Col2.KerRat.rowForm I l h u a x.1)) ∧ Submodule.span ℂ (Set.range (GlobalTheory.Mem.Col2.KerRat.rowForm I l h u a)) = ⊤ := by
  intro B X I h l u a
  refine ⟨fun s hs => ?_, ?_⟩
  · exact GlobalTheory.Core.Rk.RowRead.rowEmb_linearIndependent (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps (I := I.chIn u a)
      (I.perIn u a).b0 (I.perIn u a).til (I.perIn u a).ext (I.perIn u a).tz (tilOk I h u a).2.2 B.embLL (I.perIn u a).H
      (φ := fun x : s => x.1) hs
  · have key := GlobalTheory.Core.Rk.RowRead.rowEmb_span (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps (I := I.chIn u a)
      (I.perIn u a).b0 (I.perIn u a).til (I.perIn u a).ext (I.perIn u a).tz (tilOk I h u a).2.2 B.embLL
      (GlobalTheory.Mem.FieldsLaws.fields_ok B) (φ := id) (by rw [Set.range_id, Submodule.span_univ])
    exact key

end GlobalTheory.Mem.Col2.KerRat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowFormsCoefficientFieldFormComplexPeriodRowsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowForms_coefficientField_form_complexPeriodRows : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : GlobalTheory.Mem.Col2.TC B X) (h : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι), (∀ s : Finset (Formalism.L2.Col.MtildeV (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps), LinearIndependent B.LL (fun x : s => x.1) → LinearIndependent ℂ (fun x : s => GlobalTheory.Mem.Col2.KerRat.rowForm I l h u a x.1)) ∧ Submodule.span ℂ (Set.range (GlobalTheory.Mem.Col2.KerRat.rowForm I l h u a)) = ⊤ := by
  first | exact @GlobalTheory.Mem.Col2.KerRat.rowForm_baseChange | exact GlobalTheory.Mem.Col2.KerRat.rowForm_baseChange | (intros; apply GlobalTheory.Mem.Col2.KerRat.rowForm_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodRelationsTrueColumnsAtTuple
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG

open Formalism.L2.Col GlobalTheory.ColPeriodCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound GlobalTheory.Mem GlobalTheory.Mem.Col2
namespace GlobalTheory.TiesTrue

def baseCast {D : D7} {cc cc' : Ideal (𝓞 D.host.K)} (e : cc = cc') {δ : ℂ} (Bs : Formalism.L2.Ker.Base D cc δ) :
    Formalism.L2.Ker.Base D cc' δ := e ▸ Bs

theorem ambOf_baseCast {D : D7} {X : Fields} (s : Seam D X) {cc cc' : Ideal (𝓞 D.host.K)} (e : cc = cc') {δ : ℂ}
    (Bs : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) :
    ambOf s (baseCast e Bs) χ cD = ambOf s Bs χ cD := by
  subst e; rfl

def exOf {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : GlobalTheory.Mem.Col2.TC B X} {l : I.Laws}
    {Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)} (EX : ErrX (I.rec7 l Z)) (h1 : EX.piG = X.piG) (h2 : EX.piT = X.piT) :
    ErrX (I.rec7 l Z) :=
  ⟨X.piG, h1 ▸ EX.piG_K, h1 ▸ EX.piG_norm, X.piT, h2 ▸ EX.piT_K, h2 ▸ EX.piT_norm, h2 ▸ EX.piT_cong, EX.vPl, EX.vPl_inj,
    EX.norm_mem_place_ideal⟩

theorem exOf_eq {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : GlobalTheory.Mem.Col2.TC B X} {l : I.Laws}
    {Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)} (EX : ErrX (I.rec7 l Z)) (h1 : EX.piG = X.piG) (h2 : EX.piT = X.piT) :
    exOf EX h1 h2 = EX := by
  obtain ⟨piG, _, _, piT, _, _, _, _, _, _⟩ := EX
  obtain rfl : piG = X.piG := h1
  obtain rfl : piT = X.piT := h2
  rfl

theorem badS_subset {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : GlobalTheory.Mem.Col2.TC B X} (h : I.Ok) (l : I.Laws)
    (Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)) : badS (I.rec7 l Z) ⊆ I.S := by
  rintro p (hp | ⟨u, rfl⟩ | hp)
  · rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact h.two_q_d_mem.1
    · exact h.two_q_d_mem.2.1
    · exact h.two_q_d_mem.2.2
    · exact h.g_mem 0
    · exact h.g_mem 1
  · exact h.T_mem u
  · exact h.small_mem (Finset.mem_coe.1 hp)

theorem mem_tupGrp_of_subset {F E L : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field L]
    {S S' : Set ℕ} (hS : S' ⊆ S) {x : Chr F E L} (hx : x ∈ tupGrp F E L S) : x ∈ tupGrp F E L S' := by
  obtain ⟨h1, h4⟩ := Subgroup.mem_inf.1 hx
  refine Subgroup.mem_inf.2 ⟨h1, Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => ?_⟩
  exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h4 v) fun hg => hv ⟨hg.1, hg.2.1, fun hm => hg.2.2 (hS hm)⟩

section Gen

variable {D : D7} {EX : ErrX D} (Ch : Chars (recFields D) (recPrimes EX) D.R.m)
  (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))

def TwistTieS {S : Set ℕ} (Dx : DivX D) (μ : D.what₂.Tup) (ξ : Tup (recFields D).F (recFields D).E (recFields D).K S) : Prop :=
  ((Dx.Qp μ : Set ℕ) = QprimeN (ξ : Chr (recFields D).F (recFields D).E (recFields D).K)) ∧
    (μ = D.what₂.mu0 → (ξ : Chr (recFields D).F (recFields D).E (recFields D).K) = 1)

def FieldTieS (A : Amb (recFields D)) {S : Set ℕ} (ξ : Tup (recFields D).F (recFields D).E (recFields D).K S)
    (cst : LocCst (recFields D) (rowSG (recPrimes EX) sel ξ)) (u : D.what₂.Word) : Prop :=
  ∀ i < D.R.m, JetsRatDeg A (D.R.N i) (D.R.N (i + 1)) (Sall (Pr := recPrimes EX) sel ξ u)
    (cAof sel ξ cst * cBof sel ξ cst u) (fun τ => ∑ a, ((recWts EX).nuW u (i + 1) τ).w a)

def RowTieS (μ : D.what₂.Tup) {S : Set ℕ} (ξ : Tup (recFields D).F (recFields D).E (recFields D).K S)
    (jA : MtildeV (recWts EX) Ch sel ξ (rPsymF Ch) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ) : Prop :=
  (∀ s : Finset (MtildeV (recWts EX) Ch sel ξ (rPsymF Ch)),
      LinearIndependent D.what₂.LL (fun x : s => (x : MtildeV (recWts EX) Ch sel ξ (rPsymF Ch))) →
      LinearIndependent ℂ (fun x : s => jA x)) ∧
    Submodule.span ℂ (Set.range jA) = ⊤ ∧
    (∀ v ∈ (D.what₂.Mtilde μ).gen, v ∈ Set.range jA) ∧
    ∀ x, x ∈ MtildeL (recWts EX) Ch sel ξ (rPsymF Ch) ↔ ∃ c : D.what₂.Amb μ → 𝓞 D.what₂.LL,
      jA x = ∑ v ∈ (D.what₂.Mtilde μ).gen, D.what₂.embLL ((c v : 𝓞 D.what₂.LL) : D.what₂.LL) • v

def PerTieS (u : D.what₂.Word) (μ : D.what₂.Tup) {S : Set ℕ} (ξ : Tup (recFields D).F (recFields D).E (recFields D).K S)
    (hP : (mtildeGSD (recWts EX) Ch sel ξ (rPsymF Ch)).Ok)
    (col : MfV (recWts EX) Ch u →ₗ[D.what₂.LL] (evGSD (recWts EX) Ch sel ξ (rPsymF Ch) u).EqFun)
    (eM : (D.div.Nu u).V ≃ₗ[D.what₂.LL] MramV (recWts EX) Ch u)
    (jA : MtildeV (recWts EX) Ch sel ξ (rPsymF Ch) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ) : Prop :=
  ∀ φ x, D.what₂.perCol u μ (D.jN u φ) (jA x) =
    D.what₂.embLL (PtilE (recWts EX) Ch sel ξ (rPsymF Ch) hP u (col (eM φ : MfV (recWts EX) Ch u)) x)

def ChainTieS (Dx : DivX D) (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E) (A : Amb (recFields D))
    (u : D.what₂.Word) (μ : D.what₂.Tup) {S : Set ℕ} (ξ : Tup (recFields D).F (recFields D).E (recFields D).K S) : Prop :=
  ∃ (cst : LocCst (recFields D) (rowSG (recPrimes EX) sel ξ))
    (I : ChIdx (recFields D) (recPrimes EX) D.R (QE sel (ξ : Chr (recFields D).F (recFields D).E (recFields D).K)))
    (hI : I.Ok Ch sel ξ cst (recGlob D mu0) (D.R.m - 2))
    (b : I.β (D.R.m - 2 + 1)) (hY : YbHyp (R := D.R) sel ξ cst I u (D.R.m - 2) b)
    (hK : KerEquivC (recWts EX) Ch sel ξ cst I A u (D.R.m - 2) b hY (rPsymF Ch))
    (hF : ∀ j, (chF (recWts EX) sel ξ I u j).Ok)
    (hP : (mtildeGSD (recWts EX) Ch sel ξ (rPsymF Ch)).Ok)
    (eM : (D.div.Nu u).V ≃ₗ[D.what₂.LL] MramV (recWts EX) Ch u)
    (jA : MtildeV (recWts EX) Ch sel ξ (rPsymF Ch) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ),
    cst.sharp = true ∧ TwistTieS Dx μ ξ ∧ FieldTieS sel A ξ cst u ∧ ColTie Ch u eM ∧ RowTieS Ch sel μ ξ jA ∧
      PerTieS Ch sel u μ ξ hP (colMu (recWts EX) Ch sel ξ cst I A u (D.R.m - 2) b hY (rPsymF Ch) hK hF hI) eM jA

theorem chainPeriodRelation_read_for_character_avoiding_primes (Dx : DivX D) (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E) (A : Amb (recFields D))
    (u : D.what₂.Word) (μ : D.what₂.Tup) {S : Set ℕ} (χ : Chr (recFields D).F (recFields D).E (recFields D).K)
    (h : IsTwist (recFields D).F (recFields D).E (recFields D).K S χ)
    (h' : IsTwist (recFields D).F (recFields D).E (recFields D).K (badS D) χ)
    (H : ChainTieS Ch sel Dx mu0 A u μ (@Subtype.mk _ (IsTwist _ _ _ S) χ h)) : ChainTie Ch sel Dx mu0 A u μ := by
  obtain ⟨cst, I, hI, b, hY, hK, hF, hP, eM, jA, h1, h2, h3, h4, h5, h6⟩ := H
  exact ⟨@Subtype.mk _ (IsTwist _ _ _ (badS D)) χ h', cst, I, { hI with }, b, ⟨hY.fin⟩, hK, hF, hP, eM, jA, h1,
    ⟨h2.1, fun e => Subtype.ext (h2.2 e)⟩, h3, h4, h5, h6⟩

theorem chainTie_of (Dx : DivX D) (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E) (A : Amb (recFields D))
    (u : D.what₂.Word) (μ : D.what₂.Tup) {S : Set ℕ} (ξ : Tup (recFields D).F (recFields D).E (recFields D).K S)
    (hξ : (ξ : Chr (recFields D).F (recFields D).E (recFields D).K) ∈
      tupGrp (recFields D).F (recFields D).E (recFields D).K (badS D))
    (H : ChainTieS Ch sel Dx mu0 A u μ ξ) : ChainTie Ch sel Dx mu0 A u μ := by
  obtain ⟨χ, h⟩ := ξ
  exact chainPeriodRelation_read_for_character_avoiding_primes Ch sel Dx mu0 A u μ χ h hξ H

end Gen

theorem colTie_of_addEquiv {D : D7} {EX : ErrX D} (Ch : Chars (recFields D) (recPrimes EX) D.R.m) (u : D.what₂.Word)
    (eM : (D.div.Nu u).V ≃+ MramV (recWts EX) Ch u) (hs : ∀ (r : D.what₂.LL) x, eM (r • x) = r • eM x)
    (h : ∀ x, x ∈ DV.MramL D u ↔ eM x ∈ MramL (recWts EX) Ch u) : ColTie Ch u (eM.toLinearEquiv hs) := h

theorem span_range_comp_eq_top {K V W U : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] {σ : K →+* ℂ} (f : V →ₛₗ[σ] W) (e : W ≃ₗ[ℂ] U)
    (h : Submodule.span ℂ (Set.range f) = ⊤) : Submodule.span ℂ (Set.range (e.toLinearMap.comp f)) = ⊤ := by
  rw [LinearMap.coe_comp, Set.range_comp, Submodule.span_image, h, Submodule.map_top, LinearEquiv.range]

theorem perCol_eq {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : GlobalTheory.Mem.Col2.TC B X) (h : I.Ok) (l : I.Laws)
    (Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)) (u : B.Word) (a : (I.rec7 l Z).what₂.Tup)
    (eM : ((I.rec7 l Z).div.Nu u).V ≃+ MramV (Pr := B.primes X) B.wts I.Ch u)
    (heM3 : ∀ x, (I.rec7 l Z).nuIn u x = KerRat.colForm I l h u I.mu0 (eM x).1)
    (heM4 : ∀ a φ, (I.fm l u a).emb 0 (KerRat.colForm I l h u a φ) =
      (I.cols l).e0Tw u a ((I.fm l u I.mu0).emb 0 (KerRat.colForm I l h u I.mu0 φ)))
    (e : (I.per l u a).Mt ≃ₗ[ℂ] (I.rec7 l Z).what₂.Amb a)
    (he1 : a = (I.rec7 l Z).what₂.mu0 → HEq e ((I.rec7 l Z).eMt u))
    (he2 : a ≠ (I.rec7 l Z).what₂.mu0 → e = (I.rec7 l Z).eMtTw u a) (φ : ((I.rec7 l Z).div.Nu u).V)
    (z : MtildeV (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps) :
    (I.rec7 l Z).what₂.perCol u a ((I.rec7 l Z).jN u φ) (e (KerRat.rowForm I l h u a z)) =
      (I.per l u a).PtilCol ((I.fm l u a).emb 0 (KerRat.colForm I l h u a (eM φ).1)) (KerRat.rowForm I l h u a z) := by
  have hj := (I.rec7 l Z).nuIn_jN u φ
  rw [heM3 φ] at hj
  by_cases ha : a = (I.rec7 l Z).what₂.mu0
  · subst ha
    have e1 : e = (I.rec7 l Z).eMt u := eq_of_heq (he1 rfl)
    rw [(I.rec7 l Z).perCol_base_eq_PtilCol u, hj, e1]
    erw [LinearEquiv.symm_apply_apply]
    rfl
  · rw [(I.rec7 l Z).perCol_tie u a ha, hj, he2 ha]
    erw [LinearEquiv.symm_apply_apply]
    exact congrArg (fun w => (I.per l u a).PtilCol w (KerRat.rowForm I l h u a z)) (heM4 a (eM φ).1).symm


set_option maxHeartbeats 40000000 in
theorem tiesAt_true : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : GlobalTheory.Mem.Col2.TC B X) (h : I.Ok) (l : I.Laws) (Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)) (l0 : I.Law0 l), GlobalTheory.Mem.Col2.ColIn.JetsIn I → ∀ (EX : ErrX (I.rec7 l Z)) (Dx : DivX (I.rec7 l Z)) (a : I.ι), EX.piG = X.piG → EX.piT = X.piT → I.QpIs Dx.Qp → RowPin I h l Z a → TiesAt (I.rec7 l Z) EX Dx a := by
  intro B X I h l Z l0 hJ EX Dx a h1 h2 hQ hR
  change (I.rec7 l Z).what₂.Tup at a
  rw [← exOf_eq EX h1 h2]
  have hA : ambOf (recSeam (I.rec7 l Z)) (baseCast B.ccK_top.symm (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G)) I.chi I.J.cD = I.A :=
    (ambOf_baseCast _ _ _ _ _).trans (AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J I.chi).symm
  have hX := base_fields_primes_ok B X
  have hcc : TaylorLogMetric.IsCurveIdeal (I.rec7 l Z) ⊤ := ⟨top_ne_bot, by simp⟩
  have hδ := (I.J.ok_iff B (I.cols l) Z.W Z.V Z.S Z.N Z.G).1 h.amb_ok
  have hχ : TaylorLogMetric.IsChi (I.rec7 l Z) I.chi := GlobalTheory.Mem.ChiIdeal.isChi_chiId _ _ I.C.isChi
  have hFL : KerRat.FamilyLaws I l Z := ⟨GlobalTheory.Mem.NatEqui.eqP _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ.1 hχ,
    (GlobalTheory.NatFamily.family _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ.1 hχ).1⟩
  have hFam := KerRat.kernels_rational I l Z h hJ (Or.inr (hFL))
  refine ⟨I.Ch, I.C.mu0, I.C.eta, I.sel, I.J.δ, baseCast B.ccK_top.symm (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G), I.chi, I.J.cD, ?_, ?_, ?_, fun u => ?_⟩
  · obtain ⟨c1, c2, c3, c4, -, -, c7, -⟩ := GlobalTheory.Core.Ht2.host_fields_primes_ties I h hX.1 l Z
    exact ⟨c1, c2, c3, c4, c7⟩
  · exact ⟨h.ch_ok, h.ch_tied, h.weil, h.sel_ok⟩
  · exact ⟨by rw [show (I.rec7 l Z).host.ccK = ⊤ from B.ccK_top]; exact hδ.1, hχ, hδ.2⟩
  · have hC : ∀ A : Amb B.fields, A = I.A → ChainTie (D := I.rec7 l Z) (EX := exOf EX h1 h2) I.Ch I.sel Dx I.C.mu0 A u a := by
      rintro A rfl
      obtain ⟨hne, hb⟩ := (hFam.1 u a).period
      obtain ⟨hY, hK, hF, hM, hper⟩ := hb hne.some
      obtain ⟨eM, heM1, heM2, heM3, heM4⟩ := GlobalTheory.T.ramifiedColumns_trueColumns_eq_concrete I h l Z l0 u
      obtain ⟨e, he1, he2, he3, he4⟩ := hR u
      let rE := GlobalTheory.PeriodOnStep.rowEmb (Pr := B.primes X) (I := I.chIn u a) B.wts I.Ch I.sel (I.tup a) I.Ps (I.perIn u a).b0
        (I.perIn u a).til (I.perIn u a).ext (I.perIn u a).tz (I.perIn u a).H (KerRat.tilOk I h u a).2.2 B.embLL
      have hrf : ⇑rE = KerRat.rowForm I l h u a := rfl
      refine chainTie_of (D := I.rec7 l Z) (EX := exOf EX h1 h2) I.Ch I.sel Dx I.C.mu0 I.A u a (I.tup a) (mem_tupGrp_of_subset (badS_subset h l Z) (I.tup a).2) ?_
      refine ⟨I.cst a, I.idx a, h.idx_ok a, hne.some, hY, hK, hF, hM, (show ((I.rec7 l Z).div.Nu u).V ≃+ MramV (recWts (exOf EX h1 h2)) I.Ch u from eM).toLinearEquiv heM1, LinearMap.comp (σ₁₃ := B.embLL) e.toLinearMap rE, h.sharp a, ?_, ?_, ?_, ?_, ?_⟩
      · refine ⟨?_, fun e0 => by rw [e0]; exact congrArg Subtype.val I.trueColumn_tuple_trivial_eq_one⟩
        have hfin : (Qprime (I.tup a : Chr B.fields.F B.fields.E B.fields.K)).Finite :=
          GlobalTheory.OpenChrRam.qprime_finite _ _ _ _ (I.tup a).2.1.1.1.1.2
        ext p
        rw [Finset.mem_coe, hQ a p]
        constructor
        · rintro ⟨hp, P, hP, hpP⟩
          obtain ⟨v, hv, rfl, -⟩ := I.exists_of_mem_Q hP
          refine ⟨v, hv, ?_⟩
          have := (GlobalTheory.Mem.ReadTwist.plc_under_eq_iff (F := B.host.F) (I.sel v) hp).2 hpP
          rwa [GlobalTheory.Mem.LevTwist.under_sel h v] at this
        · rintro ⟨v, hv, rfl⟩
          have hmem : I.sel v ∈ I.Q a := by
            classical
            unfold ColIn.Q QE
            rw [dite_eq_left hfin]
            convert Finset.mem_image_of_mem I.sel (hfin.mem_toFinset.2 hv)
          have hu := (GlobalTheory.Mem.ReadTwist.plc_under_eq_iff (F := B.host.F) (I.sel v) (Formalism.L2.DIV.plc_prime' v)).1
          rw [GlobalTheory.Mem.LevTwist.under_sel h v] at hu
          exact ⟨Formalism.L2.DIV.plc_prime' v, I.sel v, hmem, hu rfl⟩
      · exact fun i hi => hJ a u i hi
      · exact colTie_of_addEquiv (EX := exOf EX h1 h2) I.Ch u eM heM1 heM2
      · obtain ⟨r1, r2⟩ := GlobalTheory.T.rowForms_coefficientField_form_complexPeriodRows I h l u a
        refine ⟨fun s hs => (r1 s hs).map' e.toLinearMap e.ker, span_range_comp_eq_top rE e r2, fun v hv => ?_, he4⟩
        obtain ⟨z, hz⟩ := he3 v hv
        exact ⟨z, hz⟩
      · intro φ x
        exact (perCol_eq I h l Z u a eM heM3 heM4 e he1 he2 φ x).trans (hper (eM φ).1 x)
    exact hC _ hA

end GlobalTheory.TiesTrue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodRelationsTrueColumnsAtTupleStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodRelations_trueColumns_at_tuple : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : GlobalTheory.Mem.Col2.TC B X) (h : I.Ok) (l : I.Laws) (Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)) (l0 : I.Law0 l), GlobalTheory.Mem.Col2.ColIn.JetsIn I → ∀ (EX : ErrX (I.rec7 l Z)) (Dx : DivX (I.rec7 l Z)) (a : I.ι), EX.piG = X.piG → EX.piT = X.piT → I.QpIs Dx.Qp → RowPin I h l Z a → TiesAt (I.rec7 l Z) EX Dx a := by
  first | exact @GlobalTheory.TiesTrue.tiesAt_true | exact GlobalTheory.TiesTrue.tiesAt_true | (intros; apply GlobalTheory.TiesTrue.tiesAt_true <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowPinSetDivZ
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.Col2 NumberField

set_option maxHeartbeats 1000000

namespace GlobalTheory.AtG

theorem rowPin_setDivZ : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (ht : B.Word → ℝ) (a : (I.rec7 l Z).what₂.Tup), GlobalTheory.AtG.RowPin I h l Z a → GlobalTheory.AtG.RowPin I h l (GlobalTheory.Mem.Db.setDivZ Z N ht) a := by
  intro B X I h l Z N ht a hp
  exact hp

end GlobalTheory.AtG
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConcreteChainAgreesAtTupleOfNormalisedRows
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Svd.tiesAt_of_rowPin : ∀ (K : Ctx) (β : BPt K), β.Is (positionOf (HasPartAnd fun _ _ _ _ w Z => ∀ a, GlobalTheory.AtG.RowPin w.I w.ok w.l Z a)) → ∀ μ, GlobalTheory.AtG.TiesAt β.D β.O.ex.errX β.O.X μ := by
  intro K β hβ μ
  have key := positionOf_ind (R := fun K X f T c => ∀ O : Obj X.toD7, ofObj O = c.O → ∀ N h μ,
      GlobalTheory.AtG.TiesAt (setDiv X.toD7 N h) (O.tr N h).ex.errX (O.tr N h).X μ) ?_ hβ
  · exact key (β.Y.obj β.p) ((show ofObj (β.Y.obj β.p) = layObj β.Y from rfl).trans β.hY) (nPrime β.p.L) β.p.ht μ
  · intro K B f T w Z c hc O hO N h μ
    obtain ⟨⟨P⟩, hrow⟩ := hc
    have hpart : Part w Z (ofObj O) := hO ▸ P
    obtain ⟨_, hpiG, hpiT, hqp, _⟩ := Part.kerTie B f T w Z O hpart
    exact GlobalTheory.T.periodRelations_trueColumns_at_tuple w.I w.ok w.l (GlobalTheory.Mem.Db.setDivZ Z N h) w.l0 P.pin.jets _ _ μ hpiG hpiT hqp
      (GlobalTheory.AtG.rowPin_setDivZ w.I w.ok w.l Z N h μ (hrow μ))
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConcreteChainAgreesAtTupleOfNormalisedRowsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.concreteChainAgreesAtTuple_of_normalisedRows : ∀ (K : Ctx) (β : BPt K), β.Is (positionOf (HasPartAnd fun _ _ _ _ w Z => ∀ a, GlobalTheory.AtG.RowPin w.I w.ok w.l Z a)) → ∀ μ, GlobalTheory.AtG.TiesAt β.D β.O.ex.errX β.O.X μ := by
  first | exact @GlobalTheory.Svd.tiesAt_of_rowPin | exact GlobalTheory.Svd.tiesAt_of_rowPin | (intros; apply GlobalTheory.Svd.tiesAt_of_rowPin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodValuationsTypePrimesOfJetTableSplitPrime
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.AtG

theorem row_atG_pinned : GlobalTheory.AtG.JetSplitAmb → ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd), (∀ K X f T c, Q K X f T c → (positionOf (HasPartAnd fun _ _ _ _ w Z => ∀ a, GlobalTheory.AtG.RowPin w.I w.ok w.l Z a)) K X f T c) → AllBundlePointProperties.ArithmeticConditionAtBundlePoints Q Lk := by
  intro hJ Bd Q Lk hQ
  exact GlobalTheory.T.typePrimePeriodRow_of_constructedPointChains hJ Q Lk
    (RowE.of_all fun _ K β _ _ _ hq _ μ _ => GlobalTheory.T.concreteChainAgreesAtTuple_of_normalisedRows K β (hQ _ _ _ _ _ hq) μ)

end GlobalTheory.AtG
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodValuationsTypePrimesOfJetTableSplitPrimeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.atGRows_bundlePoints_of_jetSplitAmbient : GlobalTheory.AtG.JetSplitAmb → ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd), (∀ K X f T c, Q K X f T c → (positionOf (HasPartAnd fun _ _ _ _ w Z => ∀ a, GlobalTheory.AtG.RowPin w.I w.ok w.l Z a)) K X f T c) → AllBundlePointProperties.ArithmeticConditionAtBundlePoints Q Lk := by
  first | exact @GlobalTheory.AtG.row_atG_pinned | exact GlobalTheory.AtG.row_atG_pinned | (intros; apply GlobalTheory.AtG.row_atG_pinned <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetTableBoundSplitPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetTableBoundSplitPrime
namespace GlobalTheory.AtG

theorem jetSplitAmb_holds : JetSplitAmb := by
  intro D X s cc δ B χ cD hok hcc hδ hχ a b S N N' p _ ι hae hbe hN hN' hsN hsN' hdisc hcD hp hpd hLa π pE hπ hππ hS c' x hc' hpc hx m
  exact Formalism.L2.Ker.Test.jetAtSplit_ambOf s B χ cD hok hcc hδ hχ a b S N N' p ι hae hbe hN hN' hsN hsN' hdisc hcD hp hpd hLa π pE hπ hππ hS c' x hc' hpc hx m

end GlobalTheory.AtG
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetTableBoundSplitPrimeStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetTableBound_splitPrime : GlobalTheory.AtG.JetSplitAmb := by
  first | exact @GlobalTheory.AtG.jetSplitAmb_holds | exact GlobalTheory.AtG.jetSplitAmb_holds | (intros; apply GlobalTheory.AtG.jetSplitAmb_holds <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.AtG

theorem row_aAtG_of_rowPin : ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd),
    (∀ K X f T c, Q K X f T c →
      (positionOf (HasPartAnd fun _ _ _ _ w Z => ∀ a, GlobalTheory.AtG.RowPin w.I w.ok w.l Z a)) K X f T c) →
    AllBundlePointProperties.ArithmeticConditionAtBundlePoints Q Lk :=
  GlobalTheory.T.atGRows_bundlePoints_of_jetSplitAmbient GlobalTheory.T.jetTableBound_splitPrime

end GlobalTheory.AtG
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holds_at_bundlePoints_of_trueColumns : ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd), (∀ K X f T c, Q K X f T c → (positionOf (HasPartAnd fun _ _ _ _ w Z => ∀ a, GlobalTheory.AtG.RowPin w.I w.ok w.l Z a)) K X f T c) → AllBundlePointProperties.ArithmeticConditionAtBundlePoints Q Lk := by
  first | exact @GlobalTheory.AtG.row_aAtG_of_rowPin | exact GlobalTheory.AtG.row_aAtG_of_rowPin | (intros; apply GlobalTheory.AtG.row_aAtG_of_rowPin <;> assumption)
