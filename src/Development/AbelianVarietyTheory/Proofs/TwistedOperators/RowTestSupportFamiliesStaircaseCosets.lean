module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftTopScalar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLocalEqCompletedHomLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarisationTwistLatticeSelfDualSameStabilisers

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestSupportFamiliesStaircaseCosets
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestSupportFamiliesStaircaseCosets
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowVal

theorem givenLevel_inner {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E) :
    ∀ p : ℕ × ℕ, 1 ≤ p.1 → 1 ≤ p.2 → givenLevel G t w p = KO (Kw w) _ := by
  rintro ⟨_ | a, _ | b⟩ h1 h2
  · simp at h1
  · simp at h1
  · simp at h2
  · rfl

theorem oneAt : Big fun ch => OneAt ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t Φ β hβ w hw0 i
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s
  have hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hch.guard t
  have hT := isTensor_Tflip hL ch.W ch.S.B t Φ hde hc w.2
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hcond : HasConductor (psiAt ch.W w.1) 1 :=
    (((Good.locGrid_isGood hL ch.G ch.W t hde hc).1 w.1 w.2).square 0 hm 0 hm).cond
  have hce : depthAt ch.G w.1 = cosExp ch.G w.1 := by
    have e : 1 ≤ cosExp ch.G w.1 := by
      classical
      unfold cosExp
      rw [if_pos hw0]
      exact ch.G.pl.depth_pos _ _
    rw [depthAt, max_eq_left e]
  rw [hce] at hT
  haveI := (isUnitVol_unitVol w.1).1
  have hJ : ∀ j, 0 < j → j < (locGrid ch.G t w.1).m →
      givenLevel ch.G t w.1 ((locGrid ch.G t w.1).m, j) = KO (Kw w.1) _ := fun j hj hj' =>
    givenLevel_inner ch.G t w.1 _ (by change 1 ≤ D.R.m; omega) hj
  have key := OneCosetProof.oneCoset_of_isTensor (ν := unitVol w.1) one_le_sLen hcond hT hJ
  have hk : keepAt ch.G w.1 = false := by
    classical
    unfold keepAt
    simp [hw0]
  have hβw := hβ w
  rw [hk] at hβw
  exact key (β w) hβw i

end GlobalTheory.RowVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestSupportFamiliesStaircaseCosetsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTest_support_families_staircase_cosets : Big fun ch => OneAt ch := by
  first | exact @GlobalTheory.RowVal.oneAt | exact GlobalTheory.RowVal.oneAt | (intros; apply GlobalTheory.RowVal.oneAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltSc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal

noncomputable section

open scoped nonZeroDivisors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowShape

variable {D : D7}

def latPi (S : HSp D) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : GlobalTheory.FinPl.Lat S :=
  Submodule.pi Set.univ fun _ => (I : Submodule (𝓞 D.host.E) D.host.E)


variable (D) in
def tiltSc (j : ℕ) (p : Fin (D.R.m - 1 - j)) : D.host.E :=
  if Odd j then
    (if 2 * p.1 < D.R.m - 1 - j then (D.host.xi0 ^ p.1)⁻¹ else star (D.host.xi0 ^ (D.R.m - 1 - j - 1 - p.1)))
  else 1


variable (D) in
def rowId (j : ℕ) (p : Fin (D.R.m - 1 - j)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
  FractionalIdeal.spanSingleton _ (tiltSc D j p) * stairId D.host.AA D.host.AAbar (D.R.m - 1 - j) p

variable {T : Type} {L : LevCh D T} {sc : Consts}

def rowN (G : GridData L sc) (j : ℕ) : GlobalTheory.FinPl.Lat (G.V (.grid D.R.m j)) :=
  if h : j < D.R.m then (G.rowDec j h).lat (G.Λ (.top j)) (rowId D j) else G.Λ (.grid D.R.m j)


variable (D) in
def lineId (j : ℕ) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
  D.host.AA ^ ((D.R.m - 2 - j) / 2 + 1) * (D.host.AAbar ^ ((D.R.m - 2 - j) / 2 + 1))⁻¹


variable (D) in
def lineL (j : ℕ) : GlobalTheory.FinPl.Lat (GlobalTheory.SeeSaw.Model.nLine D) := latPi _ (lineId D j)


variable (D) in
def topL : GlobalTheory.FinPl.Lat (GlobalTheory.RowChain.pLine D) := latPi _ 1

def coreL (G : GridData L sc) (j : ℕ) : GlobalTheory.FinPl.Lat (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) :=
  (G.Λ (.top j)).map
      ((Matrix.mulVecLin (GlobalTheory.OrthSumExists.orthDecHsum D (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)).iA).restrictScalars
        (𝓞 D.host.E)) ⊔
    (lineL D j).map
      ((Matrix.mulVecLin (GlobalTheory.OrthSumExists.orthDecHsum D (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)).iB).restrictScalars
        (𝓞 D.host.E))

end GlobalTheory.RowShape

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceAtIff
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal

namespace GlobalTheory.LocAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)


open Classical in
def PlaceCl (s : ℤˣ) (t : T) (w : Pl D.host.E)
    (β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w)) (ζ : ℂ) : Prop :=
  ∀ e, IsIdemSum e {w} → ∀ (M : Vol ch.G) (hM : M.Is t) (r r₀ h : Pts ch.G),
    OneLoc t w e r (fun j => if j ∈ idx D then sgnAt ch.G t s w j * (repsAt ch.G t w).elt β (D.R.m, j) else 1) →
    OneLoc t w e r₀ (fun j => if j = 0 then (stair (locGrid ch.G t w) (unifAt w) (cosExp ch.G w) j)⁻¹ else 1) →
    (∀ j, j ≤ D.R.m → ∃ δ, IsTilt ch.G j δ ∧ δ⁻¹ * h j ∈ GlobalTheory.FinPl.grpOff _ (· = w.under (𝓞 D.host.F))) →
    ∀ (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w).rank b.tgt)) (Fin ((locGrid ch.G t w).rank b.src)) (Kw w) → ℂ),
      (∀ i j x, φ (.ex i j) x = 1) → ∀ v f : SchDown ch.G t, (∀ j, IsThetaFunO ch.W.ψ _ _ (v j)) →
      (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (v j) (fun y => if IsHalf e y then φ (.theta D.R.m j)
        (ch.S.B.coord t w (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩
          (y.map fun a => cpt w (toEAf D a))) else 0) (f j)) →
      ∀ (I : Type) (S : Finset I) (x : I → ℂ) (d : I → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j)) (c : I → Combs ch.G),
        (∀ i ∈ S, ∀ j : Fin D.R.m, (d i j).e = e ∧ IsCombOf ch.W (d i j) ((c i).1 j)) →
        (∀ y : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))), (∀ j, IsHalf e (y j)) →
          ∑ i ∈ S, x i * ∏ j, (d i j).fn (y j) = flatTensor one_le_sLen (psiAt ch.W w) (unitVol w)
            (moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt β)
              ((locGrid ch.G t w).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) φ)) (ch.S.toGridChoice.colAt t w y) 0) →
        ∀ u, evT (conAt ch.W hM f (h * r)) 1 u 0 = ζ * ∑ i ∈ S, x i * evT (combC ch.W (c i) (conAt ch.W hM v (h * r₀))) 1 u 0

theorem placeAt_iff (s : ℤˣ) : PlaceAt ch s ↔ ∃ (κ : Pl D.host.E → ℂ) (z : T → Pl D.host.E → ℂˣ),
    (∀ t w, z t w ∈ xiVals R.toLevCh t) ∧ (∀ w, w ∉ ch.G.pl.W0 → κ w = 1) ∧
    ∀ t, ∀ w ∈ locPl ch.G t, ∀ β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w), ∃ ζ : ℂ,
      ((w ∈ ch.G.pl.W0 → ∀ i, β i = DoubleCoset.mk _ _ (stair (locGrid ch.G t w) (unifAt w) (cosExp ch.G w) (i + 1))) →
        ζ = κ w * (z t w : ℂ)⁻¹) ∧ PlaceCl ch s t w β ζ := Iff.rfl

end GlobalTheory.LocAsm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowPeriodGroupsSplitRealFiniteLargeDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowPeriodGroupsSplitRealFiniteLargeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowGrpSplit

theorem grpAt_all {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) : GrpAt ch := by
  intro j hj
  have hj' := List.mem_range'_1.1 hj
  obtain ⟨hi, hf, hc, he, hu, hrest⟩ := GlobalTheory.AdelicSplit.adelic_split D (ch.G.V (.grid D.R.m j))
  have hV := ch.G.isV (X := .grid D.R.m j) ⟨le_rfl, by omega⟩ (fun k hk => by
    simp only [Node.grid.injEq] at hk; omega)
  have hlat := congLev_open_compact (ch.G.V (.grid D.R.m j))
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ hV.sd) (𝔪 := ⊤) top_ne_bot
  have hR : IsClosed ((rowGrp ch.G j : Subgroup (GA D (ch.G.V (.grid D.R.m j)))) : Set (GA D (ch.G.V (.grid D.R.m j)))) ∧ (∀ a ∈ GinfC _, ∀ b ∈ GfC _, a * b ∈ rowGrp ch.G j → a ∈ rowGrp ch.G j ∧ b ∈ rowGrp ch.G j) ∧
      (∀ μ : Measure (rowGrp ch.G j), μ.IsHaarMeasure → μ.IsInvInvariant) ∧
      ∀ μ : Measure ((rowGrp ch.G j).subgroupOf (GfC _)), μ.IsHaarMeasure → μ.IsInvInvariant := by
    by_cases h1 : j + 2 * ((D.R.m - 1 - j) / 2) + 1 = D.R.m
    · rw [show rowGrp ch.G j = _ from dif_pos h1]
      obtain ⟨a, b, c⟩ := (hrest _ _ _).1
      exact ⟨GlobalTheory.jacGrp_isClosed D _ _ _ _, a, b, c⟩
    · have h2 : j + 2 * ((D.R.m - 2 - j) / 2) + 2 = D.R.m := by omega
      rw [show rowGrp ch.G j = _ from (dif_neg h1).trans (dif_pos h2)]
      obtain ⟨a, b, c⟩ := (hrest _ _ _).2 _ _ _
      exact ⟨GlobalTheory.BesClosed.besGrp_isClosed D _ _ _ _ _ _ _, a, b, c⟩
  exact
    { clA := hi
      clB := hf
      clR := hR.1
      comm := hc
      prod := he
      split := hR.2.1
      le := inf_le_left
      cpt := hlat.2
      opn := by
        have e : (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) :
            Set (GfC (ch.G.V (.grid D.R.m j)))) = Subtype.val ⁻¹'
            (((ch.G.levMax (.grid D.R.m j)).comap (Lev.finE _) : Subgroup (GA D (ch.G.V (.grid D.R.m j)))) :
              Set (GA D (ch.G.V (.grid D.R.m j)))) := by
          ext x
          exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
        rw [e]
        exact hlat.1.preimage continuous_subtype_val
      uniR := hR.2.2.1
      uniRB := hR.2.2.2
      uniB := hu }

theorem grpAt_big : Big fun ch => GrpAt ch :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => grpAt_all ch⟩⟩

end GlobalTheory.RowGrpSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowPeriodGroupsSplitRealFiniteLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowPeriodGroups_split_real_finite_large_depth : Big fun ch => GrpAt ch := by
  first | exact @GlobalTheory.RowGrpSplit.grpAt_big | exact GlobalTheory.RowGrpSplit.grpAt_big | (intros; apply GlobalTheory.RowGrpSplit.grpAt_big <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnQuotHeightPowMulNorm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CuspFormApprox

variable {D : D7} {V : HSp D} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}

theorem integrableOn_one (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) :
    IntegrableOn (fun _ => (1 : ℝ)) 𝓕 μ := by
  simpa using GlobalTheory.Size.integrableOn_inv_quotHeight_pow (V := V) 0 hμ h𝓕

theorem integrableOn_of_le (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) {f : GA D V → ℝ}
    (hf : Continuous f) (h0 : ∀ g, 0 ≤ f g) {C : ℝ} (hC : ∀ g, f g ≤ C) :
    IntegrableOn f 𝓕 μ ∧ ∫ g in 𝓕, f g ∂μ ≤ C * ∫ _g in 𝓕, (1 : ℝ) ∂μ := by
  have h1 := integrableOn_one hμ h𝓕
  have hC' : IntegrableOn (fun _ => C * (1 : ℝ)) 𝓕 μ := h1.const_mul C
  have hi : IntegrableOn f 𝓕 μ := by
    refine Integrable.mono' hC' hf.aestronglyMeasurable (.of_forall fun g => ?_)
    rw [Real.norm_of_nonneg (h0 g), mul_one]
    exact hC g
  refine ⟨hi, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono_of_nonneg (.of_forall fun g => h0 g) hC' (.of_forall fun g => by simpa using hC g)

theorem integrableOn_quotHeight_pow_mul_norm (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D} (hθ : IsInfFam θ)
    {N : GlobalTheory.Grid.Node D} {μ : Measure (GA D N.V)} {𝓕 : Set (GA D N.V)} (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ N.V) 𝓕 μ) {φ : GA D N.V → ℂ} (hφ : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ) (b : ℕ) :
    IntegrableOn (fun g => GlobalTheory.Grow.quotHeight N.V g ^ b * ‖φ g‖) 𝓕 μ := by
  have hr := (GlobalTheory.Size.rapidDecSm_of_cuspForm hP hθ hφ.1 hφ.2.1).rapidDec
  obtain ⟨C, hC⟩ := hr.decay b
  refine (integrableOn_of_le hμ h𝓕 (((GlobalTheory.Grow.continuous_quotHeight N.V).pow b).mul hr.continuous.norm)
    (fun g => mul_nonneg (pow_nonneg (GlobalTheory.Grow.quotHeight_pos N.V g).le b) (norm_nonneg _)) (C := C)
    (fun g => by rw [mul_comm]; exact hC g)).1

theorem weighted_uniform_approx_cusp_forms {θ : InfFam D} {N : GlobalTheory.Grid.Node D} {μ : Measure (GA D N.V)} {𝓕 : Set (GA D N.V)}
    (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ N.V) 𝓕 μ) {φ : GA D N.V → ℂ} (hc : Continuous φ) (b : ℕ)
    (hu : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (F : Fin n → N.Maps) (v : Fin n → SmT N.M), (∀ l, F l ∈ N.Cusp θ) ∧
      ∀ g, ‖φ g - ∑ l, F l (v l) g‖ * GlobalTheory.Grow.quotHeight N.V g ^ b ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (Fs : Fin n → N.Maps) (vs : Fin n → SmT N.M), (∀ k, Fs k ∈ N.Cusp θ) ∧
      IntegrableOn (fun g => GlobalTheory.Grow.quotHeight N.V g ^ b * ‖(∑ k, Fs k (vs k) g) - φ g‖) 𝓕 μ ∧
      ∫ g in 𝓕, GlobalTheory.Grow.quotHeight N.V g ^ b * ‖(∑ k, Fs k (vs k) g) - φ g‖ ∂μ ≤ ε := by
  intro ε hε
  set I := ∫ _g in 𝓕, (1 : ℝ) ∂μ
  have hI : 0 ≤ I := integral_nonneg fun _ => zero_le_one
  obtain ⟨n, F, v, hF, h⟩ := hu (ε / (I + 1)) (div_pos hε (by linarith))
  have hcs : Continuous fun g => ∑ l, F l (v l) g := by
    have := continuous_finsetSum Finset.univ fun l _ =>
      GlobalTheory.BaseChain.multT_apply_continuous θ N.M ∅ 1 (F l) (hF l) (v l)
    simpa using this
  have hcf : Continuous fun g => GlobalTheory.Grow.quotHeight N.V g ^ b * ‖(∑ l, F l (v l) g) - φ g‖ :=
    ((GlobalTheory.Grow.continuous_quotHeight N.V).pow b).mul (hcs.sub hc).norm
  obtain ⟨hi, hle⟩ := integrableOn_of_le hμ h𝓕 hcf
    (fun g => mul_nonneg (pow_nonneg (GlobalTheory.Grow.quotHeight_pos N.V g).le b) (norm_nonneg _)) (C := ε / (I + 1))
    (fun g => by rw [mul_comm, norm_sub_rev]; exact h g)
  refine ⟨n, F, v, hF, hi, hle.trans ?_⟩
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith

end GlobalTheory.CuspFormApprox

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestCellValueOfStepsLargeDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestCellValueOfStepsLargeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowVal

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem defTot_smul {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T)
    (M : Vol G) (c : ℂ) (σ : PolCol G × PolRow G →₀ ℂ) (τ : PureDat G t →₀ ℂ) (φ : Fn G (.top 0)) (F : Fn G (.grid 0 D.R.m)) :
    defTot t S M (c • σ) τ φ F = c * defTot t S M σ τ φ F := by
  unfold defTot
  rw [Finsupp.sum_smul_index (by intro P; simp), Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  dsimp only
  rw [Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring


set_option maxHeartbeats 1600000 in
theorem valAt_of_steps (ch : Choice R) (s : ℤˣ) (hFl : FlatAt ch s) (hT : TensAt ch) (hV : VolAt ch) (hW : WtAt ch s)
    (hFo : FockAt ch) (hB : BasicAt ch) (hO : OneAt ch) (hS : ∀ t a, ch.S.SumOK t (ch.Phi a)) : ValAt ch s := by
  obtain ⟨z1, hz1, hFl⟩ := hFl
  obtain ⟨z2, hz2, hFo⟩ := hFo
  obtain ⟨hBa, hBf, hBM, hBM', hBgood, hBgood', hBc⟩ := hB
  refine ⟨fun t => z1 t * z2 t, fun t => Subgroup.mul_mem _ (hz1 t) (hz2 t), ?_⟩
  intro ρ μ hρμ P p hp
  obtain ⟨c0, hc0⟩ := hW ρ μ hρμ
  obtain ⟨C, hCr, hC⟩ := hFl P.2 p hp
  obtain ⟨σ₀, hσ₀⟩ := hFo C hCr P.1
  refine ⟨c0 • σ₀, ?_⟩
  intro t a τ hτ M hM β hβ b hb M' τ' hM' hτ' y
  obtain ⟨cc, hcc⟩ := hBc t (ch.Phi a) β τ' hτ'
  obtain ⟨ζ, hζ, hid⟩ := hC t (ch.Phi a) τ hτ M hM β b hb τ' cc hτ' hcc
  have hζ' : ζ = ((z1 t : ℂˣ) : ℂ)⁻¹ := hζ (hO t _ β hβ)
  obtain ⟨sc, hsc, hwx⟩ := hc0 t (ch.Phi a) β b hb M M' hM hM'
  have hgood : ∀ d ∈ τ'.support, Good ch.W (combC ch.W (cc d) C) (combR ch.rm (cc d)) := fun d hd =>
    hBgood' C hCr (cc d) (fun j hj => ((hcc d hd).1 ⟨j, hj⟩).1)
  have h1 : tot ch.W hM P τ (colFn ch a) (formTop ch t y) (p * b) = ζ * τ'.sum fun d x =>
      x * per ch.W M t (combC ch.W (cc d) C) (combR ch.rm (cc d)) P.1 (colFn ch a) (formTop ch t y) := by
    have key := hT t M (hBM t M hM) (colFn ch a) (formTop ch t y) (hBa a) (hBf t y)
      ((SchRow ch.G × SchDown ch.G t) ⊕ PureDat ch.G t) (τ.support.disjSum τ'.support)
      (Sum.elim (fun d => τ d) (fun d => -ζ * τ' d))
      (Sum.elim (fun d => conAt ch.W hM (fockD ch.W t d.2 P.2) (p * b)) (fun d => combC ch.W (cc d) C))
      (Sum.elim Prod.fst (fun d => combR ch.rm (cc d))) ?_ ?_ P.1
    · rw [Finset.sum_disjSum] at key
      simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, mul_assoc, Finset.sum_neg_distrib] at key
      unfold tot
      rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum]
      linear_combination key
    · rintro (d | d) hd
      · exact hBgood t (ch.Phi a) τ hτ M hM d (Finset.inl_mem_disjSum.1 hd) P.2 (p * b)
      · exact hgood d (Finset.inr_mem_disjSum.1 hd)
    · intro u y'
      have e := hid u y'
      rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum] at e
      rw [Finset.sum_disjSum]
      simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, mul_assoc, Finset.sum_neg_distrib]
      rw [e]
      ring
  have h2 : (τ'.sum fun d x => x * per ch.W M t (combC ch.W (cc d) C) (combR ch.rm (cc d)) P.1 (colFn ch a) (formTop ch t y)) =
      sProd D sc * τ'.sum fun d x => x * per ch.W M' t (combC ch.W (cc d) C) (combR ch.rm (cc d)) P.1 (colFn ch a) (formTop ch t y) := by
    rw [Finsupp.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    dsimp only
    rw [hV t M M' sc (hBM t M hM) (hBM' t _ β M' hM') hsc (colFn ch a) (formTop ch t y) (hBa a) (hBf t y) _ _ (hgood d hd) P.1]
    ring
  have h3 := hσ₀ t a β M' (hBM' t _ β M' hM') (hS t a) τ' cc hτ' hcc y
  rw [h1, h2, h3, defTot_smul, hζ', Units.val_mul, mul_inv]
  linear_combination (((z1 t : ℂˣ) : ℂ)⁻¹ * ((z2 t : ℂˣ) : ℂ)⁻¹ *
    defTot t ch.S.toGridChoice M' σ₀ τ' (colFn ch a) (formTop ch t y)) * hwx

end

theorem valAt_big : Big fun ch => ∀ s, FlatAt ch s → TensAt ch → VolAt ch → WtAt ch s → FockAt ch → BasicAt ch → OneAt ch →
    (∀ t a, ch.S.SumOK t (ch.Phi a)) → ValAt ch s :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ s => valAt_of_steps ch s⟩⟩

end GlobalTheory.RowVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestCellValueOfStepsLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTest_cellValue_of_steps_large_depth : Big fun ch => ∀ s, FlatAt ch s → TensAt ch → VolAt ch → WtAt ch s → FockAt ch → BasicAt ch → OneAt ch → (∀ t a, ch.S.SumOK t (ch.Phi a)) → ValAt ch s := by
  first | exact @GlobalTheory.RowVal.valAt_big | exact GlobalTheory.RowVal.valAt_big | (intros; apply GlobalTheory.RowVal.valAt_big <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLeSelfDualHomLatticeShift
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLeSelfDualHomLatticeShift
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.RowBig

open scoped Pointwise

variable {D : D7}

theorem idLat_one {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    idLat (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) Λ = Λ := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨s, hs, y, hy, rfl⟩
    obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hs
    rw [algebraMap_smul]
    exact Λ.smul_mem r hy
  · intro y hy
    exact Submodule.subset_span ⟨1, FractionalIdeal.one_mem_one _, y, hy, (one_smul _ _).symm⟩

theorem conjFI_coe (I : Ideal (𝓞 D.host.E)) :
    GlobalTheory.SeeSaw.conjFI D (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      ((D.host.conj • I : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
  ext x
  rw [GlobalTheory.SeeSaw.mem_conjFI, FractionalIdeal.mem_coeIdeal, FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨r, hr, hx⟩
    refine ⟨D.host.conj • r, Ideal.smul_mem_pointwise_smul _ _ _ hr, ?_⟩
    show D.host.conj (r : D.host.E) = x
    rw [show (r : D.host.E) = D.host.conj x from hx, GlobalTheory.SeeSaw.conj_conj_host]
  · rintro ⟨r, hr, rfl⟩
    refine ⟨D.host.conj⁻¹ • r, Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 hr, ?_⟩
    show D.host.conj.symm (r : D.host.E) = D.host.conj (r : D.host.E)
    rw [AlgEquiv.symm_apply_eq, GlobalTheory.SeeSaw.conj_conj_host]

theorem conjFI_conjFI (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : GlobalTheory.SeeSaw.conjFI D (GlobalTheory.SeeSaw.conjFI D 𝔞) = 𝔞 := by
  ext x
  rw [GlobalTheory.SeeSaw.mem_conjFI, GlobalTheory.SeeSaw.mem_conjFI, GlobalTheory.SeeSaw.conj_conj_host]

theorem conjFI_shiftId {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) :
    GlobalTheory.SeeSaw.conjFI D (shiftId G) = (shiftId G)⁻¹ := by
  have hb : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      GlobalTheory.SeeSaw.conjFI D (G.modul : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := (conjFI_coe _).symm
  unfold shiftId
  rw [hb, map_mul, map_inv₀, conjFI_conjFI, mul_inv, inv_inv, mul_comm]

theorem shiftId_ne_zero {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) : shiftId G ≠ 0 := by
  have hm : (G.modul : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (G.pl.modul_ne_bot sc)
  have hb : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [show ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      GlobalTheory.SeeSaw.conjFI D (G.modul : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) from (conjFI_coe _).symm]
    exact (RingEquiv.map_ne_zero_iff _).2 hm
  exact mul_ne_zero hm (inv_ne_zero hb)

theorem isSelfDualC_idLat_shiftId {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {S : HSp D} (Λ : Lat S)
    (hΛ : IsSelfDualC S Λ) : IsSelfDualC S (idLat (shiftId G) Λ) := by
  refine GlobalTheory.ScaleSelfDual.isSelfDualC_scaleLat S Λ hΛ (shiftId_ne_zero G) fun c => ?_
  rw [← conjFI_shiftId, GlobalTheory.SeeSaw.mem_conjFI, Formalism.BasicNotions.bridge_star_holds D.R D.host c]

theorem latRow_le_latBig : All fun {D} _ _ _ {G} _ _ => ∀ i, 1 ≤ i → i < D.R.m → latRow G i ≤ latBig G i := by
  intro D hq T L μ0 hL sc G W M hM i hi1 him u hu
  have hS : IsSelfDualC (G.V (.grid (i + 1) 0)) (G.Λ (.grid (i + 1) 0)) :=
    (G.isV (X := .grid (i + 1) 0) ⟨by omega, by omega⟩ (fun j h => by injection h with h1 h2; omega)).sd
  have hT : IsSelfDualC (G.V (.grid i 0)) (G.Λ (.grid i 0)) :=
    (G.isV (X := .grid i 0) ⟨by omega, by omega⟩ (fun j h => by injection h with h1 h2; omega)).sd
  have h1 := idLat_one (G.Λ (.grid i 0))
  have hsh := isSelfDualC_idLat_shiftId G _ hT
  obtain ⟨e, he, -⟩ := W.cosVec_is
  have hu' : u ∈ latO (negSp (G.V (.grid (i + 1) 0))) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _)
      (G.Λ (.grid i 0) : Set _) (fun _ => True) ∧
      ∀ e : AE D, IsIdemSum e G.pl.W0 → e • u ∈ hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) := hu
  have key := GlobalTheory.T.completedHomLattice_modulus_depth_mem_shift hq μ0 hL G (G.Λ (.grid (i + 1) 0)) 1 (G.Λ (.grid i 0)) hS (by rw [h1]; exact hT)
    (by rw [one_mul]; exact hsh) u (by rw [h1]; exact GlobalTheory.RowLoc.mem_latO_negSp.1 hu'.1) ⟨e, he, by rw [h1]; exact hu'.2 e he⟩
  rw [one_mul] at key
  exact key

end GlobalTheory.RowBig

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLeSelfDualHomLatticeShiftStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthLatticeGridRow_le_selfDualHomLatticeShift : All fun {D} _ _ _ {G} _ _ => ∀ i, 1 ≤ i → i < D.R.m → latRow G i ≤ latBig G i := by
  first | exact @GlobalTheory.RowBig.latRow_le_latBig | exact GlobalTheory.RowBig.latRow_le_latBig | (intros; apply GlobalTheory.RowBig.latRow_le_latBig <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefProd
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowWt

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def colCoef (ch : Choice R) (t : T) (β : CosFam ch.G t) (j : ℕ) : ℚ :=
  ∏ w : locPl ch.G t, if h : j < D.R.m then
    invVol (conjLevel one_le_sLen (givenLevel ch.G t w) ((repsAt ch.G t w).elt (β w)) (j := j) h) else 1

theorem coef_prod (ch : Choice R) (t : T) (Φ : ch.G.Datum) (β : CosFam ch.G t) :
    ∏ w, ((ch.S.term t Φ β w).coef : ℂ) = ((idx D).map fun j => (colCoef ch t β j : ℂ)).prod := by
  have hw : ∀ w, (ch.S.term t Φ β w).coef = ∏ i : Fin (D.R.m - 2), (if h : 1 + (i : ℕ) < D.R.m then
      invVol (conjLevel one_le_sLen (givenLevel ch.G t w) ((repsAt ch.G t w).elt (β w)) (j := 1 + (i : ℕ)) h) else 1) := by
    intro w
    have hj : ∀ (j j' : ℕ) (_ : j = j') (h : j < D.R.m) (h' : j' < D.R.m),
        invVol (conjLevel one_le_sLen (givenLevel ch.G t w) ((repsAt ch.G t w).elt (β w)) (j := j) h) =
          invVol (conjLevel one_le_sLen (givenLevel ch.G t w) ((repsAt ch.G t w).elt (β w)) (j := j') h') := by
      rintro j _ rfl h h'
      rfl
    show ∏ i : Fin (D.R.m - 2), invVol (conjLevel one_le_sLen (givenLevel ch.G t w) ((repsAt ch.G t w).elt (β w))
      (j := (i : ℕ) + 1) (show (i : ℕ) + 1 < D.R.m by have := i.isLt; omega)) = _
    exact Finset.prod_congr rfl fun i _ => by
      rw [dite_eq_left (show 1 + (i : ℕ) < D.R.m by have := i.isLt; omega)]
      exact hj _ _ (Nat.add_comm _ _) _ _
  have key : ∏ w, (ch.S.term t Φ β w).coef = ((idx D).map fun j => colCoef ch t β j).prod := by
    simp only [hw]
    rw [Finset.prod_comm]
    simp only [idx, List.range'_eq_map_range, List.map_map]
    rw [← List.map_coe_finRange_eq_range, List.map_map, ← List.ofFn_eq_map, List.prod_ofFn]
    exact Finset.prod_congr rfl fun i _ => rfl
  have := congrArg (Rat.cast : ℚ → ℂ) key
  rw [Rat.cast_prod, Rat.cast_list_prod, List.map_map] at this
  exact this

end GlobalTheory.RowWt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFinitePointsOfHasLocalLatticeMatrices
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFinitePointsOfHasLocalLatticeMatrices
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowCover

theorem mem_GfC_of_hasLoc : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (B : Frames G) {j : ℕ}
    (hj : j ≤ D.R.m) (x : GA D (G.V (.grid D.R.m j)))
    (g : ∀ w : locPl G t, GL (Fin ((locGrid G t w.1).rank (D.R.m, j))) (Kw w.1)), HasLoc t B hj x g → x ∈ GfC _ := by
  intro D T L sc G t B j hj x g hx
  obtain ⟨e, ⟨⟨es, hes, rfl⟩, -⟩, hg, -⟩ := hx
  have h0 : infPart D ((∑ PP ∈ locPl G t, es PP) + cA D (∑ PP ∈ locPl G t, es PP)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum (cA D), ← Finset.sum_add_distrib, map_sum]
    refine Finset.sum_eq_zero fun PP hPP => ?_
    obtain ⟨-, -, v, ε, ⟨α, rfl, -⟩, h⟩ := (hes PP hPP).1
    rw [h]; exact TensorProduct.zero_tmul _ _
  refine Units.ext (Matrix.ext fun i j => ?_)
  have := congrArg (infPart D) (hg i j)
  rw [map_mul, h0, zero_mul, Matrix.sub_apply, map_sub, eq_comm, sub_eq_zero] at this
  refine Eq.trans this ?_
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

end GlobalTheory.RowCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFinitePointsOfHasLocalLatticeMatricesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_finitePoints_of_hasLocalLatticeMatrices : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (B : Frames G) {j : ℕ}
    (hj : j ≤ D.R.m) (x : GA D (G.V (.grid D.R.m j)))
    (g : ∀ w : locPl G t, GL (Fin ((locGrid G t w.1).rank (D.R.m, j))) (Kw w.1)), HasLoc t B hj x g → x ∈ GfC _ := by
  first | exact @GlobalTheory.RowCover.mem_GfC_of_hasLoc | exact GlobalTheory.RowCover.mem_GfC_of_hasLoc | (intros; apply GlobalTheory.RowCover.mem_GfC_of_hasLoc <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestExistsCombinationsOfExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestExistsCombinationsOfExpansion
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CombsExist

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum


set_option maxHeartbeats 1000000 in
theorem exists_comb_model {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (e : AE D)
    (Φ : WO S T → ℂ) (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (he : e * e = e)
    (hec : e * cA D e = 0) (hinf : infPart D e = 0)
    (hΦ : IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ) :
    ∃ c : WO S T →₀ ℂ, (∀ u ∈ c.support, u.map (infPart D) = 0 ∧ IsHalf (e + cA D e) u) ∧ ∀ f₀ Tm,
      IsPlaceModel ψ (symplO S T) (heisO ψ S T) e
        (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm →
      comb ψ S T c f₀ = Tm Φ := by
  classical
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have hce : cA D e * e = 0 := by rw [mul_comm, hec]
  have half1 : ∀ u : WO S T, IsHalf e u → IsHalf (e + cA D e) u := fun u hu i j => by
    rw [add_mul, hu i j, ← hu i j, ← mul_assoc, hce, zero_mul, add_zero, hu i j]
  have half2 : ∀ u : WO S T, IsHalf (cA D e) u → IsHalf (e + cA D e) u := fun u hu i j => by
    rw [add_mul, hu i j, ← hu i j, ← mul_assoc, hec, zero_mul, zero_add, hu i j]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      a • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  have hLL' : ∀ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e,
      ∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T u y) = 1 := fun u hu y hy =>
    (hdual u (infPart_of_half hinf ((isHalf_iff S T).2 hu.2))).1 hu.1 y hy.1
  have hX : ∀ x ∈ half S T e, (∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) →
      x ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e := fun x hx h => by
    refine ⟨(hdual x (infPart_of_half hinf ((isHalf_iff S T).2 hx))).2 fun u hu => ?_, hx⟩
    have := h _ (hsm _ he' u hu)
    rwa [← symplO_smul, (mem_half S T).1 hx] at this
  have hfin' : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, ∃ r ∈ R,
        ∃ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, t = r + k • u := fun k hk => by
    obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e he u hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]
  have hden : ∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ (latO S T ΛS ΛT fun _ => True) := fun y hy =>
    exists_nsmul_mem_latO'
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) y (infPart_of_half (infPart_cA hinf) ((isHalf_iff S T).2 hy))
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S T hk a, ← inv_smul_nsmul S T hk b]
    exact congrArg _ hab
  have hb := isBichar_symplO S T ψ
  have hm : Φ ∈ waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T e) (half S T (cA D e))
      ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) := by
    obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
    exact mem_waveSpan hb inf_le_right inf_le_right hLL' hX (half_div S T e) (half_div S T _) tf hfin' Φ
      (fun t ht => (isHalf_iff S T).1 (h1 t ht)) k hk (fun u hu => h2 u hu.1 ((isHalf_iff S T).2 hu.2))
      fun t ht => ⟨h3 t ht, (half S T e).nsmul_mem ((isHalf_iff S T).1 (h1 t ht)) _⟩
  clear hΦ
  induction hm using Submodule.span_induction with
  | mem _ hh =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hh
    refine ⟨ψ (symplOH S T x y) • Finsupp.single (x + y) 1, fun u hu => ?_, fun f₀ Tm hTm => ?_⟩
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset (Finsupp.support_smul hu))]
      have h1 := infPart_of_half hinf ((isHalf_iff S T).2 hx)
      have h2 := infPart_of_half (infPart_cA hinf) ((isHalf_iff S T).2 hy)
      refine ⟨?_, fun i j => ?_⟩
      · ext i j
        have a1 := congrFun (congrFun h1 i) j
        have a2 := congrFun (congrFun h2 i) j
        simp only [Matrix.map_apply, Matrix.add_apply, Matrix.zero_apply] at a1 a2 ⊢
        rw [RingHom.map_add (f := _), a1, a2, add_zero]
      · rw [Matrix.add_apply, mul_add, half1 x ((isHalf_iff S T).2 hx) i j, half2 y ((isHalf_iff S T).2 hy) i j]
    have s0 := GlobalTheory.isSBHalf_halfInd e (latO S T ΛS ΛT fun _ => True)
    have s1 : IsSBHalf e (latO S T ΛS ΛT fun _ => True)
        fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) t := by
      obtain ⟨k, hk, hk'⟩ := hden y hy
      obtain ⟨a1, k', hk1, a2, a3⟩ := s0
      refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
        fun t ht => ?_⟩
      · have e1 : halfInd e (latO S T ΛS ΛT fun _ => True) (t + (k * k') • u) =
            halfInd e (latO S T ΛS ΛT fun _ => True) t := by
          rw [mul_nsmul]
          exact a2 _ (nsmul_mem hu k) ((isHalf_iff S T).2 (nsmul_mem ((isHalf_iff S T).1 hh) k)) t
        have e2 : ψ (symplO S T ((k * k') • u) y) = 1 := by
          rw [mul_nsmul']
          exact (hb.nsmul k _ y).trans
            (hLL' _ (nsmul_mem (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hh⟩) k') _ ⟨hk', nsmul_mem hy k⟩)
        simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
      · rw [mul_nsmul']
        exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k
    have e1 : wave (fun x y : WO S T => ψ (symplO S T x y)) ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) x y =
        fun t => (fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) t) (t + x) := by
      rw [halfInd_eq_ind]; rfl
    have v1 := hTm.vac
    rw [one_smul] at v1
    rw [e1, hTm.trans _ s1 x ((isHalf_iff S T).2 hx), hTm.modul _ s0 y ((isHalf_iff S T).2 hy), v1]
    have hxy := heisL_heisL S T ψ x y f₀
    change heisO ψ S T x (heisO ψ S T y f₀) = ψ (symplOH S T x y) • heisO ψ S T (x + y) f₀ at hxy
    rw [hxy, GlobalTheory.LocComb.comb_smul, GlobalTheory.LocComb.comb_single]
  | zero => exact ⟨0, by simp, fun f₀ Tm _ => by rw [LinearMap.map_zero]; simp [comb]⟩
  | add g g' _ _ hg hg' =>
    obtain ⟨c, h1, h2⟩ := hg
    obtain ⟨c', h1', h2'⟩ := hg'
    exact ⟨c + c', fun w hw => (Finset.mem_union.1 (Finsupp.support_add hw)).elim (h1 w) (h1' w), fun f₀ Tm h => by
      rw [LinearMap.map_add (f := _), GlobalTheory.LocComb.comb_add, h2 f₀ Tm h, h2' f₀ Tm h]⟩
  | smul a g _ hg =>
    obtain ⟨c, h1, h2⟩ := hg
    exact ⟨a • c, fun w hw => h1 w (Finsupp.support_smul hw), fun f₀ Tm h => by
      rw [LinearMap.map_smul, GlobalTheory.LocComb.comb_smul, h2 f₀ Tm h]⟩

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {t : T}

theorem exists_isCombOf {p : Pair T} (hS : IsSelfDualC (G.pS p) (G.latS p)) (hT : IsSelfDualC (G.pT p) (G.latT p))
    (d : FinDatum G t p) : ∃ c, IsCombOf W d c := by
  obtain ⟨c, h1, h2⟩ := exists_comb_model W.ψ _ _ _ _ d.e d.fn W.ψ_std hS hT (idemSum_mul_self d.e_is) d.e_is.2
    (infPart_idemSum d.e_is) d.sb
  exact ⟨c, fun u hu => (h1 u hu).1, fun u hu => (h1 u hu).2, fun f₀ hth hvac =>
    ⟨(GlobalTheory.PlaceModelSum.placeModelExistsSum D W.ψ W.ψ_std _ _ _ _ hS hT d.P d.e d.e_is f₀ hth hvac).1, h2 f₀⟩⟩

theorem exists_isCombs {μ₀ : T} (hL : L.Is μ₀) (τ : PureDat G t →₀ ℂ) : ∃ c, IsCombs W τ c := by
  have sdT : ∀ j, j ≤ D.R.m → IsSelfDualC (G.V (.top j)) (G.Λ (.top j)) := fun j hj =>
    (G.isV (X := .top j) hj fun _ h => by cases h).sd
  have sdG : ∀ i, i ≤ D.R.m → IsSelfDualC (G.V (.grid i D.R.m)) (G.Λ (.grid i D.R.m)) := fun i hi => by
    cases i with
    | zero => exact (colY_isV D T L μ₀ hL D.R.m le_rfl).sd
    | succ i => exact (G.isV (X := .grid (i + 1) D.R.m) ⟨hi, le_rfl⟩ fun _ h => by cases h).sd
  choose c₁ h₁ using fun (d : PureDat G t) (j : Fin D.R.m) =>
    exists_isCombOf W (p := .top t j) (sdT j j.2.le) (sdT (j + 1) j.2) (d.1 j)
  choose c₂ h₂ using fun (d : PureDat G t) (i : Fin D.R.m) =>
    exists_isCombOf W (p := .chi i D.R.m) (isSelfDualC_neg (sdG (i + 1) i.2)) (sdG i i.2.le) (d.2 i)
  refine ⟨fun d => (fun j => if h : j < D.R.m then c₁ d ⟨j, h⟩ else 0, c₂ d), fun d _ => ⟨fun j => ?_, h₂ d⟩⟩
  dsimp only
  rw [dite_eq_left j.2]
  exact h₁ d j

theorem combs_exist : Big fun ch => ∀ t Φ β τ, ch.S.IsExpansion t Φ β τ → ∃ c, IsCombs ch.W τ c :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s ch _ _ _ _ _ τ _ => exists_isCombs ch.W s.core.lev τ⟩⟩

end GlobalTheory.CombsExist

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestExistsCombinationsOfExpansionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTest_exists_combinations_of_expansion : Big fun ch => ∀ t Φ β τ, ch.S.IsExpansion t Φ β τ → ∃ c, IsCombs ch.W τ c := by
  first | exact @GlobalTheory.CombsExist.combs_exist | exact GlobalTheory.CombsExist.combs_exist | (intros; apply GlobalTheory.CombsExist.combs_exist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRowFlagTiltUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRowFlagTiltUnique
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.TiltUnique

theorem tilt_unique : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {j : ℕ} (hj : j < D.R.m)
    (δ δ' : GA D (G.V (.grid D.R.m j))), IsTilt G j δ → IsTilt G j δ' → δ = δ' := by
  intro D T L sc G j hj δ δ' h h'
  rcases Nat.even_or_odd j with he | ho
  · rw [h.2.1 he, h'.2.1 he]
  · obtain ⟨a, ha⟩ := D.R.m_even
    obtain ⟨b, hb⟩ := ho
    have h₂ : D.R.m - 1 - j = 2 * ((D.R.m - 1 - j) / 2) := by omega
    obtain ⟨x1, x2, x3⟩ := h.2.2 _ hj h₂
    obtain ⟨y1, y2, y3⟩ := h'.2.2 _ hj h₂
    have k := (rowJac G j hj _ h₂).sum_eq_one
    have e0 : HMul.hMul (mt _ δ) (rowJac G j hj _ h₂).j0 = HMul.hMul (mt _ δ') (rowJac G j hj _ h₂).j0 := x1.trans y1.symm
    have eX : HMul.hMul (mt _ δ) (rowJac G j hj _ h₂).jX = HMul.hMul (mt _ δ') (rowJac G j hj _ h₂).jX := x2.trans y2.symm
    have eY : HMul.hMul (mt _ δ) (rowJac G j hj _ h₂).jY = HMul.hMul (mt _ δ') (rowJac G j hj _ h₂).jY := x3.trans y3.symm
    have hm : mt _ δ = mt _ δ' := by
      rw [← Matrix.mul_one (mt _ δ), ← Matrix.mul_one (mt _ δ')]
      rw [← k]
      simp only [Matrix.mul_add, ← Matrix.mul_assoc, e0, eX, eY]
    exact Subtype.ext (Units.ext hm)

end GlobalTheory.TiltUnique
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRowFlagTiltUniqueStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRowFlagTilt_unique : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {j : ℕ} (hj : j < D.R.m)
    (δ δ' : GA D (G.V (.grid D.R.m j))), IsTilt G j δ → IsTilt G j δ' → δ = δ' := by
  first | exact @GlobalTheory.TiltUnique.tilt_unique | exact GlobalTheory.TiltUnique.tilt_unique | (intros; apply GlobalTheory.TiltUnique.tilt_unique <;> assumption)
end
end
end
