module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HostTieTrueCols
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt

theorem host_tie_trueCols : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)), GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.HostTie (numDatumOfParameters (I.rec7 l Z) L) (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (B.primes X) := by
  intro B X I h l Z L
  have hX : B.fields.Ok := (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1.1
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _⟩ := host_fields_primes_ties I h hX l Z
  refine ⟨rfl, rfl, rfl, h1, h2, h3, h4, h5, h6, h7, h8, ?_, ?_, fun _ => rfl, HEq.rfl⟩
  · rw [h9]
    rfl
  · intro i; rw [h10]; rfl
end GlobalTheory.CoreHt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeightTieTrueCols
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightTieRec
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

namespace GlobalTheory.ColumnNormCompare

theorem mem_tops_rec (D : D7) (z : Bool × Formalism.MainNotions.G.HH D) :
    tauPl D z ∈ topsOf D.host D.eTau ↔ z.1 = false ∧ z.2 ∈ D.host.TT := by
  classical
  have hinj := D.R.toFrame.tau1_injective
  have hP := factPlaces D.R.toFrame
  have h0 : (D.eTau (tauPl D z) : D.R.GG) = Formalism.MainNotions.G.plGG D z := by simp [tauPl]
  unfold topsOf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [h0]
  unfold Host.topPlaces
  rw [Finset.mem_image]
  obtain ⟨b, t⟩ := z
  constructor
  · rintro ⟨t', ht, h⟩
    cases b <;> simp only [Formalism.MainNotions.G.plGG, if_true, if_false, Bool.false_eq_true] at h
    · exact ⟨rfl, (hinj h) ▸ ht⟩
    · exact absurd h (hP.2 _ _)
  · rintro ⟨h1, h2⟩
    refine ⟨t, h2, ?_⟩
    simp only at h1
    simp [Formalism.MainNotions.G.plGG, h1]

end GlobalTheory.ColumnNormCompare
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt

theorem weightTie_trueCols : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)), DelNat (I.rec7 l Z) → ∀ u : B.Word, GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.WeightTie (numDatumOfParameters (I.rec7 l Z) L) (X := B.fields) (Pr := B.primes X) B.wts (plRec (I.rec7 l Z)) u (codeRec L u) := by
  intro B X I _ l Z L hD u
  obtain ⟨n, hn⟩ := hD
  have hfl : ((⌊(I.rec7 l Z).s.Del⌋₊ : ℕ) : ℚ) = (I.rec7 l Z).s.Del := by rw [hn, Nat.floor_natCast]
  refine ⟨B.wts_isOk, fun z => ?_, fun z => ⟨?_, fun i => ?_⟩⟩
  · exact GlobalTheory.ColumnNormCompare.mem_tops_rec (I.rec7 l Z) z
  · exact B.wts_isOk.hc_row u _
  · change ((I.rec7 l Z).hcW u (plRec (I.rec7 l Z) z)).u i = _
    unfold NumDatum.uW
    obtain ⟨i, hi⟩ := i
    have hi' : i < (I.rec7 l Z).R.k := hi
    by_cases h : 1 ≤ i ∧ i + 1 < (I.rec7 l Z).R.k
    · rw [dite_eq_left h]
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      have hk : k < (I.rec7 l Z).R.k - 2 := by omega
      have a := (I.rec7 l Z).s.u_letter u (plRec (I.rec7 l Z) z) k hk
      have hv := (I.rec7 l Z).hcW_v u (plRec (I.rec7 l Z) z)
      rw [a, hv, ← hfl]
      rfl
    · rw [dite_eq_right h]
      by_cases h0 : i = 0
      · subst h0
        exact (I.rec7 l Z).hcW_first u _ hi'
      · have h1 : i = (I.rec7 l Z).R.k - 1 := by omega
        subst h1
        exact (I.rec7 l Z).hcW_last u _ (by omega)

end GlobalTheory.CoreHt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharTieTrueCols
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt

theorem charTie_trueCols : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)), GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.CharTie (numDatumOfParameters (I.rec7 l Z) L) (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (Pr := B.primes X) B.wts I.Ch I.glob I.sel := by
  intro B X I h l Z L
  exact ⟨h.ch_ok, rfl, rfl, ⟨I.C.eta, h.ch_tied⟩, h.weil, h.sel_ok⟩

end GlobalTheory.CoreHt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AnalyticTiesTrueCols
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2
attribute [local instance] GlobalTheory.Mem.Col2.starE

noncomputable section

namespace GlobalTheory.Core.Ht2

theorem analyticTies_trueCols : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (hX : B.fields.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)), ColIn.JetsIn I → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice (I.rec7 l Z) ⊤ I.J.δ ∧ TaylorLogMetric.IsChi (I.rec7 l Z) I.chi ∧ IsDgen (I.rec7 l Z) I.J.cD ∧ ∀ u a, GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.FieldOfDefinition (Pr := B.primes X) B.wts I.sel (I.tup a) (I.cst a) u I.A := by
  intro B X I h _ l Z hJ
  have hA := (I.J.ok_iff B (I.cols l) Z.W Z.V Z.S Z.N Z.G).1 h.amb_ok
  exact ⟨hA.1, GlobalTheory.Mem.ChiIdeal.isChi_chiId (I.rec7 l Z) I.C.chiPsi I.C.isChi, hA.2, fun u a i hi => hJ a u i hi⟩

end GlobalTheory.Core.Ht2

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientFieldIsFieldOfDefinitionChainSteps
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientFieldIsFieldOfDefinitionChainSteps
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ColRows.FldDef

theorem sd_of_isSdLat {B : Base} {n : ℕ} {L : Submodule (𝓞 B.host.E) (Fin n → B.host.E)}
    (h : Formalism.L2.Col.IsSdLat (E := B.fields.E) L) : letI := B.host.cmStar; IsSDLat B.host.E n L := by
  letI := B.host.cmStar
  have hspan : Submodule.span B.fields.E (L : Set (Fin n → B.fields.E)) = ⊤ := by
    apply Submodule.dualAnnihilator_eq_bot_iff.mp
    apply le_antisymm ?_ bot_le
    intro f hf
    let v : Fin n → B.fields.E := fun i => star (f (Pi.single i 1))
    have hpair : hStd B.fields.E n v = f := by
      apply (Pi.basisFun B.fields.E (Fin n)).ext
      intro i
      rw [Pi.basisFun_apply, hStd_apply, Finset.sum_eq_single i]
      · simp [v]
      · intro j _ hj
        simp [hj]
      · simp
    have hline (r : B.fields.E) : r • v ∈ L := by
      rw [← show Formalism.HermitianLatticesTheory.dual (hStd B.fields.E n) L = L from h.2,
        Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      intro y hy
      have hy0 : hStd B.fields.E n v y = 0 := by
        rw [hpair]
        exact (Submodule.mem_dualAnnihilator f).mp hf y (Submodule.subset_span hy)
      have hz : hStd B.fields.E n y v = 0 := by
        simpa [hy0] using ((hStd_isSymm (E := B.fields.E) (n := n)).eq v y).symm
      simp [hz]
    have hv : v = 0 := by
      funext i
      change v i = 0
      by_contra hi
      let coord := (LinearMap.proj i : (Fin n → B.fields.E) →ₗ[B.fields.E] B.fields.E).restrictScalars (𝓞 B.fields.E)
      have htop : L.map coord = ⊤ := by
        rw [eq_top_iff]
        intro x _
        exact ⟨(x / v i) • v, hline _, div_mul_cancel₀ _ hi⟩
      have : Module.Finite (𝓞 B.fields.E) B.fields.E := Module.finite_def.mpr (htop ▸ h.1.fg.map coord)
      exact RingOfIntegers.not_isField B.fields.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 B.fields.E) B.fields.E) (Field.toIsField B.fields.E))
    rw [Submodule.mem_bot]
    simpa [hv] using hpair.symm
  refine ⟨h.1.fg, hspan, fun y => ?_⟩
  have h2 : y ∈ Formalism.HermitianLatticesTheory.dual (hStd B.fields.E n) L ↔ y ∈ L := by rw [h.2]
  rw [← h2, Formalism.L2.Col.mem_dual]
  refine forall₂_congr fun x _ => ?_
  rw [Submodule.mem_one]
  rfl

theorem sd_stdL (D : D7) (n : ℕ) : StandardLatticesGL3.SD D (Th.stdL D.host n) := by
  exact GlobalTheory.Glob.IntegralWittCoefficients.Model.isSDLat_std _ _

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))

theorem chiRec_detId {idl : (I.rec7 l Z).Dt ⧸ (I.rec7 l Z).UO → TaylorLogMetric.IdE (I.rec7 l Z)}
    (hidl : TaylorLogMetric.RelDetPinned (I.rec7 l Z) idl) (n : ℕ) (L : Submodule (𝓞 B.host.E) (Fin n → B.host.E))
    (hL : StandardLatticesGL3.SD (I.rec7 l Z) L) :
    TaylorLogMetric.chiRec (I.rec7 l Z) idl (Th.detId B.host (Th.stdL B.host n) L) = I.chi (Th.detId B.host (Th.stdL B.host n) L) := by
  letI := B.host.cmStar
  let S0 : SDLat B.host.E n := ⟨Th.stdL B.host n, sd_stdL (I.rec7 l Z) n⟩
  let L1 : SDLat B.host.E n := ⟨L, hL⟩
  have h2 : idl ((I.rec7 l Z).relDet n S0 L1) = TaylorLogMetric.detId (I.rec7 l Z) S0.1 L1.1 := hidl.2.2.2.2 n S0 L1
  have e : TaylorLogMetric.detId (I.rec7 l Z) S0.1 L1.1 = Th.detId B.host (Th.stdL B.host n) L := rfl
  have hl : TaylorLogMetric.chiRec (I.rec7 l Z) idl (Th.detId B.host (Th.stdL B.host n) L) =
      ((TaylorLogMetric.chiQ (I.rec7 l Z) ((I.rec7 l Z).relDet n S0 L1) : ℂˣ) : ℂ) := by
    rw [← e, ← h2, TaylorLogMetric.chiRec_idl _ _ hidl.1]
  rw [hl]
  obtain ⟨t, ht⟩ := QuotientGroup.mk_surjective ((I.rec7 l Z).relDet n S0 L1)
  rw [← ht]
  have hχ := I.C.isChi
  have hK := (GlobalTheory.Mem.KerDet.kernel_open_and_factor B.R B.host).2.2.2 I.C.chiPsi hχ.triv (fun v y hy _ => hχ.unr v y hy)
    fun v _ => hχ.unr v
  have hr : (QuotientGroup.mk (toDtT B.host I.SQ t) : DtT B.host ⧸ UOT B.host) = relDetT B.host n (Th.stdL B.host n) L := by
    have h1 := toDtTMod_mk B.host I.SQ (t : DtQ B.host I.SQ)
    have h3 := toDtTMod_relDetQ B.host I.SQ n (Th.stdL B.host n) L
    have h6 : (QuotientGroup.mk (t : DtQ B.host I.SQ) : DtQ B.host I.SQ ⧸ UOQ B.host I.SQ) = relDetQ B.host I.SQ n (Th.stdL B.host n) L := ht
    rw [← h1, h6, h3]
  have h5 : ((tildeQ B.host I.SQ I.C.chiPsi t : ℂˣ) : ℂ) = ((tildeD B.host I.C.chiPsi (toDtT B.host I.SQ t) : ℂˣ) : ℂ) := by
    rw [tildeQ_eq_comp B.host I.SQ hK]; rfl
  exact h5.trans (GlobalTheory.Mem.ChiDet.tildeD_eq_chiId B.R B.host I.C.chiPsi hχ n L (Submodule.IsLattice.of_fg _ hL.1) _ hr)
end GlobalTheory.ColRows.FldDef

namespace GlobalTheory.ColRows.FldDef
open GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds

theorem fieldOfDefinition_congr {B : Base} (J : AmbIn B.host) (χ₁ χ₂ : Submodule (𝓞 B.host.E) B.host.E → ℂ)
    (hχ : ∀ (n : ℕ) (L : Submodule (𝓞 B.host.E) (Fin n → B.host.E)), Formalism.L2.Col.IsSdLat (E := B.fields.E) L →
      χ₁ (Th.detId B.host (Th.stdL B.host n) L) = χ₂ (Th.detId B.host (Th.stdL B.host n) L))
    {Pr : Primes B.fields} {R : Ranks} (W : Formalism.L2.Col.Wts B.fields Pr.Word R)
    (sel : HeightOneSpectrum (𝓞 B.fields.F) → HeightOneSpectrum (𝓞 B.fields.E)) {Sg : Set ℕ}
    (mu : Tup B.fields.F B.fields.E B.fields.K Sg) (cst : LocCst B.fields (rowSG Pr sel mu)) (u : Pr.Word) :
    FieldOfDefinition W sel mu cst u (J.amb B χ₁) → FieldOfDefinition W sel mu cst u (J.amb B χ₂) := by
  intro h i hi L L' c x hR e hdeg
  obtain ⟨y, hy⟩ := h i hi L L' c x hR e hdeg
  have hc : Th.chiFac B.host χ₁ (R.N i) (R.N (i + 1)) L L' = Th.chiFac B.host χ₂ (R.N i) (R.N (i + 1)) L L' := by
    unfold Th.chiFac
    rw [hχ _ L hR.1, hχ _ L' hR.2.1]
  have he : (J.amb B χ₁).e (R.N i) (R.N (i + 1)) L L' = (J.amb B χ₂).e (R.N i) (R.N (i + 1)) L L' := by
    funext z
    show Th.chiFac B.host χ₁ _ _ L L' * _ = Th.chiFac B.host χ₂ _ _ L L' * _
    rw [hc]
  have hth : (J.amb B χ₁).thInd (Sall sel mu u) L L' c x = (J.amb B χ₂).thInd (Sall sel mu u) L L' c x := by
    unfold Amb.thInd
    rw [he]
    rfl
  refine ⟨y, hy.trans ?_⟩
  rw [hth]
  show (Th.chiFac B.host χ₁ _ _ L L')⁻¹ * _ = (Th.chiFac B.host χ₂ _ _ L L')⁻¹ * _
  rw [hc]
  rfl
end GlobalTheory.ColRows.FldDef


open GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds in
theorem GlobalTheory.ColRows.fieldOfDefinition_of_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R), ColIn.JetsIn I → I.StdKer l Z t → HEq W B.wts → ∀ u a, GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.FieldOfDefinition W t.sel (t.tup a) (t.cst a) (t.word u) t.amb := by
  intro B X I hOk hPins l Z L hT Gi Gl K Y cX ex t W hJ hS hW u a
  obtain ⟨-, -, -, hFD⟩ := GlobalTheory.Core.Ht2.analyticTies_trueCols I hOk (GlobalTheory.Mem.Col2.base_fields_primes_ok B X).1 l Z hJ
  have hχ : ∀ (n : ℕ) (L : Submodule (𝓞 B.host.E) (Fin n → B.host.E)), Formalism.L2.Col.IsSdLat (E := B.fields.E) L →
      I.chi (Th.detId B.host (Th.stdL B.host n) L) = t.χ (Th.detId B.host (Th.stdL B.host n) L) := fun n L hL => by
    have h1 := GlobalTheory.ColRows.FldDef.chiRec_detId I l Z t.idl_ok n L (GlobalTheory.ColRows.FldDef.sd_of_isSdLat hL)
    have h2 := congrFun t.χ_rec (Th.detId B.host (Th.stdL B.host n) L)
    exact h1.symm.trans h2.symm
  have hF : ∀ (u' : (B.primes X).Word) (a' : I.ι), FieldOfDefinition (Pr := B.primes X) B.wts I.sel (I.tup a') (I.cst a') u' (I.J.amb B t.χ) :=
    fun u' a' => by
      have h3 := GlobalTheory.ColRows.FldDef.fieldOfDefinition_congr (R := B.R) I.J I.chi t.χ hχ B.wts I.sel (I.tup a') (I.cst a') u'
      have h4 : FieldOfDefinition (Pr := B.primes X) B.wts I.sel (I.tup a') (I.cst a') u' (I.J.amb B I.chi) := hFD u' a'
      exact h3 h4
  clear hFD hχ
  obtain ⟨hX, -, hPr, -, hsel, hS', hword, htup, hcst, -, -, -, hamb, -, -⟩ := hS
  cases t
  subst hX
  obtain rfl := eq_of_heq hPr
  subst hS'
  obtain rfl := eq_of_heq hsel
  obtain rfl := eq_of_heq htup
  obtain rfl := eq_of_heq hcst
  obtain rfl := eq_of_heq hword
  obtain rfl := eq_of_heq hW
  have hamb' := eq_of_heq hamb
  rw [hamb']
  exact hF u a
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientFieldIsFieldOfDefinitionChainStepsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficientField_isFieldOfDefinition_chainSteps : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R), ColIn.JetsIn I → I.StdKer l Z t → HEq W B.wts → ∀ u a, GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.FieldOfDefinition W t.sel (t.tup a) (t.cst a) (t.word u) t.amb := by
  first | exact @GlobalTheory.ColRows.fieldOfDefinition_of_stdKer | exact GlobalTheory.ColRows.fieldOfDefinition_of_stdKer | (intros; apply GlobalTheory.ColRows.fieldOfDefinition_of_stdKer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticCompatibilityStandardKernelDataTrueColum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticCompatibilityStandardKernelDataTrueColum
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.ColRows.analyticTie_of_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), ColIn.JetsIn I → I.StdKer l Z t → GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.AnalyticTie (I.rec7 l Z) t.δ t.χ t.cD ∧ t.tup (I.rec7 l Z).what₂.mu0 = 1 ∧ t.m2 = (I.rec7 l Z).R.m - 2 := by
  intro B X I hOk hPins l Z L hT Gi Gl K Y cX ex t hJ hS
  obtain ⟨-, -, hDg, -⟩ := GlobalTheory.Core.Ht2.analyticTies_trueCols I hOk (GlobalTheory.Mem.Col2.base_fields_primes_ok B X).1 l Z hJ

  have hcD : t.cD = I.J.cD := (t.O_dgen B.u₀ I.mu0).symm.trans (hS.O.dgen B.u₀ I.mu0)
  refine ⟨⟨t.cc_rec ▸ t.δ_ok, t.χ_ok, hcD ▸ hDg⟩, ?_, hS.m2⟩

  obtain ⟨hX, -, -, -, -, hSS, -, htup, -⟩ := hS
  cases t
  subst hX
  subst hSS
  cases htup
  exact I.trueColumn_tuple_trivial_eq_one
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticCompatibilityStandardKernelDataTrueColumStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analyticCompatibility_standardKernelData_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), ColIn.JetsIn I → I.StdKer l Z t → GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.AnalyticTie (I.rec7 l Z) t.δ t.χ t.cD ∧ t.tup (I.rec7 l Z).what₂.mu0 = 1 ∧ t.m2 = (I.rec7 l Z).R.m - 2 := by
  first | exact @GlobalTheory.ColRows.analyticTie_of_stdKer | exact GlobalTheory.ColRows.analyticTie_of_stdKer | (intros; apply GlobalTheory.ColRows.analyticTie_of_stdKer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightCompatibilityStandardKernelDataTrueColumns
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightCompatibilityStandardKernelDataTrueColumns
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)

noncomputable section

namespace GlobalTheory.ColRows


set_option maxHeartbeats 1000000 in
theorem weightTie_of_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), I.StdKer l Z t → HEq W B.wts → (I.rec7 l Z).s.Del = (Del : ℚ) → L.etaSz = ((I.rec7 l Z).R.m : ℝ) * (h0 : ℝ) → ∃ pl : RPl (I.rec7 l Z).R ≃ t.X.Tau, ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.WeightTie (ofRecord (I.rec7 l Z) L Del h0) W pl (t.word u) (letterOf (I.rec7 l Z) L Del h0 u) := by
  intro B X I hOk hPins l Z L hT Gi Gl K Y cX ex t W Del h0 hS hW hDel hEta
  obtain ⟨hX, -, hPr, -, -, -, hword, -, -, -, -, -, -, -, -⟩ := hS
  cases t
  subst hX
  cases hPr
  cases hword
  cases hW
  have hN := GlobalTheory.T.columnNormParameters_eq_natStepGap (I.rec7 l Z) L Del h0 hDel hEta
  refine ⟨plRec (I.rec7 l Z), fun u => ?_⟩
  have key := GlobalTheory.CoreHt.weightTie_trueCols I hOk l Z L ⟨Del, hDel⟩ u
  have gen : ∀ N : NumDatum, numDatumOfParameters (I.rec7 l Z) L = N → ∀ (W' : Wts B.fields (B.primes X).Word N.R), HEq B.wts W' →
      ∀ (pl' : RPl N.R ≃ B.fields.Tau), HEq (plRec (I.rec7 l Z)) pl' → ∀ δ : Code N, HEq (codeRec L u) δ →
      GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.WeightTie N (X := B.fields) (Pr := B.primes X) W' pl' u δ := by
    intro N hN W' hW' pl' hpl δ hδ
    subst hN
    cases hW'
    cases hpl
    cases hδ
    exact key
  exact gen _ hN _ HEq.rfl _ HEq.rfl _ HEq.rfl

end GlobalTheory.ColRows

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightCompatibilityStandardKernelDataTrueColumnsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightCompatibility_standardKernelData_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), I.StdKer l Z t → HEq W B.wts → (I.rec7 l Z).s.Del = (Del : ℚ) → L.etaSz = ((I.rec7 l Z).R.m : ℝ) * (h0 : ℝ) → ∃ pl : RPl (I.rec7 l Z).R ≃ t.X.Tau, ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.WeightTie (ofRecord (I.rec7 l Z) L Del h0) W pl (t.word u) (letterOf (I.rec7 l Z) L Del h0 u) := by
  first | exact @GlobalTheory.ColRows.weightTie_of_stdKer | exact GlobalTheory.ColRows.weightTie_of_stdKer | (intros; apply GlobalTheory.ColRows.weightTie_of_stdKer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostCompatibilityStandardKernelDataTrueColumns
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostCompatibilityStandardKernelDataTrueColumns
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColRows

theorem hostTie_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), I.StdKer l Z t → GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.HostTie (ofRecord (I.rec7 l Z) L Del h0) t.seam t.Pr := by
  intro B X I hOk hPins l Z L hT Gi Gl K Y cX ex t W Del h0 hS
  obtain ⟨hX, hseam, hPr, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hS
  cases t
  dsimp only at *
  subst hX
  obtain rfl := eq_of_heq hPr
  obtain rfl := eq_of_heq hseam
  exact GlobalTheory.CoreHt.host_tie_trueCols I hOk l Z L

end GlobalTheory.ColRows

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostCompatibilityStandardKernelDataTrueColumnsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hostCompatibility_standardKernelData_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), I.StdKer l Z t → GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.HostTie (ofRecord (I.rec7 l Z) L Del h0) t.seam t.Pr := by
  first | exact @GlobalTheory.ColRows.hostTie_stdKer | exact GlobalTheory.ColRows.hostTie_stdKer | (intros; apply GlobalTheory.ColRows.hostTie_stdKer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterCompatibilityStandardKernelDataTrueColu
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterCompatibilityStandardKernelDataTrueColu
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColRows

theorem charTie_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), I.StdKer l Z t → HEq W B.wts → GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.CharTie (ofRecord (I.rec7 l Z) L Del h0) t.seam W t.Ch t.glob t.sel := by
  intro B X I hOk hPins l Z L hT Gi Gl K Y cX ex t W Del h0 hS hW
  obtain ⟨hX, hseam, hPr, hCh, hsel, -, -, -, -, -, -, hglob, -, -, -⟩ := hS
  cases t
  dsimp only at *
  subst hX
  obtain rfl := eq_of_heq hPr
  obtain rfl := eq_of_heq hseam
  obtain rfl := eq_of_heq hCh
  rw [eq_of_heq hsel, eq_of_heq hglob, eq_of_heq hW]
  exact GlobalTheory.CoreHt.charTie_trueCols I hOk l Z L

end GlobalTheory.ColRows

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterCompatibilityStandardKernelDataTrueColuStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterCompatibility_standardKernelData_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), I.StdKer l Z t → HEq W B.wts → GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.CharTie (ofRecord (I.rec7 l Z) L Del h0) t.seam W t.Ch t.glob t.sel := by
  first | exact @GlobalTheory.ColRows.charTie_stdKer | exact GlobalTheory.ColRows.charTie_stdKer | (intros; apply GlobalTheory.ColRows.charTie_stdKer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelCompatibilitiesStandardKernelDataTrueColum
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ColRows

theorem kerTies_of_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), ColIn.JetsIn I → I.StdKer l Z t → HEq W B.wts → (I.rec7 l Z).s.Del = (Del : ℚ) → L.etaSz = ((I.rec7 l Z).R.m : ℝ) * (h0 : ℝ) → (t.cst (I.rec7 l Z).what₂.mu0).sharp = true → GlobalTheory.ColRows.KerTies t W Del h0 := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t W Del h0 hJ hS hW hDel hEta hSharp
  obtain ⟨hAn, hMu, hM2⟩ := GlobalTheory.T.analyticCompatibility_standardKernelData_trueColumns I hOk hP l Z L hT Gi Gl K Y cX ex t hJ hS
  exact
    { host := GlobalTheory.T.hostCompatibility_standardKernelData_trueColumns I hOk hP l Z L hT Gi Gl K Y cX ex t W Del h0 hS
      wts := GlobalTheory.T.weightCompatibility_standardKernelData_trueColumns I hOk hP l Z L hT Gi Gl K Y cX ex t W Del h0 hS hW hDel hEta
      chr := GlobalTheory.T.characterCompatibility_standardKernelData_trueColumns I hOk hP l Z L hT Gi Gl K Y cX ex t W Del h0 hS hW
      an := hAn
      mu0 := hMu
      sharp := hSharp
      m2 := hM2
      fld := fun u => GlobalTheory.T.coefficientField_isFieldOfDefinition_chainSteps I hOk hP l Z L hT Gi Gl K Y cX ex t W hJ hS hW u _ }

end GlobalTheory.ColRows
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelCompatibilitiesStandardKernelDataTrueColumStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelCompatibilities_standardKernelData_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), ColIn.JetsIn I → I.StdKer l Z t → HEq W B.wts → (I.rec7 l Z).s.Del = (Del : ℚ) → L.etaSz = ((I.rec7 l Z).R.m : ℝ) * (h0 : ℝ) → (t.cst (I.rec7 l Z).what₂.mu0).sharp = true → GlobalTheory.ColRows.KerTies t W Del h0 := by
  first | exact @GlobalTheory.ColRows.kerTies_of_stdKer | exact GlobalTheory.ColRows.kerTies_of_stdKer | (intros; apply GlobalTheory.ColRows.kerTies_of_stdKer <;> assumption)
end
