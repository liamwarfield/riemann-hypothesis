module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulas
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLatticeDualZIdealMul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalDatumThetaFactorsPlaceByPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegral
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameCoordsMemSelfDualLatticeCoordsIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtToEAfEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinMComp

variable {D : D7}

theorem eq_zero_of_le_exp (x : WithZero (Multiplicative ℤ)) (h : ∀ n : ℕ, x ≤ WithZero.exp (-(n : ℤ))) : x = 0 := by
  by_contra hx
  obtain ⟨m, rfl⟩ := WithZero.ne_zero_iff_exists.1 hx
  have h1 := h (Int.toNat (-(Multiplicative.toAdd m)) + 1)
  have e : ((m : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = WithZero.exp (Multiplicative.toAdd m) := rfl
  rw [e, WithZero.exp_le_exp] at h1
  omega

theorem afIso_indP (w : GlobalTheory.FinPl.Pl D) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : P.under (𝓞 D.host.F) = w) :
    GlobalTheory.Mem.Col2.afIso D.host.F D.host.E ((1 : D.host.E) ⊗ₜ[D.host.F] GlobalTheory.FinPl.KOpen.indP D (· = w)) P = 1 := by
  have hs := fun n =>
    (GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv D.host.F D.host.E).choose_spec.2.2.2
      (GlobalTheory.FinPl.KOpen.indP D (· = w)) 1 P n
  have h0 : (GlobalTheory.FinPl.KOpen.indP D (· = w)) (P.under (𝓞 D.host.F)) - algebraMap D.host.F _ 1 = 0 := by
    have := GlobalTheory.FinPl.KOpen.evalV_indP (D := D) (· = w) (P.under (𝓞 D.host.F))
    rw [if_pos hP] at this
    rw [map_one, sub_eq_zero]
    exact this
  have h1 : ∀ n : ℕ, Valued.v (GlobalTheory.Mem.Col2.afIso D.host.F D.host.E
      ((1 : D.host.E) ⊗ₜ[D.host.F] GlobalTheory.FinPl.KOpen.indP D (· = w)) P
      - algebraMap D.host.E _ (algebraMap D.host.F D.host.E 1)) ≤ WithZero.exp (-(n : ℤ)) := fun n =>
    hs n (by rw [h0, Valuation.map_zero]; exact zero_le')
  have h2 := eq_zero_of_le_exp _ h1
  rw [Valuation.zero_iff, map_one, map_one, sub_eq_zero] at h2
  exact h2

theorem indicatorAdele_mul_eq_zero (w : GlobalTheory.FinPl.Pl D) (z : Af D.host.F ⊗[D.host.F] D.host.E)
    (hz : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w z = 0) :
    (GlobalTheory.FinPl.KOpen.indP D (· = w) ⊗ₜ[D.host.F] (1 : D.host.E)) * z = 0 := by
  refine GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun v => ?_
  change GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v _ = GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v 0
  rw [map_mul, map_zero, GlobalTheory.FinPl.KOpen.compFin_e]
  by_cases hv : v = w
  · subst hv; rw [hz, mul_zero]
  · rw [if_neg hv, zero_mul]

theorem adAt_toEAf_eq_zero (w : GlobalTheory.FinPl.Pl D) (a : AE D) (ha : GlobalTheory.FinPl.compAt D w a = 0)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : P.under (𝓞 D.host.F) = w) :
    GlobalTheory.Mem.Col2.adAt D.host.F P (toEAf D a) = 0 := by
  have h0 := congrArg (fun y => GlobalTheory.Mem.Col2.adAt D.host.F P
    ((Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toAlgHom.toRingHom y))
    (indicatorAdele_mul_eq_zero w (finPart D a) ha)
  simp only [map_mul, map_zero] at h0
  have e1 : (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toAlgHom.toRingHom
      (GlobalTheory.FinPl.KOpen.indP D (· = w) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      (1 : D.host.E) ⊗ₜ[D.host.F] GlobalTheory.FinPl.KOpen.indP D (· = w) := rfl
  rw [e1, GlobalTheory.Mem.Col2.adAt_apply D.host.F P ((1 : D.host.E) ⊗ₜ[D.host.F] _), afIso_indP w P hP, one_mul] at h0
  exact h0

theorem adAt_finM_eq_one : ∀ (D : D7) (V : HSp D) {n : ℕ} (hn : V.rank = n) (Pset : GlobalTheory.FinPl.Pl D → Prop) (h : GA D V),
    h ∈ GlobalTheory.FinPl.grpAt V Pset → ∀ P : HeightOneSpectrum (𝓞 D.host.E), ¬ Pset (P.under (𝓞 D.host.F)) → ∀ r k,
      adAt D.host.F P (finM V hn h r k) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion D.host.E)) r k := by
  intro D V n hn Pset h hh P hP r k
  subst hn
  rw [GlobalTheory.AdForm.CongAtIdem.finM_rfl, Matrix.map_apply]
  have hmem := (GlobalTheory.FinPl.SetCut.mem_congGrp_iff V _ h).1 hh r k
  have hz := adAt_toEAf_eq_zero _ _ (((GlobalTheory.FinPl.mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D Pset _).1 hmem).2 _ hP) P rfl
  have e : Formalism.L2.Theta.mt V h r k = (Formalism.L2.Theta.mt V h - 1) r k + (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) r k := by
    rw [Matrix.sub_apply, sub_add_cancel]
  rw [e, RingHom.map_add (toEAf D), RingHom.map_add (GlobalTheory.Mem.Col2.adAt D.host.F P), hz, zero_add]
  by_cases hrk : r = k
  · subst hrk; simp [Matrix.one_apply]
  · simp [Matrix.one_apply, hrk]

end GlobalTheory.FinMComp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroRamifiedFormsTransportIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroRamifiedFormsTransportIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RamZero

open GlobalTheory.Mem.Col2.TwAtStd

theorem levelZero_classTransport_values {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (ψ₀ : ((I.rec7 l Z).mem u).C.cls 0 → ((I.rec7 l Z).mem u).C.Y 0 → ℂ)
    (c : (I.stp u I.mu0 0).Cl) :
    (I.rec7 l Z).e0Tw u a ψ₀ (I.eCls0 l u a c) = ψ₀ c := by
  show ψ₀ ((I.eCls0 l u a).symm (I.eCls0 l u a c)) = ψ₀ c
  rw [Equiv.symm_apply_apply]

theorem mram_iff_ramT : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), I.Law0 l → ∀ (u : B.Word) (a : I.ι) (ψ₀ : ((I.rec7 l Z).mem u).C.cls 0 → ((I.rec7 l Z).mem u).C.Y 0 → ℂ), ψ₀ ∈ ((I.rec7 l Z).mem u).A.Mram ↔ GlobalTheory.AdForm.RamT (I := I) (l := l) (u := u) (a := a) 0 ((I.rec7 l Z).e0Tw u a ψ₀) := by
  intro B X I hI l Z _ u a ψ₀
  have hval := levelZero_classTransport_values I l Z u a ψ₀
  have e1 := mem_Fi_of_free (I.stp u I.mu0 0) B.fields.emb B.embLL (lamT (B.hcW u) 0) (l.lev u I.mu0).free0 ψ₀
  have e2 := mem_Fi_of_free (I.stp u a 0) B.fields.emb B.embLL (lamT (B.hcW u) 0) (l.lev u a).free0
    ((I.rec7 l Z).e0Tw u a ψ₀)
  have hFi : ψ₀ ∈ ((I.rec7 l Z).mem u).A.Mu0 ↔ (I.rec7 l Z).e0Tw u a ψ₀ ∈ (I.fm l u a).Fi 0 := by
    refine e1.trans (Iff.trans ⟨fun h c' => ?_, fun h c => ?_⟩ e2.symm)
    · obtain ⟨c, rfl⟩ := (I.eCls0 l u a).surjective c'
      have := h c
      rw [← hval c] at this
      exact this
    · have := h (I.eCls0 l u a c)
      rw [hval c] at this
      exact this
  have hN : ∀ (v : ((I.rec7 l Z).mem u).A.vT) (c : (I.stp u I.mu0 0).Cl),
      ∑ᶠ s : ((I.atT l u a).Fv v)ˣ, (I.fm l u a).dilT 0 v s (I.eCls0 l u a c)
        ((I.rec7 l Z).e0Tw u a ψ₀ ((I.fm l u a).dil 0 v s (I.eCls0 l u a c))) = ((I.rec7 l Z).mem u).A.Nm v ψ₀ c := by
    intro v c
    have eR : ∀ c' : ((I.rec7 l Z).mem u).C.cls 0, ((I.rec7 l Z).mem u).A.Nm v ψ₀ c' =
        ∑ s, (((I.rec7 l Z).fm u).dilT 0 v s c') (ψ₀ (((I.rec7 l Z).fm u).dil 0 v s c')) := fun c' => by
      unfold ColumnsAtT.Nm
      rw [LinearMap.sum_apply, Finset.sum_apply]
      exact Finset.sum_congr rfl fun x _ => ((I.rec7 l Z).fm u).rhoT_dil v x ψ₀ c'
    rw [eR c]
    letI := (I.atT l u a).FvFin v
    letI := (I.atT l u a).FvDec v
    rw [finsum_eq_sum_of_fintype]
    refine Fintype.sum_equiv (Equiv.refl _) _ _ fun s => ?_
    show (I.atIn u a).dilT B.fields.emb B.embLL 0 v s (I.eCls0 l u a c)
        ((I.rec7 l Z).e0Tw u a ψ₀ ((I.atIn u a).dil 0 v s (I.eCls0 l u a c))) =
      (I.atIn u I.mu0).dilT B.fields.emb B.embLL 0 v s c (ψ₀ ((I.atIn u I.mu0).dil 0 v s c))
    rw [dil_eCls0 B X I hI l u a v s c, dilT_eCls0 B X I hI l u a v s c, hval]
  unfold ColumnsAtT.Mram GlobalTheory.AdForm.RamT
  rw [Submodule.mem_inf, Submodule.mem_iInf]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hFi.1 h1, fun v c' => ?_⟩
    obtain ⟨c, rfl⟩ := (I.eCls0 l u a).surjective c'
    refine (hN v c).trans ?_
    exact congrFun (LinearMap.mem_ker.1 (h2 v)) c
  · rintro ⟨h1, h2⟩
    exact ⟨hFi.2 h1, fun v => LinearMap.mem_ker.2 (funext fun c => (hN v c).symm.trans (h2 v (I.eCls0 l u a c)))⟩

end GlobalTheory.RamZero

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroRamifiedFormsTransportIffStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZero_ramifiedForms_transport_iff : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), I.Law0 l → ∀ (u : B.Word) (a : I.ι) (ψ₀ : ((I.rec7 l Z).mem u).C.cls 0 → ((I.rec7 l Z).mem u).C.Y 0 → ℂ), ψ₀ ∈ ((I.rec7 l Z).mem u).A.Mram ↔ GlobalTheory.AdForm.RamT (I := I) (l := l) (u := u) (a := a) 0 ((I.rec7 l Z).e0Tw u a ψ₀) := by
  first | exact @GlobalTheory.RamZero.mram_iff_ramT | exact GlobalTheory.RamZero.mram_iff_ramT | (intros; apply GlobalTheory.RamZero.mram_iff_ramT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorSchrodingerModelIsKFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorSchrodingerModelIsKFinite
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.StdUnn.KFin

theorem fock_kfinite : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 → ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω → ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l → ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ Φ : schwartzA θ V.rank n, Φ.1 ∈ fockA θ V n l s → FiniteDimensional ℂ (Submodule.span ℂ {Ψ : schwartzA θ V.rank n | ∃ k ∈ K D n, Ψ = ω k Φ}) := by
  intro D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, hlam, hψeq, hchart, hdat, htr⟩ :=
    GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨lam', hlam', -, l', hl', habs⟩ := GlobalTheory.StdUnn.shift_char_realPar D ψ₀ hstd θ hθ μ' hsk
  have hll : lam' = lam := (algebraMap D.host.F D.host.E).injective (hlam'.trans hlam.symm)
  subst hll
  have hl'' : HasRealPar ψ θ l' := hψeq ▸ hl'
  have hleq : l = l' := GlobalTheory.T.archimedean_parameters_addChar_unique D ψ θ hθ l l' hl hl''
  subst hleq
  obtain ⟨-, hsurj, -⟩ := GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ₀ hstd θ hθ A V μ 𝓕 hμ
  obtain ⟨f, hf, hfΦ⟩ := hsurj Φ.1 Φ.2
  obtain ⟨s', hstd', hcomm⟩ := GlobalTheory.T.exists_standardCartanInvolution_commute_compact D A μ' hsk κ hchart θ hθ
  have hfock : IsFockVec ψ₀ θ (dblSp A) V s' s f :=
    GlobalTheory.T.isFockVector_of_schrodinger_mem_fockSpace D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs f hf (hfΦ ▸ hΦ)

  have hcont := GlobalTheory.StdUnn.chart_continuous D A μ' hsk κ hchart
  let K' : Subgroup (GA D (dblSp A)) := (K D A.rank).comap κ.toMonoidHom
  have hK' : IsCompact (K' : Set (GA D (dblSp A))) := by
    have h1 : (K' : Set (GA D (dblSp A))) = κ.symm '' (K D A.rank : Set (G D A.rank)) := by
      ext g
      simp only [K', Subgroup.coe_comap, Set.mem_preimage, SetLike.mem_coe, MulEquiv.coe_toMonoidHom]
      constructor
      · intro hg; exact ⟨κ g, hg, κ.symm_apply_apply g⟩
      · rintro ⟨k, hk, rfl⟩; simpa using hk
    rw [h1]
    exact (GlobalTheory.StdUnn.HeightExists.isCompact_K).image hcont.2
  have hkf : GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.IsKFinVec omh K' f :=
    GlobalTheory.Core.Rk.IP.isKFinVec_of_isFockVec D ψ₀ θ (dblSp A) V 1 χ⁻¹ omh s' s hdat hθ
      (GlobalTheory.CartStd.isCartanInv_stdInv D A μ' hsk s' hstd') hs K' hK' (fun k hk τ => hcomm k hk τ) f hfock
  haveI : FiniteDimensional ℂ (Submodule.span ℂ {g : WO (dblSp A) V → ℂ | ∃ k ∈ K', g = omh (k, 1) f}) := hkf

  let T := Formalism.IndefR.Eqv.thetaSubO ψ₀ (dblSp A) V
  let L : T →ₗ[ℂ] (Mx D V.rank A.rank → ℂ) :=
    { toFun := fun g => sch ψ₀ A V μ 𝓕 g.1
      map_add' := fun g h => (GlobalTheory.StdUnn.sch_linear D ψ₀ hstd A V μ 𝓕 hμ g.1 h.1 g.2 h.2 1).2.2.1
      map_smul' := fun c g => (GlobalTheory.StdUnn.sch_linear D ψ₀ hstd A V μ 𝓕 hμ g.1 g.1 g.2 g.2 c).2.2.2 }
  let W : Submodule ℂ T := Submodule.span ℂ {g : T | ∃ k ∈ K', g.1 = omh (k, 1) f}
  have hWmap : W.map T.subtype ≤ Submodule.span ℂ {g : WO (dblSp A) V → ℂ | ∃ k ∈ K', g = omh (k, 1) f} := by
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨g, ⟨k, hk, hg⟩, rfl⟩
    exact ⟨k, hk, hg⟩
  haveI : FiniteDimensional ℂ (W.map T.subtype) := Submodule.finiteDimensional_of_le hWmap
  haveI : FiniteDimensional ℂ W :=
    LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective T.subtype Subtype.val_injective W).symm
  have hWL : FiniteDimensional ℂ (W.map L) := Module.Finite.map W L
  set S := Submodule.span ℂ {Ψ : schwartzA θ V.rank n | ∃ k ∈ K D n, Ψ = ω k Φ} with hSdef
  have hSmap : S.map (schwartzA θ V.rank n).subtype ≤ W.map L := by
    rw [hSdef, Submodule.map_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨Ψ, ⟨k, hk, rfl⟩, rfl⟩
    have hth : IsThetaFunO ψ₀ (dblSp A) V (omh (κ.symm k, 1) f) := hdat.om_pres _ f hf
    refine ⟨⟨_, hth⟩, Submodule.subset_span ⟨κ.symm k, ?_, rfl⟩, ?_⟩
    · show κ (κ.symm k) ∈ K D A.rank
      rw [show κ (κ.symm k) = k from κ.apply_symm_apply k]
      exact hk
    · have := htr (κ.symm k) f hf Φ hfΦ.symm
      rw [show κ (κ.symm k) = k from κ.apply_symm_apply k] at this
      exact this.symm
  haveI : FiniteDimensional ℂ (S.map (schwartzA θ V.rank n).subtype) := @Submodule.finiteDimensional_of_le _ _ _ _ _ _ _ hWL hSmap
  exact Module.Finite.equiv (Submodule.equivMapOfInjective (schwartzA θ V.rank n).subtype Subtype.val_injective S).symm

end GlobalTheory.StdUnn.KFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorSchrodingerModelIsKFiniteStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVector_schrodingerModel_isKFinite : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 → ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω → ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l → ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ Φ : schwartzA θ V.rank n, Φ.1 ∈ fockA θ V n l s → FiniteDimensional ℂ (Submodule.span ℂ {Ψ : schwartzA θ V.rank n | ∃ k ∈ K D n, Ψ = ω k Φ}) := by
  first | exact @GlobalTheory.StdUnn.KFin.fock_kfinite | exact GlobalTheory.StdUnn.KFin.fock_kfinite | (intros; apply GlobalTheory.StdUnn.KFin.fock_kfinite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineVectorPairingMemInverseIdealCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineVectorPairingMemInverseIdealCompletion
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.LineDual

variable {D : D7}

theorem intAt_zero' (P : Pl D → Prop) : (0 : AE D) ∈ intAt D P :=
  ⟨zero_mem _, by rw [RingHom.map_zero]; exact zero_mem _⟩

theorem intAt_add' {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) : a + b ∈ intAt D P :=
  ⟨add_mem ha.1 hb.1, by rw [RingHom.map_add (f := _)]; exact add_mem ha.2 hb.2⟩

theorem intAt_neg' {P : Pl D → Prop} {a : AE D} (ha : a ∈ intAt D P) : -a ∈ intAt D P :=
  ⟨neg_mem ha.1, by rw [RingHom.map_neg]; exact neg_mem ha.2⟩

theorem latV_entry_mem_idAt {S : HSp D} {M : Lat S} {P : Pl D → Prop} {y : Fin S.rank → AE D}
    (hy : y ∈ latV S M P) (i : Fin S.rank) : y i ∈ idAt D P := by
  induction hy using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, -, hα, a, -, x, -, rfl⟩ := hw
    exact LatMem.tmul_mem_idAt hα _
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

theorem idV_mem_idAt {𝔞 : FI D} {v : Pl D} {t : AE D} (ht : t ∈ idV 𝔞 v) : t ∈ idAt D (· = v) := by
  induction ht using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, -, hα, a, -, rfl⟩ := hw
    exact LatMem.tmul_mem_idAt (fun w hw => hα w hw) _
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

theorem cA_mem_idAt {v : Pl D} {a : AE D} (h : a ∈ idAt D (· = v)) : cA D a ∈ idAt D (· = v) := by
  rw [GlobalTheory.FinPl.Model.mem_idAt_iff] at h ⊢
  rw [← Algebra.smul_def] at h ⊢
  conv_rhs => rw [← h]
  rw [GlobalTheory.HeisDisj.cA_smul]

def pr (S : HSp D) (w y : Fin S.rank → AE D) : AE D := ∑ l, (∑ m, cA D (w m) * gA S m l) * y l

theorem pr_zero_left (S : HSp D) (y : Fin S.rank → AE D) : pr S 0 y = 0 := by simp [pr]
theorem pr_zero_right (S : HSp D) (w : Fin S.rank → AE D) : pr S w 0 = 0 := by simp [pr]
theorem pr_add_left (S : HSp D) (w w' y : Fin S.rank → AE D) : pr S (w + w') y = pr S w y + pr S w' y := by
  simp [pr, add_mul, Finset.sum_add_distrib]
theorem pr_add_right (S : HSp D) (w y y' : Fin S.rank → AE D) : pr S w (y + y') = pr S w y + pr S w y' := by
  simp [pr, mul_add, Finset.sum_add_distrib]
theorem pr_neg_left (S : HSp D) (w y : Fin S.rank → AE D) : pr S (-w) y = -pr S w y := by
  simp [pr]
theorem pr_neg_right (S : HSp D) (w y : Fin S.rank → AE D) : pr S w (-y) = -pr S w y := by
  simp [pr]

theorem pr_gen (S : HSp D) (α β : Af D.host.F) (x x' : Fin S.rank → D.host.E) :
    pr S (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x' i)) =
      pairA D.host.F 0 (α * β) ⊗ₜ[D.host.F] (∑ m, ∑ l, star (x m) * S.gram m l * x' l) := by
  have hc : ∀ m, cA D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x m) = pairA D.host.F 0 α ⊗ₜ[D.host.F] star (x m) :=
    fun _ => rfl
  have hg : ∀ m l, gA S m l = (1 : AF D.host.F) ⊗ₜ[D.host.F] S.gram m l := fun _ _ => rfl
  have hp : pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := Prod.ext (zero_mul _) rfl
  simp only [pr, one_mul]
  simp only [hc, hg, Finset.sum_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hp]
  rw [Finset.sum_comm]
  simp only [← TensorProduct.tmul_sum]

theorem pr_mem_intAt {S : HSp D} {M : Lat S} (hM : IsSelfDualC S M) {P : Pl D → Prop} {w y : Fin S.rank → AE D}
    (hw : w ∈ latV S M P) (hy : y ∈ latV S M P) : pr S w y ∈ intAt D P := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hw
    rw [Set.mem_singleton_iff] at ha
    subst ha
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨β, hβi, hβ, c, hc, x', hx', rfl⟩ := hz
      rw [Set.mem_singleton_iff] at hc
      subst hc
      rw [pr_gen]
      obtain ⟨b, hb⟩ := (hM.2 x').1 hx' x hx
      refine ⟨LatMem.tmul_mem_idAt (fun v hv => by rw [map_mul, hα v hv, zero_mul]) _, ?_⟩
      rw [← hb]
      exact AddSubgroup.subset_closure ⟨α * β, LatMem.intAf_mul' hαi hβi, b, rfl⟩
    | zero => rw [pr_zero_right]; exact intAt_zero' _
    | add z z' _ _ hz hz' => rw [pr_add_right]; exact intAt_add' hz hz'
    | neg z _ hz => rw [pr_neg_right]; exact intAt_neg' hz
  | zero => rw [pr_zero_left]; exact intAt_zero' _
  | add w w' _ _ hw hw' => rw [pr_add_left]; exact intAt_add' hw hw'
  | neg w _ hw => rw [pr_neg_left]; exact intAt_neg' hw

theorem line_pair_mem_idV : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A L : HSp D) (o : OrthDec S A L)
    (ζ : Fin L.rank → D.host.E) (M : Lat S) (𝔠 : FI D) (v : Pl D), IsSelfDualC S M → LineId o ζ M 𝔠 v → 𝔠 ≠ 0 →
      ∀ y ∈ latV S M (· = v), cA D (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l) ∈ idV 𝔠⁻¹ v := by
  intro D ψ hψ S A L o ζ M 𝔠 v hM hline h𝔠 y hy
  obtain ⟨h1, h2, -, h4, -⟩ := GlobalTheory.SeeSaw.idV_props D ψ hψ v
  have hX : (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l) ∈ idAt D (· = v) :=
    sum_mem fun l _ => Ideal.mul_mem_left _ _ (latV_entry_mem_idAt hy l)
  have hcX := cA_mem_idAt hX
  have hcint : ∀ s, s ∈ intAt D (· = v) → cA D s ∈ intAt D (· = v) := by
    intro s hs
    have e2 : s ∈ idV (D.host.AA ^ (0 : ℤ)) v := by rw [zpow_zero]; exact (h1 s).2 hs
    have e3 := (h4 0 s).1 e2
    rw [zpow_zero] at e3
    exact (h1 _).1 e3
  have key := (h2 𝔠 1 h𝔠 one_ne_zero _ hcX).1 (fun t ht => ?_)
  · rwa [one_mul] at key
  · have htI : t ∈ idAt D (· = v) := idV_mem_idAt ht
    have htz : t • ratV (vecB o ζ) ∈ latV S M (· = v) := (hline t htI).2 ht
    have hp := pr_mem_intAt hM htz hy
    have he : pr S (t • ratV (vecB o ζ)) y = cA D t * ∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l := by
      simp only [pr, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [he] at hp
    have h5 := hcint _ hp
    rw [map_mul, Formalism.L2.Theta.cA_cA, mul_comm] at h5
    exact (h1 _).2 h5

end GlobalTheory.LineDual

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineVectorPairingMemInverseIdealCompletionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineVector_pairing_mem_inverseIdealCompletion : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A L : HSp D) (o : OrthDec S A L)
    (ζ : Fin L.rank → D.host.E) (M : Lat S) (𝔠 : FI D) (v : Pl D), IsSelfDualC S M → LineId o ζ M 𝔠 v → 𝔠 ≠ 0 →
      ∀ y ∈ latV S M (· = v), cA D (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l) ∈ idV 𝔠⁻¹ v := by
  first | exact @GlobalTheory.LineDual.line_pair_mem_idV | exact GlobalTheory.LineDual.line_pair_mem_idV | (intros; apply GlobalTheory.LineDual.line_pair_mem_idV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalDatumFoldrLocalCombinations
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalDatumSplitPlaceCombinationMulLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalDatumSplitPlaceCombinationMulLocal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod


set_option maxHeartbeats 1000000 in
theorem ratDatum_comb_place : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → DenseRange p.pr → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (e : AE D), PP ∉ P → Formalism.L2.NTheta.IsIdemAt p.e PP → IsIdemSum e P → IsIdemSum (e + p.e) (@insert _ _ (@Finset.instInsert _ (Classical.decEq _)) PP P) → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ↔ p.up FS FT x ∈ stdHom S T) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (ΛS : Set (Fin S.rank → D.host.E)) = intVec D S.rank → (ΛT : Set (Fin T.rank → D.host.E)) = intVec D T.rank → ∀ (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (Ξk : Matrix Y Y' k → ℂ), Ξk ∈ SB (Matrix Y Y' k) → ∀ c, p.IsCombAt ψ FS FT c Ξk → ∀ f₀ f, IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (stdHom S T) f₀ → IsRatDatum ψ S T e Ξ f₀ f → IsRatDatum ψ S T (e + p.e) (fun γ => Ξ γ * Ξk (FT.γ * γ.map p.pr * FS.β)) f₀ (comb ψ S T c f) := by
  intro D k _ _ _ _ p ψ hψ hdense S T Y Y' _ _ _ _ FS FT P PP e hPP hIdemAt hE hE' hstd ΛS ΛT hS hT hΛS hΛT Ξ Ξk hΞk c hc
    f₀ f hf₀ hvac hf
  have hL : stdHom S T = latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    rw [hΛS, hΛT]
  have hf₁ := hf
  obtain ⟨Φ, hΦSB, hΦrat, -⟩ := hf₁
  have he1 : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hE
  have he2 : (e + p.e) * (e + p.e) = e + p.e := GlobalTheory.PlaceDatum.idemSum_mul_self hE'
  have hpe2 : p.e * p.e = p.e := p.split.1
  have horth : e * p.e = 0 := by
    have h2 : incA D 2 * (e * p.e) = 0 := by
      rw [map_ofNat]
      linear_combination he2 - he1 - hpe2
    have hu : incA D (1 / 2) * incA D 2 = 1 := by
      rw [← map_mul]
      norm_num
    calc e * p.e = incA D (1 / 2) * (incA D 2 * (e * p.e)) := by rw [← mul_assoc, hu, one_mul]
      _ = 0 := by rw [h2, mul_zero]
  have hstabp : ∀ u ∈ stdHom S T, u.map (fun a => p.e * a) ∈ stdHom S T := fun u hu => by
    have := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ p.e
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hpe2])) u hu
    convert this using 1
    ext i j
    rfl
  have hsb := GlobalTheory.LocMod.Place.isSBHalf_tensorAt D k p S T Y Y' FS FT e horth hstd hstabp Φ hΦSB Ξk hΞk
  have hpi1 : p.π p.e = 1 := by
    have h := p.ι_π 1
    rw [map_one, mul_one] at h
    rw [← h, p.π_ι]
  have hπe : p.π e = 0 := by
    have := congrArg p.π horth
    rwa [map_mul, hpi1, mul_one, map_zero] at this
  have hud : ∀ t : WO S T, p.up FS FT (p.down FS FT t) = t.map (fun x => p.e * x) := fun t => by
    unfold Place.up Place.down
    have hM : FT.β * (FT.γ * (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π * FS.β) * FS.γ =
        (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, FT.βγ, Matrix.one_mul, Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
    rw [hM]
    ext i j
    simp only [Matrix.map_apply, p.ι_π]
  have hrat : ∀ γ, p.tensorAt FS FT Φ Ξk (γ.map fun a => (e + p.e) * incA D a) = Ξ γ * Ξk (FT.γ * γ.map p.pr * FS.β) :=
    fun γ => by
    have hd : p.down FS FT (γ.map fun a => (e + p.e) * incA D a) = FT.γ * γ.map p.pr * FS.β := by
      unfold Place.down
      congr 2
      ext i j
      simp only [Matrix.map_apply, map_mul, map_add (f := _), hπe, hpi1, zero_add, one_mul, Place.pr]
    have hs : ((γ.map fun a => (e + p.e) * incA D a : WO S T) - p.up FS FT (p.down FS FT (γ.map fun a => (e + p.e) * incA D a)) : WO S T) =
        (γ.map fun a => e * incA D a : WO S T) := by
      rw [hud]
      ext i j
      simp only [Matrix.sub_apply, Matrix.map_apply]
      have h2 : p.e * e = 0 := by rw [mul_comm]; exact horth
      linear_combination (-(incA D (γ i j))) * h2 + (-(incA D (γ i j))) * hpe2
    simp only [Place.tensorAt]
    rw [hs, hd, hΦrat]
  have hvac' : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f₀ := by
    rw [← hL]; exact hvac
  have hex := (GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hψ S T ΛS ΛT hS hT _ (e + p.e) hE' f₀ hf₀ hvac').1
  have hsb' : IsSBHalf (e + p.e) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
      (p.tensorAt FS FT Φ Ξk) := by
    rw [← hL]; exact hsb
  obtain ⟨f', hf'⟩ := GlobalTheory.PlaceVec.exists_isThetaAt hψ hS hT he2 (GlobalTheory.PlaceDatum.infPart_idemSum hE') hex hsb'
  have hR : IsRatDatum ψ S T (e + p.e) (fun γ => Ξ γ * Ξk (FT.γ * γ.map p.pr * FS.β)) f₀ f' :=
    ⟨p.tensorAt FS FT Φ Ξk, hsb, hrat, by rw [hL]; exact hf'⟩
  have key := GlobalTheory.T.rationalDatum_theta_factors_placeByPlace D k p ψ hψ hdense S T Y Y' FS FT P PP e hPP hIdemAt hE hE' hstd Ξ _ Ξk hΞk (fun _ => rfl) c hc
    f₀ f f' hf₀ hvac hf hR
  rw [← key]
  exact hR

end GlobalTheory.LocMod
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalDatumSplitPlaceCombinationMulLocalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalDatum_splitPlace_combination_mul_local : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → DenseRange p.pr → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (e : AE D), PP ∉ P → Formalism.L2.NTheta.IsIdemAt p.e PP → IsIdemSum e P → IsIdemSum (e + p.e) (@insert _ _ (@Finset.instInsert _ (Classical.decEq _)) PP P) → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ↔ p.up FS FT x ∈ stdHom S T) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (ΛS : Set (Fin S.rank → D.host.E)) = intVec D S.rank → (ΛT : Set (Fin T.rank → D.host.E)) = intVec D T.rank → ∀ (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (Ξk : Matrix Y Y' k → ℂ), Ξk ∈ SB (Matrix Y Y' k) → ∀ c, p.IsCombAt ψ FS FT c Ξk → ∀ f₀ f, IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (stdHom S T) f₀ → IsRatDatum ψ S T e Ξ f₀ f → IsRatDatum ψ S T (e + p.e) (fun γ => Ξ γ * Ξk (FT.γ * γ.map p.pr * FS.β)) f₀ (comb ψ S T c f) := by
  first | exact @GlobalTheory.LocMod.ratDatum_comb_place | exact GlobalTheory.LocMod.ratDatum_comb_place | (intros; apply GlobalTheory.LocMod.ratDatum_comb_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalDatumFoldrLocalCombinations
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocComb

open GlobalTheory.ExportSeries

theorem ratDatum_insert (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (hPP : PP ∉ P)
    (hs : SplitSet (insert PP P)) (c : WO S T →₀ ℂ) (Ξl : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ)
    (hloc : GlobalTheory.LocMod.IsLocFac D ψ S T PP c Ξl)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hSd : IsSelfDualC S ΛS) (hTd : IsSelfDualC T ΛT) (hSi : (ΛS : Set (Fin S.rank → D.host.E)) = intVec D S.rank)
    (hTi : (ΛT : Set (Fin T.rank → D.host.E)) = intVec D T.rank) (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ)
    (f₀ f : WO S T → ℂ) (h0 : IsThetaFunO ψ S T f₀) (h1 : IsLatVac (heisO ψ S T) (stdHom S T) f₀)
    (hf : IsRatDatum ψ S T (idem P) Ξ f₀ f) :
    IsRatDatum ψ S T (idem (insert PP P)) (fun γ => Ξ γ * Ξl γ) f₀ (comb ψ S T c f) := by
  obtain ⟨k, _, _, _, _, p, Y, Y', _, _, _, _, FS, FT, Ξk, hd, hat, hint, hSB, hcomb, hΞ⟩ := hloc
  have hP : SplitSet P := hs.mono (Finset.subset_insert _ _)
  have he : idem P + p.e = idem (insert PP P) := by
    rw [idem, idem, Finset.sum_insert hPP, idemAt_eq hat, add_comm]
  have hs' : IsIdemSum (idem P + p.e) (@insert _ _ (@Finset.instInsert _ (Classical.decEq _)) PP P) := by
    rw [he]
    convert hs.isIdemSum
  have key := GlobalTheory.T.rationalDatum_splitPlace_combination_mul_local D k p ψ hψ hd S T Y Y' FS FT P PP (idem P) hPP hat hP.isIdemSum hs' hint ΛS ΛT hSd hTd hSi hTi Ξ Ξk hSB c
    hcomb f₀ f h0 h1 hf
  rw [he] at key
  have hfun : (fun γ => Ξ γ * Ξk (FT.γ * γ.map p.pr * FS.β)) = fun γ => Ξ γ * Ξl γ :=
    funext fun γ => by rw [hΞ γ]
  rwa [hfun] at key

theorem ratDatum_list (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (P₀ Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (n : ℕ) (PPn : Fin n → Formalism.L2.DIV.Pl D.host.E)
    (hinj : Function.Injective PPn) (hQ : ∀ i, PPn i ∈ Q) (hdis : Disjoint P₀ Q) (hs : SplitSet (P₀ ∪ Q))
    (c : Fin n → WO S T →₀ ℂ) (Ξl : Fin n → Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ)
    (hloc : ∀ i, GlobalTheory.LocMod.IsLocFac D ψ S T (PPn i) (c i) (Ξl i))
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hSd : IsSelfDualC S ΛS) (hTd : IsSelfDualC T ΛT) (hSi : (ΛS : Set (Fin S.rank → D.host.E)) = intVec D S.rank)
    (hTi : (ΛT : Set (Fin T.rank → D.host.E)) = intVec D T.rank)
    (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (f₀ f : WO S T → ℂ) (h0 : IsThetaFunO ψ S T f₀)
    (h1 : IsLatVac (heisO ψ S T) (stdHom S T) f₀) (hf : IsRatDatum ψ S T (idem P₀) Ξ f₀ f) :
    ∀ L : List (Fin n), L.Nodup →
      IsRatDatum ψ S T (idem (P₀ ∪ (L.map PPn).toFinset)) (fun γ => Ξ γ * (L.map fun i => Ξl i γ).prod) f₀
        (L.foldr (fun i g => comb ψ S T (c i) g) f) := by
  intro L
  induction L with
  | nil =>
    intro _
    have : (fun γ => Ξ γ * (([] : List (Fin n)).map fun i => Ξl i γ).prod) = Ξ := funext fun γ => by simp
    simpa [this] using hf
  | cons i L ih =>
    intro hnd
    rw [List.nodup_cons] at hnd
    have hsub : P₀ ∪ ((i :: L).map PPn).toFinset ⊆ P₀ ∪ Q := by
      intro x hx
      rcases Finset.mem_union.1 hx with h | h
      · exact Finset.mem_union_left _ h
      · obtain ⟨j, -, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 h)
        exact Finset.mem_union_right _ (hQ j)
    have hins : P₀ ∪ ((i :: L).map PPn).toFinset = insert (PPn i) (P₀ ∪ (L.map PPn).toFinset) := by
      rw [List.map_cons, List.toFinset_cons, Finset.union_insert]
    have hnot : PPn i ∉ P₀ ∪ (L.map PPn).toFinset := by
      intro h
      rcases Finset.mem_union.1 h with h | h
      · exact Finset.disjoint_left.1 hdis h (hQ i)
      · obtain ⟨j, hj, hji⟩ := List.mem_map.1 (List.mem_toFinset.1 h)
        exact hnd.1 (hinj hji ▸ hj)
    have step := ratDatum_insert D ψ hψ S T _ (PPn i) hnot (hins ▸ hs.mono hsub) (c i) (Ξl i) (hloc i) ΛS ΛT hSd hTd hSi hTi _ f₀ _ h0 h1
      (ih hnd.2)
    rw [← hins] at step
    have hfun : (fun γ => Ξ γ * (L.map fun i => Ξl i γ).prod * Ξl i γ) =
        fun γ => Ξ γ * ((i :: L).map fun i => Ξl i γ).prod := funext fun γ => by
      rw [List.map_cons, List.prod_cons]; ring
    rw [hfun] at step
    simpa only [List.foldr_cons] using step

theorem ratDatum_foldr_comb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (P₀ Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (n : ℕ) (PPn : Fin n → Formalism.L2.DIV.Pl D.host.E), Function.Injective PPn → (∀ PP, PP ∈ Q ↔ ∃ i, PPn i = PP) → Disjoint P₀ Q → ∀ (c : Fin n → WO S T →₀ ℂ) (Ξl : Fin n → Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ), (∀ i, GlobalTheory.LocMod.IsLocFac D ψ S T (PPn i) (c i) (Ξl i)) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (ΛS : Set (Fin S.rank → D.host.E)) = intVec D S.rank → (ΛT : Set (Fin T.rank → D.host.E)) = intVec D T.rank → ∀ (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (f₀ f : WO S T → ℂ), IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (stdHom S T) f₀ → (∀ e₀, IsIdemSum e₀ P₀ → IsRatDatum ψ S T e₀ Ξ f₀ f) → ∀ e, IsIdemSum e (P₀ ∪ Q) → IsRatDatum ψ S T e (fun γ => Ξ γ * ∏ i, Ξl i γ) f₀ ((List.finRange n).foldr (fun i g => comb ψ S T (c i) g) f) := by
  intro D ψ hψ S T P₀ Q n PPn hinj hQ hdis c Ξl hloc ΛS ΛT hSd hTd hSi hTi Ξ f₀ f h0 h1 hrat e he
  have hs : SplitSet (P₀ ∪ Q) := ⟨e, he⟩
  have hQ' : ∀ i, PPn i ∈ Q := fun i => (hQ _).2 ⟨i, rfl⟩
  have hP₀ : SplitSet P₀ := hs.mono Finset.subset_union_left
  have key := ratDatum_list D ψ hψ S T P₀ Q n PPn hinj hQ' hdis hs c Ξl hloc ΛS ΛT hSd hTd hSi hTi Ξ f₀ f h0 h1
    (hrat _ hP₀.isIdemSum) (List.finRange n) (List.nodup_finRange n)
  have hset : ((List.finRange n).map PPn).toFinset = Q := by
    ext x
    simp only [List.mem_toFinset, List.mem_map, List.mem_finRange, true_and]
    exact ⟨fun ⟨i, hi⟩ => (hQ x).2 ⟨i, hi⟩, fun h => (hQ x).1 h⟩
  rw [hset, idem_eq he] at key
  have hfun : (fun γ => Ξ γ * ((List.finRange n).map fun i => Ξl i γ).prod) = fun γ => Ξ γ * ∏ i, Ξl i γ :=
    funext fun γ => by rw [Fin.prod_univ_def]
  rwa [hfun] at key

end GlobalTheory.LocComb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalDatumFoldrLocalCombinationsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalDatum_foldr_local_combinations : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (P₀ Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (n : ℕ) (PPn : Fin n → Formalism.L2.DIV.Pl D.host.E), Function.Injective PPn → (∀ PP, PP ∈ Q ↔ ∃ i, PPn i = PP) → Disjoint P₀ Q → ∀ (c : Fin n → WO S T →₀ ℂ) (Ξl : Fin n → Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ), (∀ i, GlobalTheory.LocMod.IsLocFac D ψ S T (PPn i) (c i) (Ξl i)) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (ΛS : Set (Fin S.rank → D.host.E)) = intVec D S.rank → (ΛT : Set (Fin T.rank → D.host.E)) = intVec D T.rank → ∀ (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (f₀ f : WO S T → ℂ), IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (stdHom S T) f₀ → (∀ e₀, IsIdemSum e₀ P₀ → IsRatDatum ψ S T e₀ Ξ f₀ f) → ∀ e, IsIdemSum e (P₀ ∪ Q) → IsRatDatum ψ S T e (fun γ => Ξ γ * ∏ i, Ξl i γ) f₀ ((List.finRange n).foldr (fun i g => comb ψ S T (c i) g) f) := by
  first | exact @GlobalTheory.LocComb.ratDatum_foldr_comb | exact GlobalTheory.LocComb.ratDatum_foldr_comb | (intros; apply GlobalTheory.LocComb.ratDatum_foldr_comb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionConjugatedEqMovedFrameMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionConjugatedEqMovedFrameMatrix
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

noncomputable section

theorem GlobalTheory.LocRed.red_entry_movedFrame : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (ϖ : kˣ), GlobalTheory.SymBridge.IsCompl PP (Formalism.L2.Col.qOf PP) (q.pr.comp (incA D)) ϖ → ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∀ (Y : Type) [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) (σ : Fin V.rank ≃ Y) (b : GA D V), MovedTo (ofSplit q) V b β (F.β.submatrix id σ) → ∀ (g : GA D V) (gk : GL Y k), (ofSplit q).IsLoc F g gk → Lev.finE V (b⁻¹ * g * b) ∈ Formalism.L2.DIV.St β → ∀ (a a' : Fin V.rank) (z : 𝓞 D.host.E), (Formalism.L2.DIV.redFn β PP (Lev.finE V (b⁻¹ * g * b))).val a a' = Ideal.Quotient.mk PP.asIdeal z → valuation k (gk.val (σ a) (σ a') - (ofSplit q).pr (z : D.host.E)) < 1 := by
  intro D k _ _ _ _ q PP hPP ϖ _ V β Λ N _ Y _ _ F σ b hb g gk hg hSt a a' z hz
  have hM : (mt V g).map q.pr * F.β.submatrix id σ = F.β.submatrix id σ * gk.val.submatrix σ σ := by
    have h1 : (mt V g).map q.pr = F.β * gk.val * F.γ := hg.2
    have hs : ∀ A : Matrix (Fin V.rank) (Fin V.rank) k, A * F.β.submatrix id σ = (A * F.β).submatrix id σ := fun A => by
      ext i j; simp [Matrix.mul_apply]
    rw [h1, Matrix.submatrix_mul_equiv F.β gk.val id σ σ, hs, Matrix.mul_assoc (F.β * gk.val), F.γβ, Matrix.mul_one]
  have key := GlobalTheory.SeeSaw.LevRed.red_of_movedTo q PP hPP V β b g _ _ hb hM hSt a a' z hz.symm
  simpa [Matrix.submatrix_apply] using key

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionConjugatedEqMovedFrameMatrixStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_conjugated_eq_movedFrame_matrix : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (ϖ : kˣ), GlobalTheory.SymBridge.IsCompl PP (Formalism.L2.Col.qOf PP) (q.pr.comp (incA D)) ϖ → ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∀ (Y : Type) [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) (σ : Fin V.rank ≃ Y) (b : GA D V), MovedTo (ofSplit q) V b β (F.β.submatrix id σ) → ∀ (g : GA D V) (gk : GL Y k), (ofSplit q).IsLoc F g gk → Lev.finE V (b⁻¹ * g * b) ∈ Formalism.L2.DIV.St β → ∀ (a a' : Fin V.rank) (z : 𝓞 D.host.E), (Formalism.L2.DIV.redFn β PP (Lev.finE V (b⁻¹ * g * b))).val a a' = Ideal.Quotient.mk PP.asIdeal z → valuation k (gk.val (σ a) (σ a') - (ofSplit q).pr (z : D.host.E)) < 1 := by
  first | exact @GlobalTheory.LocRed.red_entry_movedFrame | exact GlobalTheory.LocRed.red_entry_movedFrame | (intros; apply GlobalTheory.LocRed.red_entry_movedFrame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowPairValue
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.TopFrame

theorem sumE_one_single {E : Type} [Field E] {N n : ℕ} (hN : N = n + 1) (t : Eˣ) (r b : Fin N) :
    GlobalTheory.TopStep.sumE hN (1 : Formalism.L2.Col.Sp E n ≃ₗ[E] Formalism.L2.Col.Sp E n) t (Pi.single b 1) r =
      if r.val = b.val then (if r.val + 1 = N then (t : E) else 1) else 0 := by
  rcases GlobalTheory.TopStep.idx_cases hN r with ⟨i, rfl⟩ | rfl
  · have h := congrFun (GlobalTheory.TopStep.prH_sumE hN (1 : Formalism.L2.Col.Sp E n ≃ₗ[E] Formalism.L2.Col.Sp E n) t (Pi.single b 1)) i
    refine h.trans ?_
    show (Pi.single b (1 : E) : Fin N → E) (Formalism.L2.Col.Br.iC hN i) = _
    have hi : ¬ (Formalism.L2.Col.Br.iC hN i).val + 1 = N := by
      show ¬ i.val + 1 = N
      have := i.2
      omega
    rw [if_neg hi, Pi.single_apply]
    simp only [Fin.ext_iff]
  · have hi : (Formalism.L2.Col.Br.iL hN).val + 1 = N := by
      show n + 1 = N
      omega
    rw [GlobalTheory.TopStep.sumE_last, if_pos hi, Pi.single_apply]
    simp only [Fin.ext_iff]
    split_ifs <;> simp

theorem frsF_top {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
    {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀) (hA : A.Is) (hI : I.Ok) (P : BadPr I a) (hP : P.1 ∉ (B.primes X).vGs)
    (j : ℕ) (hj : j = B.R.m) (β : Ch₀ j) (r b : Fin (B.R.N j)) :
    Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 j β).1.1 P (Pi.single b 1) r =
      if r.val = b.val then (if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1) else 0 := by
  subst hj
  have hQ : P.1 ∈ I.Q a := by
    rcases Finset.mem_union.1 P.2 with h | h
    · exact absurd h hP
    · exact h
  have hSQ : P.1 ∈ I.SQ := Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hQ⟩
  have hPr := (base_fields_primes_ok B X).2.1
  have hπ := GlobalTheory.Mem.Col2.PerLaw.piT_notMem_Q hI u a
  have h1 := hA.top β (Formalism.L2.Col.DecoF.base _ _ _ _ _) 1 1 (isPtOf_base _)
    ⟨(Matrix.one_mul _).trans (Matrix.mul_one _).symm, Matrix.one_mulVec _⟩
  rw [one_mul] at h1
  have h2 := h1.fr ⟨P.1, hQ⟩ r b
  have h3 := (hA.base _ le_rfl β).1.fr ⟨P.1, hSQ⟩ r b
  have h4 := (algebraMap B.fields.E (P.1.adicCompletion B.fields.E)).injective (h3.symm.trans h2)
  rw [frsF_eq_ptFr, ← extTo_fr I.SQ _ ⟨P.1, hSQ⟩, h4, tilF_fr I.sel (I.tup a) hPr u hπ]
  refine (sumE_one_single _ _ r b).trans ?_
  rw [unitOf_val (hπ ⟨P.1, hQ⟩)]


end GlobalTheory.Fam.TopFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionEqOneOffSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionEqOneOffSplitPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.SplitOffRed

theorem resS_eq_zero_of_cpt {D : D7} (PP' : Formalism.L2.DIV.Pl D.host.E) (s : Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h : GlobalTheory.StdFrames.cpt PP' (s : Formalism.IndefR.Datum.EAf D) = 0) : Formalism.L2.DIV.resS D.host.F PP' s = 0 := by
  obtain ⟨a, h1, h2⟩ := GlobalTheory.FunObj.Comparison₂.exists_resS_eq PP' s
  rw [h1, GlobalTheory.FunObj.Comparison₂.mk_eq_zero_iff]
  rw [GlobalTheory.FunObj.Comparison₂.cptO_apply PP' s] at h2
  change Valued.v (GlobalTheory.StdFrames.cpt PP' (s : Formalism.IndefR.Datum.EAf D) - _) < 1 at h2
  rw [h, zero_sub, Valuation.map_neg] at h2
  exact h2

theorem redFn_eq_one_off : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E}, Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (κ : GA D V), Formalism.L2.Theta.SuppAt q.e V κ → Lev.finE V κ ∈ Formalism.L2.DIV.St β → ∀ PP' : Formalism.L2.DIV.Pl D.host.E, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → Formalism.L2.DIV.redFn β PP' (Lev.finE V κ) = 1 := by
  intro D k _ _ _ _ q PP hq V β κ hS hst PP' hne
  have hPP' : PP' ≠ PP := fun h => hne (h ▸ rfl)
  have hcP : GlobalTheory.IdemSupport.cP PP' ≠ PP := fun h => hne (by rw [← h, GlobalTheory.IdemSupport.under_cP])
  have h1 : q.e * q.e = q.e := q.split.1
  have hc1 : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, h1]
  have hi1 : toEAf D q.e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := (GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP hq).1
  have hi2 : toEAf D (cA D q.e) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hc1]))
  have hint : toEAf D (q.e + cA D q.e) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [RingHom.map_add (f := _)]; exact add_mem hi1 hi2
  have hc0 : GlobalTheory.StdFrames.cpt PP' (toEAf D (q.e + cA D q.e)) = 0 := by
    rw [RingHom.map_add (f := _), RingHom.map_add (f := _), (GlobalTheory.StdFrames.cpt_of_isIdemAt hq).2 PP' hPP', zero_add,
      GlobalTheory.StdFrames.toEAf_cA]
    exact GlobalTheory.StdFrames.cpt_sg_eq_zero ((GlobalTheory.StdFrames.cpt_of_isIdemAt hq).2 _ hcP)
  have hres : Formalism.L2.DIV.resS D.host.F PP' ⟨toEAf D (q.e + cA D q.e), hint⟩ = 0 :=
    resS_eq_zero_of_cpt PP' _ hc0
  have hval : (Lev.finE V κ).val = (Formalism.L2.Theta.mt V κ).map (toEAf D) := rfl
  refine GlobalTheory.LevSplit.redFn_eq_one β PP' (Lev.finE V κ) hst ⟨toEAf D (q.e + cA D q.e), hint⟩ hres ?_
  ext i j
  have := congrArg (toEAf D) (hS i j)
  rw [RingHom.map_mul, Matrix.sub_apply, RingHom.map_sub] at this
  show toEAf D (q.e + cA D q.e) * ((Lev.finE V κ).val - 1) i j = ((Lev.finE V κ).val - 1) i j
  rw [Matrix.sub_apply, hval, Matrix.map_apply]
  have e1 : (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) i j = toEAf D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
  rw [e1]
  exact this

end GlobalTheory.SplitOffRed

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionEqOneOffSplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_eq_one_off_splitPlace : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E}, Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (κ : GA D V), Formalism.L2.Theta.SuppAt q.e V κ → Lev.finE V κ ∈ Formalism.L2.DIV.St β → ∀ PP' : Formalism.L2.DIV.Pl D.host.E, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → Formalism.L2.DIV.redFn β PP' (Lev.finE V κ) = 1 := by
  first | exact @GlobalTheory.SplitOffRed.redFn_eq_one_off | exact GlobalTheory.SplitOffRed.redFn_eq_one_off | (intros; apply GlobalTheory.SplitOffRed.redFn_eq_one_off <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesTopStep
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesTopStep
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopMove

section Package

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem weil_rec {n k : ℕ} (e : n = k) {χS χT : (AE D)ˣ →* Circle} {o : Om (Yc D n) D.sp.X'}
    (h : IsWeilDatumO R.ψ (Yc D n) D.sp.X' χS χT o) :
    IsWeilDatumO R.ψ (Yc D k) D.sp.X' χS χT (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') o e) := by
  subst e
  exact h

theorem vac_rec {n k : ℕ} (e : n = k) {f : WO (Yc D n) D.sp.X' → ℂ}
    (h : IsVacO R.ψ R.θ (Yc D n) D.sp.X' (cart (R.MY n)) (cart R.MX) (R.ΛY n) R.ΛX f) :
    IsVacO R.ψ R.θ (Yc D k) D.sp.X' (cart (R.MY k)) (cart R.MX) (R.ΛY k) R.ΛX
      (Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) f e) := by
  subst e
  exact h

theorem weil_omT (hω : R.chain_ωX) (t : T) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    IsWeilDatumO R.ψ (Yc D (j + 1)) D.sp.X' (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).1
      (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).2 (omT R t j h) :=
  weil_rec R (idx_top h) (hω t)

theorem isVacO_vacT (hv : R.chain_vX) (t : T) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    IsVacO R.ψ R.θ (Yc D (j + 1)) D.sp.X' (cart (R.MY (j + 1))) (cart R.MX) (R.ΛY (j + 1)) R.ΛX (vacT R j h) :=
  vac_rec R (idx_top h) (hv t).1

end Package

theorem fock_vac_moved_top : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (g : GA D (Yc D (j + 1))) (gT : GA D D.sp.X'), g ∈ GfC (Yc D (j + 1)) → gT ∈ GfC D.sp.X' → ∀ (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (LT : GlobalTheory.FinPl.Lat D.sp.X'), IsSelfDualC (Yc D (j + 1)) M' → IsSelfDualC D.sp.X' LT → (∀ P, GlobalTheory.FinPl.Moves (Yc D (j + 1)) g ((pk W).ΛY (j + 1)) M' P) → (∀ P, GlobalTheory.FinPl.Moves D.sp.X' gT (pk W).ΛX LT P) → (∀ P, GlobalTheory.FinPl.Vac (pk W).ψ (Yc D (j + 1)) D.sp.X' M' LT (fun _ => True) (omT (pk W) W.P.A3.A.μ0 j h (g, gT) (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (vacT (pk W) j h) P))) ∧ omT (pk W) W.P.A3.A.μ0 j h (g, gT) (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (vacT (pk W) j h) 1) ≠ 0 := by
  intro D L hT Gi Gl Kc Yd cX ex W hW j h g gT hg hgT M' LT hM' hLT hm hmT
  have hLev := hW.bot.hyp.2.2.2.1.lev
  have sdY : IsSelfDualC (Yc D (j + 1)) ((pk W).ΛY (j + 1)) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY (j + 1) (by omega))
  have sdX : IsSelfDualC D.sp.X' (pk W).ΛX := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hLev.βX
  have key := GlobalTheory.StepMove.gen (weil_omT (pk W) W.Q.charW.base.chain.ωX W.P.A3.A.μ0 j h) sdY hM' sdX hLT hg hgT (hm _) (hmT _)
    (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (isVacO_vacT (pk W) W.Q.charW.base.chain.vX W.P.A3.A.μ0 j h)
  refine ⟨fun P => ?_, key.2⟩
  have h1 := key.1 P 1 (one_mem _) 1 (one_mem _)
  rwa [one_mul, one_mul] at h1

end GlobalTheory.TopMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesTopStepStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_lattices_top_step : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (g : GA D (Yc D (j + 1))) (gT : GA D D.sp.X'), g ∈ GfC (Yc D (j + 1)) → gT ∈ GfC D.sp.X' → ∀ (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (LT : GlobalTheory.FinPl.Lat D.sp.X'), IsSelfDualC (Yc D (j + 1)) M' → IsSelfDualC D.sp.X' LT → (∀ P, GlobalTheory.FinPl.Moves (Yc D (j + 1)) g ((pk W).ΛY (j + 1)) M' P) → (∀ P, GlobalTheory.FinPl.Moves D.sp.X' gT (pk W).ΛX LT P) → (∀ P, GlobalTheory.FinPl.Vac (pk W).ψ (Yc D (j + 1)) D.sp.X' M' LT (fun _ => True) (omT (pk W) W.P.A3.A.μ0 j h (g, gT) (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (vacT (pk W) j h) P))) ∧ omT (pk W) W.P.A3.A.μ0 j h (g, gT) (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (vacT (pk W) j h) 1) ≠ 0 := by
  first | exact @GlobalTheory.TopMove.fock_vac_moved_top | exact GlobalTheory.TopMove.fock_vac_moved_top | (intros; apply GlobalTheory.TopMove.fock_vac_moved_top <;> assumption)
end
end
