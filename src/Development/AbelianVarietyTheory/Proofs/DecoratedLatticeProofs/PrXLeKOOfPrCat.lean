module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricLevelsCharactersDoubleCosetsAgreeRation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemR1IffLocalHom
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemidirectHaarMeasureFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContAutRapidDecBoundedIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBesselGroupsClosedHaarProduct
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalHeckeOperatorEqSmulOfLocalParameter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevFormEqZeroOnSmoothOfKFiniteDiscreteSeries
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ExistsNatSmulSingle

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrXLeKOOfPrCat
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.LevProd

theorem prX_le_KO_of_prCat (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀)
    (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k]
    [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (hok : cst.Ok) (hat : AtTwist (R := R) sel mu cst σ₀ P ι s W)
    (j c : ℕ) (h : j + (c + 1) = s + 1) (γ : AutY X R j) (g : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k)
    (hg : IsGL ι γ g) (hle : prCat (Pr := Pr) cst.sharp j P.1 γ ≤ GLint X.E (R.N j) P.1) :
    prX (Cgrp ((W.T s R).lev j (c + 1) h).J g) ≤ KO k _ := by
  have hLev := GlobalTheory.TwBridge.Lev.levelAgree X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hok hat
  obtain ⟨e, he, hge⟩ := hg
  have hcc : cOf R j = c + 1 := by unfold cOf; have := hat.steps; omega
  have heR : ∀ i : Fin (c + 1), (e (Sum.inr i)).val = R.N j + i.val := fun i => he (Sum.inr i)
  have hgφ : g = GlobalTheory.VolBridge.locHom ι e γ := Units.ext hge
  have hreg : (W.T s R).Regular := Chain.ofTwist_regular _ _ _ _ _
  obtain ⟨hJo, -, -⟩ := hreg.2.2 j (c + 1) h
  set J := ((W.T s R).lev j (c + 1) h).J with hJdef
  set φ := GlobalTheory.VolBridge.locHom ι e with hφ
  have hcompl := hat.compl
  have hIsGL : ∀ x : AutY X R j, IsGL ι (γ⁻¹ * x * γ) (g⁻¹ * φ x * g) := by
    intro x
    refine ⟨e, he, ?_⟩
    rw [hgφ, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hC : ∀ x : AutY X R j, x ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) γ ↔ φ x ∈ Cgrp J g := by
    intro x
    rw [mem_Cgrp, ← GlobalTheory.RankOneMatrix.mem_rationalFirstParabolic_iff_localGL_mem_rootExchange ι e hcc heR x, (hLev j (c + 1) h _ _ (hIsGL x)).1]
    simp [Loc.Cbe, Subgroup.mem_comap, MulAut.conj_apply]
  have hN1 := GlobalTheory.UnipRead.mem_N1_iff_local_hom ι e hcc heR
  have hdN := GlobalTheory.VolBridge.exists_N1_local_hom_mem_open ι hcompl.dense e hcc heR
  set e' := GlobalTheory.VolBridge.eX e hcc heR with he'
  set φ' := GlobalTheory.VolBridge.locHom ι e' with hφ'
  have hOo : IsOpen {w : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k | g⁻¹ * w * g ∈ J} :=
    hJo.preimage (by fun_prop)
  have hOR : ∀ z ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1,
      z ∈ Cgrp J g ↔ z ∈ {w | g⁻¹ * w * g ∈ J} := fun z hz => by
    simp [mem_Cgrp, hz]
  have hCR : Cgrp J g ≤ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 := fun z hz => (mem_Cgrp.1 hz).1
  have hP : ∀ y, y ∈ prCat (Pr := Pr) cst.sharp j P.1 γ ↔ φ' y ∈ prX (Cgrp J g) :=
    GlobalTheory.VolBridge.prX_iff_locHom ι e hcc heR hN1 hdN _ _ _ hOo hOR hCR hC
  have hG : ∀ y, y ∈ GLint X.E (R.N j) P.1 ↔ φ' y ∈ KO k _ := fun y =>
    GlobalTheory.VolBridge.mem_stabL_stdAt_iff_locHom_mem_KO P.1 ι hcompl.int e' y
  have hpo : IsOpen (prX (Cgrp J g) : Set (GL (XIx (Fin R.k) (Fin R.t) j) k)) :=
    GlobalTheory.OpenPr.isOpen_prX _ _ hOo (by simp [J.one_mem]) (fun z hz hzO => (hOR z hz).2 hzO)
  intro z hz
  have hV : IsOpen {v : GL (XIx (Fin R.k) (Fin R.t) j) k |
      v⁻¹ * z ∈ ((prX (Cgrp J g) ⊓ KO k _ : Subgroup _) : Set _)} :=
    (hpo.inter GlobalTheory.SplitFlip.isOpen_KO).preimage (by fun_prop)
  obtain ⟨y, hy⟩ := GlobalTheory.denseGL_completion ι hcompl.dense e' z _ hV (by simp [one_mem, hz])
  have hy1 : (φ' y)⁻¹ * z ∈ prX (Cgrp J g) := hy.1
  have hy2 : (φ' y)⁻¹ * z ∈ KO k _ := hy.2
  have hyC : φ' y ∈ prX (Cgrp J g) := by
    have := mul_mem hz (inv_mem hy1); simpa using this
  have hyK : φ' y ∈ KO k _ := (hG y).1 (hle ((hP y).2 hyC))
  have := mul_mem hyK hy2; simpa using this

end GlobalTheory.LevProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageLevelSphericalOffSet
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageLevelSphericalOffSet
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOntoSph

variable {D : D7}


open Classical in
theorem sep_level {c : Com D} {j : ℕ} {s : PiLocalization₂ D} (hs : s.Is c j) {P : HeightOneSpectrum (𝓞 D.host.E)}
    (hP : OffS D c.S P) : ∀ PP, PP ∈ s.L.Pg ∨ PP ∈ s.L.Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
  obtain ⟨hr, ξ, hL⟩ := hs.lev
  have hPg : s.L.Pg = c.Pg := by rw [hL]; rfl
  have hQ : s.L.Q = ∅ := by rw [hL]; rfl
  rintro PP (h | h)
  · rw [hPg] at h
    exact GlobalTheory.HeckeOffLevel.sep_of_offS hP (by unfold Com.S; exact Finset.mem_image.2 ⟨PP, h, rfl⟩)
  · rw [hQ] at h
    exact absurd h (Finset.notMem_empty _)

theorem exists_unif_of_F (P : HeightOneSpectrum (𝓞 D.host.E)) :
    ∃ x : 𝓞 D.host.F, ∃ y : 𝓞 D.host.E, (y : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) ∧
      y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2 := by
  haveI := P.isPrime
  haveI : Algebra.IsUnramifiedAt (𝓞 D.host.F) P.asIdeal :=
    Algebra.unramified_iff_forall.1 (GlobalTheory.InertOfConj.unram D) ⟨P.asIdeal, P.isPrime⟩
  have hle : (P.asIdeal.under (𝓞 D.host.F)).map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ P.asIdeal :=
    Ideal.map_comap_le
  have h1 : Ideal.ramificationIdx' (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal = 1 := by
    letI := Localization.AtPrime.algebraOfLiesOver (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal
    exact (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff P.ne_bot hle).2
      ((Algebra.isUnramifiedAt_iff_map_eq (𝓞 D.host.F) (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal).1 ‹_›).2
  have h2 : ¬ (P.asIdeal.under (𝓞 D.host.F)).map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ P.asIdeal ^ 2 :=
    fun h => (Ideal.ramificationIdx'_ne_one_iff hle).2 h h1
  rw [Ideal.map_le_iff_le_comap] at h2
  obtain ⟨x, hx, hx2⟩ := SetLike.not_le_iff_exists.1 h2
  exact ⟨x, algebraMap _ _ x, rfl, Ideal.mem_comap.1 hx, fun h => hx2 (Ideal.mem_comap.2 h)⟩

theorem level_spherical_off_S : ∀ D : D7, ForStage D fun c _ s => SphOff (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S ∧
    SphOff (levS s.V s.β s.L) (fun k => conj (Lev.levChi s.V s.β s.L k)) c.S ∧
    (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, OffS D c.S P → IsPrimeIdem P e f → ∀ k ∈ Lev.levG s.V s.β s.L,
      ∃ k₁ ∈ Lev.levG s.V s.β s.L, ∃ k₂ ∈ Lev.levG s.V s.β s.L, SuppF s.V f k₁ ∧ SuppF s.V (1 - f) k₂ ∧ k = k₁ * k₂) ∧
    (∀ P : HeightOneSpectrum (𝓞 D.host.E), OffS D c.S P ↔ P.under (𝓞 D.host.F) ∉ c.S) ∧
    ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ x : 𝓞 D.host.F, ∃ y : 𝓞 D.host.E,
      (y : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) ∧ y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2 := by
  intro D c _ j _ s hs
  obtain ⟨N, hB, hNP⟩ := hs.base
  have hoff : ∀ P, OffS D c.S P ↔ P.under (𝓞 D.host.F) ∉ c.S := fun P => GlobalTheory.GoodPrimes.offS_iff _ P
  have key := fun P e f (hP : OffS D c.S P) (hi : IsPrimeIdem P e f) =>
    (GlobalTheory.LevSplit.lev_split s.V s.β s.Λ N s.L hB).2 P e f hi (hNP P ((hoff P).1 hP)) (sep_level hs hP)
  have hex := fun P => (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents s.V).2.1 P
  refine ⟨fun P hP => ?_, fun P hP => ?_, fun P e f hP hi => (key P e f hP hi).2.2, hoff, exists_unif_of_F⟩
  · obtain ⟨e, f, hi⟩ := hex P
    obtain ⟨h1, h2, -⟩ := key P e f hP hi
    exact ⟨e, f, hi, h1, h2⟩
  · obtain ⟨e, f, hi⟩ := hex P
    obtain ⟨h1, h2, -⟩ := key P e f hP hi
    refine ⟨e, f, hi, h1, fun g hg hf => ?_⟩
    show conj (Lev.levChi s.V s.β s.L g) = 1
    rw [h2 g hg hf, map_one]

end GlobalTheory.ChainOntoSph

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageLevelSphericalOffSetStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainStage_level_spherical_off_set : ∀ D : D7, ForStage D fun c _ s => SphOff (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S ∧ SphOff (levS s.V s.β s.L) (fun k => conj (Lev.levChi s.V s.β s.L k)) c.S ∧ (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, OffS D c.S P → IsPrimeIdem P e f → ∀ k ∈ Lev.levG s.V s.β s.L, ∃ k₁ ∈ Lev.levG s.V s.β s.L, ∃ k₂ ∈ Lev.levG s.V s.β s.L, SuppF s.V f k₁ ∧ SuppF s.V (1 - f) k₂ ∧ k = k₁ * k₂) ∧ (∀ P : HeightOneSpectrum (𝓞 D.host.E), OffS D c.S P ↔ P.under (𝓞 D.host.F) ∉ c.S) ∧ ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ x : 𝓞 D.host.F, ∃ y : 𝓞 D.host.E, (y : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) ∧ y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2 := by
  first | exact @GlobalTheory.ChainOntoSph.level_spherical_off_S | exact GlobalTheory.ChainOntoSph.level_spherical_off_S | (intros; apply GlobalTheory.ChainOntoSph.level_spherical_off_S <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageConjugateValuesHeckeOperators
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageConjugateValuesHeckeOperators
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjVal

variable {D : D7}

def Good (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (f : GA D V → ℂ) : Prop :=
  Continuous f ∧ (∃ C : ℝ, ∀ g, ‖f g‖ ≤ C) ∧ (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) ∧ ∀ k ∈ J, ∀ g, f (g * k) = χ k * f g

theorem Good.add {V : HSp D} {J : Set (GA D V)} {χ : GA D V → ℂ} {f f' : GA D V → ℂ}
    (h : Good V J χ f) (h' : Good V J χ f') : Good V J χ (f + f') := by
  obtain ⟨c, ⟨C, hC⟩, l, r⟩ := h
  obtain ⟨c', ⟨C', hC'⟩, l', r'⟩ := h'
  refine ⟨c.add c', ⟨C + C', fun g => (norm_add_le _ _).trans (add_le_add (hC g) (hC' g))⟩,
    fun γ hγ g => by simp [l γ hγ g, l' γ hγ g], fun k hk g => by simp [r k hk g, r' k hk g, mul_add]⟩

theorem Good.smul {V : HSp D} {J : Set (GA D V)} {χ : GA D V → ℂ} {f : GA D V → ℂ} (a : ℂ)
    (h : Good V J χ f) : Good V J χ (a • f) := by
  obtain ⟨c, ⟨C, hC⟩, l, r⟩ := h
  refine ⟨continuous_const.mul c, ⟨‖a‖ * C, fun g => ?_⟩,
    fun γ hγ g => by simp [l γ hγ g], fun k hk g => by simp [r k hk g, mul_left_comm]⟩
  rw [Pi.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hC g) (norm_nonneg a)

theorem good_val (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D}
    {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ}
    (u : (⨂[ℂ] τ, M.sm τ) →ₗ[ℂ] (GA D V → ℂ)) (hu : u ∈ MultT θ M J χ) (v : ⨂[ℂ] τ, M.sm τ) :
    Good V J χ (u v) := by
  have hT := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT θ M J χ u).1 hu)
  have hu' : u = PiTensorProduct.lift (PiTensorProduct.lift.symm u) := (LinearEquiv.apply_symm_apply _ _).symm
  induction v using PiTensorProduct.induction_on with
  | smul_tprod a x =>
    rw [map_smul]
    refine Good.smul a ?_
    rw [hu', PiTensorProduct.lift.tprod]
    exact ⟨(hT.aut x).cont, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (hT.aut x) (hT.cusp x), (hT.aut x).left,
      hT.lev x⟩
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact hx.add hy

theorem conj_eq_one_iff' (z : ℂ) : conj z = 1 ↔ z = 1 := by
  constructor
  · intro h; simpa using congrArg conj h
  · intro h; simp [h]

theorem conj_values_hecke : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ForStage D fun c _ s =>
    (∀ (u : s.CC c) v, Continuous (PiLocalization₂.val u v) ∧ (∃ C : ℝ, ∀ g, ‖PiLocalization₂.val u v g‖ ≤ C) ∧
      (∀ γ ∈ GQ s.V, ∀ g, PiLocalization₂.val u v (γ * g) = PiLocalization₂.val u v g) ∧
      ∀ k ∈ levS s.V s.β s.L, ∀ g, PiLocalization₂.val u v (g * k) = Lev.levChi s.V s.β s.L k * PiLocalization₂.val u v g) ∧
    (∀ P d R, Hecke₂ s.V (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S P d R ↔
      Hecke₂ s.V (levS s.V s.β s.L) (fun k => conj (Lev.levChi s.V s.β s.L k)) c.S P d R) ∧
    ∀ (R : Finset (GA D s.V)) (f : GA D s.V → ℂ),
      heckeLin s.V R (fun g => conj (f g)) = fun g => conj (heckeLin s.V R f g) := by
  intro hP D c hc j _ s _
  refine ⟨fun u v => good_val hP hc.inf (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) u.2 v, fun P d R => ?_, fun R f => ?_⟩
  · simp only [Hecke₂, conj_eq_one_iff']
  · funext g
    set_option synthInstance.maxHeartbeats 100000 in
      simp [heckeLin, map_sum]

end GlobalTheory.ConjVal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageConjugateValuesHeckeOperatorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainStage_conjugate_values_hecke_operators : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ForStage D fun c _ s => (∀ (u : s.CC c) v, Continuous (PiLocalization₂.val u v) ∧ (∃ C : ℝ, ∀ g, ‖PiLocalization₂.val u v g‖ ≤ C) ∧ (∀ γ ∈ GQ s.V, ∀ g, PiLocalization₂.val u v (γ * g) = PiLocalization₂.val u v g) ∧ ∀ k ∈ levS s.V s.β s.L, ∀ g, PiLocalization₂.val u v (g * k) = Lev.levChi s.V s.β s.L k * PiLocalization₂.val u v g) ∧ (∀ P d R, Hecke₂ s.V (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S P d R ↔ Hecke₂ s.V (levS s.V s.β s.L) (fun k => conj (Lev.levChi s.V s.β s.L k)) c.S P d R) ∧ ∀ (R : Finset (GA D s.V)) (f : GA D s.V → ℂ), heckeLin s.V R (fun g => conj (f g)) = fun g => conj (heckeLin s.V R f g) := by
  first | exact @GlobalTheory.ConjVal.conj_values_hecke | exact GlobalTheory.ConjVal.conj_values_hecke | (intros; apply GlobalTheory.ConjVal.conj_values_hecke <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMatrixCoefficientEqZeroOfHeisenbergRelations
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMatrixCoefficientEqZeroOfHeisenbergRelations
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

theorem coef_zero_of_heis_relations : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (m : Measure (WO S T)) (X : Set (WO S T)), IsCovolOne (ratL T S) m X → ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F → ∀ (g : GA D S) (n : ℕ) (a : Fin n → ℂ) (y : Fin n → WO S T), ∑ i, a i • heisO ψ S T (y i) F = F → ∑ i, conj (a i) • heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) F = 0 → ∫ w in X, om (g, 1) F w * conj (F w) ∂m = 0 := by
  intro D ψ S T χS χT om hw m X hm F hF g n a y h1 h2
  have hψ := hw.std
  have hth := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  have laws := fun {u v : WO S T → ℂ} (hu : IsThetaFunO ψ S T u) (hv : IsThetaFunO ψ S T v) =>
    GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T m X hψ hm u v hu hv
  have hG : IsThetaFunO ψ S T (om (g, 1) F) := hw.om_pres _ F hF

  have key : ∀ i, (∫ x in X, om (g, 1) F x * conj (heisO ψ S T (y i) F x) ∂m) =
      ∫ x in X, om (g, 1) (heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) F) x * conj (F x) ∂m := by
    intro i
    have hact : actO S T g 1 (actO S T g⁻¹ 1 (-(y i))) = -(y i) := by
      have := GlobalTheory.AdelicLatMove.actO_actO_inv S T g 1 (-(y i))
      rwa [inv_one] at this
    rw [hw.om_heis g 1 _ F hF, hact]
    have := ((laws hG hF).2.2.2.2.2.2.1 (-(y i))).2
    rw [neg_neg] at this
    exact this.symm
  have hpt : ∀ x, om (g, 1) F x * conj (F x) =
      ∑ i, conj (a i) * (om (g, 1) F x * conj (heisO ψ S T (y i) F x)) := by
    intro x
    have e := congrFun h1 x
    rw [Finset.sum_apply] at e
    conv_lhs => rw [← e]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  have hz : ∀ x, om (g, 1) (∑ i, conj (a i) • heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) F) x * conj (F x) =
      ∑ i, conj (a i) * (om (g, 1) (heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) F) x * conj (F x)) := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  calc (∫ x in X, om (g, 1) F x * conj (F x) ∂m)
      = ∫ x in X, ∑ i, conj (a i) * (om (g, 1) F x * conj (heisO ψ S T (y i) F x)) ∂m :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∑ i, conj (a i) * ∫ x in X, om (g, 1) F x * conj (heisO ψ S T (y i) F x) ∂m := by
        rw [integral_finsetSum _ (fun i _ => ((laws hG (hth _ F hF)).1).const_mul _)]
        exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
    _ = ∑ i, conj (a i) * ∫ x in X, om (g, 1) (heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) F) x * conj (F x) ∂m :=
        Finset.sum_congr rfl fun i _ => by rw [key i]
    _ = ∫ x in X, ∑ i, conj (a i) * (om (g, 1) (heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) F) x * conj (F x)) ∂m := by
        rw [integral_finsetSum _ (fun i _ => ((laws (hw.om_pres _ _ (hth _ F hF)) hF).1).const_mul _)]
        exact Finset.sum_congr rfl fun i _ => (integral_const_mul _ _).symm
    _ = ∫ x in X, om (g, 1) (∑ i, conj (a i) • heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) F) x * conj (F x) ∂m :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => (hz x).symm)
    _ = 0 := by simp [h2]

end GlobalTheory.ChainOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMatrixCoefficientEqZeroOfHeisenbergRelationsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilMatrixCoefficient_eq_zero_of_heisenberg_relations : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (m : Measure (WO S T)) (X : Set (WO S T)), IsCovolOne (ratL T S) m X → ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F → ∀ (g : GA D S) (n : ℕ) (a : Fin n → ℂ) (y : Fin n → WO S T), ∑ i, a i • heisO ψ S T (y i) F = F → ∑ i, conj (a i) • heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) F = 0 → ∫ w in X, om (g, 1) F w * conj (F w) ∂m = 0 := by
  first | exact @GlobalTheory.ChainOnto.coef_zero_of_heis_relations | exact GlobalTheory.ChainOnto.coef_zero_of_heis_relations | (intros; apply GlobalTheory.ChainOnto.coef_zero_of_heis_relations <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupQuotientFundamentalDomainCocompact
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupQuotientFundamentalDomainCocompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BesselQuot

theorem besGrp_quotient : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ), B.μR.IsHaarMeasure ∧ IsClosed (besGrp B.d B.o : Set (GA D B.V)) ∧ (∃ Ω : Set (GA D B.V), IsCompact Ω ∧ ∀ s ∈ besGrp B.d B.o, ∃ γ ∈ GQ B.V ⊓ besGrp B.d B.o, γ * s ∈ Ω) ∧ ∃ 𝓢 : Set (besGrp B.d B.o), IsFundamentalDomain ((GQ B.V).subgroupOf (besGrp B.d B.o)) 𝓢 B.μR ∧ B.μR 𝓢 < ⊤ ∧ ∀ F : GA D B.V → ℂ, ContinuousOn F (besGrp B.d B.o : Set (GA D B.V)) → (∀ γ ∈ GQ B.V ⊓ besGrp B.d B.o, ∀ s ∈ besGrp B.d B.o, F (γ * s) = F s) → IntegrableOn (fun s : besGrp B.d B.o => F s) 𝓢 B.μR ∧ ∫ s in 𝓢, F s ∂B.μR = ∫ a in B.vA.𝓕, ∫ n in B.vN.𝓝, F (n.1 * embA B.d B.o a) ∂B.vN.ν ∂B.vA.μ := by
  intro D ρ B
  obtain ⟨-, hcl, hHaar⟩ := GlobalTheory.MixPer.jacGrp_besGrp_haar D B.V B.V₀ B.A B.L ρ B.d B.o B.vN.ν B.vN.𝓝 B.vN.unit
  have hμR : B.μR.IsHaarMeasure := hHaar B.vA.μ B.vA.haar
  obtain ⟨hsc, hNcl, hnorm, huniq, hrat⟩ := GlobalTheory.Unf.besSemi D ρ B
  obtain ⟨⟨KN, hKN, hKNcov⟩, -⟩ :=
    GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B.V ρ B.d.e (GlobalTheory.MixPer.isIsoSub_e B.d)
  obtain ⟨KA, hKA, hKAcov⟩ := B.cpt
  have hγA : ∀ γ ∈ GQ B.A, embA B.d B.o γ ∈ GQ B.V := fun γ hγ => by
    have h1 := (hrat 1 (one_mem _) γ).2 ⟨one_mem _, hγ⟩
    simpa using h1
  set Ω : Set (GA D B.V) := (fun p : GA D B.V × GA D B.A => p.1 * embA B.d B.o p.2) '' ((Subtype.val '' KN) ×ˢ KA) with hΩ
  have hΩc : IsCompact Ω :=
    ((hKN.image continuous_subtype_val).prod hKA).image (continuous_fst.mul (hsc.comp continuous_snd))
  have hΩsub : Ω ⊆ (besGrp B.d B.o : Set (GA D B.V)) := by
    rintro _ ⟨⟨_, a⟩, ⟨⟨k, hk, rfl⟩, -⟩, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left k.2) (Subgroup.mem_sup_right ⟨a, rfl⟩)
  have hcov : ∀ s ∈ besGrp B.d B.o, ∃ γ ∈ GQ B.V ⊓ besGrp B.d B.o, γ * s ∈ Ω := by
    intro s hs
    obtain ⟨n, hn, a, rfl⟩ := (GlobalTheory.CharLaws.mem_besGrp B.d B.o s).1 hs
    obtain ⟨γA, hγAQ, hγAK⟩ := hKAcov a
    have hn1 : embA B.d B.o γA * n * (embA B.d B.o γA)⁻¹ ∈ flagN B.d := hnorm n hn γA
    obtain ⟨γN, hγN, k, hk, he⟩ := hKNcov ⟨_, hn1⟩
    have he' : embA B.d B.o γA * n * (embA B.d B.o γA)⁻¹ = γN.1 * k.1 := congrArg Subtype.val he
    have hk1 : k.1 = γN.1⁻¹ * (embA B.d B.o γA * n * (embA B.d B.o γA)⁻¹) := eq_inv_mul_of_mul_eq he'.symm
    have hQ : γN.1⁻¹ * embA B.d B.o γA ∈ GQ B.V :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.1 hγN)) (hγA γA hγAQ)
    have hR : γN.1⁻¹ * embA B.d B.o γA ∈ besGrp B.d B.o :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left γN.2)) (Subgroup.mem_sup_right ⟨γA, rfl⟩)
    refine ⟨γN.1⁻¹ * embA B.d B.o γA, Subgroup.mem_inf.2 ⟨hQ, hR⟩, ?_⟩
    refine ⟨(k.1, γA * a), ⟨⟨k, hk, rfl⟩, hγAK⟩, ?_⟩
    simp only [hk1, map_mul]
    group
  have hcovA : ∀ g : GA D B.A, ∃ γ ∈ GQ B.A, ∃ k ∈ KA, g = γ * k := fun g => by
    obtain ⟨γ, hγ, hk⟩ := hKAcov g
    exact ⟨γ⁻¹, Subgroup.inv_mem _ hγ, γ * g, hk, by group⟩
  have := B.vA.haar
  have hFfin : B.vA.μ B.vA.𝓕 < ⊤ :=
    GlobalTheory.BesselConvDefinite.measure_fundamentalDomain_lt_top (GQ B.A) hKA hcovA B.vA.μ B.vA.fund
  have hNfin : B.vN.ν B.vN.𝓝 < ⊤ := by rw [B.vN.unit.2.2]; exact ENNReal.one_lt_top
  obtain ⟨𝓡, hfd, hint⟩ := GlobalTheory.Unf.semiFd_iterated D B.V B.A (flagN B.d) (embA B.d B.o) hsc hNcl hnorm huniq hrat B.vA
    B.vN.ν B.vN.𝓝 B.vN.unit.1 B.vN.unit.2.1 hμR
  have : IsFiniteMeasure (B.vA.μ.restrict B.vA.𝓕) := isFiniteMeasure_restrict.2 hFfin.ne
  have : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) := isFiniteMeasure_restrict.2 hNfin.ne
  refine ⟨hμR, hcl, ⟨Ω, hΩc, hcov⟩, 𝓡, ?_, ?_, ?_⟩
  · rw [← Subgroup.inf_subgroupOf_right]; exact hfd
  · have h1 := (hint (fun _ => (1 : ℂ)) measurable_const).1.2 (integrable_const _)
    exact ((integrableOn_const_iff).1 h1).resolve_left (by simp)
  · intro F hF hinv
    classical
    set F' : GA D B.V → ℂ := (besGrp B.d B.o : Set (GA D B.V)).piecewise F 0 with hF'
    have hF'm : Measurable F' := hF.measurable_piecewise continuousOn_const hcl.measurableSet
    obtain ⟨C, hC⟩ := hΩc.exists_bound_of_continuousOn (hF.mono hΩsub)
    have hb : ∀ x, ‖F' x‖ ≤ max C 0 := by
      intro x
      by_cases hx : x ∈ (besGrp B.d B.o : Set (GA D B.V))
      · obtain ⟨γ, hγ, hγx⟩ := hcov x hx
        rw [hF', Set.piecewise_eq_of_mem _ _ _ hx, ← hinv γ hγ x hx]
        exact (hC _ hγx).trans (le_max_left _ _)
      · rw [hF', Set.piecewise_eq_of_notMem _ _ _ hx]; simp
    have hAC : AbsConv B.vA.μ B.vA.𝓕 B.vN.ν B.vN.𝓝 fun h n => F' (n.1 * embA B.d B.o h) := by
      refine Integrable.of_bound ?_ (max C 0) (Filter.Eventually.of_forall fun p => hb _)
      exact (hF'm.comp ((continuous_subtype_val.comp continuous_snd).mul
        (hsc.comp continuous_fst)).measurable).aestronglyMeasurable
    have hpt : ∀ r : ↥(flagN B.d ⊔ (embA B.d B.o).range), F' r = F r := fun r => Set.piecewise_eq_of_mem _ _ _ r.2
    have hpt2 : ∀ a (n : flagN B.d), F' (n.1 * embA B.d B.o a) = F (n.1 * embA B.d B.o a) := fun a n =>
      Set.piecewise_eq_of_mem _ _ _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨a, rfl⟩))
    obtain ⟨hi1, hi2⟩ := hint F' hF'm
    have e1 : (fun r : ↥(flagN B.d ⊔ (embA B.d B.o).range) => F' r) =
        fun r : ↥(flagN B.d ⊔ (embA B.d B.o).range) => F r := funext hpt
    have e2 : (fun a => ∫ n in B.vN.𝓝, F' (n.1 * embA B.d B.o a) ∂B.vN.ν) =
        fun a => ∫ n in B.vN.𝓝, F (n.1 * embA B.d B.o a) ∂B.vN.ν := funext fun a => by simp only [hpt2]
    refine ⟨?_, ?_⟩
    · have h3 := hi1.2 hAC
      rw [e1] at h3
      exact h3
    · have h3 := hi2 hAC
      rw [e1, e2] at h3
      exact h3

end GlobalTheory.BesselQuot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupQuotientFundamentalDomainCocompactStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselGroup_quotient_fundamentalDomain_cocompact : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ), B.μR.IsHaarMeasure ∧ IsClosed (besGrp B.d B.o : Set (GA D B.V)) ∧ (∃ Ω : Set (GA D B.V), IsCompact Ω ∧ ∀ s ∈ besGrp B.d B.o, ∃ γ ∈ GQ B.V ⊓ besGrp B.d B.o, γ * s ∈ Ω) ∧ ∃ 𝓢 : Set (besGrp B.d B.o), IsFundamentalDomain ((GQ B.V).subgroupOf (besGrp B.d B.o)) 𝓢 B.μR ∧ B.μR 𝓢 < ⊤ ∧ ∀ F : GA D B.V → ℂ, ContinuousOn F (besGrp B.d B.o : Set (GA D B.V)) → (∀ γ ∈ GQ B.V ⊓ besGrp B.d B.o, ∀ s ∈ besGrp B.d B.o, F (γ * s) = F s) → IntegrableOn (fun s : besGrp B.d B.o => F s) 𝓢 B.μR ∧ ∫ s in 𝓢, F s ∂B.μR = ∫ a in B.vA.𝓕, ∫ n in B.vN.𝓝, F (n.1 * embA B.d B.o a) ∂B.vN.ν ∂B.vA.μ := by
  exact @GlobalTheory.BesselQuot.besGrp_quotient
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharTameAtOfFactorsThroughResidue
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharTameAtOfFactorsThroughResidue
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Filter Topology

namespace GlobalTheory.ChainOnto.TameRes

variable {E : Type} [Field E] [NumberField E]

theorem isOpen_ltOne (P : HeightOneSpectrum (𝓞 E)) :
    IsOpen {z : P.adicCompletion E | Valued.v z < 1} := by
  have h := Valued.isOpen_ball (P.adicCompletion E) 1
  simpa only [Valuation.restrict_lt_iff_lt_embedding, map_one] using h

theorem val_alg (P : HeightOneSpectrum (𝓞 E)) (k : E) :
    Valued.v (algebraMap E (P.adicCompletion E) k) = P.valuation E k :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P k

theorem valuation_eq_one_of_not_mem (P : HeightOneSpectrum (𝓞 E)) (s : 𝓞 E) (hs : s ∉ P.asIdeal) :
    P.valuation E (algebraMap (𝓞 E) E s) = 1 :=
  le_antisymm (P.valuation_le_one s) (not_lt.mp fun h => hs ((P.valuation_lt_one_iff_mem s).mp h))

theorem locK_eq_one (D : D7) (H : Formalism.L2.Host.HChar D.host.E) (PP : Pl D.host.E) (c : (kP PP)ˣ →* ℂˣ)
    (hc : IsRes H PP c) (k : D.host.Eˣ) (hk : PP.valuation D.host.E ((k : D.host.E) - 1) < 1) :
    H.locK PP k = 1 := by
  have hv1 : PP.valuation D.host.E (k : D.host.E) = 1 := by
    have e : (k : D.host.E) = 1 + ((k : D.host.E) - 1) := by ring
    have h1 : PP.valuation D.host.E ((k : D.host.E) - 1) < PP.valuation D.host.E 1 := by rwa [map_one]
    rw [e]
    first
      | rw [Valuation.map_add_eq_of_lt_right _ h1, map_one]
      | rw [Valuation.map_add_eq_of_lt_left _ h1, map_one]
      | rw [add_comm, Valuation.map_add_eq_of_lt_right _ h1, map_one]
      | rw [add_comm, Valuation.map_add_eq_of_lt_left _ h1, map_one]
  obtain ⟨a, s, h⟩ := PP.exists_primeCompl_mul_eq_of_integer (k : D.host.E) hv1.le
  have hs : (s : 𝓞 D.host.E) ∉ PP.asIdeal := s.2
  have hsv := valuation_eq_one_of_not_mem PP _ hs
  have hav : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E a) = 1 := by
    rw [← h, map_mul, hv1, hsv, one_mul]
  have ha : a ∉ PP.asIdeal := by
    intro hm
    have hlt : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E a) < 1 :=
      (PP.valuation_lt_one_iff_mem (K := D.host.E) a).mpr hm
    exact absurd hav (ne_of_lt hlt)
  have hs0 : algebraMap (𝓞 D.host.E) D.host.E s ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hsv; exact zero_ne_one hsv
  have ha0 : algebraMap (𝓞 D.host.E) D.host.E a ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hav; exact zero_ne_one hav
  have hdiff : a - (s : 𝓞 D.host.E) ∈ PP.asIdeal := by
    apply (PP.valuation_lt_one_iff_mem (K := D.host.E) _).mp
    show PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E (a - (s : 𝓞 D.host.E))) < 1
    rw [map_sub, ← h, ← sub_one_mul, map_mul, hsv, mul_one]
    exact hk
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  have hms : (Ideal.Quotient.mk PP.asIdeal (s : 𝓞 D.host.E) : kP PP) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hs
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv hms
  let u : (kP PP)ˣ := Units.mkOfMulEqOne _ b hb
  let ka : D.host.Eˣ := Units.mk0 _ ha0
  let ks : D.host.Eˣ := Units.mk0 _ hs0
  have e1 : c u = H.locK PP ks := hc (s : 𝓞 D.host.E) ks u rfl rfl
  have e2 : c u = H.locK PP ka := hc a ka u rfl (Ideal.Quotient.eq.mpr hdiff).symm
  have hk' : k = ka * ks⁻¹ := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, ka, ks]
    rw [← h, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
  rw [hk', map_mul, map_inv, ← e1, ← e2, mul_inv_cancel]

theorem tameAt_of_isRes : ∀ (D : D7) (H : Formalism.L2.Host.HChar D.host.E) (PP : Pl D.host.E) (a : (kP PP)ˣ →* ℂˣ),
    IsRes H PP a → H.TameAt PP := by
  intro D H PP c hc
  unfold Formalism.L2.Host.HChar.TameAt Formalism.L2.Host.HChar.LevelLe
  intro x _ hx1
  by_contra hne
  have hcont : Continuous (H.loc PP) := H.2.1.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele PP)
  have hW : IsOpen {y : (PP.adicCompletion D.host.E)ˣ | H.loc PP y ≠ 1} := isOpen_ne_fun hcont continuous_const
  obtain ⟨T, hT, hTe⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hW
  have hlt : WithZero.exp (-((1 : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by norm_num)
  have hxT : (x : PP.adicCompletion D.host.E) ∈ T ∩ {z | Valued.v (z - 1) < 1} := by
    refine ⟨?_, lt_of_le_of_lt hx1 hlt⟩
    have : x ∈ (Units.val ⁻¹' T : Set (PP.adicCompletion D.host.E)ˣ) := by rw [hTe]; exact hne
    exact this
  have hU : IsOpen (T ∩ {z : PP.adicCompletion D.host.E | Valued.v (z - 1) < 1}) :=
    hT.inter ((isOpen_ltOne PP).preimage (continuous_sub_right 1))
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap D.host.E PP).exists_mem_open hU ⟨_, hxT⟩
  have hk1 : PP.valuation D.host.E (k - 1) < 1 := by
    rw [← val_alg, map_sub, map_one]; exact hk.2
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk1
  have hloc := locK_eq_one D H PP c hc (Units.mk0 k hk0) hk1
  have hmem : Formalism.L2.Host.atFin PP (Units.mk0 k hk0) ∈ (Units.val ⁻¹' T : Set (PP.adicCompletion D.host.E)ˣ) := hk.1
  rw [hTe] at hmem
  exact hmem hloc

end GlobalTheory.ChainOnto.TameRes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharTameAtOfFactorsThroughResidueStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_tameAt_of_factors_through_residue : ∀ (D : D7) (H : Formalism.L2.Host.HChar D.host.E) (PP : Pl D.host.E) (a : (kP PP)ˣ →* ℂˣ), IsRes H PP a → H.TameAt PP := by
  first | exact @GlobalTheory.ChainOnto.TameRes.tameAt_of_isRes | exact GlobalTheory.ChainOnto.TameRes.tameAt_of_isRes | (intros; apply GlobalTheory.ChainOnto.TameRes.tameAt_of_isRes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalOperatorEigenvaluesDeterminedByParams
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalOperatorEigenvaluesDeterminedByParams
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ParamEigen

variable {D : D7} {V : HSp D}

theorem heckeLin_eq_of_rep {K : Subgroup (GA D V)} {α α' : GA D V} {R R' : Finset (GA D V)}
    (hR : IsCosetRep V (K : Set (GA D V)) α R) (hR' : IsCosetRep V (K : Set (GA D V)) α' R')
    {a b : GA D V} (ha : a ∈ K) (hb : b ∈ K) (hα : α' = a * α * b) {f : GA D V → ℂ}
    (hf : ∀ k ∈ K, ∀ g, f (g * k) = f g) : heckeLin V R f = heckeLin V R' f := by
  classical
  have m1 : ∀ γ ∈ R, ∃ k₁ ∈ (K : Set (GA D V)), ∃ k₂ ∈ (K : Set (GA D V)), γ = k₁ * α' * k₂ := fun γ hγ => by
    obtain ⟨-, k₁, h₁, k₂, h₂, rfl⟩ := hR.1 γ hγ
    exact ⟨k₁ * a⁻¹, K.mul_mem h₁ (K.inv_mem ha), b⁻¹ * k₂, K.mul_mem (K.inv_mem hb) h₂, by rw [hα]; group⟩
  have m2 : ∀ γ ∈ R', ∃ k₁ ∈ (K : Set (GA D V)), ∃ k₂ ∈ (K : Set (GA D V)), γ = k₁ * α * k₂ := fun γ hγ => by
    obtain ⟨-, k₁, h₁, k₂, h₂, rfl⟩ := hR'.1 γ hγ
    exact ⟨k₁ * a, K.mul_mem h₁ ha, b * k₂, K.mul_mem hb h₂, by rw [hα]; group⟩
  have inv : ∀ x y : GA D V, x⁻¹ * y ∈ K → y⁻¹ * x ∈ K := fun x y h => by
    simpa using K.inv_mem h
  funext g
  simp only [heckeLin, LinearMap.coe_mk, AddHom.coe_mk]
  refine Finset.sum_bij' (fun γ hγ => (hR'.2 γ (m1 γ hγ)).exists.choose)
    (fun γ hγ => (hR.2 γ (m2 γ hγ)).exists.choose)
    (fun γ hγ => (hR'.2 γ (m1 γ hγ)).exists.choose_spec.1)
    (fun γ hγ => (hR.2 γ (m2 γ hγ)).exists.choose_spec.1) ?_ ?_ ?_
  · intro γ hγ
    have s1 := (hR'.2 γ (m1 γ hγ)).exists.choose_spec
    set γ' := (hR'.2 γ (m1 γ hγ)).exists.choose
    have s2 := (hR.2 γ' (m2 γ' s1.1)).exists.choose_spec
    exact (hR.2 γ' (m2 γ' s1.1)).unique s2 ⟨hγ, inv _ _ s1.2⟩
  · intro γ hγ
    have s1 := (hR.2 γ (m2 γ hγ)).exists.choose_spec
    set γ' := (hR.2 γ (m2 γ hγ)).exists.choose
    have s2 := (hR'.2 γ' (m1 γ' s1.1)).exists.choose_spec
    exact (hR'.2 γ' (m1 γ' s1.1)).unique s2 ⟨hγ, inv _ _ s1.2⟩
  · intro γ hγ
    have s1 := (hR'.2 γ (m1 γ hγ)).exists.choose_spec
    set γ' := (hR'.2 γ (m1 γ hγ)).exists.choose
    have e : g * γ = g * γ' * (γ'⁻¹ * γ) := by group
    rw [e, hf _ s1.2]

end GlobalTheory.ParamEigen

namespace GlobalTheory.ParamEigen

variable {D : D7} {V : HSp D}


open GlobalTheory.AdelicU GlobalTheory.PRep in
theorem heckeLin_eq_heckeVec {v : HeightOneSpectrum (𝓞 D.host.F)} {K : Set (GA D V)}
    (hK : ∀ x, x ∈ K ↔ ∃ k ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v, emb D.sp.cm.sig V.gram v k = x)
    (g : GLoc D.sp.cm.sig V.gram v) {R : Finset (GA D V)} (hR : IsCosetRep V K (emb D.sp.cm.sig V.gram v g) R)
    {φ : GA D V → ℂ}
    (hφ : φ ∈ fixed ((rightReg ℂ _ ℂ).comp (emb D.sp.cm.sig V.gram v)) (stabLoc D.sp.cm.sig V.gram (frameLat V) v)) :
    heckeLin V R φ = GlobalTheory.LFun.heckeVec ((rightReg ℂ _ ℂ).comp (emb D.sp.cm.sig V.gram v))
      (stabLoc D.sp.cm.sig V.gram (frameLat V) v)
      (Formalism.UG.dosetInd ℂ (stabLoc D.sp.cm.sig V.gram (frameLat V) v) g) φ := by
  classical
  let H : Subgroup (GA D V) := (stabLoc D.sp.cm.sig V.gram (frameLat V) v).map (emb D.sp.cm.sig V.gram v)
  have hKH : K = (H : Set (GA D V)) := Set.ext fun x => (hK x).trans (by simp [H])
  subst hKH
  have := GlobalTheory.HeckeDual.isLattice_frameLat V
  obtain ⟨R₀, r1, r2⟩ := GlobalTheory.HeckeDual.exists_rep _ (isOpen_stabLoc D.sp.cm.sig V.gram (frameLat V) v)
    (isCompact_stabLoc D.sp.cm.sig V.gram (frameLat V) v) g
  obtain ⟨s1, s2⟩ := GlobalTheory.LFun.rep_image (emb D.sp.cm.sig V.gram v) (emb_injective _ _ v) hK r1 r2
  have hR₀ : IsCosetRep V (H : Set (GA D V)) (emb D.sp.cm.sig V.gram v g) (R₀.image (emb D.sp.cm.sig V.gram v)) :=
    ⟨fun γ hγ => ⟨by
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hγ
      exact mem_finPts.2 (projInf_emb _ _ v y), s1 γ hγ⟩, s2⟩
  have hinv : ∀ k ∈ H, ∀ x, φ (x * k) = φ x := by
    rintro _ ⟨k, hk, rfl⟩ x
    exact congrFun (GlobalTheory.LGrp.mem_fixed.1 hφ k hk) x
  rw [heckeLin_eq_of_rep hR hR₀ (one_mem H) (one_mem H) (by group) hinv,
    GlobalTheory.LFun.heckeVec_dosetInd hφ (R := R₀) (fun γ hγ => DoubleCoset.mem_doubleCoset.2 (r1 γ hγ))
      fun x hx => r2 x (DoubleCoset.mem_doubleCoset.1 hx)]
  funext x
  rw [heckeLin_apply, Finset.sum_image (emb_injective _ _ v).injOn, Finset.sum_apply]
  rfl

theorem doubleCoset_of_divAt {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} (hP : IsPrimeIdem P e f)
    {ϖ ϖ' : 𝓞 D.host.E} (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) (h1' : ϖ' ∈ P.asIdeal)
    (h2' : ϖ' ∉ P.asIdeal ^ 2) {d : List ℤ} (hd : d.Pairwise (fun a b => b ≤ a)) {α α' : GA D V}
    (hα : SuppF V f α) (hα' : SuppF V f α') (hD : DivAt V e (ϖ : D.host.E) d α)
    (hD' : DivAt V e (ϖ' : D.host.E) d α') :
    ∃ a b, a ∈ KsphC V ∅ ∧ SuppF V f a ∧ b ∈ KsphC V ∅ ∧ SuppF V f b ∧ α' = a * α * b := by
  rcases id hP with ⟨hi, rfl⟩ | ⟨rfl, -, -⟩
  · obtain ⟨a, ⟨ha, ha'⟩, b, ⟨hb, hb'⟩, hab⟩ :=
      GlobalTheory.SplitLabel.split_label V P e ϖ ϖ' d α α' hi h1 h2 h1' h2' hα hα' hD hD'
    exact ⟨a, b, ha, ha', hb, hb', hab⟩
  · exact (GlobalTheory.InertDoubleCoset.inert_double_cosets V P _ hP (GlobalTheory.SphLabelOps.exists_real_unif D P) α hα).2.2
      ϖ ϖ' d α' h1 h2 h1' h2' hd hα' hD hD'

end GlobalTheory.ParamEigen

namespace GlobalTheory.ParamEigen

variable {D : D7} {V : HSp D}


open GlobalTheory.AdelicU GlobalTheory.PRep in
theorem exists_eig {J : Set (GA D V)} {χ : GA D V → ℂ} {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    (hJ : SphOff J χ Sb) (B : GlobalTheory.LFun.Fam D.host.E) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) :
    ∃ z : ℂ, ∀ f : GA D V → ℂ, GlobalTheory.LFun.IsParamFunV V Sb f B → ∀ R, Hecke₂ V J χ Sb P d R →
      heckeLin V R f = z • f := by
  classical
  by_cases h : ∃ R, Hecke₂ V J χ Sb P d R
  swap
  · exact ⟨0, fun f _ R hR => absurd ⟨R, hR⟩ h⟩
  obtain ⟨R₀, e₀, f₀, ϖ₀, α₀, hS, hP₀, p1, p2, hd, hJ1, -, hα₀, hD₀, -, hR₀⟩ := h
  have hv : P.under (𝓞 D.host.F) ∉ Sb := GlobalTheory.LFun.offS_iff.1 hS
  have hs := Supp.suppF_iff_of_isPrimeIdem V hP₀ rfl
  have hK : ∀ x, x ∈ {k | k ∈ J ∧ SuppF V f₀ k} ↔
      ∃ k ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) (P.under (𝓞 D.host.F)), emb D.sp.cm.sig V.gram _ k = x :=
    fun x => by
      constructor
      · rintro ⟨m1, m2⟩
        obtain ⟨k, rfl⟩ := (hs x).1 m2
        exact ⟨k, (Supp.emb_mem_KsphC V k).1 ((hJ1 _ m2).1 m1), rfl⟩
      · rintro ⟨k, hk, rfl⟩
        have := (hs _).2 ⟨k, rfl⟩
        exact ⟨(hJ1 _ this).2 ((Supp.emb_mem_KsphC V k).2 hk), this⟩
  let H : Subgroup (GA D V) :=
    (stabLoc D.sp.cm.sig V.gram (frameLat V) (P.under (𝓞 D.host.F))).map (emb D.sp.cm.sig V.gram _)
  have hKH : {k | k ∈ J ∧ SuppF V f₀ k} = (H : Set (GA D V)) := Set.ext fun x => (hK x).trans (by simp [H])
  obtain ⟨g₀, rfl⟩ := (hs α₀).1 hα₀
  obtain ⟨z, hz⟩ := GlobalTheory.T.sphericalHeckeOperator_eq_smul_of_localParameter _ _ D.sp.cm.sig V.rank V.gram (frameLat V) _ P rfl (B P) _
    (Formalism.UG.Final.DosetIndMem _ (stabLoc D.sp.cm.sig V.gram (frameLat V) (P.under (𝓞 D.host.F))) ℂ g₀)
  refine ⟨z, fun f hf R hR => ?_⟩
  obtain ⟨e, f', ϖ, α, -, hP', q1, q2, -, -, -, hα, hD, -, hRc⟩ := hR
  obtain ⟨rfl, rfl⟩ :=
    ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e₀ f₀ hP₀).2.2.2.1 e f' hP'
  have hpv := hf _ hv P rfl
  have hfix := hpv.mem_fixed
  obtain ⟨a, b, ha, ha', hb, hb', hab⟩ := doubleCoset_of_divAt hP₀ p1 p2 q1 q2 hd hα₀ hα hD₀ hD
  have hmem : ∀ k, k ∈ KsphC V ∅ → SuppF V f' k → k ∈ H := fun k hk hk' => by
    rw [← SetLike.mem_coe, ← hKH]
    exact ⟨(hJ1 k hk').2 hk, hk'⟩
  have hinv : ∀ k ∈ H, ∀ x, f (x * k) = f x := by
    rintro _ ⟨k, hk, rfl⟩ x
    exact congrFun (GlobalTheory.LGrp.mem_fixed.1 hfix k hk) x
  rw [hKH] at hRc hR₀
  rw [heckeLin_eq_of_rep hRc hR₀ (H.inv_mem (hmem a ha ha')) (H.inv_mem (hmem b hb hb')) (by rw [hab]; group) hinv,
    heckeLin_eq_heckeVec hK g₀ (hKH ▸ hR₀) hfix, hz _ _ f hpv]

end GlobalTheory.ParamEigen

namespace GlobalTheory.ParamEigen

theorem eig_of_param : ∀ (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), SphOff J χ Sb → ∀ B : GlobalTheory.LFun.Fam D.host.E,
    ∃ a : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, ∀ f : GA D V → ℂ, GlobalTheory.LFun.IsParamFunV V Sb f B →
      ∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = a P d • f := by
  intro D V J χ Sb hJ B
  choose a ha using exists_eig (V := V) hJ B
  exact ⟨a, fun f hf P d R hR => ha P d f hf R hR⟩

end GlobalTheory.ParamEigen

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalOperatorEigenvaluesDeterminedByParamsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalOperator_eigenvalues_determined_by_params : ∀ (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), SphOff J χ Sb → ∀ B : GlobalTheory.LFun.Fam D.host.E, ∃ a : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, ∀ f : GA D V → ℂ, GlobalTheory.LFun.IsParamFunV V Sb f B → ∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = a P d • f := by
  first | exact @GlobalTheory.ParamEigen.eig_of_param | exact GlobalTheory.ParamEigen.eig_of_param | (intros; apply GlobalTheory.ParamEigen.eig_of_param <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralQuotientEqSetIntegralFundamentalDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralQuotientEqSetIntegralFundamentalDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem integral_autMeasure_eq_setIntegral : ∀ (D : D7) (V : HSp D) (ν : Measure (GA D V)) (X : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) X ν → ∀ F : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, F (γ * g) = F g) → AEStronglyMeasurable F ν → ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) F q ∂(GlobalTheory.AutomorphicL2Unitary.autMeasure V ν) = ∫ g in X, F g ∂ν := by
  intro D V ν X hν hX F hF _
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) F := hF
  rw [GlobalTheory.AutomorphicL2Unitary.autMeasure, GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure hX]
  simp only [hL.descend_mk]

end GlobalTheory.ChainOnto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralQuotientEqSetIntegralFundamentalDomainStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_quotient_eq_setIntegral_fundamentalDomain : ∀ (D : D7) (V : HSp D) (ν : Measure (GA D V)) (X : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) X ν → ∀ F : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, F (γ * g) = F g) → AEStronglyMeasurable F ν → ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) F q ∂(GlobalTheory.AutomorphicL2Unitary.autMeasure V ν) = ∫ g in X, F g ∂ν := by
  first | exact @GlobalTheory.ChainOnto.integral_autMeasure_eq_setIntegral | exact GlobalTheory.ChainOnto.integral_autMeasure_eq_setIntegral | (intros; apply GlobalTheory.ChainOnto.integral_autMeasure_eq_setIntegral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TprodEqZeroOfKFinOff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem kFin_le_sm (hHC : GlobalTheory.Published.HarishChandraModules) {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel V S) (τ : D.what₂.Tau) : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ≤ M.sm τ := by
  intro w hw
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have h := GlobalTheory.TypeSum.std_of_isDS hHC (M.ds τ)
  exact (GlobalTheory.SmoothCyclic.sm_eq M τ).ge (h.2.2.1 w hw)

theorem tprod_eq_zero_of_kFin_off (hHC : GlobalTheory.Published.HarishChandraModules) {D : D7} {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : DSModel V S) (Λ : SmT M →ₗ[ℂ] ℂ) (hΛ : SepCont M Λ)
    (h0 : ∀ v : M.Vec, KVecP M v → Λ (PiTensorProduct.tprod ℂ v) = 0) (s : Finset D.what₂.Tau) :
    ∀ v : M.Vec, (∀ τ, τ ∉ s → IsKFin (M.ε τ) (M.σ τ) (v τ : M.H τ)) → Λ (PiTensorProduct.tprod ℂ v) = 0 := by
  induction s using Finset.induction_on with
  | empty => exact fun v hv => h0 v fun τ => hv τ (Finset.notMem_empty τ)
  | insert a s ha ih =>
    intro v hv
    obtain ⟨ℓ, hℓ, hℓv⟩ := hΛ a v
    have hk : ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M a, ℓ w = 0 := by
      intro w hw
      rw [hℓv ⟨w, kFin_le_sm hHC M a hw⟩]
      refine ih _ fun τ hτ => ?_
      by_cases e : τ = a
      · subst e
        rw [Function.update_self]
        exact hw
      · rw [Function.update_of_ne e]
        exact hv τ (by simp [e, hτ])
    have := GlobalTheory.KFiniteDense.eq_zero_of_kFin hHC D V S M a ℓ hℓ hk (v a) (v a).2
    rw [hℓv (v a), Function.update_eq_self] at this
    exact this

theorem eq_zero_of_sepCont : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : SmT M →ₗ[ℂ] ℂ), SepCont M Λ → (∀ v : M.Vec, KVecP M v → Λ (PiTensorProduct.tprod ℂ v) = 0) → Λ = 0 := by
  intro hHC D V S M Λ hΛ h0
  refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.zero_apply]
  exact tprod_eq_zero_of_kFin_off hHC M Λ hΛ h0 Finset.univ v fun τ hτ => absurd (Finset.mem_univ τ) hτ

end GlobalTheory.Core.Mi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightEqOneLatticeStabilizerComponents
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightEqOneLatticeStabilizerComponents
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem hgt_one_components : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ → (∀ v, ∀ k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV V Λ v k = 1) ∧ (∀ κ ∈ GfC V, ∀ w, GlobalTheory.AdelicU.projArch D.sp.cm.sig V.gram w κ = 1) ∧ ∀ b ∈ GinfC V, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v b = 1 := by
  intro D V Λ hΛ
  haveI : Submodule.IsFullLattice D.host.E Λ := Formalism.IndefR.Fin.PDA.selfDual_isFullLattice V Λ hΛ
  refine ⟨fun v k hk => ?_, fun κ hκ w => ?_, fun b hb v => ?_⟩
  · have hK := (GlobalTheory.Doubling.ioH_mem_KFin (L := Λ) (GlobalTheory.Doubling.gram_hdbl V) (g := k) (g' := 1)).2 ⟨hk, one_mem _⟩
    have := GlobalTheory.Doubling.hgtH_of_mem (GlobalTheory.Doubling.continuous_absEv v) (GlobalTheory.Doubling.isCompact_KFin v) hK
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV
    exact_mod_cast this
  · exact GlobalTheory.AdelicU.mem_finPts_iff_forall.1 hκ w
  · exact GlobalTheory.AdelicU.mem_infPts_iff_forall.1 hb v

end GlobalTheory.ChainOnto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightEqOneLatticeStabilizerComponentsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doublingHeight_eq_one_lattice_stabilizer_components : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ → (∀ v, ∀ k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV V Λ v k = 1) ∧ (∀ κ ∈ GfC V, ∀ w, GlobalTheory.AdelicU.projArch D.sp.cm.sig V.gram w κ = 1) ∧ ∀ b ∈ GinfC V, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v b = 1 := by
  first | exact @GlobalTheory.ChainOnto.hgt_one_components | exact GlobalTheory.ChainOnto.hgt_one_components | (intros; apply GlobalTheory.ChainOnto.hgt_one_components <;> assumption)
end
end
