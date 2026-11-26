module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RayFieldTheta
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiDatumAgreeColumnDatumAtTypePrime
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.Grow GlobalTheory.Size

namespace GlobalTheory.Chain.LiftConv

variable {D : D7} {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f : WO V W → ℂ}

theorem thetaKO_left (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f) (g : GA D V) :
    ∀ γ ∈ GQ W, ∀ h, thetaKO ω g (γ * h) f = thetaKO ω g h f := by
  intro γ hγ h

  have hsplit : ((g, γ * h) : GA D V × GA D W) = (1, γ) * (g, h) := by
    ext <;> simp
  have hpres : IsThetaFunO ψ V W (ω (g, h) f) := hω.om_pres _ _ hf
  unfold thetaKO
  rw [hsplit, map_mul, Module.End.mul_apply]
  exact hω.om_aut 1 (one_mem _) γ hγ _ hpres

theorem thetaKO_continuous (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f) (g : GA D V) :
    Continuous fun h => thetaKO ω g h f := by

  have hpair : Continuous fun h : GA D W => ((g, h) : GA D V × GA D W) := by fun_prop
  unfold thetaKO
  exact (hω.om_cont f hf 0).comp hpair

theorem thetaKO_modGrowth (hG : GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth.ThetaGrowth D) (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω)
    (hf : IsThetaFunO ψ V W f) (g : GA D V) : ModGrowth W fun h => thetaKO ω g h f := by
  obtain ⟨A, d, hAd⟩ := hG V.rank W.rank
  obtain ⟨U, hUo, hfU⟩ := GlobalTheory.Size.isTheta_iff_level.mp hf
  obtain ⟨μ, 𝓕, hcov⟩ := GlobalTheory.Size.exists_isCovolOne V W
  obtain ⟨C, -, hC⟩ := (hAd V W rfl rfl).real ψ hθ hUo
  obtain ⟨-, hbd⟩ := hC χS χT ω hω μ 𝓕 hcov f hfU

  refine ⟨C * (sobO ψ θ μ 𝓕 d f).toReal * height V g ^ A, A, fun h => ?_⟩
  have key := hbd g h
  unfold thetaKO
  calc ‖ω (g, h) f 0‖ ≤ C * (sobO ψ θ μ 𝓕 d f).toReal * (height V g * height W h) ^ A := key
    _ = C * (sobO ψ θ μ 𝓕 d f).toReal * height V g ^ A * height W h ^ A := by
      rw [mul_pow]; ring

theorem integrableOn_of_rapidDec (hG : GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth.ThetaGrowth D) (hθ : IsInfFam θ)
    (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f) {ν : Measure (GA D W)} {𝓕 : Set (GA D W)}
    (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ W) 𝓕 ν) {F : GA D W → ℂ} (hF : RapidDec W F) (g : GA D V) :
    IntegrableOn (fun h => thetaKO ω g h f * F h) 𝓕 ν := by
  have hcont := thetaKO_continuous hω hf g
  exact hF.integrableOn_modGrowth_mul hν h𝓕 (thetaKO_modGrowth hG hθ hω hf g)
    (thetaKO_left hω hf g) hcont.aestronglyMeasurable

theorem liftInteg_of_growth (hP : GlobalTheory.Published.CuspRapidDecay) (D : D7) (hG : GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth.ThetaGrowth D) :
    LiftInteg D := by
  intro V W θ ψ χS χT ω hθ hω ν 𝓕 hν h𝓕 f F hf hFs hFc g

  have hdec : RapidDec W F := rapidDec_of_cuspForm hP hθ hFs hFc
  exact integrableOn_of_rapidDec hG hθ hω hf hν h𝓕 hdec g

end GlobalTheory.Chain.LiftConv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharacterUpdateOfWeakRealisation
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR.Links Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharRealise

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def toCx3One (R : RealDat3 D A3 Ks) (F : Face3 D A3) : CxData A3.fam3.amb3 where
  FC t := Tw (twAt D.what₂.embLL A3.A.v0) (R.HX t).H
  jR t := Tw.semi _ R.toRealDat.emb0 (R.jX t)
  EE := Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H
  Θ t := Tw.map _ (R.Th t)
  EEp p := Tw.sub _ (R.EEp3 p)
  EEl b := Tw.sub _ ((R.toRealDat.EEat (R.toRealDat.levR F.lv2 b)).comap R.HE.e)
  FLC i t := Tw (twAt D.what₂.embLL A3.A.v0) (R.HV i t).H
  jL i t := Tw.semi _ R.toRealDat.emb0 (R.jV i t)
  W i := Tw (twAt D.what₂.embLL A3.A.v0) (R.HW i (sg0 D A3.A)).H
  θ' i t := Tw.map _ (R.thG i t)
  Wp i p := Tw.sub _ (R.Wp3 i p)
  dW b i := Module.finrank D.what₂.LL (R.toRealDat.WL F.lv2 b i)
  WC b i v := Tw (twAt D.what₂.embLL v) (R.toRealDat.WS F.lv2 b i (sgAt D.what₂.embLL v))
  bW b i _ k := Tw.mk _ ⟨R.toRealDat.bC F.lv2 b i _ k, Submodule.subset_span ⟨k, rfl⟩⟩
  eW b i := Tw.map _ (((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) • (R.toRealDat.WS F.lv2 b i (sg0 D A3.A)).subtype)
  M b i := (R.FW i).Mcoord (F.lv2.lvl b).P (F.lv2.lvl b).ψ⁻¹ (fun g => (idemOf A3.A.X).coeff g) (R.toRealDat.bL F.lv2 b i)
  nP := RealDat.nP F.lv2
  μ := R.mu
  Tw := R.twPl
  κ _ := R.kap
  lam := R.lam3
  err0 := R.err0

theorem toCx3_eq_one (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hph : ∀ i, R.phs i = 1) : R.toCx3 F = toCx3One R F := by
  unfold RealDat3.toCx3 toCx3One
  congr 1
  funext i t
  simp only [hph, one_smul]

end GlobalTheory.CharRealise
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdemUnder

theorem under_eq_of_isIdemAt : ∀ (D : D7) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), Formalism.L2.NTheta.IsIdemAt e PP → IsPlaceIdem D v ε → e + cA D e = algebraMap (AF D.host.F) (AE D) ε → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v := by
  intro D e PP v ε he hv hsum

  obtain ⟨hee, hec, -⟩ := he.1
  have hfix : e * algebraMap (AF D.host.F) (AE D) ε = e := by
    rw [← hsum, mul_add, hee, hec, add_zero]

  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hone : Φ e PP = 1 := (GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ he).2.1
  by_contra hne
  have hzero := (GlobalTheory.IdemSupport.place_comp hΦ hv).2.2 PP hne
  have hcomp := GlobalTheory.IdemSupport.ev_mul (Φ := Φ) e (algebraMap (AF D.host.F) (AE D) ε) PP
  rw [hfix, hzero, mul_zero, hone] at hcomp
  exact one_ne_zero hcomp

end GlobalTheory.IdemUnder
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOverStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeIdempotent_under_eq_of_lies_over : ∀ (D : D7) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), Formalism.L2.NTheta.IsIdemAt e PP → IsPlaceIdem D v ε → e + cA D e = algebraMap (AF D.host.F) (AE D) ε → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v := by
  first | exact @GlobalTheory.IdemUnder.under_eq_of_isIdemAt | exact GlobalTheory.IdemUnder.under_eq_of_isIdemAt | (intros; apply GlobalTheory.IdemUnder.under_eq_of_isIdemAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersUnramifiedOffLevelPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersUnramifiedOffLevelPlaces
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory
namespace LevelPlaces
open Formalism.L2.Col Formalism.HermitianLatticesTheory GlobalTheory.SplitOffPlaces

theorem under_eq_of_isConjPl {D : D7} {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl P P') :
    P.under (𝓞 D.host.F) = P'.under (𝓞 D.host.F) := by
  refine HeightOneSpectrum.ext ((P.under (𝓞 D.host.F)).isMaximal.eq_of_le (P'.under (𝓞 D.host.F)).isPrime.ne_top
    fun a ha => ?_)
  obtain ⟨c', h1, h2⟩ := h (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) ha
  have hfix : star (algebraMap D.host.F D.host.E (a : D.host.F)) = algebraMap D.host.F D.host.E (a : D.host.F) :=
    (D.sp.cm.fixed _).2 ⟨_, rfl⟩
  have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a = c' := RingOfIntegers.ext (h2.trans hfix).symm
  change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a ∈ P'.asIdeal
  rwa [e]

theorem natCast_mem_of_isConjPl {D : D7} {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl P P')
    {n : ℕ} (hn : (n : 𝓞 D.host.E) ∈ P.asIdeal) : (n : 𝓞 D.host.E) ∈ P'.asIdeal := by
  obtain ⟨c', h1, h2⟩ := h _ hn
  have e : (n : 𝓞 D.host.E) = c' := RingOfIntegers.ext (by
    rw [h2]
    change (n : D.host.E) = star (n : D.host.E)
    rw [star_natCast])
  rwa [e]

theorem isConjPl_conjSpec {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.IndefR.Lev.IsConjPl P (conjSpec P) :=
  fun c hc => ⟨cO D.host.E c, by
    change cO D.host.E (cO D.host.E c) ∈ P.asIdeal
    rwa [cO_cO], rfl⟩

theorem not_mem_of_prime {A : Type} [CommRing A] {I : Ideal A} (hI : I ≠ ⊤) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : q ≠ p) (h : (q : A) ∈ I) : (p : A) ∉ I := by
  intro h'
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hp).2 hne)
  apply hI
  rw [Ideal.eq_top_iff_one]
  have e : (1 : A) = a * (q : A) + b * (p : A) := by
    exact_mod_cast congrArg (Int.cast : ℤ → A) hab.symm
  rw [e]
  exact add_mem (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ h')

theorem div_or_div_conj {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (k : Fin 2) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hk : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) : Pb.Div k P ∨ Pb.Div k (conjSpec P) := by
  by_contra hc
  have h1 : Pb.pb k ≠ P.under (𝓞 D.host.K) := fun e => hc (Or.inl e.symm)
  have h2 : Pb.pb k ≠ (conjSpec P).under (𝓞 D.host.K) := fun e => hc (Or.inr e.symm)
  obtain ⟨x, hx, hx1, hx2⟩ := exists_mem_not_mem h1 h2
  obtain ⟨x', n, hx', hn⟩ := exists_norm D x
  have hnP : (n : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro h
    have e : (n : 𝓞 D.host.E) = algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x * cO D.host.E (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x) := by
      rw [← hx', ← map_mul, hn, map_intCast]
    rw [e] at h
    rcases P.isPrime.mem_or_mem h with h | h
    · exact hx1 h
    · exact hx2 h
  have hnb : (n : 𝓞 D.host.K) ∈ (Pb.pb k).asIdeal := hn ▸ Ideal.mul_mem_right _ _ hx
  have hp : Prime (D.host.g k : ℤ) := Nat.prime_iff_prime_int.1 (D.host.g_prime k)
  by_cases hd : (D.host.g k : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hd
    apply hnP
    push_cast
    exact Ideal.mul_mem_right _ _ hk
  · obtain ⟨a, b, hab⟩ := (hp.irreducible.coprime_iff_not_dvd).2 hd
    apply (Pb.pb k).isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have e : (1 : 𝓞 D.host.K) = a * ((D.host.g k : ℕ) : 𝓞 D.host.K) + b * n := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.host.K) hab.symm
    rw [e]
    exact add_mem (Ideal.mul_mem_left _ _ (Pb.pb_over k)) (Ideal.mul_mem_left _ _ hnb)

theorem mem_of_div {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (k : Fin 2) (P : HeightOneSpectrum (𝓞 D.host.E))
    (h : Pb.Div k P) : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
  have h1 := Pb.pb_over k
  rw [← (show P.under (𝓞 D.host.K) = Pb.pb k from h)] at h1
  have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal := h1
  rwa [map_natCast] at h2

theorem not_mem_of_twist {D : D7} {Q : Finset (Pl D.host.E)} (hQ : Formalism.IndefR.Lev.IsTwistPlaces D.host.g Q)
    {P : Pl D.host.E} (hP : P ∈ Q) (k : Fin 2) : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hQ P hP
  refine not_mem_of_prime P.isPrime.ne_top (D.host.g_prime k) hq (hne k) ?_
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hcard, ← nsmul_one]
  exact card_nsmul_eq_zero' (G := 𝓞 D.host.E ⧸ P.asIdeal)

end LevelPlaces


open LevelPlaces SplitOffPlaces in
theorem levCh_unramified_places : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → ∀ t : T0, Disjoint L.Pg (L.Q t) ∧ (∀ PP ∈ L.Pg, (L.xiH t).UnrAt PP) ∧ (∀ PP ∈ L.Q t, ∀ j, (L.C.mu0 j).UnrAt PP) ∧ ∀ P : Pl D.host.E, (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q t → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ P.under (𝓞 D.host.F)) → (L.xiH t).UnrAt P ∧ ∀ j, (L.C.mu0 j).UnrAt P := by
  intro D T0 L μ0 hL t
  have hPg : ∀ PP ∈ L.Pg, ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP h => by
    obtain ⟨k, hk⟩ := (hL.Pg PP).1 h
    exact ⟨k, mem_of_div _ k PP hk⟩
  have hQ : ∀ PP ∈ L.Q t, ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP h k =>
    not_mem_of_twist (hL.Q_pl t) h k
  refine ⟨Finset.disjoint_left.2 fun PP h h' => ?_, fun PP h => ?_, fun PP h j => ?_, fun P hP => ⟨?_, fun j => ?_⟩⟩
  · obtain ⟨k, hk⟩ := hPg PP h
    exact hQ PP h' k hk
  · obtain ⟨k, hk⟩ := hPg PP h
    by_contra hc
    rcases (hL.Q_ram t PP).1 hc with h' | ⟨PP', h', hc'⟩
    · exact hQ PP h' k hk
    · obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hL.Q_pl t PP' h'
      have hq' : (q : 𝓞 D.host.E) ∈ PP'.asIdeal := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hcard, ← nsmul_one]
        exact card_nsmul_eq_zero' (G := 𝓞 D.host.E ⧸ PP'.asIdeal)
      exact not_mem_of_prime PP.isPrime.ne_top (D.host.g_prime k) hq (hne k) (natCast_mem_of_isConjPl hc' hq') hk
  · exact (L.C.isMu0 j).unr PP fun k => hQ PP h k
  · by_contra hc
    rcases (hL.Q_ram t P).1 hc with h' | ⟨PP', h', hc'⟩
    · exact hP P (Or.inr h') rfl
    · exact hP PP' (Or.inr h') (under_eq_of_isConjPl hc')
  · refine (L.C.isMu0 j).unr P fun k hk => ?_
    rcases div_or_div_conj L.C.P k P hk with h | h
    · exact hP P (Or.inl ((hL.Pg P).2 ⟨k, h⟩)) rfl
    · exact hP _ (Or.inl ((hL.Pg _).2 ⟨k, h⟩)) (under_eq_of_isConjPl (isConjPl_conjSpec P)).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersUnramifiedOffLevelPlacesStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacters_unramified_off_levelPlaces : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → ∀ t : T0, Disjoint L.Pg (L.Q t) ∧ (∀ PP ∈ L.Pg, (L.xiH t).UnrAt PP) ∧ (∀ PP ∈ L.Q t, ∀ j, (L.C.mu0 j).UnrAt PP) ∧ ∀ P : Pl D.host.E, (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q t → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ P.under (𝓞 D.host.F)) → (L.xiH t).UnrAt P ∧ ∀ j, (L.C.mu0 j).UnrAt P := by
  first | exact @GlobalTheory.levCh_unramified_places | exact GlobalTheory.levCh_unramified_places | (intros; apply GlobalTheory.levCh_unramified_places <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.AdSpan

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D}

def RealScal (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (B : C.Bas) (a : GA D T) (z : ℂ) : Prop :=
  ∀ φ : TF S.rank C.g, SW.IsSB φ → om (1, a) (C.Th (C.xB B) φ) = z • C.Th (C.xB (C.mvB a B)) φ

def HolUpTo (C : Ctx S T) (B : C.Bas) (la : Wt C.X.Ψ T.rank) (z φ : GA D T → ℂ) : Prop :=
  ∀ g : GA D T, ∃ Q : Frame C.X.Ψ T.rank → ℂ, DifferentiableOn ℂ Q C.X.dom ∧
    (∀ x ∈ C.X.dom, ∀ b ∈ Bor C.X.Ψ T.rank, Q (rmul x b) = bchar la b * Q x) ∧
    ∀ a ∈ GinfC T, φ (g * a) = z a * Q (C.xB (C.mvB a B))

def detPow (θ : InfFam D) (V : HSp D) (m : D.what₂.Tau → ℤ) (a : GA D V) : ℂ :=
  ∏ ρ, (compAt θ ρ (Formalism.L2.Theta.mt V a)).det ^ m ρ

def torAt (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (ρ : D.what₂.Tau)
    (t : Fin V.rank → ℝ) : GA D V :=
  atTau θ V ρ (B ρ * diagonal (fun a => cexp ((t a : ℂ) * I)) * (B ρ)⁻¹)

def LowKilled (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) : Prop :=
  HolRead.SmoothReal θ V φ ∧ ∀ ρ (c d : Fin V.rank), d < c → RderC θ V ρ (B ρ * Matrix.single c d 1 * (B ρ)⁻¹) φ = 0

def revPos {n : ℕ} (p : ℕ) (a : Fin n) : Fin n :=
  if h : (a : ℕ) < p ∧ p ≤ n then ⟨p - 1 - a, by omega⟩ else a

theorem revPos_revPos {n : ℕ} (p : ℕ) (a : Fin n) : revPos p (revPos p a) = a := by
  by_cases h : (a : ℕ) < p ∧ p ≤ n
  · have h' : p - 1 - (a : ℕ) < p ∧ p ≤ n := ⟨by omega, h.2⟩
    ext
    simp only [revPos, dif_pos h, Fin.val_mk, dif_pos h']
    omega
  · simp only [revPos, dif_neg h]

def revB {ι : Type} {n : ℕ} (p : ℕ) (B : ι → Matrix (Fin n) (Fin n) ℂ) : ι → Matrix (Fin n) (Fin n) ℂ :=
  fun τ => (B τ).submatrix id (revPos p)

def thetaSet (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (B : C.Bas) (u : WO S T → ℂ)
    (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) : Set (GA D T → ℂ) :=
  {φ | ∃ (h : GA D S) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ), C.toH Q ∈ Harm.rowHighest ℂ c c' ∧
    φ = fun g => om (h, g) (C.fvec B u Q) 0}

def ContT (ψ : AddChar (AF D.host.F) ℂ) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop :=
  ∀ f, IsThetaFunO ψ S T f → ∀ w, Continuous fun g : GA D T => om (1, g) f w

abbrev reS (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : HSp D := StdFrame.reframe S b

def frP (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : Matrix (Fin S.rank) (Fin S.rank) D.host.E :=
  S.frame.toMatrix b

def frPinv (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : Matrix (Fin S.rank) (Fin S.rank) D.host.E :=
  b.toMatrix S.frame

def reW (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (x : WO (reS S b) T) : WO S T :=
  HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x ((frPinv S b).map (incA D))

def reF (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : (WO S T → ℂ) →ₗ[ℂ] (WO (reS S b) T → ℂ) :=
  LinearMap.funLeft ℂ ℂ (reW S T b)

theorem reF_apply (b : Module.Basis (Fin S.rank) D.host.E S.V) (f : WO S T → ℂ) (x : WO (reS S b) T) :
    reF S T b f x = f (reW S T b x) := rfl

theorem reF_zero (b : Module.Basis (Fin S.rank) D.host.E S.V) (f : WO S T → ℂ) : reF S T b f 0 = f 0 := by
  rw [reF_apply]
  congr 1
  exact Matrix.zero_mul _

end GlobalTheory.AdSpan

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFamilyIffRationalHecke
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.HeckeTieCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.FWT
  Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Local

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

variable {WL : ℕ → Type} [∀ j, AddCommGroup (WL j)] [∀ j, Module D.what₂.LL (WL j)]
  (e : ∀ i : Fin D.R.m, WL ((i : ℕ) + 1) ≃ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL))

theorem isSplitPl_iff (P : PlE D.host) :
    IsSplitPl D.host P ↔ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal := by
  have hc : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = (GlobalTheory.SplitOffPlaces.conjSpec P).asIdeal := by
    rw [Formalism.L2.Col.conjIdeal_eq]; rfl
  rw [hc]
  constructor
  · rintro ⟨x, hx, h⟩ he
    refine h (Formalism.L2.Col.cO D.host.E x) (bridge_star_holds D.R D.host _) ?_
    rw [← he] at hx
    exact hx
  · intro hne
    by_contra h
    refine hne (P.isMaximal.eq_of_le (GlobalTheory.SplitOffPlaces.conjSpec P).isPrime.ne_top fun x hx => ?_).symm
    by_contra hx'
    refine h ⟨x, hx, fun y hy hyP => hx' ?_⟩
    have : y = Formalism.L2.Col.cO D.host.E x := RingOfIntegers.ext (hy.trans (bridge_star_holds D.R D.host _).symm)
    rw [this] at hyP
    exact hyP

theorem level_notMem {P : PlE D.host} (h : ∃ i', P ∉ D.ntw.S0 i') :
    ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  obtain ⟨i', hi⟩ := h
  intro hm
  rw [Nat.cast_mul] at hm
  rcases P.isPrime.mem_or_mem hm with h | h
  · exact hi (D.ntw.placesOver_subset_exceptional i' 0 h)
  · exact hi (D.ntw.placesOver_subset_exceptional i' 1 h)

theorem scalar_eq (i : Fin D.R.m) (P : PlE D.host) (k : ℕ) :
    (((R.C.mu0 i).val P : ℂˣ) : ℂ)⁻¹ ^ k * (((Nat.card (kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹ = heckeScalar R i P k := by
  rw [heckeScalar, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, inv_pow]

theorem exists_family (t : ∀ i : Fin D.R.m, ℕ → PlE D.host → Module.End D.what₂.LL (Fin (R.nW i) → D.what₂.LL)) :
    ∃ hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (WL j),
      ∀ (i : Fin D.R.m) k P, (e i).conj (hL ((i : ℕ) + 1) k P) = t i k P := by
  refine ⟨fun j => match j with
    | 0 => fun _ _ => 0
    | n + 1 => fun k P => if h : n < D.R.m then (e ⟨n, h⟩).symm.conj (t ⟨n, h⟩ k P) else 0, fun i k P => ?_⟩
  simp only [dif_pos i.2]
  exact (e i).conj.apply_symm_apply (t i k P)

end Local

section Comparison₂

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  {WL : ℕ → Type} [∀ j, AddCommGroup (WL j)] [∀ j, Module D.what₂.LL (WL j)]
  (e : ∀ i : Fin D.R.m, WL ((i : ℕ) + 1) ≃ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL))

end Comparison₂

end GlobalTheory.HeckeTieCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvInjOfIsModelsOfTie
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvalAtUnitVectorFinal

theorem evInj_of_isModels_of_tie : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.IsModels → FWTie T R κ v₀ → EvInj T R v₀ := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hM ht
  have hHW : R.models_HW := by
    cases hM
    assumption
  exact GlobalTheory.EvalAtUnitVector.evInj T R v₀ hHW ht.hv₀

end GlobalTheory.EvalAtUnitVectorFinal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRightOfMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory Formalism.L2.Theta Formalism.IndefR GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefiniteClassAvg

theorem measurePreserving_mul_right_of_mem {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] (J : Subgroup G) (hJ : IsOpen (J : Set G)) (h0 : μ J ≠ 0) (htop : μ J ≠ ⊤) {g : G}
    (hg : g ∈ J) : MeasurePreserving (· * g) μ μ := by
  refine ⟨measurable_mul_const g, ?_⟩
  set c := Measure.haarScalarFactor (Measure.map (· * g) μ) μ with hcdef
  have e : Measure.map (· * g) μ = c • μ := Measure.isMulLeftInvariant_eq_smul _ _
  have hpre : (· * g) ⁻¹' (J : Set G) = J := by
    ext x
    simp only [Set.mem_preimage, SetLike.mem_coe]
    exact J.mul_mem_cancel_right hg
  have h1 : Measure.map (· * g) μ J = μ J := by
    rw [Measure.map_apply (measurable_mul_const g) hJ.measurableSet, hpre]
  rw [e, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
  have hc : ((c : ENNReal)) = 1 := by
    have h2 : (c : ENNReal) * μ J / μ J = (c : ENNReal) := ENNReal.mul_div_cancel_right h0 htop
    rw [h1, ENNReal.div_self h0 htop] at h2
    exact h2.symm
  have hc' : c = 1 := by exact_mod_cast hc
  rw [e, hc', one_smul]

theorem setIntegral_comp_mul_right_of_mp {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant]
    (Γ : Subgroup G) [Countable Γ] (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (f : G → ℂ)
    (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (g : G) (hg : MeasurePreserving (· * g) μ μ) :
    ∫ x in 𝓕, f (x * g) ∂μ = ∫ x in 𝓕, f x ∂μ := by
  have hg' : MeasurePreserving (MeasurableEquiv.mulRight g) μ μ := hg
  have h2 : IsFundamentalDomain Γ ((fun x => x * g) '' 𝓕) μ :=
    h𝓕.image_of_equiv (MeasurableEquiv.mulRight g).toEquiv hg'.symm.quasiMeasurePreserving (Equiv.refl _)
      (fun γ x => by
        show (γ • x) * g = γ • (x * g)
        simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc])
  rw [← hg.setIntegral_image_emb (measurableEmbedding_mulRight g) f 𝓕]
  refine h2.setIntegral_eq h𝓕 ?_
  intro γ x
  rw [Subgroup.smul_def, smul_eq_mul]
  exact hf γ γ.2 x

end GlobalTheory.DefiniteClassAvg

namespace GlobalTheory.DefiniteClassAvg

theorem integral_eq_sum_avg (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [SecondCountableTopology G] (μ : Measure G) [μ.IsMulLeftInvariant] (Γ K Kf : Subgroup G) [Countable Γ]
    (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hK : IsOpen (K : Set G)) (hKfin : μ K ≠ ⊤)
    (U : Type) [Group U] [TopologicalSpace U] [IsTopologicalGroup U] [CompactSpace U] [MeasurableSpace U] [BorelSpace U]
    (ν : Measure U) [ν.IsMulLeftInvariant] [IsProbabilityMeasure ν] (j : U →* G) (hj : Continuous j)
    (hrt : ∀ w, MeasurePreserving (· * j w) μ μ)
    (hdec : ∀ k ∈ K, ∃ k' ∈ Kf, ∃ w, k = k' * j w) (hcomm : ∀ k ∈ Kf, ∀ w, k * j w = j w * k)
    (ι : Type) [Fintype ι] (h : ι → G) (huniq : ∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k)
    (hfin : ∀ i, {γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.Finite) (f : G → ℂ) (hf : Continuous f)
    (hfl : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (hfr : ∀ k ∈ Kf, ∀ x, f (x * k) = f x) :
    IntegrableOn f 𝓕 μ ∧ ∫ x in 𝓕, f x ∂μ = ((μ K).toReal : ℂ) *
      ∑ i, (({γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.ncard : ℕ) : ℂ)⁻¹ * ∫ v, f (h i * j v) ∂ν := by
  have key : ∀ x, ∀ k' ∈ Kf, ∀ w, f (x * (k' * j w)) = f (x * j w) := by
    intro x k' hk' w
    rw [hcomm k' hk' w, ← mul_assoc, hfr k' hk']
  have hbd : ∃ C, ∀ x, ‖f x‖ ≤ C := by
    have hi : ∀ i, ∃ C, ∀ v, ‖f (h i * j v)‖ ≤ C := fun i =>
      (isCompact_range ((hf.comp (continuous_const.mul hj)).norm)).bddAbove.imp
        fun C hC v => hC ⟨v, rfl⟩
    choose B hB using hi
    refine ⟨∑ i, |B i|, fun x => ?_⟩
    obtain ⟨i, ⟨γ, hγ, k, hk, rfl⟩, -⟩ := huniq x
    obtain ⟨k', hk', w, rfl⟩ := hdec k hk
    rw [mul_assoc, hfl γ hγ, key _ k' hk' w]
    exact (hB i w).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |B i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)))
  obtain ⟨C, hC⟩ := hbd
  have hFl : ∀ γ ∈ Γ, ∀ x, ∫ v, f (γ * x * j v) ∂ν = ∫ v, f (x * j v) ∂ν := by
    intro γ hγ x
    congr 1; funext v; rw [mul_assoc, hfl γ hγ]
  have hFr : ∀ k ∈ K, ∀ x, ∫ v, f (x * k * j v) ∂ν = ∫ v, f (x * j v) ∂ν := by
    intro k hk x
    obtain ⟨k', hk', w, rfl⟩ := hdec k hk
    have e : ∀ v, f (x * (k' * j w) * j v) = f (x * j (w * v)) := by
      intro v
      have : x * (k' * j w) * j v = x * j (w * v) * k' := by
        calc x * (k' * j w) * j v = x * j w * (k' * j v) := by
                rw [hcomm k' hk' w]; simp only [mul_assoc]
          _ = x * j w * (j v * k') := by rw [hcomm k' hk' v]
          _ = x * j (w * v) * k' := by rw [map_mul]; simp only [mul_assoc]
      rw [this, hfr k' hk']
    simp_rw [e]
    exact integral_mul_left_eq_self (fun v => f (x * j v)) w
  obtain ⟨hfin𝓕, -, hFeq⟩ := GlobalTheory.Ker.integral_fundamentalDomain_eq_sum_doubleCoset G μ Γ K 𝓕 h𝓕 hK
    hKfin ι h huniq hfin (fun x => ∫ v, f (x * j v) ∂ν) hFl hFr
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 hfin𝓕
  have hint : IntegrableOn f 𝓕 μ :=
    Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  refine ⟨hint, ?_⟩
  have hc : Continuous fun p : G × U => f (p.1 * j p.2) :=
    hf.comp (continuous_fst.mul (hj.comp continuous_snd))
  have hI : Integrable (Function.uncurry fun x v => f (x * j v)) ((μ.restrict 𝓕).prod ν) :=
    Integrable.of_bound hc.aestronglyMeasurable C (Filter.Eventually.of_forall fun p => hC _)
  have hsh : ∀ v, ∫ x in 𝓕, f (x * j v) ∂μ = ∫ x in 𝓕, f x ∂μ := fun v =>
    setIntegral_comp_mul_right_of_mp μ Γ 𝓕 h𝓕 f hfl (j v) (hrt v)
  calc ∫ x in 𝓕, f x ∂μ = ∫ x in 𝓕, ∫ v, f (x * j v) ∂ν ∂μ := by
        rw [integral_integral_swap hI]
        simp only [hsh]
        simp
    _ = _ := hFeq

end GlobalTheory.DefiniteClassAvg

namespace GlobalTheory.DefiniteClassAvg

variable {D : D7}

noncomputable def realPart (V : HSp D) (y : GA D V) : GA D V :=
  Eqv.UI.brg (Eqv.UI.framesV D V) (((Eqv.UI.brg (Eqv.UI.framesV D V)).symm y).1, 1)

noncomputable def finPart (V : HSp D) (y : GA D V) : GA D V :=
  Eqv.UI.brg (Eqv.UI.framesV D V) (1, ((Eqv.UI.brg (Eqv.UI.framesV D V)).symm y).2)

theorem realPart_mem (V : HSp D) (y : GA D V) : realPart V y ∈ GinfC V := (Eqv.brg_mem_GinfC _ _).2 rfl

theorem finPart_mem (V : HSp D) (y : GA D V) : finPart V y ∈ GfC V := (Eqv.brg_mem_GfC _ _).2 rfl

theorem realPart_mul_finPart (V : HSp D) (y : GA D V) : realPart V y * finPart V y = y := by
  unfold realPart finPart
  rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  exact (Eqv.UI.brg (Eqv.UI.framesV D V)).apply_symm_apply y

theorem finPart_mul_realPart (V : HSp D) (y : GA D V) : finPart V y * realPart V y = y := by
  rw [← Eqv.Act.comm_inf_fin (realPart_mem V y) (finPart_mem V y)]
  exact realPart_mul_finPart V y

theorem continuous_realPart (V : HSp D) : Continuous (realPart V) :=
  (Eqv.UI.brg (Eqv.UI.framesV D V)).continuous.comp
    ((continuous_fst.comp (Eqv.UI.brg (Eqv.UI.framesV D V)).symm.continuous).prodMk continuous_const)

theorem finE_eq_one_of_mem {V : HSp D} {a : GA D V} (ha : a ∈ GinfC V) : Lev.finE V a = 1 := by
  have h : finHom V a = 1 := ha
  show Formalism.UG.bc (Lev.swapAE D) (finHom V a) = 1
  rw [h, map_one]

theorem finE_finPart (V : HSp D) (y : GA D V) : Lev.finE V (finPart V y) = Lev.finE V y := by
  conv_rhs => rw [← realPart_mul_finPart V y]
  rw [map_mul, finE_eq_one_of_mem (realPart_mem V y), one_mul]

theorem finPart_mem_levA (V : HSp D) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))} {y : GA D V}
    (h : Lev.finE V y ∈ K) : finPart V y ∈ Lev.levA V K :=
  Subgroup.mem_inf.2 ⟨finPart_mem V y, by show Lev.finE V (finPart V y) ∈ K; rw [finE_finPart]; exact h⟩

theorem continuous_of_level (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (ho : IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V))) (Φ : GA D V → ℂ)
    (hr : ∀ k ∈ Lev.levA V K, ∀ h, Φ (h * k) = Φ h) (hc : ∀ x, Continuous fun k : GinfC V => Φ (x * k)) :
    Continuous Φ := by
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hG := hT.2.2.2.2.1
  rw [continuous_iff_continuousAt]
  intro x0
  let p : GA D V → GinfC V := fun x => ⟨realPart V (x0⁻¹ * x), realPart_mem V _⟩
  have hp : Continuous p :=
    ((continuous_realPart V).comp (continuous_const_mul x0⁻¹)).subtype_mk _
  have hev : (fun x => Φ (x0 * (p x : GA D V))) =ᶠ[𝓝 x0] Φ := by
    have hn : (fun x => x0⁻¹ * x) ⁻¹' ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) ∈ 𝓝 x0 :=
      (ho.preimage (continuous_const_mul x0⁻¹)).mem_nhds (by
        simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
        exact (K.comap (Lev.finE V)).one_mem)
    filter_upwards [hn] with x hx
    have hx' : Lev.finE V (x0⁻¹ * x) ∈ K := hx
    have hq := finPart_mem_levA V hx'
    show Φ (x0 * realPart V (x0⁻¹ * x)) = Φ x
    calc Φ (x0 * realPart V (x0⁻¹ * x)) = Φ (x0 * realPart V (x0⁻¹ * x) * finPart V (x0⁻¹ * x)) := (hr _ hq _).symm
      _ = Φ x := by rw [mul_assoc, realPart_mul_finPart, mul_inv_cancel_left]
  exact ((hc x0).comp hp).continuousAt.congr hev

end GlobalTheory.DefiniteClassAvg

namespace GlobalTheory.DefiniteClassAvg

theorem existsUnique_doubleCoset {G H : Type} [Group G] [Group H] (π : G →* H) (Γ : Subgroup G) (J : Subgroup H) {I : Type}
    (y : I → H) (hy : Bridge.IsReps (π.comp Γ.subtype) J y) (a : I → G) (ha : ∀ i, π (a i) = y i) :
    ∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ J.comap π, x = γ * a i * k := by
  intro x
  refine (existsUnique_congr fun i => ?_).1 (hy (π x))
  constructor
  · rintro ⟨γ, k, e⟩
    refine ⟨γ, γ.2, ((γ : G) * a i)⁻¹ * x, ?_, by group⟩
    rw [Subgroup.mem_comap, map_mul, map_inv, map_mul, ha, e]
    change (π γ * y i)⁻¹ * (π γ * y i * k) ∈ J
    rw [inv_mul_cancel_left]
    exact k.2
  · rintro ⟨γ, hγ, k, hk, rfl⟩
    exact ⟨⟨γ, hγ⟩, ⟨π k, hk⟩, by rw [map_mul, map_mul, ha]; rfl⟩

end GlobalTheory.DefiniteClassAvg

namespace GlobalTheory.DefiniteClassAvg

end GlobalTheory.DefiniteClassAvg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightTranslate
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SquareComm

variable {D : D7} {M X V : HSp D} (ω : WRep M X) (j : GA D V → GA D X) (G : GA D V → ℂ)
  (ν : Measure (GA D M)) (𝓕 : Set (GA D M)) (μ : Measure (GA D V)) (𝓔 : Set (GA D V))

variable {ω j G ν 𝓕 μ 𝓔}

theorem ofSgn_symm_mem_GQ (ε : Bool) {γ : GA D M} (hγ : γ ∈ GQ M) : (ofSgn ε M).symm γ ∈ GQ (sgn ε M) := by
  have hγ' : γ.1 ∈ HFin (AF D.host.F) D.sp.cm.sig M.gram := hγ
  cases ε
  · exact hγ'
  · have hm : γ.1 ∈ HFin (AF D.host.F) D.sp.cm.sig (-M.gram) := by
      unfold HFin at hγ' ⊢
      rw [UJ_neg]
      exact hγ'
    rw [← neg_gram] at hm
    exact hm

theorem integral_rightTranslate (h : IsHaarFD M ν 𝓕) {f : GA D M → ℂ} (hf : ∀ γ ∈ GQ M, ∀ w, f (γ * w) = f w) (u : GA D M) :
    (IntegrableOn (fun w => f (w * u)) 𝓕 ν ↔ IntegrableOn f 𝓕 ν) ∧ ∫ w in 𝓕, f (w * u) ∂ν = ∫ w in 𝓕, f w ∂ν := by
  obtain ⟨hH, hFD⟩ := h
  obtain ⟨_, _, _, hB, hTG, _, hC⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D M
  have : ν.IsMulRightInvariant :=
    (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D M ν hH).1
  have hpres : MeasurePreserving (fun w => w * u) ν ν := measurePreserving_mul_right ν u
  have hemb : MeasurableEmbedding (fun w : GA D M => w * u) := (MeasurableEquiv.mulRight u).measurableEmbedding
  set S : Set (GA D M) := (fun w => w * u⁻¹) ⁻¹' 𝓕 with hSdef
  have hS : IsFundamentalDomain (GQ M) S ν :=
    hFD.preimage_of_equiv (measurePreserving_mul_right ν u⁻¹).quasiMeasurePreserving Function.bijective_id
      (fun g x => by simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc])
  have hset : (fun w => w * u) ⁻¹' S = 𝓕 := by
    ext w
    simp [hSdef]
  have hinv : ∀ (g : GQ M) (x : GA D M), f (g • x) = f x := fun g x => hf g g.2 x
  refine ⟨?_, ?_⟩
  · have h1 := hpres.integrableOn_comp_preimage hemb (f := f) (s := S)
    rw [hset] at h1
    exact h1.trans (hS.integrableOn_iff hFD hinv)
  · have h2 := hpres.setIntegral_preimage_emb hemb f S
    rw [hset] at h2
    exact h2.trans (hS.setIntegral_eq hFD hinv)

end GlobalTheory.SquareComm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedAtPlaceIdempotentOfHeckeCharUnramifi
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedAtPlaceIdempotentOfHeckeCharUnramifi
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Links Formalism.L2.Host GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnramOver

theorem map_eq_one_of_supp {R K : Type} [CommRing R] [CommRing K] (f : R →+* K) {e x : R}
    (hx : e * (x - 1) = x - 1) (he : f e = 0) : f x = 1 := by
  have h := congrArg f hx
  rw [map_mul, map_sub, map_one, he, zero_mul] at h
  exact sub_eq_zero.mp h.symm

theorem val_eq_one_of_unit {R K Γ : Type} [CommRing R] [CommRing K] [LinearOrderedCommMonoidWithZero Γ]
    (w : Valuation K Γ) (f : R →+* K) (x : Rˣ) (a : w (f x) ≤ 1) (b : w (f (x⁻¹ : Rˣ)) ≤ 1) : w (f x) = 1 := by

  have hprod : w (f x) * w (f (x⁻¹ : Rˣ)) = 1 := by
    rw [← Valuation.map_mul, ← map_mul f, Units.mul_inv, map_one f, Valuation.map_one]
  refine le_antisymm a ?_
  calc (1 : Γ) = w (f x) * w (f (x⁻¹ : Rˣ)) := hprod.symm
    _ ≤ w (f x) := mul_le_of_le_one_right' b

theorem unramAt_of_unrAt : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ →
    ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
    (∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) = v → χ.UnrAt P) → UnramAt ε c := by
  classical
  intro D c χ hce v ε hε hunr x hsupp hxi hxii
  obtain ⟨ι, hι1, hint, happ⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hmain⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι hι1 hint
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι hι1 hint happ) c χ hce
  obtain ⟨α, rfl, -, hα0⟩ := hε

  have hinf0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E))
      (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    rw [Algebra.TensorProduct.map_tmul]
    exact TensorProduct.zero_tmul _ _
  have hfin : finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = α ⊗ₜ[D.host.F] (1 : D.host.E) := by
    show (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
      (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = _
    rw [Algebra.TensorProduct.map_tmul]
    rfl

  have hx1 : infPart D (x : AE D) = 1 := map_eq_one_of_supp (infPart D) hsupp hinf0

  have hval : ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι (finPart D (x : AE D)) P) = 1 := fun P =>
    val_eq_one_of_unit Valued.v ((GlobalTheory.CharLocProd.evalAt P).comp (ι.toRingHom.comp (finPart D))) x
      ((hint _).1 hxi P) ((hint _).1 hxii P)

  have hoff : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) ≠ v →
      ι (finPart D (x : AE D)) P = 1 := by
    intro P hP
    refine map_eq_one_of_supp ((GlobalTheory.CharLocProd.evalAt P).comp (ι.toRingHom.comp (finPart D))) hsupp ?_
    show ι (finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α))) P = 0
    rw [hfin]
    have hα : α (P.under (𝓞 D.host.F)) = 0 := hα0 _ hP
    apply GlobalTheory.PlaceIdem.eq_zero_of_val
    intro n
    have h := happ α 0 P n (by rw [hα, map_zero, sub_zero, Valuation.map_zero]; exact zero_le')
    rwa [map_zero, map_zero, sub_zero] at h

  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN
    (Units.map (ι.toRingHom.comp (finPart D)).toMonoidHom x)
  have hXP : ∀ P, ((Units.map (ι.toRingHom.comp (finPart D)).toMonoidHom x : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      FiniteAdeleRing (𝓞 D.host.E) D.host.E) P = ι (finPart D (x : AE D)) P := fun _ => rfl
  have hS2 : ∀ P ∈ S, Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k P : D.host.E) ∧
      Valued.v (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k P : D.host.E)) ≤
        P.valuation D.host.E (N : D.host.E) * P.valuation D.host.E (k P : D.host.E) := by
    intro P hP
    have h := hS P hP
    rw [hXP] at h
    exact ⟨h.1, h.2.1⟩
  have hS'2 : ∀ P, P ∉ S → Valued.v (ι (finPart D (x : AE D)) P) = 1 ∧ (N : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro P hP
    have h := hS' P hP
    rwa [hXP] at h

  obtain ⟨k', hk'1, hk'2⟩ : ∃ k' : HeightOneSpectrum (𝓞 D.host.E) → D.host.Eˣ,
      (∀ P, P.under (𝓞 D.host.F) = v → k' P = k P) ∧ (∀ P, P.under (𝓞 D.host.F) ≠ v → k' P = 1) :=
    ⟨fun P => if P.under (𝓞 D.host.F) = v then k P else 1, fun _ h => if_pos h, fun _ h => if_neg h⟩
  have hcx := hmain x hx1 S k' ?_ ?_
  · have hprod : ∏ P ∈ S, ((χ.locK P (k' P) : ℂˣ) : ℂ) = 1 := by
      apply Finset.prod_eq_one
      intro P hPS
      by_cases hP : P.under (𝓞 D.host.F) = v
      · rw [hk'1 P hP]
        have hu : χ.loc P (atFin P (k P)) = 1 := by
          apply hunr P hP
          show Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (k P : D.host.E)) = 1
          rw [GlobalTheory.CharLocProd.val_algebraMap, ← (hS2 P hPS).1]
          exact hval P
        show ((χ.loc P (atFin P (k P)) : ℂˣ) : ℂ) = 1
        rw [hu, Units.val_one]
      · rw [hk'2 P hP, map_one, Units.val_one]
    exact Circle.coe_eq_one.mp (hcx.trans hprod)
  · intro P hPS
    by_cases hP : P.under (𝓞 D.host.F) = v
    · rw [hk'1 P hP]
      exact hS2 P hPS
    · rw [hk'2 P hP, hoff P hP]
      refine ⟨?_, ?_⟩
      · rw [Units.val_one, Valuation.map_one, map_one]
      · rw [Units.val_one, map_one, sub_self, Valuation.map_zero]
        exact zero_le'
  · intro P hPS
    exact hS'2 P hPS

end GlobalTheory.UnramOver
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedAtPlaceIdempotentOfHeckeCharUnramifiStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε → (∀ P : Pl D.host.E, P.under (𝓞 D.host.F) = v → χ.UnrAt P) → UnramAt ε c := by
  first | exact @GlobalTheory.UnramOver.unramAt_of_unrAt | exact GlobalTheory.UnramOver.unramAt_of_unrAt | (intros; apply GlobalTheory.UnramOver.unramAt_of_unrAt <;> assumption)
end
end
