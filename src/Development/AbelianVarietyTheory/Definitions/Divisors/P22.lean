module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.OfPositiveTrivial
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
public import Development.AbelianVarietyTheory.PublishedTheorems.ThetaCharacteristics.ThetaCharZero
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.ExistsLinearIndependentNormLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FlatSecInhabited
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.P22
namespace GlobalTheory.CovTop

structure Hypotheses₂ : Prop where
  p1 : GlobalTheory.Published.ToroidalCompactification
  p2 : GlobalTheory.Published.VolGe
  p3 : GlobalTheory.Published.VolNef
  p4 : GlobalTheory.Published.ArCalc
  p5 : GlobalTheory.Published.AbelianDeRham
  p6 : GlobalTheory.Published.TamagawaSpecialUnitary
  p8 : GlobalTheory.Published.RayClassFieldSt
  p12 : GlobalTheory.Published.SemistableReductionSt
  p13 : GlobalTheory.Published.StrongApproxSU
  p14 : GlobalTheory.Published.GreenSeriesSt
  p16 : GlobalTheory.Published.MumfordProportionality
  p18 : GlobalTheory.Published.FinitenessOfHermitianClasses
  p19 : GlobalTheory.Published.LandherrSt
  p20 : GlobalTheory.Published.HasseNormSt
  p22 : GlobalTheory.Published.SemiAbelianHomExtension
  p23 : GlobalTheory.Published.InducedSimpleLowestAlcove
  p25 : GlobalTheory.Published.principalPolarisationOneSection
  p26 : GlobalTheory.Published.AbMulNSt

end GlobalTheory.CovTop
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlatTw

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine
  GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

def IntOff {K : Type} [Field K] [NumberField K] (B : Finset ℕ) (ρ : HeightOneSpectrum (𝓞 K) → ℝ) : Prop :=
  ∀ w, (∀ p ∈ B, ((p : ℕ) : 𝓞 K) ∉ w.asIdeal) → ∃ n : ℤ, ρ w = n

def logSum (B : Finset ℕ) : ℝ := ∑ p ∈ B, Real.log p

theorem IntOff.add {K : Type} [Field K] [NumberField K] {B : Finset ℕ} {ρ ρ' : HeightOneSpectrum (𝓞 K) → ℝ}
    (h : IntOff B ρ) (h' : IntOff B ρ') : IntOff B (ρ + ρ') := fun w hw => by
  obtain ⟨n, hn⟩ := h w hw
  obtain ⟨m, hm⟩ := h' w hw
  exact ⟨n + m, by simp [hn, hm]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)

structure TwSec (Z : Comp Xo c) (G₀ : WTZ E) : Type where
  even : Even G₀.2

  sig : Rul Xo c

  inv : Rul Xo c
  sig_mem : sig ∈ secZ Xo c (exZ Dw G₀)
  inv_mem : inv ∈ secZ Xo c (-exZ Dw G₀)
  idem_sig : idem Z * sig = sig
  idem_inv : idem Z * inv = inv
  mul_inv : sig * inv = idem Z

  cInf : (c.F →+* ℂ) → ℝ
  cInf_pos : ∀ σ, 0 < cInf σ
  norm_inf : ∀ σ, ∀ z ∈ framesOn (U (goodOf c σ)) Z, homN (U (goodOf c σ)) x G₀ sig z = cInf σ
  cusp_sig : ∀ G : WTZ E, Even G.2 → ∀ f ∈ cuspOn U Z G, f * sig ∈ cuspOn U Z (G + G₀)
  cusp_inv : ∀ G : WTZ E, Even G.2 → ∀ f ∈ cuspOn U Z (G + G₀), f * inv ∈ cuspOn U Z G

  lo : HeightOneSpectrum (𝓞 c.F) → ℝ

  hi : HeightOneSpectrum (𝓞 c.F) → ℝ
  lo_le : ∀ w, ∀ v ∈ valOn Z w, ((lo w : ℝ) : EReal) ≤ v sig
  le_hi : ∀ w, ∀ v ∈ valOn Z w, v sig ≤ ((hi w : ℝ) : EReal)
  finite_lo : (Function.support lo).Finite
  finite_hi : (Function.support hi).Finite

  pts : HasPts U Z := by assumption

variable {U x}

def TwSec.degLo {Z : Comp Xo c} {G₀ : WTZ E} (s : TwSec U x Z G₀) : ℝ := lineDeg s.cInf s.lo

theorem mul_smul_idem_mem {Z : Comp Xo c} {G : WTZ E} {f : Rul Xo c} (hf : f ∈ cuspOn U Z G) (a : c.F) :
    f * (a • idem Z) ∈ cuspOn U Z G := by
  have h : idem Z * f = f := idem_mul_eq (e := exZ Dw G) ⟨cuspW_le_secZ G hf.1, hf.2⟩
  rw [mul_smul_comm, mul_comm f, h]
  exact Submodule.smul_mem _ _ hf

theorem exZ_add_eq (G G' : WTZ E) : exZ Dw (G + G') = exZ Dw G + exZ Dw G' := funext fun i => exZ_add _ _ i

theorem exZ_neg_eq (G : WTZ E) : exZ Dw (-G) = -exZ Dw G := by
  funext i; cases i <;> rfl

namespace TwSec

variable {Z : Comp Xo c} {G₀ G₁ : WTZ E}

theorem sig_mem_suppOn (s : TwSec U x Z G₀) : s.sig ∈ suppOn Z := by
  rw [← s.idem_sig, mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)

theorem cInf_congr (s : TwSec U x Z G₀) {σ σ' : c.F →+* ℂ} (h : goodOf c σ = goodOf c σ') : s.cInf σ = s.cInf σ' := by
  obtain ⟨z, hz⟩ := (s.pts.1 σ).1
  have h2 := s.norm_inf σ'
  rw [← h] at h2
  rw [← s.norm_inf σ z hz, h2 z hz]

theorem homN_mul_sig (s : TwSec U x Z G₀) {G : WTZ E} (hG : Even G.2) (f : Rul Xo c) {σ : c.F →+* ℂ} {z}
    (hz : z ∈ framesOn (U (goodOf c σ)) Z) :
    homN (U (goodOf c σ)) x (G + G₀) (f * s.sig) z = homN (U (goodOf c σ)) x G f z * s.cInf σ := by
  rw [homN_mul _ x hG s.even _ _ _ hz.1, s.norm_inf σ z hz]

theorem exists_val (s : TwSec U x Z G₀) {w} {v : Rul Xo c → EReal} (hv : v ∈ valOn Z w) :
    ∃ b : ℝ, v s.sig = b ∧ v s.inv = ((-b : ℝ) : EReal) ∧ s.lo w ≤ b ∧ b ≤ s.hi w := by
  have h1 := s.lo_le w v hv
  have h2 := s.le_hi w v hv
  have h := (isVal_valOn hv).mul s.sig s.inv
  rw [s.mul_inv, val_idem hv] at h
  lift v s.sig to ℝ using ⟨(h2.trans_lt (EReal.coe_lt_top _)).ne, ((EReal.bot_lt_coe _).trans_le h1).ne'⟩ with a
  have ht : v s.inv ≠ ⊤ := fun h' => by rw [h', EReal.coe_add_top] at h; exact EReal.zero_ne_top h
  lift v s.inv to ℝ using ⟨ht, (isVal_valOn hv).ne_bot s.inv⟩ with b
  rw [← EReal.coe_add, ← EReal.coe_zero, EReal.coe_eq_coe_iff] at h
  exact ⟨a, rfl, EReal.coe_eq_coe_iff.2 (by linarith), EReal.coe_le_coe_iff.1 h1, EReal.coe_le_coe_iff.1 h2⟩

def copy (s : TwSec U x Z G₀) (h : G₀ = G₁) : TwSec U x Z G₁ :=
  { s with
    even := h ▸ s.even, sig_mem := h ▸ s.sig_mem, inv_mem := h ▸ s.inv_mem, norm_inf := h ▸ s.norm_inf,
    cusp_sig := h ▸ s.cusp_sig, cusp_inv := h ▸ s.cusp_inv }

def mul (s : TwSec U x Z G₀) (t : TwSec U x Z G₁) : TwSec U x Z (G₀ + G₁) where
  even := s.even.add t.even
  sig := s.sig * t.sig
  inv := s.inv * t.inv
  sig_mem := exZ_add_eq (Dw := Dw) G₀ G₁ ▸ mul_mem_secZ s.sig_mem t.sig_mem
  inv_mem := by rw [exZ_add_eq, neg_add]; exact mul_mem_secZ s.inv_mem t.inv_mem
  idem_sig := by rw [← mul_assoc, s.idem_sig]
  idem_inv := by rw [← mul_assoc, s.idem_inv]
  mul_inv := by rw [mul_mul_mul_comm, s.mul_inv, t.mul_inv, idem_mul_idem]
  cInf := s.cInf * t.cInf
  cInf_pos σ := mul_pos (s.cInf_pos σ) (t.cInf_pos σ)
  norm_inf σ z hz := by rw [t.homN_mul_sig s.even _ hz, s.norm_inf σ z hz]; rfl
  cusp_sig G hG f hf := by
    rw [← mul_assoc, ← add_assoc]
    exact t.cusp_sig _ (hG.add s.even) _ (s.cusp_sig G hG f hf)
  cusp_inv G hG f hf := by
    rw [← add_assoc] at hf
    rw [mul_comm s.inv, ← mul_assoc]
    exact s.cusp_inv G hG _ (t.cusp_inv _ (hG.add s.even) f hf)
  lo := s.lo + t.lo
  hi := s.hi + t.hi
  lo_le w v hv := by
    rw [(isVal_valOn hv).mul, Pi.add_apply, EReal.coe_add]; exact add_le_add (s.lo_le w v hv) (t.lo_le w v hv)
  le_hi w v hv := by
    rw [(isVal_valOn hv).mul, Pi.add_apply, EReal.coe_add]; exact add_le_add (s.le_hi w v hv) (t.le_hi w v hv)
  finite_lo := (s.finite_lo.union t.finite_lo).subset (Function.support_add _ _)
  finite_hi := (s.finite_hi.union t.finite_hi).subset (Function.support_add _ _)
  pts := s.pts

theorem degLo_mul (s : TwSec U x Z G₀) (t : TwSec U x Z G₁) : (s.mul t).degLo = s.degLo + t.degLo :=
  lineDeg_mul s.cInf_pos t.cInf_pos s.finite_lo t.finite_lo

def symm (s : TwSec U x Z G₀) : TwSec U x Z (-G₀) where
  even := s.even.neg
  sig := s.inv
  inv := s.sig
  sig_mem := exZ_neg_eq (Dw := Dw) G₀ ▸ s.inv_mem
  inv_mem := by rw [exZ_neg_eq, neg_neg]; exact s.sig_mem
  idem_sig := s.idem_inv
  idem_inv := s.idem_sig
  mul_inv := by rw [mul_comm, s.mul_inv]
  cInf := s.cInf⁻¹
  cInf_pos σ := inv_pos.2 (s.cInf_pos σ)
  norm_inf σ z hz := by
    have h := s.homN_mul_sig (G := -G₀) s.even.neg s.inv hz
    rw [neg_add_cancel, mul_comm s.inv, s.mul_inv, homN_idem _ x hz.1 hz.2 ((s.pts.1 σ).2 z hz _)] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  cusp_sig G hG f hf := s.cusp_inv _ (hG.add s.even.neg) f (by rwa [neg_add_cancel_right])
  cusp_inv G hG f hf := by
    have h := s.cusp_sig _ (show Even (G + -G₀).2 from hG.add s.even.neg) f hf
    rwa [neg_add_cancel_right] at h
  lo := -s.hi
  hi := -s.lo
  lo_le w v hv := by
    obtain ⟨b, -, h, -, h'⟩ := s.exists_val hv
    rw [h]; exact EReal.coe_le_coe_iff.2 (neg_le_neg h')
  le_hi w v hv := by
    obtain ⟨b, -, h, h', -⟩ := s.exists_val hv
    rw [h]; exact EReal.coe_le_coe_iff.2 (neg_le_neg h')
  finite_lo := by simpa using s.finite_hi
  finite_hi := by simpa using s.finite_lo
  pts := s.pts

def ofConst {la : GlobalTheory.AllWt.Weight Dw} {δ : HeightOneSpectrum (𝓞 c.F) → ℝ} (s : ConstSec U x Z la δ)
    (hδ : (Function.support δ).Finite)
    (h₁ : ∀ G : WTZ E, Even G.2 → ∀ f ∈ cuspOn U Z G, f * s.sig ∈ cuspOn U Z (G + wtOf Dw la 0))
    (h₂ : ∀ G : WTZ E, Even G.2 → ∀ f ∈ cuspOn U Z (G + wtOf Dw la 0), f * s.inv ∈ cuspOn U Z G) :
    TwSec U x Z (wtOf Dw la 0) where
  even := even_wtOf _ _
  sig := s.sig
  inv := s.inv
  sig_mem := s.sig_mem
  inv_mem := s.inv_mem
  idem_sig := s.idem_sig
  idem_inv := s.idem_inv
  mul_inv := s.mul_inv
  cInf := s.cInf
  cInf_pos := s.cInf_pos
  norm_inf _ _ hz := s.homN_eq hz
  cusp_sig := h₁
  cusp_inv := h₂
  lo := δ + s.rho_vw
  hi := δ + s.rho_vw
  lo_le _ _ hv := (s.val_eq hv).ge
  le_hi _ _ hv := (s.val_eq hv).le
  finite_lo := (hδ.union s.finite_rho).subset (Function.support_add _ _)
  finite_hi := (hδ.union s.finite_rho).subset (Function.support_add _ _)
  pts := s.hasPts


variable (x) in
def const (h : HasPts U Z) (a : c.F) (ha : a ≠ 0) : TwSec U x Z 0 :=
  (ofConst ((ConstSec.one x h).smul a ha) (by simp)
    (fun G _ f hf => by rw [wtOf_zero, add_zero]; exact mul_smul_idem_mem hf a)
    (fun G _ f hf => by rw [wtOf_zero, add_zero] at hf; exact mul_smul_idem_mem hf a⁻¹)).copy wtOf_zero

theorem const_spec (h : HasPts U Z) (a : c.F) (ha : a ≠ 0) :
    (const x h a ha).sig = a • idem Z ∧ (∀ σ, (const x h a ha).cInf σ = ‖σ a‖) ∧
      (∀ w, (const x h a ha).lo w = vAdd w a) ∧ (∀ w, (const x h a ha).hi w = vAdd w a) ∧
      (const x h a ha).degLo = 0 := by
  have h1 : ∀ σ, (const x h a ha).cInf σ = ‖σ a‖ := fun σ => mul_one _
  have h2 : ∀ w, (const x h a ha).lo w = vAdd w a := fun w => (zero_add _).trans (add_zero _)
  refine ⟨rfl, h1, h2, h2, ?_⟩
  rw [degLo, funext h1, funext h2]
  exact lineDeg_num ha

end TwSec


variable (Xo c) in
def UnramPts (B : Finset ℕ) : Prop :=
  ∀ (Z : Comp Xo c) (w : HeightOneSpectrum (𝓞 c.F)), (∀ p ∈ B, ((p : ℕ) : 𝓞 c.F) ∉ w.asIdeal) →
    ∃ v ∈ valOn Z w, ∀ f : Rul Xo c, v f = ⊤ ∨ ∃ n : ℤ, v f = ((n : ℝ) : EReal)

def badPrimes (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) : Finset ℕ :=
  (2 * H.d * (discr E).natAbs * l.M').primeFactors

theorem badPrimes_prime (p : ℕ) (hp : p ∈ badPrimes H l) : p.Prime := Nat.prime_of_mem_primeFactors hp

theorem mem_badPrimes {p : ℕ} :
    p ∈ badPrimes H l ↔ p.Prime ∧ (p = 2 ∨ p = H.d ∨ p ∣ (discr E).natAbs ∨ p ∣ l.M ∨ p ∣ l.A) := by
  have hM : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  have hD : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
  have hne : 2 * H.d * (discr E).natAbs * l.M' ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero H.d_prime.ne_zero) hD) hM
  rw [badPrimes, Nat.mem_primeFactors_of_ne_zero hne]
  refine and_congr_right fun hp => ?_
  simp only [hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp Nat.prime_two, Nat.prime_dvd_prime_iff_eq hp H.d_prime,
    Level.M', hp.dvd_lcm, or_assoc]

theorem UnramPts.of_index_one {B : Finset ℕ}
    (h : ∀ (Z : Comp Xo c) (w : HeightOneSpectrum (𝓞 c.F)), (∀ p ∈ B, ((p : ℕ) : 𝓞 c.F) ∉ w.asIdeal) →
      ∃ (T : CDVR) (ι : c.F →+* T.Fr) (y : IntFr Xo c T ι), OverLa w T.V ι 1 ∧ algOn Z T ι y) :
    UnramPts Xo c B := fun Z w hw => by
  obtain ⟨T, ι, y, ho, hy⟩ := h Z w hw
  refine ⟨_, ⟨PtV.mk w ho y hy () trivial, rfl⟩, fun f => ?_⟩
  show nval T.V 1 (evI y f) = ⊤ ∨ ∃ n : ℤ, nval T.V 1 (evI y f) = _
  by_cases h0 : evI y f = 0
  · rw [h0, nval_zero]; exact Or.inl rfl
  · exact Or.inr ⟨vV T.V (evI y f), by rw [nval_of_ne h0]; simp⟩

end GlobalTheory.FlatTw
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FactorDepth

namespace GlobalTheory.RefSum

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) {c : Coeff l} {p : ℕ}

def PolyBetween (la : PointsOfFlagModel.abelian₂ p c) {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) (A B : ℝ) : Prop :=
  letI := H.starRing
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ y : IntFr Xo c T io, y.IsAlg →
    ∀ (Ch : IntegralChartA3 Xo c T io y) (k : ℕ),
      (A : EReal) ≤ nuLocOf Ch (vV T.V (p : T.Fr)).toNat k (MvPolynomial.map io P) ∧
        nuLocOf Ch (vV T.V (p : T.Fr)).toNat k (MvPolynomial.map io P) ≤ (B : EReal)


variable (l) in
def HalfSplit (g g' : ℕ) (π π' : 𝓞 E) : Prop :=
  g.Prime ∧ g'.Prime ∧ g ≠ g' ∧ l.M = g' * g ∧ π * H.bar π = (g : 𝓞 E) ∧ π' * H.bar π' = (g' : 𝓞 E) ∧
    l.Mb = Ideal.span {π * π'} ∧ GlobalTheory.PtTie.SplitsIn E g ∧ GlobalTheory.PtTie.SplitsIn E g'

theorem HalfSplit.symm {g g' : ℕ} {π π' : 𝓞 E} (h : HalfSplit l g g' π π') : HalfSplit l g' g π' π := by
  obtain ⟨a, b, c, d, e, f, i, j, k⟩ := h
  exact ⟨b, a, c.symm, d.trans (mul_comm _ _), f, e, by rw [i, mul_comm], k, j⟩

end Free

def JetNum (D : D7) (dF : ℕ) (cst : ℝ) : Prop :=
  ∀ k, 4 * dF + 4 ≤ D.host.g k ∧ (dF : ℝ) * (2 * Real.sqrt (2 * D.R.f * D.R.m)) < D.host.g k ∧
    GlobalTheory.PtTie.rr0 D * (2 * D.R.f * D.R.m : ℝ) ^ 3 * ((D.R.r : ℝ) * (2 * D.R.f * D.R.m) / 4 + 2 * (dF : ℝ) ^ 2) / D.host.g k ≤ cst

end GlobalTheory.RefSum

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLevFnPow
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain TensorProduct Formalism.L2.DIV

namespace GlobalTheory.AdeleEv

variable {l : ℕ} [Fact l.Prime]

theorem norm_int_le {E : Type} [Field E] [NumberField E] (τ : E →+* PadicAlgCl l) (x : 𝓞 E) : ‖τ x‖ ≤ 1 := by
  obtain ⟨v, hv⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding E l τ
  by_contra h
  have h0 : (x : E) ≠ 0 := by
    rintro h0
    rw [h0, map_zero, norm_zero] at h
    exact h zero_le_one
  have h1 : ‖τ (x : E)⁻¹‖ < 1 := by
    rw [map_inv₀, norm_inv]
    exact inv_lt_one_of_one_lt₀ (not_le.1 h)
  have h2 := (hv _).2 h1
  rw [map_inv₀] at h2
  have h3 : v.valuation E (x : E) ≤ 1 := v.valuation_le_one x
  have h4 : v.valuation E (x : E) ≠ 0 := (map_ne_zero _).2 h0
  exact absurd ((inv_lt_one₀ (zero_lt_iff.2 h4)).1 h2) (not_lt.2 h3)

end GlobalTheory.AdeleEv

end
end

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpFrame

open Formalism.CohomologicalDescent.DepthNonnegative

def Embeds (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam mu : ι → ℕ → ℕ) (ϖ : O) (Gm : Type) [AddCommGroup Gm]
    [Module (alg O N lam) Gm] : Prop :=
  ∃ ψ : Gm →+ (NablaT O N mu ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N mu))), Function.Injective ψ ∧
    (∀ (c : O) z, ψ (algebraMap O (alg O N lam) c • z) = c • ψ z) ∧
    (∀ g z y, ψ z = Submodule.Quotient.mk y → ψ (grpA O N lam g • z) = Submodule.Quotient.mk (grp O N mu g y)) ∧
    ∀ τ w (a : alg O N lam) (a' : Module.End O (NablaT O N mu)), IsProj O N lam τ w a → IsProj O N mu τ w a' →
      ∀ z y, ψ z = Submodule.Quotient.mk y → ψ (a • z) = Submodule.Quotient.mk (a' y)

def SubQ (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O) (Gm : Type) [AddCommGroup Gm]
    [Module (alg O N lam) Gm] : Prop :=
  ∃ (U : Submodule (alg O N lam) (NablaT O N lam)) (π : U →ₗ[alg O N lam] Gm), Function.Surjective π ∧
    ∀ (x : U) (y : NablaT O N lam), (x : NablaT O N lam) = ϖ • y → π x = 0

section Tests

variable (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O)




end Tests

theorem exists_intHom {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {J : Type} [Group J]
    (x : J →* GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) {β : GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))} (hβ : β = 1)
    (h : ∀ κ, x κ ∈ Formalism.L2.DIV.St β) :
    ∃ y : J →* GL (Fin n) (Formalism.L2.Herm.intAf F E), ∀ κ a b, ((y κ).val a b : TensorProduct F E (Formalism.L2.Herm.Af F)) = (x κ).val a b := by
  subst hβ
  choose y hy using h
  have h2 : ∀ κ, Formalism.L2.DIV.intGL F E n (y κ) = x κ := fun κ => by simpa [Formalism.L2.DIV.frGL] using hy κ
  refine ⟨MonoidHom.mk' y fun κ κ' => Formalism.L2.DIV.intGL_injective (by rw [map_mul, h2, h2, h2, map_mul]), fun κ a b => ?_⟩
  exact congrArg (fun g : GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F)) => g.val a b) (h2 κ)

end GlobalTheory.ExpFrame

end

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts HidaSetting WInputsLink h0)
open GlobalTheory.ExpFrame

namespace GlobalTheory.ExpTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev presJ {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {K : Type} [Field K]
    [NumberField K] [StarRing K] {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
    (_ : Bridge.ClassPres ι S σ ρ J χ) : Subgroup G := J

abbrev presChi {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {K : Type} [Field K]
    [NumberField K] [StarRing K] {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres ι S σ ρ J χ) : presJ P →* ℂˣ := χ

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

def hkA (j : Fin D.R.m) (t : p.P.T) (i : (blk p j t).Pl × ℕ) : Finset (Bridge.Gf (Vc D j)) := (p.R.B.L j t).hecke.hA i

def levJ (j : Fin D.R.m) (t : p.P.T) : Subgroup (Bridge.Gf (Vc D j)) := presJ (K := D.what₂.LL) (p.R.B.L j t).pres

def levChi (j : Fin D.R.m) (t : p.P.T) : levJ p j t →* ℂˣ := presChi (p.R.B.L j t).pres

def plOf (j : Fin D.R.m) (t : p.P.T) (P : (blk p j t).Pl) : HeightOneSpectrum (𝓞 D.host.E) := p.R.pl ((blk p j t).pl P)

def matOf (j : Fin D.R.m) (g : Bridge.Gf (Vc D j)) :
    Matrix (Fin (Vc D j).rank) (Fin (Vc D j).rank) ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E) := g.1.val


set_option maxHeartbeats 1600000 in
structure Tied (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ} (F : Frame l D.what₂.Tau N) (e0 : D.what₂.LL →+* PadicAlgCl l)
    (ix : F.I → (blk p j t).Pl × ℕ) (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl l)) where

  rk : Fin N ≃o Fin (Vc D j).rank

  e : F.G ≃* Bridge.Gf (Vc D j)

  io : PadicAlgCl l ≃+* ℂ

  ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l)

  bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl l)

  sh : D.what₂.Tau → ℤ

  liftFrame_embedding_base : ∀ x, io (e0 x) = D.what₂.embLL x

  half : IsHalf inc

  lab : ∀ τ, inc τ = e0.comp (Links.labLL D τ) ∨ inc τ = cj (e0.comp (Links.labLL D τ))

  ev_rat : ∀ τ x, ev τ (1 ⊗ₜ[D.host.F] x) = inc τ x

  ev_int : ∀ τ (a : FiniteAdeleRing (𝓞 D.host.F) D.host.F), (∀ v, a v ∈ v.adicCompletionIntegers D.host.F) →
    ‖ev τ (a ⊗ₜ[D.host.F] 1)‖ ≤ 1

  rat : ∀ g, g ∈ F.Γ ↔ e g ∈ (Bridge.ratF (Vc D j)).range

  lev : ∀ g, g ∈ F.K ↔ e g ∈ levJ p j t

  kap : ∀ (κ : F.K) τ, (Matrix.GeneralLinearGroup.map F.emb (F.kap κ τ)).val =
    ((bs τ)⁻¹).val * ((matOf j (e κ)).map (ev τ)).submatrix rk rk * (bs τ).val

  chi : ∀ (κ : F.K) (h : e κ ∈ levJ p j t),
    io (F.emb (F.chi κ) * ∏ τ, F.emb (F.kap κ τ).val.det ^ sh τ) * ((levChi p j t ⟨e κ, h⟩ : ℂˣ) : ℂ) = 1

  ix_inj : Function.Injective ix

  ix_range : ∀ i, i ∈ Set.range ix ↔ 1 ≤ i.2 ∧ i.2 ≤ N ∧ ((l : ℕ) : 𝓞 D.host.E) ∉ (plOf p j t i.1).asIdeal

  tr : ∀ i g, g ∈ F.tr i ↔ e g ∈ hkA p j t (ix i)

  cst : ∀ i, F.cst i = 1

theorem isHalf_lab {l : ℕ} [Fact l.Prime] (e0 : D.what₂.LL →+* PadicAlgCl l) : IsHalf fun τ => e0.comp (Links.labLL D τ) := by
  let s : D.R.GG → (D.host.E →+* PadicAlgCl l) := fun g =>
    (e0.comp D.embE).comp (D.host.sigmaOf g : D.host.E →+* D.host.E)
  have hinj : Function.Injective s := fun g g' h =>
    (D.host.gal).symm.injective
      (AlgEquiv.ext fun x => (e0.comp D.embE).injective (RingHom.congr_fun h x))
  have hsurj : Function.Surjective s := by
    haveI := D.host.hostE_isGalois
    haveI : Finite (D.R.GG) := Finite.of_equiv _ (D.host.gal).toEquiv
    refine ((Nat.bijective_iff_injective_and_card s).2 ⟨hinj, ?_⟩).2
    rw [← Nat.card_congr (D.host.gal).toEquiv, IsGalois.card_aut_eq_finrank,
      Nat.card_eq_fintype_card, NumberField.Embeddings.card]
  have hcj : ∀ g, GlobalTheory.ExpFrame.cj (s g) = s (g * D.R.cc) := fun g => by
    ext x
    have h1 : IsCMField.complexConj D.host.E x = D.host.sigmaOf (D.R.cc) x := by
      apply D.host.φ₀.injective
      rw [IsCMField.complexEmbedding_complexConj]
      exact (D.host.conjE_apply D.host.φ₀ x).symm
    show (e0.comp D.embE) (D.host.sigmaOf g (IsCMField.complexConj D.host.E x)) = (e0.comp D.embE) (D.host.sigmaOf (g * _) x)
    rw [h1, Formalism.BasicNotions.Host.sigmaOf, Formalism.BasicNotions.Host.sigmaOf, Formalism.BasicNotions.Host.sigmaOf, map_mul]
    rfl
  refine ⟨fun τ τ' h => D.eTau.injective (Subtype.ext (hinj h)), fun τ τ' h => ?_, fun i => ?_⟩
  · have h1 := hinj ((hcj (D.eTau τ).1).symm.trans h)
    have hi := (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau τ).2
    have hj := (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau τ').2
    have h2 : (D.eTau τ').1.1.2 = (D.eTau τ).1.1.2 * (-1) := by rw [← h1]; rfl
    rw [hi, hj] at h2
    exact absurd h2 (by decide)
  · obtain ⟨g, rfl⟩ := hsurj i
    rcases Int.units_eq_one_or g.1.2 with hg | hg
    · refine ⟨D.eTau.symm ⟨g, (Formalism.HC.Frame.mem_Psi_iff _).2 hg⟩, Or.inl ?_⟩
      show s g = s (D.eTau (D.eTau.symm _)).1
      rw [Equiv.apply_symm_apply]
    · have hm : g * (D.R.cc)⁻¹ ∈ D.R.Psi := by
        refine (Formalism.HC.Frame.mem_Psi_iff _).2 ?_
        show g.1.2 * (-1)⁻¹ = 1
        rw [hg]; decide
      refine ⟨D.eTau.symm ⟨_, hm⟩, Or.inr ?_⟩
      show s g = GlobalTheory.ExpFrame.cj (s (D.eTau (D.eTau.symm _)).1)
      rw [Equiv.apply_symm_apply, hcj, inv_mul_cancel_right]

theorem levJ_eq (j : Fin D.R.m) (t : p.P.T) : levJ p j t = (levEnv (Vc D j) (p.R.βV j) (p.R.datVt j t)).J := rfl



omit p in
theorem mem_St_of_levEnv {V : Formalism.BasicNotions.TH.HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {Lv : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}
    {g : Bridge.Gf V} (h : g ∈ (levEnv V β Lv).J) : Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) g.1 ∈ St β := parLev_St h.1


omit p in
theorem exists_intHom_of {V : Formalism.BasicNotions.TH.HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} (hβ : β = 1) (J : Subgroup (Bridge.Gf V))
    (h : ∀ g ∈ J, Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) g.1 ∈ St β) :
    ∃ y : J →* GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E),
      ∀ κ a b, ((y κ).val a b : Formalism.IndefR.Lev.EAf D) = Formalism.IndefR.Lev.swapAE D (κ.1.1.val a b) :=
  exists_intHom ((Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D)).comp ((Bridge.Gf V).subtype.comp J.subtype)) hβ fun κ => h κ.1 κ.2

theorem exists_levInt (j : Fin D.R.m) (t : p.P.T) :
    ∃ y : levJ p j t →* GL (Fin (Vc D j).rank) (Formalism.L2.Herm.intAf D.host.F D.host.E),
      ∀ κ a b, ((y κ).val a b : Formalism.IndefR.Lev.EAf D) = Formalism.IndefR.Lev.swapAE D (matOf j κ.1 a b) :=
  exists_intHom_of (p.betaStd.1 j) (levJ p j t) fun _ h => mem_St_of_levEnv ((levJ_eq p j t).le h)



open Classical in
def FrameAt (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime], ∃ (F : Frame (Formalism.EigenvalueLevelCeiling.plc w) D.what₂.Tau P.Nr) (R : Reads F W.lam (blk p j (p.R.mu w)) w)
    (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))), F.Ok ∧ Nonempty (Tied p j (p.R.mu w) F R.e0 R.ix inc)


open Classical in
def GalAt (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (F : Frame (Formalism.EigenvalueLevelCeiling.plc w) D.what₂.Tau P.Nr) (R : Reads F W.lam (blk p j (p.R.mu w)) w)
    (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))), F.Ok → Tied p j (p.R.mu w) F R.e0 R.ix inc →
    GalSide (AlgebraicClosure D.host.E) inc P W F R.HasBlock

def SmallAt (j : Fin D.R.m) (P : Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  (Formalism.EigenvalueLevelCeiling.plc w).Prime ∧ P.Nr + 1 < Formalism.EigenvalueLevelCeiling.plc w ∧ ¬ ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : ℤ) ∣ NumberField.discr D.host.E ∧
    (∀ i, subZ p j (p.R.mu w) ≤ (subZ p j (p.R.mu w)).comap ((blk p j (p.R.mu w)).op i)) ∧
    subZ p j (p.R.mu w) ≤ (blk p j (p.R.mu w)).ZH

end GlobalTheory.ExpTie

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
section -- merged from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FactorDepthInertBounds
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds

open NumberField IsDedekindDomain
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def boundAll (p i k : ℕ) : ℝ := (i : ℝ) * k / ((p : ℝ) - 1)

def boundInert (p j' i k : ℕ) : ℝ := 2 * (i : ℝ) * k / ((p : ℝ) * ((p : ℝ) - 1)) + 2 * (j' : ℝ) * k / ((p : ℝ) - 1)

def upperInert (p N j' k : ℕ) : ℝ :=
  (k : ℝ) * ((j' : ℝ) / ((p : ℝ) - 1) + ((N : ℝ) - 2 * j') * p / ((p : ℝ) ^ 2 - 1))

def boundFine (p N j' i k : ℕ) : ℝ :=
  (k : ℝ) * ((N : ℝ) - 2 * j' - i) * p / ((p : ℝ) ^ 2 - 1) +
    (k : ℝ) * j' * (3 + 1 / 2 * Real.logb p k) / ((p : ℝ) - 1) + (i : ℝ) ^ 2 * (Real.logb p k + 1)

variable {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
  {p : ℕ} [Fact p.Prime]

def AtEvery (la : PointsOfFlagModel.abelian₂ p c) (Q : ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → Prop) : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ y : IntFr Xo c T io, Q T io y


def OscLe (la : PointsOfFlagModel.abelian₂ p c) (f : Lt1 Dw) (k : ℕ) (b : ℝ) : Prop :=
  AtEvery Xo c la fun _ _ y => AtEvery Xo c la fun _ _ η => nuFac p y f k ≤ nuFac p η f k + (b : EReal)

end GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BigBlockCharacters
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters

open NumberField IsDedekindDomain
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth

section Group

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {i d : ℕ}

def pairDet (l w : Fin i → Fin d → C) : C := (Matrix.of fun a b : Fin i => ∑ e, l b e * w a e).det

def IsFrameOf (v : AddValuation C (WithTop ℝ)) (u w : Fin i → Fin d → C) : Prop :=
  IsSatFrame v w ∧ ∀ a, w a ∈ Submodule.span C (Set.range u)

def HasChars (G : LogFGL v d) (u : Fin i → Fin d → C) (r : EReal) : Prop :=
  ∃ l : Fin i → Fin d → C, (∀ b, IsCharLog G (l b)) ∧
    ∀ w : Fin i → Fin d → C, IsFrameOf v u w → toE (v (pairDet l w)) ≤ r

theorem isFrameOf_self {u : Fin i → Fin d → C} (hu : IsSatFrame v u) : IsFrameOf v u u :=
  ⟨hu, fun a => Submodule.subset_span ⟨a, rfl⟩⟩

theorem v_pairDet_eq {u w : Fin i → Fin d → C} (hu : IsSatFrame v u) (hw : IsFrameOf v u w)
    (l : Fin i → Fin d → C) : v (pairDet l w) = v (pairDet l u) := by
  choose M hM using fun a => (Submodule.mem_span_range_iff_exists_fun C).1 (hw.2 a)
  have hwe : ∀ a e, w a e = ∑ k, M a k * u k e := fun a e => by
    rw [← hM a]; simp [Finset.sum_apply]
  have hmin : ∀ r : Fin i → Fin d, (Matrix.of fun a b => w a (r b)).det =
      (Matrix.of M).det * (Matrix.of fun a b => u a (r b)).det := fun r => by
    rw [← Matrix.det_mul]; congr 1; ext a b; simp [Matrix.mul_apply, hwe]
  have hint : ∀ (x : Fin i → Fin d → C), (∀ a e, IsIntV v (x a e)) → ∀ r : Fin i → Fin d,
      0 ≤ v (Matrix.of fun a b => x a (r b)).det := fun x hx r => by
    rw [Matrix.det_apply']
    refine AddValuation.map_le_sum v fun σ _ => ?_
    rw [AddValuation.map_mul]
    refine add_nonneg ?_ ?_
    · rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    · refine Finset.prod_induction _ (fun z => 0 ≤ v z) (fun a b ha hb => ?_) (by simp) fun k _ => hx _ _
      rw [AddValuation.map_mul]; exact add_nonneg ha hb
  obtain ⟨r, hr⟩ := hu.2
  obtain ⟨r', hr'⟩ := hw.1.2
  have h1 : 0 ≤ v (Matrix.of M).det := by
    have := hint w hw.1.1 r
    rwa [hmin, AddValuation.map_mul, hr, add_zero] at this
  have h2 : v (Matrix.of M).det ≤ 0 := by
    rw [hmin, AddValuation.map_mul] at hr'
    exact hr' ▸ le_add_of_nonneg_right (hint u hu.1 r')
  have h3 : pairDet l w = (Matrix.of M).det * pairDet l u := by
    unfold pairDet
    rw [← Matrix.det_mul]; congr 1; ext a b
    simp only [Matrix.mul_apply, Matrix.of_apply, hwe, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun e _ => by ring
  rw [h3, AddValuation.map_mul, le_antisymm h2 h1, zero_add]

theorem hasChars_iff {G : LogFGL v d} {u : Fin i → Fin d → C} (hu : IsSatFrame v u) (r : EReal) :
    HasChars G u r ↔ ∃ l : Fin i → Fin d → C, (∀ b, IsCharLog G (l b)) ∧ toE (v (pairDet l u)) ≤ r :=
  exists_congr fun l => and_congr_right fun _ =>
    ⟨fun h => h u (isFrameOf_self hu), fun h w hw => by rwa [v_pairDet_eq hu hw]⟩

end Group

section Prime

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def SplitInK (H : Host E) (p : ℕ) : Prop := (H.d : ZMod p) ≠ 0 ∧ IsSquare (-(H.d : ZMod p))

def InertInK (H : Host E) (p : ℕ) : Prop := ¬ IsSquare (-(H.d : ZMod p))

variable {H : Host E} {l : Level H} (c : Coeff l) {T : CDVR} (io : c.F →+* T.Fr) {p : ℕ} [Fact p.Prime]
  (X : ValExt T p)

def embX (τ : E →+* ℂ) : 𝓞 E →+* X.C := X.ιF.comp (io.comp (embK c τ))

end Prime

end GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SplitQuadraticMinSums
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification

open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

variable {H : Host E} {Dw : Datum H}

def IsBig (k : ℕ) (f : Lt1 Dw) : Prop := InPsi H f.1 ∧ k ≤ rk f + 1

def IsSpread (k : ℕ) (f : Lt1 Dw) : Prop := InPsi H f.1 ∧ rk f + 2 ≤ k

def IsSmall (f : Lt1 Dw) : Prop := ¬ InPsi H f.1

theorem not_isBig_iff (k : ℕ) (f : Lt1 Dw) : ¬ IsBig k f ↔ IsSmall f ∨ IsSpread k f := by
  unfold IsBig IsSmall IsSpread
  by_cases h : InPsi H f.1
  · simp only [h, true_and, not_true, false_or]; omega
  · simp [h]


open Classical in
def sumBig (k : ℕ) (cx : Lt1 Dw → ℕ) : ℕ := ∑ f ∈ Finset.univ.filter (IsBig k), cx f


open Classical in
def sumSmallSpread (k : ℕ) (cx : Lt1 Dw → ℕ) : ℕ :=
  ∑ f ∈ Finset.univ.filter (fun f => IsSmall f ∨ IsSpread k f), rk f * cx f

section Place

variable {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] {p : ℕ} [Fact p.Prime]

end Place

end GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification
end
end

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FactorDepth GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig sumSmallSpread)

namespace GlobalTheory.RefSum

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)


open Classical in
def ExpBd (k : ℕ) (cx : Lt1 Dw → ℕ) (Mb Sm : ℝ) (M : ℕ) : Prop :=
  0 ≤ Mb ∧ (∀ τ : E →+* ℂ, ((∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f ∧ f.1 = τ), cx f : ℕ) : ℝ) ≤ Mb) ∧
    (sumSmallSpread k cx : ℝ) ≤ Sm ∧ ∀ f, cx f ≤ M

def Shape (F k m : ℕ) : Prop :=
  Dw.p + Dw.q + 1 = k + m ∧ Dw.q ≤ m ∧ m ≤ k ∧ 1 ≤ m ∧ 2 ≤ k ∧ Module.finrank ℚ E = 2 * F

def WtBd (k n : ℕ) (u : GlobalTheory.AllWt.Weight Dw) (B : ℕ) (Sg : ℝ) : Prop :=
  (∀ τ, Antitone (u τ)) ∧ (∀ τ (i : Fin (Dw.p + Dw.q)), (i : ℕ) + 2 = k → u τ i = 0) ∧
    (∀ τ (i j : Fin (Dw.p + Dw.q)), (i : ℕ) + 1 = Dw.p → (j : ℕ) = Dw.p → (n : ℤ) + 1 ≤ u τ i - u τ j) ∧
    (∀ τ i, |u τ i| ≤ B) ∧
    ∀ τ, (∑ i ∈ Finset.univ.filter (fun i : Fin (Dw.p + Dw.q) => (i : ℕ) + 2 < k), (u τ i : ℝ)) ≤ Sg

end Free

def eSmall (F N m : ℕ) (Mb Sm : ℝ) (M p : ℕ) : ℝ :=
  (F * m * Mb * (4 + Real.logb p M / 2) + Sm) / ((p : ℝ) - 1) + F * (m + 1) * (N : ℝ) ^ 2 * (Real.logb p M + 1)


open Classical in
def eOf (F N k m : ℕ) (Mb Sm : ℝ) (vd : ℕ → ℝ) (M : ℕ) (S R : Finset ℕ) (p : ℕ) : ℝ :=
  if M < p then 0 else if p ∈ S then F * m * (1 + vd p / 2) * Mb + Sm
  else if p ∈ R then (F * N * Mb + Sm) / ((p : ℝ) - 1)
  else if m * p < k then eSmall F N m Mb Sm M p + 1 else (6 * F * m * Mb + Sm) / ((p : ℝ) - 1) + 1

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

def WtAt (PP C : ℝ) (u1 : GlobalTheory.AllWt.Weight (dat p i)) : Prop :=
  Shape (dat p i) D.R.f D.R.k D.R.m ∧ D.R.k ≤ (dat p i).p + 1 ∧ ∃ (B : ℕ) (Sg : ℝ), WtBd (dat p i) D.R.k (nCol (dat p i)) u1 B Sg ∧
    lenT p i PP * ((B : ℝ) + 1) ≤ C * L.sc.b ∧ lenT p i PP * Sg ≤ C * L.sc.b ∧ 1 ≤ lenT p i PP

def NumAt (PP C : ℝ) : Prop :=
  1 ≤ L.sc.L ∧ 1 ≤ L.sc.b ∧ Real.log L.sc.b ≤ C * L.sc.L ∧ 1 ≤ Real.log (Real.log L.sc.x) ∧
    D.R.f * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) ≤ C * unitE p ∧
    Real.log (Real.log D.R.k) ≤ C * Real.log (Real.log L.sc.x) ∧ Real.log D.R.r ≤ C * L.sc.L ∧ Formalism.MainNotions.DIV.Cons.vd2 D ≤ C * L.sc.L ∧
    lenT p i PP * (D.R.r : ℝ) ^ 3 ≤ C * L.sc.b ∧
    ∀ q ∈ ({D.host.q, D.host.d} : Finset ℕ), D.R.r * Real.log q / ((q : ℝ) - 1) ≤ C * D.R.m * L.sc.L

end Point

def NumPt : Prop := Lifts fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → NumAt p i PP C

end GlobalTheory.RefSum

end
end
