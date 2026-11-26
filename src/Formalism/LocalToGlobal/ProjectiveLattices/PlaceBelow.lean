module

public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral

@[expose] public section

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open MvPowerSeries NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Copies

variable {R : Type} [CommRing R] {d : ℕ}

def DofN (F : Fin d → PS R 2 d) {n : ℕ} (b : Fin n) (u : Fin d → R) (f : PS R n d) : PS R n d :=
  ∑ j : Fin d, (∑ i : Fin d, C (u i) * ev (n := n) ![pt R d b, 0] (pderiv (R := R) ((1 : Fin 2), i) (F j))) *
    pderiv (R := R) (b, j) f

def DmonN (F : Fin d → PS R 2 d) {n : ℕ} {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → R)
    (m : ι →₀ ℕ) (f : PS R n d) : PS R n d :=
  (Finset.univ : Finset ι).toList.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) f

def DpolyN (F : Fin d → PS R 2 d) {n : ℕ} {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → R)
    (P : MvPolynomial ι R) (f : PS R n d) : PS R n d :=
  ∑ m ∈ P.support, C (P.coeff m) * DmonN F cp u m f

def nabValN {O : Type} [CommRing O] [StarRing O] (B : FB R d O) (k : Type) [CommRing k] [Algebra ℚ k]
    [Algebra R k] (h : PS k 2 d) (w0 : O) (m : ℕ) {n : ℕ} (f : PS k n d) {ι : Type} [Fintype ι]
    (cp : ι → Fin n) (u : ι → Fin d → k) (P : MvPolynomial ι k) : k :=
  constantCoeff (DpolyN (B.FK k) cp u P
    (f * FB.expS k ((m : k) • ∑ b : Fin n, ev (n := n) ![pt k d b] (B.hL k h w0))))

end Copies

section Loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

variable [StarRing (𝓞 E)]

abbrev IntChart (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) := IntegralChartA3 Xo c T io y

def FFV (T : CDVR) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (MvPolynomial (LtN Dw n) T.Fr) :=
  HaO Dw.mult n T.Fr (algebraMap T.V T.Fr).range ComplexEmbedding.conjugate (InPsi H) fun τ i => a (τ, i)

def nuLocC {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (C : IntChart T io y) (e k : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : EReal :=
  letI := io.toAlgebra
  ⨅ (P : MvPolynomial (LtN Dw n) T.Fr) (_ : P ∈ FFV (Dw := Dw) T a n) (f : PS T.Fr n C.ch.d) (_ : IsIntPS T f),
    letI := io.toAlgebra
    nval T.V e (nabValN C.ch.B T.Fr C.ch.h H.w0 k f (fun ℓ => ℓ.2.2) (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) P)

def nuLoc {T : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io) (e k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    EReal :=
  ⨅ C : IntChart T io y, nuLocC C e k a n

variable (Xo c)

def nuSup (la : HeightOneSpectrum (𝓞 c.F)) (k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : EReal :=
  ⨆ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (_ : OverLa la T.V io e) (y : IntFr Xo c T io) (_ : y.IsAlg),
    nuLoc y e k a n

def nuW (la : HeightOneSpectrum (𝓞 c.F)) (k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : EReal :=
  max 0 (nuSup Xo c la k a n)

end Loc

section Num

structure DepPage where
  T : ℕ
  g1 : ℕ
  g2 : ℕ
  q1 : ℕ
  dd : ℕ
  sm : Finset ℕ
  f : ℕ
  r : ℕ
  vd : ℕ → ℝ

namespace DepPage

variable (Q : DepPage)

def n' : ℕ := 8 * Q.f * Q.r + 4

def q : ℕ := Q.g1 * Q.g2

def IsRam (p : ℕ) : Prop := p ∈ Q.sm ∨ p = Q.q1 ∨ p = Q.dd

def IsBad (p : ℕ) : Prop := Q.IsRam p ∨ p = Q.g1 ∨ p = Q.g2


open Classical in
def cP (DF : ℕ) (p : ℕ) : ℕ := if Q.IsRam p then ⌈Q.vd p * (DF : ℝ)⌉.toNat else 0


open Classical in
def nuN (DFL : ℕ) (nu : ℝ) (p : ℕ) : ℝ :=
  if p = Q.g1 then (DFL : ℝ) / ((Q.g1 : ℝ) - 1)
  else if p = Q.g2 then (DFL : ℝ) / ((Q.g2 : ℝ) - 1)
  else nu + (Q.cP DFL p : ℝ)


open Classical in
def eLam (eL : ℕ) (nuStar : ℝ) (p : ℕ) : ℕ :=
  ⌈(eL : ℝ) * (Q.T : ℝ) * (nuStar + if Q.IsBad p then 1 else 0)⌉.toNat

def Z1 (DFL DFF : ℕ) : ℕ :=
  (∏ p ∈ Q.sm.filter Nat.Prime, p ^ (Q.T * Q.cP DFL p + Q.cP DFF p)) * Q.q1 ^ (Q.T * Q.cP DFL Q.q1 + Q.cP DFF Q.q1) *
    Q.dd ^ (Q.T * Q.cP DFL Q.dd + Q.cP DFF Q.dd)

end DepPage

def nnOf {K : Type} [CommRing K] (pi pibar : Fin 2 → K) (Dp Dm : ℕ) : K :=
  ∏ i : Fin 2, pibar i ^ Dp * pi i ^ Dm

def sigOf {K : Type} [CommRing K] (Q : DepPage) (pi pibar : Fin 2 → K) (Dp Dm DFL DFF : ℕ) : K :=
  nnOf pi pibar Dp Dm * ((Q.q : K) ^ (Q.f * Q.r * Q.n') * (Q.Z1 DFL DFF : K))

end Num

section Places

def resCharOf {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) : ℕ :=
  ringChar (𝓞 K ⧸ la.asIdeal)

def ramOverZ {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) : ℕ :=
  Ideal.ramificationIdx' (Ideal.span {((resCharOf la : ℕ) : ℤ)}) la.asIdeal

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L]
  [Algebra (𝓞 K) (𝓞 L)] [Algebra.IsIntegral (𝓞 K) (𝓞 L)]

def placeBelow (v : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 K) where
  asIdeal := v.asIdeal.under (𝓞 K)
  isPrime := inferInstance
  ne_bot := Ideal.under_ne_bot (𝓞 K) v.ne_bot

def ramOver (v : HeightOneSpectrum (𝓞 L)) : ℕ :=
  Ideal.ramificationIdx' (placeBelow (K := K) v).asIdeal v.asIdeal

def expE (Q : DepPage) (nuStar : HeightOneSpectrum (𝓞 K) → ℝ) (v : HeightOneSpectrum (𝓞 L)) : ℕ :=
  ramOver (K := K) v * Q.eLam (ramOverZ (placeBelow (K := K) v)) (nuStar (placeBelow v))
    (resCharOf (placeBelow (K := K) v))

end Places

private lemma le_ceil_toNat_lemma (a x b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * x ≤ ((⌈a * (x + b)⌉.toNat : ℕ) : ℝ) := by
  have h1 : a * x ≤ a * (x + b) := mul_le_mul_of_nonneg_left (by linarith) ha
  have h2 : a * (x + b) ≤ (⌈a * (x + b)⌉ : ℝ) := Int.le_ceil _
  have h3 : ((⌈a * (x + b)⌉ : ℤ) : ℝ) ≤ ((⌈a * (x + b)⌉.toNat : ℕ) : ℝ) := by
    exact_mod_cast Int.self_le_toNat _
  linarith

theorem DepPage.le_eLam (Q : DepPage) (eL : ℕ) (nu : ℝ) (p : ℕ) :
    (eL : ℝ) * (Q.T : ℝ) * nu ≤ (Q.eLam eL nu p : ℝ) := by
  unfold DepPage.eLam
  refine le_ceil_toNat_lemma _ _ _ (by positivity) ?_
  split_ifs <;> norm_num

section Inst

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

structure DepData (E : Type) [Field E] [NumberField E] where
  Q : DepPage
  aL : ℕ → (E →+* ℂ) × ℕ → ℕ
  aF : ℕ → (E →+* ℂ) × ℕ → ℕ
  nW : ℕ → ℕ
  Dp : ℕ → ℕ
  Dm : ℕ → ℕ
  pi : Fin 2 → 𝓞 E

variable {Xo c}

def nuWAt (D : DepData E) (la : HeightOneSpectrum (𝓞 c.F)) (j : ℕ) : EReal :=
  nuW Xo c la l.M (D.aL j) (D.nW j)

def nuStarAt (D : DepData E) (la : HeightOneSpectrum (𝓞 c.F)) (j : ℕ) : ℝ :=
  D.Q.nuN (DF Dw (D.aL j)) ((nuWAt (Xo := Xo) D la j).toReal / (ramOverZ la : ℝ)) (resCharOf la)

variable {LL : Type} [Field LL] [NumberField LL] [Algebra (𝓞 c.F) (𝓞 LL)] [Algebra.IsIntegral (𝓞 c.F) (𝓞 LL)]

def EAt (D : DepData E) (v : HeightOneSpectrum (𝓞 LL)) (j : ℕ) : ℕ :=
  expE (K := c.F) D.Q (fun la => nuStarAt (Xo := Xo) D la j) v

variable [Algebra (𝓞 E) LL]

def nnKAt (D : DepData E) (j : ℕ) : LL :=
  nnOf (fun i => algebraMap (𝓞 E) LL (D.pi i)) (fun i => algebraMap (𝓞 E) LL (H.bar (D.pi i))) (D.Dp j) (D.Dm j)

def sigAt (D : DepData E) (j : ℕ) : LL :=
  sigOf D.Q (fun i => algebraMap (𝓞 E) LL (D.pi i)) (fun i => algebraMap (𝓞 E) LL (H.bar (D.pi i))) (D.Dp j) (D.Dm j)
    (DF Dw (D.aL j)) (DF Dw (D.aF j))

end Inst

section Props

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

def IntChartEx : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → Nonempty (IntChart T io y)

def ChartIndep : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C C' : IntChart T io y) (e k : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), nuLocC C e k a n = nuLocC C' e k a n

variable {Xo c}

def PiSplit (D : DepData E) : Prop :=
  D.pi 0 * H.bar (D.pi 0) = (D.Q.g1 : 𝓞 E) ∧ D.pi 1 * H.bar (D.pi 1) = (D.Q.g2 : 𝓞 E)

def LevelQ (D : DepData E) : Prop := (l.M : ℕ) = D.Q.g1 * D.Q.g2

def TPos (D : DepData E) : Prop := 1 ≤ D.Q.T

end Props

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.NrmContPf
noncomputable section

namespace Formalism.L2.Pj

open MeasureTheory Topology NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]

def STLoc (h : GenFrEx Xo c) (Dd N : ℕ) (uL : WtR E) (wR : Fin (N + 1) → Rul Xo c)
    (jc : Comp Xo c → Fin (N + 1)) : Prop :=
  FnTrdeg Xo c Dd → FnFG Xo c → (∀ Z, evC h Z (wR (jc Z)) ≠ 0) → ∀ (Z : Comp Xo c) (sg : c.F →+* ℂ),
    ∃ S : Set (Fin Dd → Metric.sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1),
      MeasurableSet S ∧
      Measure.pi (fun _ => (volume : Measure (EuclideanSpace ℂ (Fin (N + 1)))).toSphere) S = 0 ∧
      ∀ t0 ∈ Sᶜ, ∃ U ∈ 𝓝 t0, ∃ (n : ℕ)
        (Q : Fin n → (Fin Dd → Metric.sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) → (Om Z →+* ℂ)),
        (∀ k (a : Om Z), ContinuousOn (fun t => Q k t a) (U ∩ Sᶜ)) ∧
        ∀ t ∈ U ∩ Sᶜ, Function.Injective (fun k => Q k t) ∧
          Set.range (fun k => Q k t) = {P : Om Z →+* ℂ | P ∈ PT sg ∧ ∀ i, ∑ j,
            (t i : EuclideanSpace ℂ (Fin (N + 1))) j *
              P (ratio (Ω := Om Z) (valG h uL (wR j) Z) (valG h uL (wR (jc Z)) Z)) = 0}

def NrmAlong (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) : Prop :=
  ∀ (Z : Comp Xo c) (sg : c.F →+* ℂ) {G : WTZ E} {f : AC Z}, f ∈ AG Z G → f ≠ 0 →
    ∀ {X : Type} [TopologicalSpace X] (U : Set X) (Q : X → (Om Z →+* ℂ)), (∀ x ∈ U, Q x ∈ PT sg) →
      (∀ a, ContinuousOn (fun x => Q x a) U) → ContinuousOn (fun x => nrmC fn (yP Z) G f (Q x)) U

theorem nrmContOff_of (h : GenFrEx Xo c) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N : ℕ) (uL : WtR E) (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (hst : STLoc h Dd N uL wR jc) (hna : NrmAlong fn yP) (hfn : FnNe Xo c fn) (htr : FnTrdeg Xo c Dd) (hfg : FnFG Xo c)
    (hwb : ∀ Z, evC h Z (wR (jc Z)) ≠ 0) :
    NrmContOff h fn yP Dd N uL wR jc := by
  intro Z sg G f hf hf0
  obtain ⟨S, hSm, hS0, hloc⟩ := hst htr hfg hwb Z sg
  refine ⟨S, hSm, hS0, ?_⟩

  have hne : ∀ P : Om Z →+* ℂ, nrmC fn (yP Z) G f P ≠ 0 := by
    intro P
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hf
    have ha : a ≠ 0 := by rintro rfl; exact hf0 (zero_smul _ _)
    unfold nrmC
    refine mul_ne_zero ?_ ?_
    · rw [norm_ne_zero_iff, map_ne_zero]
      simpa using ha
    · exact Finset.prod_ne_zero_iff.2 fun i _ => by
        have := abs_pos.2 (hfn _ (yP Z P) i)
        positivity
  intro t0 ht0
  obtain ⟨U, hU, n, Q, hQc, hQ⟩ := hloc t0 ht0
  have hg : ContinuousOn (fun t => ∑ k, Real.log (nrmC fn (yP Z) G f (Q k t))) (U ∩ Sᶜ) := by
    refine continuousOn_finsetSum _ fun k _ => ContinuousOn.log ?_ fun t _ => hne _
    refine hna Z sg hf hf0 (U ∩ Sᶜ) (fun t => Q k t) ?_ (fun a => hQc k a)
    intro t ht
    have hm : Q k t ∈ Set.range (fun k => Q k t) := ⟨k, rfl⟩
    rw [(hQ t ht).2] at hm
    exact hm.1
  have key : ∀ t ∈ U ∩ Sᶜ, ∑ᶠ P ∈ Set.range (fun k => Q k t), Real.log (nrmC fn (yP Z) G f P) =
      ∑ k, Real.log (nrmC fn (yP Z) G f (Q k t)) := fun t ht => by
    rw [finsum_mem_range (hQ t ht).1, finsum_eq_sum_of_fintype]
  have hgw := hg.continuousWithinAt ⟨mem_of_mem_nhds hU, ht0⟩
  rw [Set.inter_comm] at hgw
  refine ((continuousWithinAt_inter hU).1 hgw).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [inter_mem_nhdsWithin Sᶜ hU] with t ht
    rw [← key t ⟨ht.2, ht.1⟩, (hQ t ⟨ht.2, ht.1⟩).2]
    rfl
  · rw [← key t0 ⟨mem_of_mem_nhds hU, ht0⟩, (hQ t0 ⟨mem_of_mem_nhds hU, ht0⟩).2]

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.KapTrdegPf
section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.KapTrdegPfB
namespace Formalism.L2.Pj.TranscendenceDegreeLemmas

open AlgebraicGeometry CategoryTheory

theorem primeIdealOf_mem_minimalPrimes {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) {Z : Set X}
    (hZ : Z ∈ irreducibleComponents X) (hx : hZ.1.genericPoint ∈ V) :
    (hV.primeIdealOf ⟨_, hx⟩).asIdeal ∈ minimalPrimes Γ(X, V) := by
  have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  have hgen : IsGenericPoint hZ.1.genericPoint Z := by
    have := hZ.1.isGenericPoint_genericPoint_closure
    rwa [hZc.closure_eq] at this
  refine ⟨⟨(hV.primeIdealOf ⟨_, hx⟩).isPrime, bot_le⟩, fun q hq hle => ?_⟩
  let y : PrimeSpectrum Γ(X, V) := ⟨q, hq.1⟩
  have hsp : y ⤳ hV.primeIdealOf ⟨_, hx⟩ := (PrimeSpectrum.le_iff_specializes _ _).1 hle
  have hsp' : hV.fromSpec y ⤳ hZ.1.genericPoint := by
    have := hsp.map hV.fromSpec.continuous
    rwa [hV.fromSpec_primeIdealOf] at this
  have hirr : IsIrreducible (closure {hV.fromSpec y}) := isIrreducible_singleton.closure
  have hZle : Z ⊆ closure {hV.fromSpec y} := by
    rw [← hgen.def]
    exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hsp')) isClosed_closure
  have heq : closure {hV.fromSpec y} = Z := (hZ.2 hirr hZle).antisymm hZle
  have hmem : hV.fromSpec y ∈ Z := heq ▸ subset_closure rfl
  have hxy : hV.fromSpec y = hZ.1.genericPoint := (hsp'.antisymm (hgen.specializes hmem)).eq
  have hy : y = hV.primeIdealOf ⟨_, hx⟩ :=
    hV.fromSpec.isOpenEmbedding.injective (hxy.trans (hV.fromSpec_primeIdealOf ⟨_, hx⟩).symm)
  have := congrArg PrimeSpectrum.asIdeal hy
  exact le_of_eq this.symm

theorem fg_residueField_genericPoint {K : Type} [Field K] [CharZero K] [FiniteDimensional ℚ K]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) [Algebra K (X.residueField hZ.1.genericPoint)] :
    (⊤ : IntermediateField K (X.residueField hZ.1.genericPoint)).FG := by
  classical
  obtain ⟨U, hU, V, hV, hxV, e, hP⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) hZ.1.genericPoint
  have hUtop : U = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have hfx : f hZ.1.genericPoint ∈ U := e hxV
    rwa [Subsingleton.elim y (f hZ.1.genericPoint)]
  subst hUtop
  let e0 : K ≃+* Γ(Spec (CommRingCat.of K), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  let ψ : K →+* Γ(X, V) := (f.appLE ⊤ V e).hom.comp (e0 : K →+* _)
  let _ : Algebra K Γ(X, V) := ψ.toAlgebra
  have hsm : Algebra.IsStandardSmoothOfRelativeDimension n K Γ(X, V) :=
    hP.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv e0)
  have hmin := primeIdealOf_mem_minimalPrimes hV hZ hxV
  let _ : Algebra Γ(X, V) (X.presheaf.stalk hZ.1.genericPoint) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hZ.1.genericPoint, hxV⟩
  have hloc := hV.isLocalization_stalk ⟨hZ.1.genericPoint, hxV⟩
  let eL := IsLocalization.algEquiv (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.primeCompl
    (Localization.AtPrime (hV.primeIdealOf ⟨_, hxV⟩).asIdeal) (X.presheaf.stalk hZ.1.genericPoint)
  let eR : (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField ≃+* X.residueField hZ.1.genericPoint :=
    IsLocalRing.ResidueField.mapEquiv eL.toRingEquiv
  have hc1 : CharZero (X.residueField hZ.1.genericPoint) :=
    charZero_of_injective_algebraMap (algebraMap K _).injective
  have hc2 : CharZero (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField :=
    charZero_of_injective_algebraMap (algebraMap K _).injective
  have t1 : IsScalarTower ℚ K (X.residueField hZ.1.genericPoint) :=
    IsScalarTower.of_algebraMap_eq fun q => ((algebraMap K _).map_rat_algebraMap q).symm
  have t2 : IsScalarTower ℚ K (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun q => ((algebraMap K _).map_rat_algebraMap q).symm
  have f00 : Algebra.IsStandardSmooth K Γ(X, V) := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have f01 : Algebra.FinitePresentation K Γ(X, V) := inferInstance
  have f0 : Algebra.EssFiniteType K Γ(X, V) := inferInstance
  have f1 : Algebra.EssFiniteType K (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField :=
    Algebra.EssFiniteType.comp K Γ(X, V) _
  have f2 : Algebra.EssFiniteType ℚ K := inferInstance
  have f3 : Algebra.EssFiniteType ℚ (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField :=
    Algebra.EssFiniteType.comp ℚ K _
  have f4 : Algebra.EssFiniteType ℚ (X.residueField hZ.1.genericPoint) :=
    (Algebra.EssFiniteType.iff_of_algEquiv eR.toRatAlgEquiv).1 f3
  have f5 : Algebra.EssFiniteType K (X.residueField hZ.1.genericPoint) := Algebra.EssFiniteType.of_comp ℚ K _
  exact IntermediateField.fg_top K _

end Formalism.L2.Pj.TranscendenceDegreeLemmas
end

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

set_option backward.isDefEq.respectTransparency.types false in
instance smoothOfRelativeDimension_strK (Xo : Moduli Dw l) (c : Coeff l) :
    SmoothOfRelativeDimension Dw.dim (strK (Xo := Xo) (c := c)) := by
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} Dw.dim
  exact MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension Dw.dim) _ _ Xo.smooth

theorem kapFG_pf (Xo : Moduli Dw l) (c : Coeff l) : KapFG Xo c := by
  intro Z
  have h := @TranscendenceDegreeLemmas.fg_residueField_genericPoint c.F _ _ _ _
    (strK (Xo := Xo) (c := c)) Dw.dim _ _ Z.2 (algKap Z)
  exact h

end Formalism.L2.Pj

end
end
