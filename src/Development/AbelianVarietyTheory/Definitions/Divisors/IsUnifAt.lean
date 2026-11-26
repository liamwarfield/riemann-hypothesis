module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NoCommonZeroIffOfSec
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatB
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def toSub {G : Type} [Group G] (H : Subgroup G) (g : G) : H := if h : g ∈ H then ⟨g, h⟩ else 1

def trOn {V : Type} [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V) (L : V →ₗ[ℂ] V) : ℂ :=
  if h : ∀ v ∈ M, L v ∈ M then LinearMap.trace ℂ M (L.restrict h) else 0

def hint {H : Type} [Group H] (K : Subgroup H) (u : H → ℂ) : ℂ :=
  (((rStab u ⊓ K).relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H ⧸ (rStab u ⊓ K), u q.out

def IsMu (μ : HChar E) (e : InfinitePlace E → ℤ) : Prop :=
  μ.IsUnitary ∧ (∀ x, μ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E x) = (GlobalTheory.GalOfCusp.quadChar E).1 x) ∧
    (∀ w : Pl E, ¬ IsSplitAt w → μ.loc w = GlobalTheory.SmGL.unrChar (w.adicCompletion E) (-1)) ∧ (∀ v, Odd (e v)) ∧
    ∀ z : (Cinf E)ˣ, (chiInf μ z : ℂ) = ∏ v, (z.1 v / (‖z.1 v‖ : ℂ)) ^ e v

def blk {a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    GLw n w :=
  let M := Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
    (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val)
  if hM : IsUnit M then hM.unit else 1

def intMat (a b : ℕ) (w : Pl E) : Subgroup (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :=
  Subgroup.closure {X | ∀ i j, Valued.v (Multiplicative.toAdd X i j) ≤ 1}

def ct {a b : ℕ} (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ) (m : GLw a w × GLw b w) : ℂ :=
  absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) *
    hint (intMat a b w) fun X => avg fun k : GlobalTheory.LFun.KGL w (n := n) => f ((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k)

def ctMu {a b : ℕ} (h : a + b = n) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ)
    (m : GLw a w × GLw b w) : ℂ :=
  (μ ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂ) *
    ct h w (fun y => f (toSub _ y)) m

def iwGL (n : ℕ) (w : Pl E) : Subgroup (GLw n w) := GlobalTheory.SmGL.iwahori (w.adicCompletion E) (Fin n)

def tdiag {w : Pl E} (ϖ : (w.adicCompletion E)ˣ) (a : Fin n → ℤ) : GLw n w :=
  GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) fun i => ϖ ^ a i

def dcos (n : ℕ) (w : Pl E) (t : GLw n w) : GLw n w → ℂ :=
  fun y => if ∃ x ∈ iwGL n w, ∃ z ∈ iwGL n w, y = x * t * z then 1 else 0

def IsUnifAt {w : Pl E} (ϖ : (w.adicCompletion E)ˣ) : Prop := ordL (ϖ : w.adicCompletion E) = 1 ∧ cj w ϖ = ϖ

def IsWitt (n : ℕ) (w : Pl E) (b : GLw n w) : Prop :=
  b ∈ GlobalTheory.LFun.KGL w (n := n) ∧ (b.val.map (cj w))ᵀ * b.val = antiJ (w.adicCompletion E) n

def iwU (n : ℕ) (w : Pl E) (b : GLw n w) : Subgroup (UL n w) :=
  ((iwGL n w).map (MulAut.conj b).toMonoidHom).subgroupOf (UL n w)

def wexp (n : ℕ) (l : Fin (n / 2) → ℤ) (i : Fin n) : ℤ :=
  if h : i.val < n / 2 then l ⟨i, h⟩ else if h' : n - 1 - i.val < n / 2 then -l ⟨_, h'⟩ else 0

def Cone {m : ℕ} (l : Fin m → ℤ) : Prop := (∀ i j : Fin m, (j : ℕ) = i + 1 → 2 ≤ l i - l j) ∧ ∀ i, 2 ≤ l i

def fU (n : ℕ) (w : Pl E) (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ) (l : Fin (n / 2) → ℤ) : UL n w → ℂ :=
  fun γ => if ∃ x ∈ iwU n w b, ∃ z ∈ iwU n w b, γ.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * z.1 then 1 else 0

def qh (w : Pl E) : ℂ := (Real.sqrt (qV E w : ℝ) : ℝ)

def dlt (n : ℕ) (w : Pl E) (l : Fin (n / 2) → ℤ) : ℂ := qh w ^ (∑ i : Fin (n / 2), ((n : ℤ) - 1 - 2 * (i : ℕ)) * l i)

def vRes (n a : ℕ) (l : Fin (n / 2) → ℤ) (s : Finset (Fin (n / 2))) : ℤ :=
  -2 * (∑ i ∈ s, ∑ j ∈ sᶜ, max (l i) (l j)) -
    (if n % 2 = 1 then (if a % 2 = 1 then ∑ j ∈ sᶜ, l j else ∑ j ∈ s, l j) else 0)

def HasVals {w : Pl E} (Q : (w.adicCompletion E)[X]) (a : Fin n → ℤ) : Prop :=
  ∃ u : Fin n → w.adicCompletion E, Q = ∏ i, (X - C (u i)) ∧ ∀ i, u i ≠ 0 ∧ ordL (u i) = a i

def pw {m : ℕ} (y : Fin m → ℂˣ) (l : Fin m → ℤ) : ℂ := ∏ i, ((y i ^ l i : ℂˣ) : ℂ)

def SatUL {w : Pl E} (b : GLw n w) (ϖ : w.adicCompletion E) (q : ℕ) (σ : SmIrr (UL n w)) (α : Fin (n / 2) → ℂˣ) : Prop :=
  ∃ (p : UL n w ≃* GU (cj w) n) (σ' : SmIrr (GU (cj w) n)), (∀ x, (p x).1 = b⁻¹ * x.1 * b) ∧
    GlobalTheory.LFun.HasSatU ϖ q σ'.ρ α ∧ Nonempty (σ.ρ.Equiv (σ'.ρ.comp p.toMonoidHom))

def UE (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Subgroup (GL (Fin n) E) :=
  UJ (IsCMField.complexConj E).toRingEquiv.toRingHom 1

def finPt (γ : UE E n) : finU (E := E) (n := n) := toSub _ (toSub _ (finGL E n (ratF E n γ.1)))

def ratFinU (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Subgroup (finU (E := E) (n := n)) :=
  (((UE E n).map ((finGL E n).comp (ratF E n))).comap (UA E n).subtype).comap (finU (E := E) (n := n)).subtype

def locPt (w : Pl E) (γ : UE E n) : UL n w := toSub _ (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1)

def globLev (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) : Subgroup (finU (E := E) (n := n)) :=
  ⨅ w ∈ S, ((K' w).map (UL n w).subtype).comap ((cLoc w).comp (finU (E := E) (n := n)).subtype)

def globFn (S : Set (Pl E)) (f : ∀ w : Pl E, UL n w → ℂ) (x : finU (E := E) (n := n)) : ℂ := ∏ᶠ w ∈ S, f w (toSub _ (cLoc w x.1))

def RF (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Representation ℂ (finU (E := E) (n := n)) (UA E n → ℂ) :=
  (RU E n).comp (finU (E := E) (n := n)).subtype

def forms (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)) :
    Submodule ℂ (UA E n → ℂ) :=
  ⨆ (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧ ∀ v, HasWeightAt π v.embedding (lam v)),
    π ⊓ fixed (RF E n) (globLev S K')

def hop (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ) :
    (UA E n → ℂ) →ₗ[ℂ] (UA E n → ℂ) :=
  levOp (RF E n) (globLev S (KL n)) (globLev S K') (globFn S f) LinearMap.id

def dimW (lam : InfinitePlace E → DomWeight n) : ℂ :=
  ∏ v, LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n (lam v) 1)

def geomURat (lam : InfinitePlace E → DomWeight n) (orb : UE E n → ℂ) : ℂ :=
  ∑ᶠ c : TwCl (MonoidHom.id (UE E n)), if c.rep.1.val.charpoly.Separable then
    mass (MonoidHom.id _) (ratFinU E n) (finPt c.rep) * chW lam c.rep.1.val.charpoly * orb c.rep else 0

def nfac {k : Type} [Field k] (P : k[X]) : ℕ := Multiset.card (UniqueFactorizationMonoid.normalizedFactors P)

end GlobalTheory.BCT
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
noncomputable section

namespace GlobalTheory.LevGeo

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Laws (D : D7) (j : ℕ) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l)
    (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r)
    (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) : Prop where

  inR : InR D j

  host : H.d = D.host.d ∧ (H.rt : D.host.E) = D.host.sqrtMinusD ∧ H.rt0 = D.host.φ₀ D.host.sqrtMinusD ∧
    ∀ t : D.what₂.Tau, DV.tauEmb D t (H.rt : D.host.E) = H.rt0

  dat : IsDatW D j Dw

  levA : l.A = 1

  unf : ∀ σ, GoodEmb c σ → IsUnf (U σ)

  chiTriv : ∀ σ, GoodEmb c σ → ∀ a n, Dom a n → ∀ k, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ (laU (U σ) a n k) γ = 1

  dictU : ∀ σ, GoodEmb c σ → ∃ Kf th hr, IsLevelK (D.sp.W j) l.M Kf ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
    DictIsUnif (D.sp.W j) (dict σ) Kf th hr ∧
    ∀ g τ k, ‖dmin ((U σ).X (dict σ g).1).Gm (dict σ g).2 τ k‖ = 1

  modelW : ∀ σ, GoodEmb c σ → ∃ hr : (D.sp.W j).rank = D.R.r, ∀ k, ModelW (D.sp.W j) hr ((U σ).X k)

section Derived

variable {D : D7} {j : ℕ} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r}
  {dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r}

theorem Laws.unTest (_ : Laws D j Xo c U dict) : ∀ σ, GoodEmb c σ → ∀ k x,
    FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((U σ).un k x) := fun σ _ k x =>
  haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  GlobalTheory.TransferCompare.allTest_framed Xo c (CAt σ) ((U σ).un k x)

theorem Laws.xiAbs (h : Laws D j Xo c U dict) : ∀ σ, GoodEmb c σ → ∀ k (τ : D.host.E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xiR D := by
  intro σ hσ k τ
  obtain ⟨hr, hm⟩ := h.modelW σ hσ
  rw [(hm k).2, map_neg, norm_neg]
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatB.norm_embedding_hostFormConstant_eq D τ

end Derived

def coreDict {D : D7} (T : Core D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (g : GA D (D.sp.W j)) : Σ k, Frame ((T.U j σ).X k).Ψ D.R.r :=
  open Classical in if h : T.V j σ = D.sp.W j then T.dict j σ (h ▸ g) else T.dict j σ 1

theorem unif_of_space_eq {D : D7} {r : ℕ} {C : Type} {X : C → Data D.host.E r} (V W : HSp D) (h : V = W)
    (dict : GA D V → Σ k, Frame (X k).Ψ r) (M : ℕ) (Kf : Subgroup (GA D V)) (hK : IsLevelK V M Kf)
    (hd : ∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif V dict Kf th hr)
    (hu : ∀ g τ k, ‖dmin (X (dict g).1).Gm (dict g).2 τ k‖ = 1) :
    ∃ Kf th hr, IsLevelK W M Kf ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
      DictIsUnif W (fun g => dict (h ▸ g)) Kf th hr ∧
      ∀ (g : GA D W) τ k, ‖dmin (X (dict (h ▸ g)).1).Gm (dict (h ▸ g)).2 τ k‖ = 1 := by
  subst h
  obtain ⟨th, hr, h1, h2⟩ := hd
  exact ⟨Kf, th, hr, hK, h1, h2, hu⟩

theorem laws_core (D : D7) (T : CoreJ D) (j : ℕ) (h : LawsJ T) (hj : InR D j) :
    Laws D j (T.Q.Xo j) T.Q.c (T.U j) (coreDict T.toCore j) := by
  refine ⟨hj, h.pins.1, h.pins.2.2.2 j hj, h.pins.2.1.2, h.unf j hj, h.chiTriv j hj, ?_, ?_⟩
  · intro σ hσ
    have hV := h.spaceW j hj σ hσ
    have e : coreDict T.toCore j σ = fun g => T.dict j σ (hV ▸ g) := by
      funext g
      simp only [coreDict, dite_eq_left hV]
    rw [e, h.pins.2.1.1]
    exact unif_of_space_eq _ _ hV (T.dict j σ) _ (T.Kf j σ) (h.levelK j hj σ hσ) (h.dictU j hj σ hσ)
      (h.muUnit j hj σ hσ).2.2.2
  · intro σ hσ
    have := h.modelW j hj σ hσ
    rw [h.spaceW j hj σ hσ] at this
    exact this

section Consts

variable (E : Type) [Field E] [NumberField E] (r : ℕ)

def chartRad (w : ℝ) : ℝ := 1 / (200 * (r : ℝ) ^ 3 * (w + fdeg E))

def multBd (ε : ℝ) : ℝ := (1 + 2 * (2 * (fdeg E : ℝ) * r) ^ 2 * dE E / ε) ^ (2 * fdeg E * r ^ 2)

def dimFl : ℕ := fdeg E * (r * (r - 1) / 2)

def locConst (w ε : ℝ) : ℝ :=
  8 * ((dimFl E r).factorial : ℝ) / (Real.pi * chartRad E r w ^ 2) ^ dimFl E r * multBd E r ε

def massLev (M : ℕ) : ℝ := GlobalTheory.UCls.massBd E r M (classNumber E * M ^ (2 * fdeg E))

def epsLev (d M : ℕ) (w : ℝ) : ℝ := epStar (2 * M * Real.sqrt d) (fdeg E) w 1

def supConst (d M : ℕ) (w : ℝ) : ℝ := locConst E r w (epsLev E d M w) * massLev E r M

def cmLen (q d M : ℕ) (w : ℝ) : ℝ :=
  frameBasisRadius r q (fdeg E) (dE E) (Real.sqrt (epsLev E d M w)) (3 * frameRadius w r / 5)

def lamSup (q d M : ℕ) (Om s t : ℝ) : ℝ :=
  (Formalism.L2.LamCM.pDeg Om + 1 / 2 * Real.log (cmLen E r q d M (s + t + 1))) * (s + t) +
    s * Real.log (r * cmLen E r q d M (s + t + 1))

def lamPet (q d M : ℕ) (Om s t : ℝ) : ℝ := lamSup E r q d M Om s t + 1 / 2 * Real.log (supConst E r d M (s + t + 1))

theorem one_le_multBd {ε : ℝ} (hε : 0 < ε) : 1 ≤ multBd E r ε := by
  unfold multBd
  refine one_le_pow₀ (le_add_of_nonneg_right ?_)
  have : 0 ≤ dE E := abs_nonneg _
  positivity

end Consts

def absA {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (a : (E →+* ℂ) × ℕ → ℕ) : ℕ := ∑ b : E →+* ℂ, ∑ i : Fin (Dw.mult b), a (b, i)

end GlobalTheory.LevGeo
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHt

open MvPolynomial NumberField IsDedekindDomain Module Filter GlobalTheory.ChowHt GlobalTheory.AllWt
open scoped ENNReal

section Generic

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]

theorem frameNorm_conj {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.det ≠ 0) (x : Fin N → ℂ) :
    frameNorm (A.map (starRingEnd ℂ)) (fun j => starRingEnd ℂ (x j)) = frameNorm A x := by
  have h : (A.map (starRingEnd ℂ))⁻¹ = A⁻¹.map (starRingEnd ℂ) := Matrix.inv_eq_left_inv (by
    rw [← Matrix.map_mul, A.nonsing_inv_mul hA.isUnit, Matrix.map_one _ (map_zero _) (map_one _)])
  rw [frameNorm, frameNorm, h]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [← Complex.norm_conj (A⁻¹.mulVec x i), RingHom.map_mulVec]
  rfl

theorem exists_isFrame [IsScalarTower (𝓞 K) K V] (hK : ∀ σ : K →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ)
    {Nm : (K →+* ℂ) → V → ℝ} (hc : ∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) (hG : HasGram Nm)
    {L : Submodule (𝓞 K) V} (hL : L.FG) (hs : Submodule.span K (L : Set V) = ⊤) :
    ∃ (N n : ℕ) (b : Basis (Fin N) K V) (w : Matrix (Fin N) (Fin n) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ),
      IsFrame Nm L b w A := by
  classical
  obtain ⟨N, ⟨b, X⟩, hX⟩ := hG
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hL
  have hd : ∀ v, (X v).det ≠ 0 := fun v => (hX v).1.ne_zero
  have hdc : ∀ v, ((X v).map (starRingEnd ℂ)).det ≠ 0 := fun v => by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (map_ne_zero _).2 (hd v)
  have hmk : ∀ σ : K →+* ℂ, InfinitePlace.mk ((starRingEnd ℂ).comp σ) = InfinitePlace.mk σ :=
    InfinitePlace.mk_conjugate_eq
  have hor : ∀ σ : K →+* ℂ, (InfinitePlace.mk σ).embedding ≠ σ →
      (InfinitePlace.mk σ).embedding = (starRingEnd ℂ).comp σ := fun σ h =>
    (InfinitePlace.embedding_mk_eq σ).resolve_left h
  have hn : ∀ (v : InfinitePlace K) x, frameNorm (X v) (fun j => v.embedding (b.repr x j)) = Nm v.embedding x :=
    fun v x => (hX v).2 x
  refine ⟨N, n, b, Matrix.of fun j k => b.repr (g k) j, fun σ => if (InfinitePlace.mk σ).embedding = σ then
    X (InfinitePlace.mk σ) else (X (InfinitePlace.mk σ)).map (starRingEnd ℂ), ?_, ?_, fun σ => ?_, fun σ x => ?_,
    fun σ x => ?_⟩
  · simp only [Matrix.of_apply, Basis.sum_repr]; exact hg
  · have h1 : Submodule.span K (Set.range g) = ⊤ := by rw [← hs, ← hg, Submodule.span_span_of_tower]
    have h2 := congrArg (Submodule.map b.equivFun.toLinearMap) h1
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at h2
    exact h2
  · split_ifs
    exacts [hd _, hdc _]
  · simp only [hmk]
    by_cases h : (InfinitePlace.mk σ).embedding = σ
    · rw [if_pos h, if_neg fun h' => hK σ (h'.symm.trans h), frameNorm_conj (hd _)]
    · rw [if_neg h, if_pos (hor σ h), ← frameNorm_conj (hd _)]
      simp only [Complex.conj_conj]
  · by_cases h : (InfinitePlace.mk σ).embedding = σ
    · rw [if_pos h]
      have := hn (InfinitePlace.mk σ) x
      rwa [h] at this
    · have := hn (InfinitePlace.mk σ) x
      rw [hor σ h, hc, ← frameNorm_conj (hd _)] at this
      rw [if_neg h, ← this]
      simp only [RingHom.comp_apply, Complex.conj_conj]

structure IsShortGen {κ : Type} (Nm : κ → V → ℝ) (L : Submodule (𝓞 K) V) {n : ℕ} (w : Fin n → V) (abelian₂ : ℝ) : Prop where

  gen : ∀ x, x ∈ L ↔ x ∈ Submodule.span ℤ (Set.range w)

  le : ∀ i k, Nm k (w i) ≤ abelian₂

  one_le : 1 ≤ abelian₂

theorem exists_isShortGen {κ : Type} [Finite κ] (Nm : κ → V → ℝ) {L : Submodule (𝓞 K) V} (hL : L.FG) :
    ∃ (n : ℕ) (w : Fin n → V) (abelian₂ : ℝ), IsShortGen Nm L w abelian₂ := by
  obtain ⟨n, w, hw⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (hL.restrictScalars (R := ℤ))
  obtain ⟨B, hB⟩ := (Set.finite_range fun p : Fin n × κ => Nm p.2 (w p.1)).bddAbove
  exact ⟨n, w, max B 1, fun x => by rw [hw]; rfl, fun i k => (hB ⟨(i, k), rfl⟩).trans (le_max_left _ _),
    le_max_right _ _⟩


end Generic

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

instance fintypePsi : Fintype (Psi H) := Fintype.ofFinite _

def dimFlag (Dw : Datum H) : ℕ := Formalism.DegreeFormula.dimFl (Psi H) (Dw.p + Dw.q)

def hodgeWt (Dw : Datum H) : GlobalTheory.AllWt.Weight Dw := barWt (Psi H) (Dw.p + Dw.q) Dw.p

def uPrime (Dw : Datum H) (u : GlobalTheory.AllWt.Weight Dw) : GlobalTheory.AllWt.Weight Dw := u - (3 * ((Dw.p + Dw.q : ℕ) : ℤ)) • hodgeWt Dw

theorem uPrime_apply (u : GlobalTheory.AllWt.Weight Dw) (τ : Psi H) (i : Fin (Dw.p + Dw.q)) :
    uPrime Dw u τ i = if (i : ℕ) < Dw.p then u τ i else u τ i + 3 * ((Dw.p + Dw.q : ℕ) : ℤ) := by
  simp only [uPrime, hodgeWt, barWt, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

def rhoB (Dw : Datum H) (u : GlobalTheory.AllWt.Weight Dw) : ℝ := rhoOf (uPrime Dw u) u

theorem nsmul_wtOf (t : ℕ) (la : GlobalTheory.AllWt.Weight Dw) (m : ℤ) : t • wtOf Dw la m = wtOf Dw (t • la) (t • m) := by
  induction t with
  | zero => simp only [zero_smul, wtOf_zero]
  | succ t ih => rw [succ_nsmul, succ_nsmul, succ_nsmul, ih, wtOf_add]

def genVal (Z : Comp Xo c) : Rul Xo c →ₐ[c.F] Om Z :=
  evCAlg (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1 ((Reg.genFrEx_and_genFromTest E H Dw l Xo c).2 _) Z

theorem genVal_apply (h : GenFrEx Xo c) (Z : Comp Xo c) (f : Rul Xo c) : genVal Z f = evC h Z f := rfl

variable (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) {D : D7} (V : (c.F →+* ℂ) → HSp D)
  (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r)

set_option synthInstance.maxHeartbeats 100000 in
def genPoint (Z : Comp Xo c) (C : Submodule c.F (Rul Xo c)) : C →ₗ[c.F] Om Z := (genVal Z).toLinearMap ∘ₗ C.subtype

section

set_option synthInstance.maxHeartbeats 100000

def compIdeal (Z : Comp Xo c) (G : WTZ E) {N : ℕ} (b : Basis (Fin N) c.F (cuspOn U Z G)) :
    Ideal (MvPolynomial (Fin N) c.F) := imageIdeal (genPoint Z (cuspOn U Z G)) b


def compDeg (Z : Comp Xo c) (G : WTZ E) : ℕ := imageDeg (genPoint Z (cuspOn U Z G)) (dimFlag Dw)

def compHeight (Z : Comp Xo c) (G : WTZ E) : ℝ :=
  imageHeight (normOn U x V dict Z G) (latOn U Z G) (genPoint Z (cuspOn U Z G)) (dimFlag Dw)

def CompPresents (Z : Comp Xo c) (G : WTZ E) (T : Adelic.HermSys c.F) : Prop :=
  T.D = dimFlag Dw ∧ Presents T (normOn U x V dict Z G) (latOn U Z G) (genPoint Z (cuspOn U Z G))

end

theorem not_goodEmb_conj {σ : c.F →+* ℂ} (h : GoodEmb c σ) : ¬ GoodEmb c ((starRingEnd ℂ).comp σ) := fun h' => by
  have h1 : starRingEnd ℂ H.rt0 = H.rt0 := (congrArg (starRingEnd ℂ) h).symm.trans h'
  have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h1
  have hre := congrArg Complex.re H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  simp only [sq, Complex.mul_re, him, Complex.neg_re, Complex.natCast_re] at hre
  nlinarith [mul_self_nonneg H.rt0.re]

theorem goodOf_conj (σ : c.F →+* ℂ) : goodOf c ((starRingEnd ℂ).comp σ) = goodOf c σ := by
  have e : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp σ) = σ := RingHom.ext fun a => Complex.conj_conj _
  by_cases h : GoodEmb c σ
  · rw [goodOf, goodOf, if_pos h, if_neg (not_goodEmb_conj h), e]
  · have h' := goodEmb_goodOf c σ
    rw [goodOf, if_neg h] at h'
    rw [goodOf, goodOf, if_neg h, if_pos h']

theorem conj_comp_ne (σ : c.F →+* ℂ) : (starRingEnd ℂ).comp σ ≠ σ := fun e => by
  have h := goodEmb_goodOf c σ
  have e' : goodOf c σ = σ := by rw [goodOf, e, ite_self]
  rw [e'] at h
  exact not_goodEmb_conj h (e.symm ▸ h)

theorem petOn_conj (Z : Comp Xo c) (G : WTZ E) (σ : c.F →+* ℂ) (f : Rul Xo c) :
    petOn U x V dict Z G ((starRingEnd ℂ).comp σ) f = petOn U x V dict Z G σ f :=
  congrArg (fun s => petAt (U s) x (V s) (dict s) (muOn (U s) (V s) (dict s) Z) G f) (goodOf_conj σ)



def CompShortGen (G : WTZ E) {n : ℕ} (w : Fin n → cuspW Xo c U G) (abelian₂ : ℝ) : Prop :=
  IsShortGen (fun (k : (c.F →+* ℂ) × Comp Xo c) (f : cuspW Xo c U G) => petOn U x V dict k.2 G k.1 f) (latW U G) w abelian₂

def depth_vw (G : WTZ E) (v : Rul Xo c → EReal) : EReal := ⨅ w ∈ latW U G, v w

set_option synthInstance.maxHeartbeats 100000 in
def growthOn (Z : Comp Xo c) (G : WTZ E) : ℝ≥0∞ :=
  growth (dimFlag Dw) fun τ => Cardinal.toENat (Module.rank c.F (cuspOn U Z (τ • G)))

def vZero (Z : Comp Xo c) : ℝ :=
  (growthOn U Z (wtOf Dw (stdWt (Psi H) (Dw.p + Dw.q)) 0)).toReal / (vdm (stdWt (Psi H) (Dw.p + Dw.q)) : ℤ)

theorem vZero_nonneg (Z : Comp Xo c) : 0 ≤ vZero U Z :=
  div_nonneg ENNReal.toReal_nonneg (Int.cast_pos.2 (vdm_pos strictAnti_stdWt)).le

def topDeg (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw) : ℝ := vZero U Z * (vdm la : ℤ)

def delPrime (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw) : ℝ := topDeg U Z (uPrime Dw u)

theorem delPrime_eq (Z : Comp Xo c) {u : GlobalTheory.AllWt.Weight Dw} (h : vdm u ≠ 0) :
    delPrime U Z u = (1 - rhoB Dw u) * topDeg U Z u := by
  rw [delPrime, topDeg, topDeg, ← one_sub_rhoOf_mul (u' := uPrime Dw u) h, rhoB]
  ring


variable (Xo c) in
def ValFam : Type :=
  {Vs : HeightOneSpectrum (𝓞 c.F) → Set (Rul Xo c → EReal) // ∀ la, ∀ v ∈ Vs la, IsVal la v}


variable (Xo c) in
def recVals : ValFam Xo c := ⟨valSet Xo c (algCls Xo c), isVal_valSet⟩


open Classical in
def ValFam.patch (S : Set ℕ) (A B : ValFam Xo c) : ValFam Xo c :=
  ⟨fun la => if ∃ p ∈ S, ((p : ℕ) : 𝓞 c.F) ∈ la.asIdeal then A.1 la else B.1 la, fun la v hv => by
    beta_reduce at hv
    split_ifs at hv
    exacts [A.2 la v hv, B.2 la v hv]⟩

def latVal (Vs : ValFam Xo c) (Z : Comp Xo c) (G : WTZ E) : Submodule (𝓞 c.F) (cuspOn U Z G) :=
  latOf (cuspOn U Z G) Vs.1 Vs.2

def smallOn (Vs : ValFam Xo c) (Z : Comp Xo c) (G : WTZ E) (R : ℝ) : Set (cuspOn U Z G) :=
  {f | f ∈ latVal U Vs Z G ∧ ∀ σ, GoodEmb c σ → ∀ z ∈ framesOn (U σ) Z, homN (U σ) x G f z ≤ R}

def compVol (a : ℕ) (Vs : ValFam Xo c) (Z : Comp Xo c) (G : WTZ E) (t : ℝ) : ℝ≥0∞ :=
  countVol (dimFlag Dw) (finrank ℚ c.F) a fun τ => (smallOn U x Vs Z (τ • G) (Real.exp (τ * t))).encard

def compVolSlope (a : ℕ) (Vs : ValFam Xo c) (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw) : EReal :=
  volSlope (topDeg U Z la) (compVol U x a Vs Z (wtOf Dw la 0))

theorem le_compVolSlope_iff (a : ℕ) (Vs : ValFam Xo c) {Z : Comp Xo c} {la : GlobalTheory.AllWt.Weight Dw} (h : 0 < topDeg U Z la) (s : ℝ) :
    (s : EReal) ≤ compVolSlope U x a Vs Z la ↔
      ∀ t : ℝ, ENNReal.ofReal (topDeg U Z la * (s + t)) ≤ compVol U x a Vs Z (wtOf Dw la 0) t :=
  le_volSlope_iff h _ s

end GlobalTheory.CompHt
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.CechPic

namespace GlobalTheory.Mix

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

structure MLine (p : X ⟶ Sp k) (σ : k →+* ℂ) where

  B : LB X

  φ : Weight p σ B

  cInf : φ.IsCInf

namespace MLine

def ofHerm (L : HermLB p) (σ : k →+* ℂ) : MLine p σ := ⟨L.B, L.φ σ, L.cInf σ⟩

def tens (A B : MLine p σ) : MLine p σ := ⟨CechPic.tens A.B B.B, A.φ.tens B.φ, A.cInf.tens B.cInf⟩

def pull (A : MLine p σ) {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) : MLine q σ :=
  ⟨A.B.pull π, A.φ.pull π hπ, A.cInf.pull π hπ⟩

def ofFun (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) : MLine p σ :=
  ⟨LB.triv X, Weight.ofFun u, Weight.isCInf_ofFun hu⟩

def addFn (A : MLine p σ) (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) : MLine p σ :=
  ⟨A.B, A.φ.addFn u, A.cInf.addFn hu⟩

def Isom (L M : MLine p σ) : Prop :=
  ∃ w : LB.Iso L.B M.B, w.IsGen ∧ ∀ (a : M.B.ι) (b : L.B.ι) (y : CxPts p σ),
    y ∈ ptsIn p σ (M.B.U a) → y ∈ ptsIn p σ (L.B.U b) →
      M.φ.φ a y = L.φ.φ b y + Real.log (‖ev p σ _ (w.s (a, b)).val y‖ ^ 2)

def logSec (M : MLine p σ) (s : M.B.Sec) (y : CxPts p σ) : ℝ := Real.log (M.φ.nsq (secVal p σ s) y) / 2

end MLine

abbrev ptMap {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) (σ : k →+* ℂ) : CxPts q σ → CxPts p σ :=
  PtsOver.map π hπ (spMap σ)

def dens (L : Fin D → MLine p σ) (c : AlgChart p σ D) (y : CxPts p σ) : ℝ :=
  (Real.pi ^ D)⁻¹ * (∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l =>
    c.hess (L (τ l)).φ (pick (L (τ l)).φ.isLB y) y j l).det).re

def part (L : Fin D → MLine p σ) (ε : ℤˣ) : Measure (CxPts p σ) :=
  glueMeas (fun c : AlgChart p σ D => c.e) fun c y => ENNReal.ofReal ((ε : ℤ) * dens L c y)

def Intg (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ) : Prop := Integrable f (part L 1) ∧ Integrable f (part L (-1))

def int (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ) : ℝ := ∫ y, f y ∂part L 1 - ∫ y, f y ∂part L (-1)

def clos (z : X) : Scheme.{0} := (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z})).subscheme

def closι (z : X) : clos z ⟶ X := (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z})).subschemeι

instance (z : X) : IsClosedImmersion (closι z) :=
  inferInstanceAs (IsClosedImmersion (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z})).subschemeι)

def CycIntg (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ) (z : X) : Prop :=
  Intg (fun i => (L i).pull (closι z) rfl) fun y => f (ptMap (closι z) rfl σ y)

def cycInt (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ) (z : X) : ℝ :=
  int (fun i => (L i).pull (closι z) rfl) fun y => f (ptMap (closι z) rfl σ y)

def side [IsIntegral X] [IsLocallyNoetherian X] (N : MLine p σ) (L : Fin D → MLine p σ) (f g : CxPts p σ → ℝ)
    (Δ : CartierDiv X) : ℝ :=
  int (Fin.cons N L : Fin (D + 1) → MLine p σ) f + ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L g z

theorem dens_const (N : MLine p σ) (c : AlgChart p σ D) (y : CxPts p σ) :
    dens (fun _ => N) c y = c.chernDens N.φ y := by
  have e : (Matrix.of fun j l => c.hess N.φ (pick N.φ.isLB y) y j l) = c.hess N.φ (pick N.φ.isLB y) y := rfl
  simp only [dens, AlgChart.chernDens, e, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
  ring

theorem part_const (N : MLine p σ) (ε : ℤˣ) : part (fun _ : Fin D => N) ε = N.φ.chernPart D ε := by
  simp only [part, Weight.chernPart, dens_const]

section Generic

variable (t : X ⟶ Sp ℤ)

variable {t}

end Generic

end GlobalTheory.Mix
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy

namespace GlobalTheory.PairStep

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]

def IsQCart [IsLocallyNoetherian X] (D : X → ℚ) : Prop :=
  ∃ (m : ℕ) (D₀ : CartierDiv X), 0 < m ∧ D₀.Eff ∧ D = qWeil D₀ m

def QNum [IsLocallyNoetherian X] (p : X ⟶ Sp k) (N : LB X) (b : ℚ) (D : X → ℚ) : Prop :=
  letI := algebraΓOfHom p
  ∃ (m : ℕ) (D₀ : CartierDiv X), 0 < m ∧ D₀.Eff ∧ D = qWeil D₀ m ∧
    ∀ C : Closeds X, IsCompleteCurve k C →
      (interNumRed k C ![toLB D₀] : ℚ) / m = b * interNumRed k C ![N]


omit [IsIntegral X] in
def Off (B : X → ℚ) (z : X) : Prop := ∀ w, w ⤳ z → B w = 0

def CentreAt {p : X ⟶ Sp k} (E : DivOver p) (z : X) : Prop :=
  E.Through z ∧ ∀ f : X.functionFieldˣ, RegAt z (f : X.functionField) → E.ord f = 0 →
    RegAt z ((f⁻¹ : X.functionFieldˣ) : X.functionField)

def IsNkltCentre (p : X ⟶ Sp k) (n : ℕ) (Γ : X → ℚ) (z : X) : Prop :=
  ∃ (E : DivOver p) (η : RatForms p n) (m : ℕ) (g : X.functionFieldˣ),
    η ≠ 0 ∧ 0 < m ∧ IsLogEqn p Γ η z m g ∧ CentreAt E z ∧ discrep E η m g ≤ -1

def LcCut (p : X ⟶ Sp k) (n : ℕ) (Γ : X → ℚ) (x : X) (j : ℕ) : Prop :=
  LcAt p n Γ x ∧ ¬ KltAt p n Γ x ∧
    ∀ z, z ⤳ x → ¬ KltAt p n Γ z → topologicalKrullDim (closure ({z} : Set X)) ≤ j

theorem QNum.isQCart [IsLocallyNoetherian X] {p : X ⟶ Sp k} {N : LB X} {b : ℚ} {D : X → ℚ}
    (h : QNum p N b D) : IsQCart D := by
  obtain ⟨m, D₀, hm, he, hD, -⟩ := h
  exact ⟨m, D₀, hm, he, hD⟩

end GlobalTheory.PairStep
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
noncomputable section

namespace GlobalTheory.UPel.Sm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel

variable {F : Type} [Field F] [NumberField F] [IsCMField F]

section KS

variable {k H O : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O]

def IsKS (ρ : O →+* Module.End k H) (φ : LinearMap.BilinForm k H) (Fil Z : Submodule k H)
    (f : H →ₗ[k] H) : Prop :=
  (∀ a, ∀ x ∈ Fil, f (ρ a x) - ρ a (f x) ∈ Fil) ∧ (∀ x ∈ Z, f x ∈ Fil) ∧
    ∀ x ∈ Fil, ∀ y ∈ Fil, φ (f x) y + φ x (f y) = 0

def KSDim (ρ : O →+* Module.End k H) (φ : LinearMap.BilinForm k H) (Fil Z : Submodule k H) (d : ℕ) :
    Prop :=
  ∃ f : Fin d → (H →ₗ[k] H), (∀ i, IsKS ρ φ Fil Z (f i)) ∧
    ∀ g, IsKS ρ φ Fil Z g → ∃! c : Fin d → k, ∀ x ∈ Fil, g x - ∑ i, c i • f i x ∈ Fil

end KS

end GlobalTheory.UPel.Sm
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

def Le (B A : HermLB p) : Prop :=
  ∃ P : Pair p, P.L = A ∧ P.A = B ∧ (1 : X.functionField) ∈ P.Bl 1 (-1) 1


omit [IsIntegral X] in
def HtNef (M : HermLB p) (D : ℕ) : Prop :=
  M.SemiPos D ∧ ∀ h : X → ℝ, M.IsArithHeight h → ∀ x, 0 ≤ h x

def Total {J : Type} (f : J → X.functionField) : Prop :=
  (∀ j, f j ≠ 0) ∧ ∀ (x : X) (j l : J), RegAt x (f j / f l) ∨ RegAt x (f l / f j)

def SmallFam (B : HermLB p) {J : Type} (f : J → X.functionField) (w : J → ℝ) : Prop :=
  ∃ β : B.B.ι → X.functionFieldˣ, IsRatSec B.B β ∧
    (∀ (x : X) c, x ∈ B.B.U c → ∀ j, RegAt x (f j * (β c : X.functionField))) ∧
    ∀ (σ : k →+* ℂ) (y : CxPts p σ) c, y ∈ ptsIn p σ (B.B.U c) → ∀ j,
      ‖ratVal (f j * (β c : X.functionField)) y‖ * Real.exp (-(B.φ σ).φ c y / 2) ≤ Real.exp (-w j)

def IsFS (M : HermLB p) {J : Type} [Fintype J] (f : J → X.functionField) (w : J → ℝ) : Prop :=
  ∃ ρ : M.B.ι → X.functionFieldˣ, IsRatSec M.B ρ ∧
    (∀ (x : X) c, x ∈ M.B.U c → (∀ j, RegAt x (f j * (ρ c : X.functionField))) ∧ ∃ j, UnitAt x (f j * (ρ c : X.functionField))) ∧
    ∀ (σ : k →+* ℂ) (y : CxPts p σ) c, y ∈ ptsIn p σ (M.B.U c) →
      (M.φ σ).φ c y = Real.log (∑ j, ‖ratVal (f j * (ρ c : X.functionField)) y‖ ^ 2 * Real.exp (2 * w j))

structure IsModel {Y : Scheme.{0}} [IsIntegral Y] (π : Y ⟶ X) (φ : X.functionField →+* Y.functionField) : Prop where

  gen : π (genericPoint Y) = genericPoint X

  deg : π.residueDegree (genericPoint Y) = 1

  compat : ∀ (y : Y) (a : X.presheaf.stalk (π y)),
    φ (algebraMap _ X.functionField a) = algebraMap _ Y.functionField (π.stalkMap y a)

def boxFam {K J : Type} [Field K] {D : ℕ} (e : J → K) (x : Fin D → K) : J × Finset (Fin D) → K :=
  fun c => e c.1 * ∏ i ∈ c.2, x i

def shiftA (P : Pair p) (u : ℝ) : Pair p :=
  ⟨P.L, P.A.shift (fun _ => u) fun _ => rfl, P.r, P.r', P.hr, P.hr'⟩

def GenAt (P : Pair p) (c : ℕ) : Prop :=
  ∃ (n : ℕ) (v : Fin n → X.functionField), (∀ i, v i ∈ P.H 0 c) ∧
    ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ i, P.nu 0 c σ y (v i) ≠ 0

def Regime (P : Pair p) (D : ℕ) : Prop :=
  ∃ α β : ℝ, ∀ t : ℝ, 0 ≤ t →
    Tendsto (fun m : ℕ => P.lc 0 m (Real.exp (t * m)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 (α + β * t))

def bound (D q : ℕ) (b g : ℝ) : ℝ :=
  let Δ := Real.log ((q : ℝ) / 2)
  let α := (b + (D + 1) * (Δ + D * Real.log 2 / 2) * g) / ((D + 1).factorial * Δ)
  let β := (D + 1) * g / (2 * ((D + 1).factorial * Δ))
  Real.log q * (α + β * Real.log ((α + 2 * β + 1) ^ 2))

def AmpleHS : Prop :=
  ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (P : Pair p) (a : ℝ), IsAmpleLB P.L.B → P.L.SemiPos D → P.L.IsSelfInter a →
      ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
        Tendsto (fun m : ℕ => P.lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1)) atTop
          (𝓝 ((a + ((D : ℝ) + 1) * t * gdeg P.L D) / ((D + 1).factorial : ℝ)))

def SemiPull : Prop :=
  ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ), IsArithVar p D → IsArithVar q E →
    ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p), L.SemiPos D → (L.pull π hπ).SemiPos E

theorem shiftA_H (P : Pair p) (u : ℝ) (a b : ℤ) : (shiftA P u).H a b = P.H a b := rfl

end GlobalTheory.HSNef
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
set_option autoImplicit false

noncomputable section

open MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.ChartGlue GlobalTheory.HermFrame GlobalTheory.GoodMetric

namespace GlobalTheory.GoodTop

variable {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]

abbrev EndValuedForm11Coeffs (n : ℕ) (r : Type) : Type := Fin n → Fin n → Matrix r r ℂ

def mixTop (K : Fin n → EndValuedForm11Coeffs n r) : ℂ :=
  (n.factorial : ℂ)⁻¹ * ∑ p : Fin n → r, ∑ π : Equiv.Perm (Fin n), ∑ u : Equiv.Perm (Fin n),
    ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
      (Matrix.of fun i b => K i (u i) b (p i) (p (π i))).det

def intersection_update_fsHerm_neg_one {α : Type} (K₁ L K₀ : α) (j : Fin n) : Fin n → α :=
  fun i => if i < j then K₁ else if i = j then L else K₀

def curvAt (G : V n → Matrix r r ℂ) (v : V n) : EndValuedForm11Coeffs n r :=
  fun a b => curv G v (coordVec a) (coordVec b)

def cutForm (ρ : V n → ℝ) (G₀ G₁ : V n → Matrix r r ℂ) (v : V n) : EndValuedForm11Coeffs n r :=
  fun a b => dbar (fun x => (ρ x : ℂ)) v (coordVec b) • (conn G₁ v (coordVec a) - conn G₀ v (coordVec a))

def corrC (ρ : V n → ℝ) (G₀ G₁ : V n → Matrix r r ℂ) (v : V n) : ℂ :=
  ∑ j : Fin n, mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) (cutForm ρ G₀ G₁ v) (curvAt G₀ v) j)

def corrTop (ρ : V n → ℝ) (G₀ G₁ : V n → Matrix r r ℂ) (v : V n) : ℝ := (Real.pi ^ n)⁻¹ * (corrC ρ G₀ G₁ v).re

def offHyp (S : Finset (Fin n)) (U : Set (V n)) : Set (V n) := {v | v ∈ U ∧ ∀ a ∈ S, v a ≠ 0}

section Glue

variable {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] {κ : Type}

def HasInt (e : κ → OpenPartialHomeomorph Y (V n)) (d : κ → Y → ℝ) (S : Set Y) (t : ℝ) : Prop :=
  (∀ ε : ℤˣ, glueMeas e (fun i y => ENNReal.ofReal ((ε : ℤ) * d i y)) S ≠ ⊤) ∧
    (glueMeas e fun i y => ENNReal.ofReal (((1 : ℤˣ) : ℤ) * d i y)).real S -
      (glueMeas e fun i y => ENNReal.ofReal (((-1 : ℤˣ) : ℤ) * d i y)).real S = t

structure IsTopForm (e : κ → OpenPartialHomeomorph Y (V n)) (d : κ → Y → ℝ) (S : Set Y) : Prop where
  trans : ∀ i j y, y ∈ S → y ∈ (e i).source → y ∈ (e j).source → d i y = ‖transDet (e i) (e j) y‖ ^ 2 * d j y
  meas : ∀ i, AEMeasurable (fun v => d i ((e i).symm v)) (volume.restrict ((e i).target ∩ (e i).symm ⁻¹' S))

end Glue

section Var

open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle

variable {F : Type} [Field F] {X : Var F} {σ : F →+* ℂ} {m : ℕ}

def topDens (E : Fr (ratOf X) (fun _ : Unit => m) 0)
    (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ)
    (c : AlgChart X.str σ X.dim) (y : CxPts X.str σ) : ℝ :=
  chernTop (MvPolynomial.X ((), X.dim)) (fun v => H (E.nonempty (under y)).choose (c.e.symm v)) (c.e y)

def corrDens (E : Fr (ratOf X) (fun _ : Unit => m) 0)
    (H₀ H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ) (ρ : CxPts X.str σ → ℝ)
    (c : AlgChart X.str σ X.dim) (y : CxPts X.str σ) : ℝ :=
  corrTop (fun v => ρ (c.e.symm v)) (fun v => H₀ (E.nonempty (under y)).choose (c.e.symm v) ())
    (fun v => H (E.nonempty (under y)).choose (c.e.symm v) ()) (c.e y)

structure GoodPatch (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens)
    (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ)
    (e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)) (S : Finset (Fin X.dim)) (A : Mat (fun _ : Unit => m) X.Fn)
    (W : Set (CxPts X.str σ)) (c : ℝ) : Prop where
  holo : IsHoloChart e
  isOpen : IsOpen W
  sub : W ⊆ e.source
  frame : ∀ z ∈ W, A ∈ E.S (under z)
  small : ∀ z ∈ W, ∀ a ∈ S, ‖e z a‖ ≤ 1 / 2
  mem : ∀ z ∈ W, z ∈ ptsIn X.str σ O ↔ ∀ a ∈ S, e z a ≠ 0
  form : ∀ z ∈ W, z ∈ ptsIn X.str σ O → ∀ a i j,
    ‖conn (fun v => H A (e.symm v) ()) (e z) (coordVec a) i j‖ * poinWt S (e z) a ≤ c
  dbar : ∀ z ∈ W, z ∈ ptsIn X.str σ O → ∀ a b i j,
    ‖curv (fun v => H A (e.symm v) ()) (e z) (coordVec a) (coordVec b) i j‖ * (poinWt S (e z) a * poinWt S (e z) b) ≤ c

theorem hasChernIntegral_iff (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens)
    (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ) (t : ℝ) :
    HasChernIntegral E O H (MvPolynomial.X ((), X.dim)) t ↔
      HasInt (fun c : AlgChart X.str σ X.dim => c.e) (topDens E H) (ptsIn X.str σ O) t := Iff.rfl

end Var

end GlobalTheory.GoodTop
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.Tpr
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep Formalism.REAL

namespace GlobalTheory.WigAlg

def cx {E : Type} [Field E] {a : ℕ} {N : Type} [AddCommGroup N] [Module ℂ N] (τ : E →+* ℂ) (φ : Lie E a → N)
    (i j : Fin a) : N :=
  (1 / 2 : ℂ) • (φ (toL (Matrix.single i j (atEmb τ 1))) - Complex.I • φ (toL (Matrix.single i j (atEmb τ Complex.I))))

end GlobalTheory.WigAlg

end
end
