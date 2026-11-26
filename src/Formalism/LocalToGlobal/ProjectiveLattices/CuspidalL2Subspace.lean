module

public import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort

@[expose] public section

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Core (D : D7) : Type 1 where
  Q : Par D
  U : ∀ j (σ : Q.c.F →+* ℂ), Unf (Q.Xo j) Q.c σ D.R.r
  V : ℕ → (Q.c.F →+* ℂ) → HSp D
  dict : ∀ j σ, GA D (V j σ) → Σ k, Frame ((U j σ).X k).Ψ D.R.r
  mu : ∀ j σ, GA D (V j σ) → ℂ
  Kf : ∀ j σ, Subgroup (GA D (V j σ))
  pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)

variable {D : D7}

def latHat (V : HSp D) : AddSubgroup (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {z | ∃ a : Af D.host.F, (∀ v, a v ∈ v.adicCompletionIntegers D.host.F) ∧
    ∃ x ∈ V.L0, z = fun i => a ⊗ₜ V.frame.repr x i}

def IsLevelK (V : HSp D) (N : ℕ) (Kf : Subgroup (GA D V)) : Prop :=
  ∀ k, k ∈ Kf ↔ k ∈ GfC V ∧ ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y

def xiR (D : D7) : ℝ := ‖D.host.φ₀ D.host.xi0‖

namespace Core

variable (T : Core D)

def σ₀ : T.Q.c.F →+* ℂ := T.Q.c.F.val.toRingHom

theorem good_σ₀ : GoodEmb T.Q.c T.σ₀ := rfl

abbrev R (j : ℕ) : Type := Rul (T.Q.Xo j) T.Q.c

abbrev cuspA (j : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Submodule T.Q.c.F (T.R j) :=
  cusp (T.Q.Xo j) T.Q.c (T.U j) a n

abbrev X₀ (j : ℕ) : (T.U j T.σ₀).Comp → Data D.host.E D.R.r := (T.U j T.σ₀).X

def frI (_T : Core D) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E := 1

abbrev PtM (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) : Type :=
  valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la

def nrmM (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtM j la) (f : T.R j) : ℝ := nrmOf la (y.1 f)

theorem nrmM_le_one_iff (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtM j la) (f : T.R j) :
    T.nrmM j la y f ≤ 1 ↔ 0 ≤ y.1 f := by
  unfold nrmM nrmOf
  have hy := y.2
  unfold valSet at hy
  obtain ⟨x, hx⟩ := hy
  unfold vAtV at hx
  obtain ⟨T1, io, e, -, y', -, eta, -, hxe⟩ := x.2
  rw [hxe] at hx
  unfold profI at hx
  have key : y.1 f = nval T1.V e (evI y' f) := by rw [← hx]
  unfold nval at key
  have hN : (1 : ℝ) < (Ideal.absNorm la.asIdeal : ℝ) := by
    have h0 : Ideal.absNorm la.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact la.ne_bot
    have h1 : Ideal.absNorm la.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact la.isPrime.ne_top
    exact_mod_cast (by omega : 1 < Ideal.absNorm la.asIdeal)
  rw [key]
  by_cases hz : evI y' f = 0
  · simp [hz]
  · simp only [hz, if_false, EReal.coe_ne_top, EReal.toReal_coe, EReal.coe_nonneg]
    constructor
    · intro h
      by_contra hneg
      exact absurd h (not_le.mpr (Real.one_lt_rpow hN (neg_pos.mpr (not_le.mp hneg))))
    · intro h
      exact Real.rpow_le_one_of_one_le_of_nonpos hN.le (neg_nonpos.mpr h)

def phiAd (j : ℕ) (σ : T.Q.c.F →+* ℂ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) : GA D (T.V j σ) → ℂ :=
  (lieFac (T.Q.Dw j) (xiR D) a : ℂ) • adel (T.V j σ) (T.dict j σ) (T.mu j σ) (rdU (T.U j σ) f)

end Core

structure LawsM (T : Core D) : Prop where

  pins : T.Q.Pins

  half : (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (T.pb k).asIdeal) ∧
    T.Q.l.Mb = ∏ k, (T.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

  evalWD : ∀ j, InR D j → EvalWD (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z)

  unf : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → IsUnf (T.U j σ)

  unTest : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k x,
    FromTest (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) ((T.U j σ).un k x)
  chiTriv : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ a n, Dom a n → ∀ k, ∀ γ ∈ ((T.U j σ).X k).Γ,
    ((T.U j σ).X k).χ (laU (T.U j σ) a n k) γ = 1

  dictU : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
    DictIsUnif (T.V j σ) (T.dict j σ) (T.Kf j σ) th hr

  spaceW : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → T.V j σ = D.sp.W j
  levelK : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → IsLevelK (T.V j σ) (D.host.g 0 * D.host.g 1) (T.Kf j σ)

  xiAbs : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k (τ : D.host.E →+* ℂ), ‖τ ((T.U j σ).X k).ξ0‖ = xiR D
  muUnit : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → MuUnit (T.V j σ) (T.dict j σ) (T.mu j σ)
  muCont : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → Continuous (T.mu j σ)
  finVol : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → FinVol (T.V j σ)

  cuspFD : ∀ j, InR D j → CuspFD (T.Q.Xo j) T.Q.c (T.U j)

  supDef : ∀ j, InR D j → SupDef (T.Q.Xo j) T.Q.c (T.U j)

  cuspidalL2Subspace : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → CuspL2 (T.U j) σ (T.V j σ) (T.dict j σ) (T.mu j σ)
  l2Def : ∀ j (hj : InR D j) σ (hσ : GoodEmb T.Q.c σ),
    L2DefiniteCuspForms (T.U j) σ (T.V j σ) (T.dict j σ) (T.mu j σ) (cuspidalL2Subspace j hj σ hσ)

  unitIndep : ∀ j, InR D j → UnitIndep (T.Q.Xo j) T.Q.c
  ptNe : ∀ j, InR D j → IntFrNe (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c)

structure LawsCore (T : Core D) : Prop extends LawsM T where

  cuspMul : ∀ j, InR D j → CuspMul (T.Q.Xo j) T.Q.c (T.U j)

  latZ : ∀ j, InR D j → FJ.LatZ (T.X₀ j) (WeightFamilies.rho D j)
  cuNe : ∀ j, InR D j → FJ.CuNeF (T.X₀ j) (WeightFamilies.rho D j)
  expo : ∀ j, InR D j → FJ.ExpoMatch (T.X₀ j) T.frI (WeightFamilies.rho D j) (D.host.g 0 * D.host.g 1)

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def trivialClassCondition (T : CDVR) (io : c.F →+* T.Fr) (_y : IntFr Xo c T io) : Prop := True

theorem valSet_alg_subset (la : HeightOneSpectrum (𝓞 c.F)) :
    valSet Xo c (algCls Xo c) la ⊆ valSet Xo c (trivialClassCondition Xo c) la := by

  unfold valSet
  rintro v ⟨⟨x, hx⟩, rfl⟩
  refine ⟨⟨x, ?_⟩, rfl⟩
  obtain ⟨T, io, e, h1, y, -, h2⟩ := hx
  exact ⟨T, io, e, h1, y, trivial, h2⟩

def trivSet : Set (Rul Xo c → EReal) :=
  {q | ∃ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io),
    (∀ a : c.F, a ≠ 0 → vV T.V (io a) = 0) ∧ q = fun f => nval T.V 1 (evI y f)}

def NoCommonZero {n : ℕ} (ws : Fin n → Rul Xo c) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y : FrPt Xo c k), ∃ i, evR Xo c (ws i) y ≠ 0

abbrev DomWt (E : Type) [Field E] : Type := {x : ((E →+* ℂ) × ℕ → ℕ) × ℕ // Dom x.1 x.2}

def regular₂ {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : Prop :=
  ReciprocityTheory.ChartRestriction.G.T0.RegLaw (Λ := HeightOneSpectrum (𝓞 c.F)) (Wt := DomWt E)
    (fun w => cusp Xo c U w.1.1 w.1.2)
    (fun la => valSet Xo c (algCls Xo c) la) (fun la => valSet Xo c (trivialClassCondition Xo c) la)
    (fun la v => ⟨v.1, valSet_alg_subset Xo c la v.2⟩) (fun _ v _ F => v.1 F.1)
    (trivSet Xo c) (fun q _ F => q.1 F.1) (fun ws => NoCommonZero Xo c fun i => (ws i).1) ∧
  ∀ a n, Dom a n → ∀ (m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ cusp Xo c U a n) → NoCommonZero Xo c ws →
    ∀ nu : HeightOneSpectrum (𝓞 c.F) → ℝ,
      (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, (⨅ i, v (ws i)) ≤ (nu la : EReal)) →
        ∀ la, ∀ v ∈ valSet Xo c (trivialClassCondition Xo c) la, (⨅ i, v (ws i)) ≤ (nu la : EReal)

variable {Xo c}

theorem regular₂.int {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} (h : regular₂ Xo c U) {a n} (hd : Dom a n)
    {f : Rul Xo c} (hf : f ∈ cusp Xo c U a n)
    (h0 : ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) :
    ∀ la, ∀ v ∈ valSet Xo c (trivialClassCondition Xo c) la, 0 ≤ v f := by
  intro la v hv
  have h1 := h.1
  unfold ReciprocityTheory.ChartRestriction.G.T0.RegLaw at h1
  exact (h1.1 ⟨(a, n), hd⟩ ⟨f, hf⟩ (fun la' y => h0 la' y.1 y.2)).1 la ⟨v, hv⟩

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.IntAll
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

def IntAll : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → T.FinRes →
    ∀ y : (letI := io.toAlgebra; FrPt Xo c T.Fr),
      ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (e' : ℕ) (y' : IntFr Xo c T' io'), OverLa la T'.V io' e' ∧ y'.IsAlg ∧
        letI := io.toAlgebra; letI := io'.toAlgebra
        ∃ (φ : T.Fr →ₐ[c.F] T'.Fr) (z : FrPt Xo c T'.Fr) (t : Ix Dw → T'.Frˣ),
          (∀ a : T.V, φ (algebraMap T.V T.Fr a) ∈ Set.range (algebraMap T'.V T'.Fr)) ∧ FrMap φ y z ∧ FrBor t z y'.1

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
noncomputable section

namespace Formalism.L2.Pj

open scoped TensorProduct
open MeasureTheory
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem pnorm_of_eq_zero (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) (h : P x = 0) :
    X.pnorm la P x = 0 := by
  unfold Data.pnorm
  rw [h, norm_zero, zero_mul]

end Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

variable {Xo c}

variable {D : D7} (σ : c.F →+* ℂ) (V : HSp D) (dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r) (mu : GA D V → ℂ)

def AdelMeas : Prop :=
  ∀ (la : ∀ k, Wt ((U σ).X k).Ψ r) (P : FDSec (U σ).X), IsHolCusp (U σ).X la P →
    AEStronglyMeasurable (onQ V (adel V dict mu P)) (muQ1 V)

def AeDom : Prop :=
  ∀ (la : ∀ k, Wt ((U σ).X k).Ψ r) (P : FDSec (U σ).X), P ∈ holSub (U σ).X la →
    onQ V (adel V dict mu P) =ᵐ[muQ1 V] 0 → ∀ k, ∀ x ∈ ((U σ).X k).dom, P k x = 0

variable {U σ V dict mu}

theorem aesm_of_holSub (hm : AdelMeas U σ V dict mu) (la : ∀ k, Wt ((U σ).X k).Ψ r) {P : FDSec (U σ).X}
    (hP : P ∈ holSub (U σ).X la) : AEStronglyMeasurable (onQ V (adel V dict mu P)) (muQ1 V) := by
  induction hP using Submodule.span_induction with
  | mem P hP => exact hm la P hP
  | zero => rw [map_zero, map_zero]; exact aestronglyMeasurable_const
  | add P Q _ _ h1 h2 => rw [map_add (f := _), map_add (f := _)]; exact h1.add h2
  | smul a P _ h1 => rw [map_smul, map_smul]; exact h1.const_smul a

theorem cusp_L2_of_measurable (hσ : GoodEmb c σ) (hd : ∀ g, (dict g).2 ∈ ((U σ).X (dict g).1).dom)
    (hmu : MuUnit V dict mu) (hm : AdelMeas U σ V dict mu) : CuspL2 U σ V dict mu := by
  intro a n _ f
  have hhol : rdU (U σ) (f : Rul Xo c) ∈ holSub (U σ).X (laU (U σ) a n) :=
    ((mem_cusp Xo c U a n f).1 f.2).2 σ hσ
  have hfin := supE_cusp_ne_top hσ f.2
  show MemLp (onQ V (adel V dict mu (rdU (U σ) (f : Rul Xo c)))) 2 (muQ1 V)
  refine MemLp.of_bound (aesm_of_holSub hm _ hhol) (supN (U σ).X (laU (U σ) a n) (rdU (U σ) (f : Rul Xo c)))
    (Filter.Eventually.of_forall fun q => ?_)
  set g := q.out
  show ‖mu g * rdU (U σ) (f : Rul Xo c) (dict g).1 (dict g).2‖ ≤ _
  rw [norm_mul, hmu.2.1 g, one_mul, ← pnorm_eq_of_unit ((U σ).X (dict g).1) (laU (U σ) a n (dict g).1)
    (rdU (U σ) (f : Rul Xo c) (dict g).1) (dict g).2 (hmu.2.2.2 g)]
  show _ ≤ (supE (U σ).X (laU (U σ) a n) (rdU (U σ) (f : Rul Xo c))).toReal
  rw [← ENNReal.ofReal_le_iff_le_toReal hfin]
  exact le_iSup (fun p : FPt (U σ).X => ENNReal.ofReal (((U σ).X p.1).pnorm (laU (U σ) a n p.1)
    (rdU (U σ) (f : Rul Xo c) p.1) p.2)) ⟨(dict g).1, ⟨(dict g).2, hd g⟩⟩

theorem l2Def_of_cusp (hσ : GoodEmb c σ) (hsup : SupDef Xo c U) (hae : AeDom U σ V dict mu)
    (h : CuspL2 U σ V dict mu) : L2DefiniteCuspForms U σ V dict mu h := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro a n hdom f h0
    have hhol : rdU (U σ) (f : Rul Xo c) ∈ holSub (U σ).X (laU (U σ) a n) :=
      ((mem_cusp Xo c U a n f).1 f.2).2 σ hσ
    have hz : (h a n hdom f).toLp _ = 0 := norm_eq_zero.1 h0
    have hz' : jFn V σ (rdC U σ a n) dict mu f =ᵐ[muQ1 V] 0 :=
      (MemLp.coeFn_toLp (h a n hdom f)).symm.trans (Lp.eq_zero_iff_ae_eq_zero.1 hz)
    have hv := hae (laU (U σ) a n) (rdU (U σ) (f : Rul Xo c)) hhol hz'
    have hE : supE (U σ).X (laU (U σ) a n) (rdU (U σ) (f : Rul Xo c)) = 0 := by
      refine le_antisymm (iSup_le fun p => ?_) zero_le
      rw [pnorm_of_eq_zero _ _ _ _ (hv p.1 p.2 p.2.2), ENNReal.ofReal_zero]
    have hN : supN (U σ).X (laU (U σ) a n) (rdU (U σ) (f : Rul Xo c)) = 0 := by
      unfold supN
      rw [hE, ENNReal.toReal_zero]
    exact Subtype.ext (hsup a n hdom σ hσ f f.2 hN)

theorem dict_dom_of {Comp : Type} {X : Comp → Data E r} {V : HSp D} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {Kf : Subgroup (GA D V)} {th} {hr}
    (h : DictIsUnif V dict Kf th hr) : ∀ g, (dict g).2 ∈ (X (dict g).1).dom :=
  h.2.2.2.1

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def offZero {Comp : Type} (X : Comp → Data E r) : Submodule ℂ (FDSec X) where
  carrier := {P | ∀ k x, x ∉ (X k).dom → P k x = 0}
  zero_mem' _ _ _ := rfl
  add_mem' hP hQ k x hx := by simp [hP k x hx, hQ k x hx]
  smul_mem' a P hP k x hx := by simp [hP k x hx]

def holSub0 {Comp : Type} (X : Comp → Data E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) : Submodule ℂ (FDSec X) :=
  holSub X la ⊓ offZero X

variable {Xo c} in
theorem rdU_mem_offZero {σ : c.F →+* ℂ} (V : Unf Xo c σ r) (f : Rul Xo c) : rdU V f ∈ offZero V.X :=
  fun _ _ hx => dif_neg hx


end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ThClass
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD NumberField
open MvPolynomial Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def thLaValAt (nab : NabV Xo c) {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) (La : GenLat E n) (N : ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) : Prop :=
  ShortValAt Xo c nab w La 1 N P y v

abbrev LevQc (Dw : Datum H) (l : Level H) : Type := Dw.La ⧸ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)

def phiHat {n : ℕ} (φ : (Fin n → LevQc Dw l) → c.F) : (Fin n → LevQ Dw l) → c.F :=
  fun q => ∑ᶠ x : Fin n → LevQc Dw l, φ x * zetaM c ^ pairL (l := l) (fun b => qRep (x b)) (fun b => levRep (q b))

def indPhi {n : ℕ} (x0 : Fin n → LevQc Dw l) : (Fin n → LevQc Dw l) → c.F :=
  open Classical in fun x => if x = x0 then 1 else 0

section Cls

variable {n : ℕ} {Cl : Type} [Fintype Cl] {Vs : Type} [AddCommGroup Vs] [Module c.F Vs]

def ThClsValAt (nab : NabV Xo c) (w : Cl → (Fin n → LevQ Dw l) → c.F) (La : Cl → GenLat E n) (Nc : Cl → ℕ)
    (gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (xi : Rul Xo c) (x : Cl → Vs)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) : Prop :=
  ∃ vc : Cl → S, (∀ k, thLaValAt Xo c nab (w k) (La k) (Nc k) (io (x k)) y (vc k)) ∧
    v = evR Xo c xi y * ∑ k, algebraMap c.F S (vol * ((gam k : c.F))⁻¹ * ep k) * vc k

def GenLat.SplitSupp (H : Host E) (Λ : GenLat E n) : Prop :=
  ∃ m : 𝓞 E, m ≠ 0 ∧ Ideal.span {m} • Λ.La ≤ stdLat E n ∧ Ideal.span {m} • stdLat E n ≤ Λ.La ∧
    ∀ P : Ideal (𝓞 E), P.IsPrime → m ∈ P → P.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ P

def RepsOK (bad : ℕ) (La : Cl → GenLat E n) (Nc : Cl → ℕ) (gam : Cl → ℕ) : Prop :=
  ∀ k, (La k).Unimod ∧ (La k).TrivAt bad ∧ (La k).TrivAt l.M ∧ (La k).LevOK (Nc k) l.M ∧ 0 < gam k ∧
    GenLat.SplitSupp H (La k)

end Cls

def gaStar {n : ℕ} (ga : Matrix (Fin n) (Fin n) E) : MvPolynomial (LtN Dw n) c.F →ₐ[c.F] MvPolynomial (LtN Dw n) c.F :=
  aeval fun ℓ => letB (Dw := Dw) c ℓ.1 ℓ.2.1 (fun j => ga j ℓ.2.2)

def minorPolynomial {n : ℕ} (σ : E →+* ℂ) (i : ℕ) (hi : i < Dw.mult σ) (col : Fin (i + 1) → Fin n) :
    MvPolynomial (LtN Dw n) c.F :=
  Matrix.det (Matrix.of fun s b : Fin (i + 1) => X (⟨σ, ⟨s.val, by omega⟩, col b⟩ : LtN Dw n))

def aStep (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (σ : E →+* ℂ) (i : ℕ) : ℕ :=
  a (σ, i) - (if i + 1 < Dw.mult σ then a (σ, i + 1) else 0)


open Classical in
def pG (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : MvPolynomial (LtN Dw n) c.F :=
  ∏ σ : E →+* ℂ, ∏ i : Fin (Dw.mult σ),
    (if h : i.val + 1 ≤ n then
      (if InPsi H σ then minorPolynomial c σ i.val i.isLt (Fin.castLE h)
        else minorPolynomial c σ i.val i.isLt (fun b => Fin.cast (by omega) (Fin.natAdd (n - (i.val + 1)) b)))
      else 0) ^ aStep Dw a σ i.val

def idlE (I : Ideal (𝓞 E)) : Submodule (𝓞 E) E := Submodule.map (Algebra.linearMap (𝓞 E) E) I

def EpIs {n : ℕ} (bad : ℕ) (B : Ideal (𝓞 E) → c.F) (epF : Submodule (𝓞 E) (Fin n → E) → c.F) : Prop :=
  ∀ (L : Submodule (𝓞 E) (Fin n → E)) (cc : Ideal (𝓞 E)),
    (⟨L⟩ : GenLat E n).Unimod → (⟨L⟩ : GenLat E n).TrivAt bad → GenLat.SplitSupp H (⟨L⟩ : GenLat E n) →
    cc ⊔ cc.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ →
    Submodule.span (𝓞 E) (detSet L) * idlE (cc.map (H.bar : 𝓞 E →+* 𝓞 E)) = idlE cc →
    ∃ q : ℚ, 0 < q ∧
      q ^ 2 * (((L ⊓ stdLat E n).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index : ℚ) ^ (Dw.p + Dw.q) =
        (Ideal.absNorm cc : ℚ) ∧
      epF L = (B cc)⁻¹ * (q : c.F)

section Io

variable {n : ℕ} {Vs : Type} [AddCommGroup Vs] [Module c.F Vs] [Module (𝓞 c.F) Vs] [IsScalarTower (𝓞 c.F) c.F Vs]

def IoLF (a : (E →+* ℂ) × ℕ → ℕ) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
    (rho : Matrix (Fin n) (Fin n) E → Vs →ₗ[c.F] Vs) (cga : Matrix (Fin n) (Fin n) E → c.F)
    (nab0 : Submodule (𝓞 c.F) Vs) (hw : Vs) (pG : MvPolynomial (LtN Dw n) c.F) : Prop :=
  Dw.p + Dw.q ≤ n ∧ Function.Injective io ∧
  LinearMap.range io = Submodule.span c.F (HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H)
    (fun τ i => a (τ, i))) ∧
  (∀ ga : Matrix (Fin n) (Fin n) E, ga.conjTranspose * ga = 1 → ∀ v, io (rho ga v) = cga ga • gaStar c (ga.map (IsCMField.complexConj E)) (io v)) ∧
  hw ∈ nab0 ∧ (∀ s : c.F, s • hw ∈ nab0 → ∃ o : 𝓞 c.F, s = (o : c.F)) ∧ io hw = pG ∧
  harmA (Dw := Dw) c a n ⊆ io '' (nab0 : Set Vs)

def LatPin {Cl : Type} (Lh : Cl → Submodule (𝓞 E) (Fin n → E)) (La : Cl → GenLat E n) : Prop :=
  ∀ k (v : Fin n → E), v ∈ (La k).La ↔ (fun j => IsCMField.complexConj E (v j)) ∈ Lh k

end Io

section Ep

variable {n : ℕ} {Cl : Type}

end Ep

section Row

variable {n : ℕ} {Cl : Type} [Fintype Cl] {Vs : Type} [AddCommGroup Vs] [Module c.F Vs]

def OneMod {n : ℕ} (lev : ℕ) (ga : Matrix (Fin n) (Fin n) E) : Prop :=
  ∃ k : ℕ, Nat.Coprime k lev ∧ ∀ i j, ∃ o : 𝓞 E, (k : E) * (ga - 1) i j = (lev : E) * (o : E)

def IsThClsD (dδ : DeltaDat Xo c n) (w : Cl → (Fin n → LevQ Dw dδ.l₂) → c.F) (La : Cl → GenLat E n) (Nc : Cl → ℕ)
    (gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (x : Cl → Vs)
    (f : Rul Xo c) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra dδ.c₂.F k],
    (∀ a : c.F, algebraMap dδ.c₂.F k (dδ.eF a) = algebraMap c.F k a) →
    ∀ (y : FrPt Xo c k) (y₂ : FrPt dδ.Xo₂ dδ.c₂ k), FrOver dδ y₂ y →
      ∃ vc : Cl → k, (∀ cl, thLaValAt dδ.Xo₂ dδ.c₂ dδ.nab₂ (fun q => dδ.eF (w cl q)) (La cl) (Nc cl)
          (MvPolynomial.map (dδ.eF : c.F →+* dδ.c₂.F) (io (x cl))) y₂ (vc cl)) ∧
        evR Xo c f y = evR dδ.Xo₂ dδ.c₂ dδ.cδ y₂ *
          ∑ cl, algebraMap c.F k (vol * ((gam cl : c.F))⁻¹ * ep cl) * vc cl

def OneMapRow {D : D7} (V : HSp D) {σ0 : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ0 r)
    (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (mu : GA D V → ℂ) (xr : ℝ) (a : (E →+* ℂ) × ℕ → ℕ)
    {G : Type} [Group G] (act : G → Rul Xo c →ₗ[c.F] Rul Xo c) {Tup : Type*} (dδ : Tup → DeltaDat Xo c n)
    (Cl' : Tup → Type) [∀ t, Fintype (Cl' t)]
    (w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c.F) (La : ∀ t, Cl' t → GenLat E n) (Nc : ∀ t, Cl' t → ℕ)
    (gam : ∀ t, Cl' t → ℕ) (vol : Tup → c.F) (ep : ∀ t, Cl' t → c.F) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
    (thAd : ∀ t, (Cl' t → Vs) → (AutQ V → ℂ)) (Pl : ∀ t, (Cl' t → Vs) → Prop) (LL : IntermediateField ℚ ℂ)
    (Cu : Submodule c.F (Rul Xo c)) (cc : U.Comp → ℂ) (ph : ℂ) : Prop :=
  (∀ k, ‖cc k‖ = 1) ∧ ‖ph‖ = 1 ∧ ∃ z : G, z ∈ Subgroup.center G ∧
    ∀ t : Tup, ∃ ze : ℂ, ze ∈ LL ∧ (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧ ∀ x : Cl' t → Vs, Pl t x →
      (∃ f ∈ Cu, IsThClsD Xo c (dδ t) (w t) (La t) (Nc t) (gam t) (vol t) (ep t) io x f) ∧
      (∀ f ∈ sec Xo c a n, IsThClsD Xo c (dδ t) (w t) (La t) (Nc t) (gam t) (vol t) (ep t) io x f →
        ∀ q : AutQ V, ph * thAd t x q =
          ze * cc (dict q.out).1 * (lieFac Dw xr a : ℂ) * jFn V σ0 (rdU U) dict mu (act z f) q)

end Row

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ArcTheta
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}


set_option maxHeartbeats 400000 in
theorem frame_of_gen (Xo : Moduli Dw l) {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (t' : SAB H (Sp S))
    (m1 : SABMap t' Xo.univ.t x) (σ' : LB.Sec t'.PP.L)
    (hgen : ∀ s' : LB.Sec t'.PP.L, ∃! a : S, ∀ i, s'.f i = constFn t'.G.hom _ a * σ'.f i) :
    ∃ (s : LB.Sec (PPx x)) (w1 : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m1.φ)) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m1.φ)),
      RigIso m1 w1 ∧ IsoMaps w1 σ' s1 ∧
      (∀ g : t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m1.φ →
        g ≫ (fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom →
        ∀ j (h : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)),
          s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))) ∧
      ∀ s'' : LB.Sec (PPx x), ∃! a : S, ∀ i, s''.f i = scal x a i * s.f i := by
  obtain ⟨w1, hw1, hrig, -⟩ := m1.lin
  have hPG := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff w1).1 hw1
  obtain ⟨s1, hs1⟩ := thf_secUp hPG Xo.univ.t.PP.isLB t'.PP.isLB σ'
  have pb := m1.cart.1
  have hcond : (snd (Over.mk x) Xo.univ.t.G).left ≫ Xo.univ.t.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ x :=
    (Over.w (snd (Over.mk x) Xo.univ.t.G)).trans (Over.w (fst (Over.mk x) Xo.univ.t.G)).symm
  obtain ⟨h, hF, hS⟩ : ∃ h : Gx x ⟶ t'.G.left, h ≫ m1.φ = (snd (Over.mk x) Xo.univ.t.G).left ∧
      h ≫ t'.G.hom = (fst (Over.mk x) Xo.univ.t.G).left :=
    ⟨pb.lift _ _ hcond, pb.lift_fst _ _ hcond, pb.lift_snd _ _ hcond⟩
  obtain ⟨g0, g0F, g0S, hhg⟩ : ∃ g0 : t'.G.left ⟶ Gx x, g0 ≫ (snd (Over.mk x) Xo.univ.t.G).left = m1.φ ∧
      g0 ≫ (fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom ∧ h ≫ g0 = 𝟙 _ := by
    let P : Over Xo.X := Over.mk (m1.φ ≫ Xo.univ.t.G.hom)
    let a : P ⟶ Over.mk x := Over.homMk t'.G.hom pb.w.symm
    let b : P ⟶ Xo.univ.t.G := Over.homMk m1.φ rfl
    let hO : (Over.mk x ⊗ Xo.univ.t.G) ⟶ P := Over.homMk h (by
      show h ≫ m1.φ ≫ Xo.univ.t.G.hom = _
      rw [← Category.assoc, hF]
      exact Over.w (snd (Over.mk x) Xo.univ.t.G))
    have e : hO ≫ lift a b = 𝟙 _ := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, lift_fst, Category.id_comp]
        ext
        exact hS
      · rw [Category.assoc, lift_snd, Category.id_comp]
        ext
        exact hF
    exact ⟨(lift a b).left, congrArg (fun f => f.left) (lift_snd (f := a) (g := b)),
      congrArg (fun f => f.left) (lift_fst (f := a) (g := b)), congrArg (fun f => f.left) e⟩
  have hgh0 : g0 ≫ h = 𝟙 _ := pb.hom_ext
    (by rw [Category.assoc, hF, g0F, Category.id_comp])
    (by rw [Category.assoc, hS, g0S, Category.id_comp])
  refine ⟨thfPull1 Xo.univ.t.PP.L h hF s1, w1, s1, ⟨hw1, hrig⟩, ?_, ?_, ?_⟩
  · intro i k
    refine fn_ext fun y hy => ?_
    have key := hs1 _ (𝟙 _) y i k hy.1 hy.2
    rw [gs_res (𝟙 _) y _ hy, key, gs_mul (𝟙 _) y _ hy, gs_res (𝟙 _) y _ hy]
    congr 1
    exact (gs_unit (𝟙 _) y _ hy (w1.s (i, k))).symm
  · intro g hgs hgf j hj
    have hgh : g ≫ h = 𝟙 _ := pb.hom_ext
      (by rw [Category.assoc, hF, hgs, Category.id_comp])
      (by rw [Category.assoc, hS, hgf, Category.id_comp])
    refine fn_ext fun y hy => ?_
    have e1 := gs_appLE g _ _ hj (𝟙 _) y hy ((thfPull1 Xo.univ.t.PP.L h hF s1).f (fun _ => j PUnit.unit))
    have e2 : gs g y ((PPx x).U (fun _ => j PUnit.unit)) ((thfPull1 Xo.univ.t.PP.L h hF s1).f (fun _ => j PUnit.unit)) =
        gs (g ≫ h) y _ (s1.f (fun _ => j PUnit.unit)) :=
      gs_appLE h _ _ _ g y (hj hy) _
    rw [Category.id_comp] at e1
    rw [e1, e2, hgh]
    all_goals rfl
  · intro s''
    have hle : ∀ j, m1.φ ⁻¹ᵁ Xo.univ.t.PP.L.U j ≤ g0 ⁻¹ᵁ (PPx x).U (fun _ => j) := by
      intro j y hy
      have e : (g0 ≫ (snd (Over.mk x) Xo.univ.t.G).left) y ∈ Xo.univ.t.PP.L.U j := by
        rw [g0F]
        exact hy
      show g0.base y ∈ (⋂ k : Fin 1, ((snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U j : Set _)))
      exact Set.mem_iInter.2 fun _ => e
    have mm : ∀ (y : t'.G.left) j, m1.φ y ∈ Xo.univ.t.PP.L.U j → g0 y ∈ (PPx x).U (fun _ => j) :=
      fun y j hj => hle j hj
    have hσ : ∀ (y : t'.G.left) (j j' : Xo.univ.t.PP.L.ι), m1.φ y ∈ Xo.univ.t.PP.L.U j →
        m1.φ y ∈ Xo.univ.t.PP.L.U j' →
        gs (𝟙 _) y _ ((g0.appLE _ _ (hle j)).hom (s''.f (fun _ => j))) =
          (gm m1.φ y (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j')).val *
            gs (𝟙 _) y _ ((g0.appLE _ _ (hle j')).hom (s''.f (fun _ => j'))) := by
      intro y j j' hj hj'
      have e1 := gs_appLE g0 _ _ (hle j) (𝟙 _) y (show y ∈ m1.φ ⁻¹ᵁ Xo.univ.t.PP.L.U j from hj) (s''.f (fun _ => j))
      have e2 := gs_appLE g0 _ _ (hle j') (𝟙 _) y (show y ∈ m1.φ ⁻¹ᵁ Xo.univ.t.PP.L.U j' from hj')
        (s''.f (fun _ => j'))
      have e3 := gs_compat s'' g0 y (mm y j hj) (mm y j' hj')
      have e4 := gm_linComb Xo.univ.t.PP.L (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left) (fun _ => (1 : ℤ))
        g0 y (fun _ => j) (fun _ => j') (mm y j hj) (mm y j' hj')
      simp only [Fin.prod_univ_one, zpow_one, g0F] at e4
      rw [e1, e2, Category.id_comp, e3]
      erw [e4]
    obtain ⟨σ'', hσ''⟩ := sec_down hPG Xo.univ.t.PP.isLB t'.PP.isLB
      (fun j => (g0.appLE _ _ (hle j)).hom (s''.f (fun _ => j))) hσ
    obtain ⟨a, ha, hau⟩ := hgen σ''
    refine ⟨a, fun i => ?_, fun b hb => hau b ?_⟩
    · obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨i 0, funext fun k => congrArg i (Subsingleton.elim _ _)⟩
      refine fn_ext fun y hy => ?_
      obtain ⟨k, hk⟩ : ∃ k, h y ∈ t'.PP.L.U k := by
        have : h y ∈ ⨆ i, t'.PP.L.U i := by
          rw [t'.PP.isLB.cover]
          trivial
        exact TopologicalSpace.Opens.mem_iSup.1 this
      have hF' : m1.φ (h y) ∈ Xo.univ.t.PP.L.U j := by
        have e : (h ≫ m1.φ) y ∈ Xo.univ.t.PP.L.U j := by
          rw [hF]
          exact LB.wchart_le Xo.univ.t.PP.L (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left) (fun _ => j) 0 hy
        exact e
      have eR1 : gs (𝟙 _) y _ (scal x a (fun _ => j)) = cst (fst (Over.mk x) Xo.univ.t.G).left y a := by
        have := gs_constFn (fst (Over.mk x) Xo.univ.t.G).left ((PPx x).U (fun _ => j)) (𝟙 _) y hy a
        rw [Category.id_comp] at this
        exact this
      have eR2 : gs (𝟙 _) y ((PPx x).U (fun _ => j)) ((thfPull1 Xo.univ.t.PP.L h hF s1).f (fun _ => j)) =
          (gw w1 h y j k).val * gs h y _ (σ'.f k) := by
        have := gs_appLE h _ _ (chart_le_pullback_open Xo.univ.t.PP.L h hF (fun _ => j)) (𝟙 _) y hy (s1.f (fun _ => j))
        rw [Category.id_comp] at this
        exact this.trans (hs1 _ h y (fun _ => j) k (mem_pull.2 hF') hk)
      have eL : gs (𝟙 _) y _ (s''.f (fun _ => j)) =
          (gw w1 h y j k).val * (cst (fst (Over.mk x) Xo.univ.t.G).left y a * gs h y _ (σ'.f k)) := by
        have e5 := gs_appLE g0 _ _ (hle j) h y (show h y ∈ m1.φ ⁻¹ᵁ Xo.univ.t.PP.L.U j from hF') (s''.f (fun _ => j))
        rw [hhg] at e5
        rw [← e5, hσ'' _ h y j k hF' hk, ha k, gs_mul h y _ hk, gs_constFn t'.G.hom _ h y hk a, hS]
      rw [gs_mul (𝟙 _) y _ hy, eR1, eR2, eL, mul_left_comm]
    · intro k
      refine fn_ext fun y hy => ?_
      obtain ⟨j, hj⟩ : ∃ j, m1.φ y ∈ Xo.univ.t.PP.L.U j := by
        have : m1.φ y ∈ ⨆ i, Xo.univ.t.PP.L.U i := by
          rw [Xo.univ.t.PP.isLB.cover]
          trivial
        exact TopologicalSpace.Opens.mem_iSup.1 this
      have e1 := hσ'' _ (𝟙 _) y j k hj hy
      have c1 : gs g0 y _ (scal x b (fun _ => j)) = cst t'.G.hom y b := by
        have := gs_constFn (fst (Over.mk x) Xo.univ.t.G).left ((PPx x).U (fun _ => j)) g0 y (mm y j hj) b
        rw [g0S] at this
        exact this
      have c2 : gs g0 y ((PPx x).U (fun _ => j)) ((thfPull1 Xo.univ.t.PP.L h hF s1).f (fun _ => j)) =
          gs (𝟙 _) y _ (s1.f (fun _ => j)) := by
        have := gs_appLE h _ _ (chart_le_pullback_open Xo.univ.t.PP.L h hF (fun _ => j)) g0 y (mm y j hj) (s1.f (fun _ => j))
        rw [hgh0] at this
        exact this
      have e2 : gs (𝟙 _) y _ ((g0.appLE _ _ (hle j)).hom (s''.f (fun _ => j))) =
          cst t'.G.hom y b * ((gw w1 (𝟙 _) y j k).val * gs (𝟙 _) y _ (σ'.f k)) := by
        rw [gs_appLE g0 _ _ (hle j) (𝟙 _) y (show y ∈ m1.φ ⁻¹ᵁ Xo.univ.t.PP.L.U j from hj), Category.id_comp,
          hb (fun _ => j), gs_mul g0 y _ (mm y j hj), c1, c2, hs1 _ (𝟙 _) y (fun _ => j) k (mem_pull.2 hj) hy]
      have e3 := e1.symm.trans e2
      rw [mul_left_comm] at e3
      rw [gs_mul (𝟙 _) y _ hy, gs_constFn t'.G.hom _ (𝟙 _) y hy b, Category.id_comp]
      exact (Units.mul_right_inj (gw w1 (𝟙 _) y j k)).1 e3

theorem pull_sec {R S : Type} [CommRing R] [CommRing S] (G : SAB H (Sp R)) (t' : SAB H (Sp S)) {f : Sp S ⟶ Sp R}
    (m2 : SABMap t' G f) (θ : LB.Sec G.PP.L) :
    ∃ (w2 : LB.Iso t'.PP.L (G.PP.L.pull m2.φ)) (σ' : LB.Sec t'.PP.L),
      RigIso m2 w2 ∧ IsoMaps w2 σ' (thfPull G.PP.L m2.φ θ) := by
  obtain ⟨w2, hgen, hrig, -⟩ := m2.lin
  obtain ⟨σ', hσ'⟩ := sec_pull_down ((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff w2).1 hgen) G.PP.isLB t'.PP.isLB θ
  refine ⟨w2, σ', ⟨hgen, hrig⟩, fun i k => fn_ext fun y hy => ?_⟩
  have h1 : m2.φ y ∈ G.PP.L.U (i PUnit.unit) := mem_pull.1 hy.1
  have key := hσ' _ (𝟙 _) y (i PUnit.unit) k h1 hy.2
  have hl : gs (𝟙 _) y _ ((thfPull G.PP.L m2.φ θ).f i) = gs (𝟙 _ ≫ m2.φ) y _ (θ.f (i PUnit.unit)) :=
    gs_appLE m2.φ _ _ _ (𝟙 _) y hy.1 _
  rw [gs_res (𝟙 _) y _ hy, hl, key, gs_mul (𝟙 _) y _ hy, gs_res (𝟙 _) y _ hy]
  congr 1
  exact (gs_unit (𝟙 _) y _ hy (w2.s (i, k))).symm

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.DatIndep
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.MainNotions

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

def NabUniq : Prop :=
  ∀ (_ : StarRing (𝓞 E)) (nab nab' : NabV Xo c), IsNab Xo c nab → IsNab Xo c nab' →
    ∀ a n, Dom a n → thGen Xo c nab a n = thGen Xo c nab' a n

def DatIndep : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (Tw Tw' : PointsOfFlagModel.Tower (WeightAlgebra.resCh la) Xo c), PointsOfFlagModel.TowerAt Tw → PointsOfFlagModel.TowerAt Tw' →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io), OverLa la T.V io e → algCls Xo c T io y →
      ∀ z z', LiesOverBaseChange la Tw T io y z → LiesOverBaseChange la Tw' T io y z' →
        ∀ (A : DatAt (Tw.Y z.1) z.2.2.1) (A' : DatAt (Tw'.Y z'.1) z'.2.2.1),
          ∃ f : A.Ylat ≃ₗ[𝓞 E] A'.Ylat, ∀ a b, A'.beta (f a) (f b) = A.beta a b

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.RegularityR2Quotient
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def trivCls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop :=
  fun T ι _ => ∀ a : c.F, a ≠ 0 → ∃ u : T.Vˣ, algebraMap T.V T.Fr (u : T.V) = ι a

structure QPt where
  T : CDVR
  ι : c.F →+* T.Fr
  y : IntFr Xo c T ι
  triv : trivCls Xo c T ι y

def ordQ (q : QPt Xo c) (f : Rul Xo c) : EReal := nval q.T.V 1 (evI q.y f)

def RegularityR1Quotient (C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ C a n,
    (∃ la : HeightOneSpectrum (𝓞 c.F), ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) →
      ∀ q : QPt Xo c, 0 ≤ ordQ Xo c q f

def RegularityR2Quotient (C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ (aL : (E →+* ℂ) × ℕ → ℕ) (nL : ℕ) (aE : (E →+* ℂ) × ℕ → ℕ) (nE k : ℕ) (ws : Fin k → Rul Xo c)
    (et : Rul Xo c) (c' : ℝ), 0 ≤ c' → (∀ i, ws i ∈ C aL nL) → et ∈ C aE nE →
    (∃ (la : HeightOneSpectrum (𝓞 c.F)) (nu : ℝ), ∀ v ∈ valSet Xo c (algCls Xo c) la,
      0 ≤ v et ∧ (∃ i, v (ws i) ≠ ⊤) ∧ (v et ≠ ⊤ → (⨅ i, v (ws i)) ≤ (nu : EReal) + (c' : EReal) * v et)) →
    ∀ q : QPt Xo c, 0 ≤ ordQ Xo c q et ∧
      (ordQ Xo c q et ≠ ⊤ → (⨅ i, ordQ Xo c q (ws i)) ≤ (c' : EReal) * ordQ Xo c q et)

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ResChPrime
noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7} (Q : Par D)

structure In66 : Type 1 where
  P : ModuliIntegralCharts.Prov D
  dat : ℕ → P.Dat
  Tw : ∀ j p, PointsOfFlagModel.Tower p (Q.Xo j) Q.c
  rel : ∀ j p, (P.loc (dat j) p).Pt (P.loc (dat j) p).YY → PointsOfFlagModel.Pt (Tw j p) .yy → Prop

namespace In66

variable {Q} (G : In66 Q)

abbrev PY (j p : ℕ) : Type := (G.P.loc (G.dat j) p).Pt (G.P.loc (G.dat j) p).YY

def PinDat : Prop := ∀ j, 1 ≤ j → j < D.R.m → G.P.rk (G.dat j) = D.R.r ∧ G.P.jj (G.dat j) = (D.R.sigW j).1

def PinTower : Prop := ∀ j, 1 ≤ j → j < D.R.m → ∀ p, p.Prime → PointsOfFlagModel.TowerAt (G.Tw j p)

def IsAlgPt (j : ℕ) (la : HeightOneSpectrum (𝓞 Q.c.F)) (z : PointsOfFlagModel.Pt (G.Tw j (WeightAlgebra.resCh la)) .yy) : Prop :=
  ∃ (T : CDVR) (io : Q.c.F →+* T.Fr) (e : ℕ) (y : IntFr (Q.Xo j) Q.c T io), OverLa la T.V io e ∧
    algCls (Q.Xo j) Q.c T io y ∧ LiesOverBaseChange la (G.Tw j (WeightAlgebra.resCh la)) T io y z

def HasData : Prop := ∀ j, 1 ≤ j → j < D.R.m → ∀ la z, G.IsAlgPt j la z →
  Nonempty (DatAt ((G.Tw j (WeightAlgebra.resCh la)).Y z.1) z.2.2.1)

def PinPts : Prop := ∀ j, 1 ≤ j → j < D.R.m → ∀ la z, G.IsAlgPt j la z →
  (∃ η, G.rel j _ η z) ∧ ∀ η, G.rel j _ η z → (G.P.loc (G.dat j) _).fld η = PointsOfFlagModel.fld z

def PinLat : Prop := ∀ j, 1 ≤ j → j < D.R.m → ∀ la z, G.IsAlgPt j la z → ∀ η, G.rel j _ η z →
  ∀ A : DatAt ((G.Tw j (WeightAlgebra.resCh la)).Y z.1) z.2.2.1,
    ∃ e : (G.P.loc (G.dat j) _).Ylat η ≃ₗ[𝓞 D.host.E] A.Ylat,
      ∀ a b, A.beta (e a) (e b) = (G.P.loc (G.dat j) _).be η a b

def BaseChange : Prop := ∀ j, 1 ≤ j → j < D.R.m →
  ∀ (la : HeightOneSpectrum (𝓞 Q.c.F)) (T : CDVR) (io : Q.c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e →
    ∀ y : IntFr (Q.Xo j) Q.c T io, algCls (Q.Xo j) Q.c T io y →
      ∃ z, LiesOverBaseChange la (G.Tw j (WeightAlgebra.resCh la)) T io y z

def lies (j : ℕ) (la : HeightOneSpectrum (𝓞 Q.c.F)) (T : CDVR) (io : Q.c.F →+* T.Fr)
    (y : IntFr (Q.Xo j) Q.c T io) (η : G.PY j (WeightAlgebra.resCh la)) : Prop :=
  j < D.R.m → ∃ z, G.rel j (WeightAlgebra.resCh la) η z ∧ LiesOverBaseChange la (G.Tw j (WeightAlgebra.resCh la)) T io y z

end In66

theorem resCh_prime {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) : (WeightAlgebra.resCh la).Prime := by
  unfold WeightAlgebra.resCh
  haveI := la.isPrime
  haveI : Finite (𝓞 K ⧸ la.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot la.asIdeal la.ne_bot
  first
  | exact CharP.char_is_prime (𝓞 K ⧸ la.asIdeal) _
  | exact (CharP.char_is_prime_or_zero (𝓞 K ⧸ la.asIdeal) _).resolve_right
      (ringChar.char_ne_zero_of_finite _)

variable {Q}

theorem In66.liesTotal (G : In66 Q) (h1 : G.PinPts) (h2 : G.BaseChange) {j : ℕ} (hj : InR D j) :
    LiesTotal (Q.Xo j) Q.c (algCls (Q.Xo j) Q.c) (fun la => G.PY j (WeightAlgebra.resCh la)) (G.lies j) := by
  intro la T io e ho y hy
  by_cases hm : j < D.R.m
  · obtain ⟨z, hz⟩ := h2 j hj.1 hm la T io e ho y hy
    obtain ⟨η, hη⟩ := (h1 j hj.1 hm la z ⟨T, io, e, y, ho, hy, hz⟩).1
    exact ⟨η, fun _ => ⟨z, hη, hz⟩⟩
  · exact ⟨(G.P.ex (G.dat j) (WeightAlgebra.resCh la)).yEta
      (Classical.choice ((G.P.ex (G.dat j) (WeightAlgebra.resCh la)).genNe _)), fun h => absurd h hm⟩

end Formalism.L2.Pj
end
end
