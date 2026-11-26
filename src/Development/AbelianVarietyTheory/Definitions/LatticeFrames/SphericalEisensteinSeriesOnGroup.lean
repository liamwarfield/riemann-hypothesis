module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqOfSplitFactor
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch

variable {D : D7}

structure Lvl (V : HSp D) where

  L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)

  c : GL (Fin V.rank) (AE D)

def Lvl.K {V : HSp D} (l : Lvl V) : Subgroup (GA D V) := levelAll D.sp.cm.sig V.gram l.L l.c

def Lvl.Good {V : HSp D} (l : Lvl V) : Prop :=
  Submodule.IsFullLattice D.host.E l.L ∧ (∀ v, IsSelfDualAt D.sp.cm.sig V.gram l.L v) ∧ IsMaj V l.c

def Lvl.form {V : HSp D} (l : Lvl V) : Mx D V.rank V.rank := adj (l.c⁻¹).1 * (l.c⁻¹).1

theorem Lvl.Good.isCompact_K {V : HSp D} {l : Lvl V} (h : l.Good) : IsCompact (l.K : Set (GA D V)) :=
  haveI := h.1
  isCompact_levelAll (isCMExt_host D) _ _ _

section SlopeTestRemainingChoices

variable {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (K : Subgroup (GA D T))

def sphericalSectionIwasawa (s : ℂ) : GA D T → ℂ := fun h => npow (iwAbs (absDet d) K h) (s + rhoH T r)

def sphericalEisensteinSeriesOnGroup (h : GA D T) : ℂ → ℂ := fun s => cosetSum (stab d) (GQ T) (sphericalSectionIwasawa d K s) h

end SlopeTestRemainingChoices

section Centre

variable (θ : InfFam D) (n : ℕ) (τ : D.what₂.Tau)

end Centre

section Ops

variable {n : ℕ}

def projS {T : HSp D} {K : Subgroup (GA D T)} (ν : Measure K) (Φ : Mx D T.rank n → ℂ) : Mx D T.rank n → ℂ :=
  fun x => ∫ k, Φ (mt T (k : GA D T)⁻¹ * x) ∂ν

def ikS {T T' : HSp D} {t : ℕ} (d : HypDec T T' t) (μ : Measure (Mx D t n)) (Φ : Mx D T.rank n → ℂ) : Mx D T'.rank n → ℂ :=
  fun a => ∫ x, Φ (d.jX * x + d.j0 * a) ∂μ

variable (θ : InfFam D) (τ : D.what₂.Tau)

variable {θ} {V V₀ : HSp D} {r : ℕ} (ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n))

variable (d : HypDec V V₀ r) (K : Subgroup (GA D V))

def eisS (H : StdUnn.G D n → ℝ≥0) (Φ : schwartzA θ V.rank n) (g : StdUnn.G D n) : ℂ → ℂ :=
  fun s => cosetSum (StdUnn.P D n) (StdUnn.GF D n) (StdUnn.sect ω H Φ s) g

end Ops

end GlobalTheory.RegSch

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.Model

open GlobalTheory.AdelicU GlobalTheory.AdelicU.Supp

variable {D : D7}

local instance relAt (v : Pl D) : ValuativeRel (Fv D.host.F v) := GlobalTheory.LocalData.complRel v
local instance locAt (v : Pl D) : IsNonarchimedeanLocalField (Fv D.host.F v) := GlobalTheory.LocalData.isLocalField v

def secAt {v : Pl D} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : Fv D.host.F v →+ AE D :=
  AddMonoidHom.mk' (fun a => singleTens D.host.E v (a ⊗ₜ[D.host.F] (1 : D.host.E)) * splitIdemAd (isCMExt_host D) τ)
    fun a b => by rw [TensorProduct.add_tmul, map_add (f := _), add_mul]

def prAt {v : Pl D} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : AE D →+* Fv D.host.F v :=
  (splitProj τ).toRingHom.comp (GlobalTheory.AdelicU.compFin D.host.F D.host.E v)

theorem mem_int_iff {v : Pl D} (a : Fv D.host.F v) : a ∈ 𝒪[Fv D.host.F v] ↔ Valued.v a ≤ 1 := by
  have : (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [Valuation.mem_integer_iff,
    (isEquiv (valuation (Fv D.host.F v)) (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one]

def splitPt {v : Pl D} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : SplitPt D (Fv D.host.F v) where
  v := v
  e := splitIdemAd (isCMExt_host D) τ
  split := isSplitIdem_iff_exists.2 ⟨v, τ, rfl⟩
  above := ⟨_, isPlaceIdem_placeIdem D v, (splitAt_splitIdemAd τ).2.2⟩
  pr := prAt τ
  sec := secAt τ
  pr_sec a := by
    change splitProj τ (GlobalTheory.AdelicU.compFin _ _ v (singleTens _ v _ * singleTens _ v _)) = a
    rw [map_mul, compFin_singleTens_self, compFin_singleTens_self, map_mul, splitProj_tmul, splitProj_splitIdem, map_one,
      mul_one, mul_one]
  sec_pr x := (splitIdemAd_mul (isCMExt_host D) τ x).symm
  cont_pr := (continuous_splitProj τ).comp
    (GlobalTheory.AutFunCompare.continuous_tensNU (E := D.host.E) (evFin D.host.F v).toLinearMap (map_mul (evFin D.host.F v)) (by
      exact (RestrictedProduct.continuous_eval v).comp continuous_snd))
  cont_sec := by
    have h1 : Continuous fun a : AF D.host.F => (a ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) :=
      (continuous_id.smul (continuous_const (y := (1 : AE D)))).congr fun a => by
        change a • ((1 : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) = _
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    exact (h1.comp (Continuous.prodMk continuous_const (continuous_singleFin v))).mul continuous_const
  int_iff a := (mem_int_iff a).trans (GlobalTheory.IdemPrime.mem_iff (splitAt_splitIdemAd τ) a).symm

theorem eq_single {v : Pl D} {a : AE D} (ha : a ∈ idAt D (· = v)) : a = singleTens D.host.E v (compAt D v a) := by
  have hc : ∀ u (z : AE D), GlobalTheory.AdelicU.compFin D.host.F D.host.E u z = compAt D u z := fun u z =>
    (tens_map_map (sndA D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F u) z).symm
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 ha
  refine adTens_ext (fun w => ?_) fun u => ?_
  · rw [compInf_singleTens]
    refine (tens_map_map (fstA D.host.F) (GlobalTheory.AutFunCompare.evW w) a).symm.trans ?_
    exact (congrArg (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id D.host.F D.host.E)) h1).trans (map_zero _)
  · by_cases e : u = v
    · subst e; rw [compFin_singleTens_self, hc]
    · rw [compFin_singleTens_ne e, hc]
      exact (Submodule.mem_iInf _).1 h2 ⟨u, e⟩

theorem compAt_eq (u : Pl D) (z : AE D) : compAt D u z = GlobalTheory.AdelicU.compFin D.host.F D.host.E u z :=
  tens_map_map (sndA D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F u) z

theorem single_mem_idAt (v : Pl D) (y : Fv D.host.F v ⊗[D.host.F] D.host.E) : singleTens D.host.E v y ∈ idAt D (· = v) := by
  refine Submodule.mem_inf.2 ⟨?_, (Submodule.mem_iInf _).2 fun u => ?_⟩
  · induction y using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
    | tmul a x => exact TensorProduct.zero_tmul _ x
  · exact (compAt_eq u.1 _).trans (compFin_singleTens_ne u.2 y)

theorem mem_idAt_iff {v : Pl D} {a : AE D} :
    a ∈ idAt D (· = v) ↔ algebraMap (AF D.host.F) (AE D) (placeIdem v) * a = a := by
  rw [← singleTens_one, singleTens_mul, one_mul, ← compAt_eq]
  exact ⟨fun h => (eq_single h).symm, fun h => h ▸ single_mem_idAt v _⟩

theorem mem_grpAt_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S : HSp D) (g : GA D S) : g ∈ grpAt S (· = p.v) ↔ SuppAt p.e S g := by
  obtain ⟨ε, h1, h2⟩ := p.above
  obtain rfl := isPlaceIdem_iff.1 h1
  rw [SuppAt, h2]
  simp only [← mem_idAt_iff]
  rw [grpAt, congGrp, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
  have : Ideal.Quotient.mk (idAt D (· = p.v)) ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) =
      (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D ⧸ idAt D (· = p.v))) i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [this]
  exact Iff.rfl

def intGrp (D : D7) (v : Pl D) : AddSubgroup (AE D) :=
  (idAt D (· = v)).toAddSubgroup ⊓ (intAE D).comap (finPart D).toAddMonoidHom

theorem latV_le_int (S : HSp D) (L : Lat S) (hL : ∀ x ∈ L, ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = x i) (v : Pl D) :
    latV S L (· = v) ≤ AddSubgroup.pi Set.univ fun _ => intGrp D v := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, h0, a, rfl, x, hx, rfl⟩ i -
  obtain ⟨b, hb⟩ := hL x hx i
  refine ⟨Submodule.mem_inf.2 ⟨TensorProduct.zero_tmul _ _, (Submodule.mem_iInf _).2 fun u => ?_⟩,
    AddSubgroup.subset_closure ⟨α, hα, b, by rw [hb, ← one_mul (x i)]; rfl⟩⟩
  change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F u.1 α ⊗ₜ[D.host.F] _ = 0
  rw [h0 _ u.2, TensorProduct.zero_tmul]

theorem single_mem_latV (S : HSp D) (L : Lat S) (v : Pl D) (i : Fin S.rank)
    (hL : ∀ b : 𝓞 D.host.E, Pi.single i (b : D.host.E) ∈ L) :
    intAE D ≤ (latV S L (· = v)).comap ((AddMonoidHom.single (fun _ : Fin S.rank => AE D) i).comp
      ((singleTens D.host.E v).toAddMonoidHom.comp (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v).toAddMonoidHom)) := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, b, rfl⟩
  refine AddSubgroup.subset_closure ⟨singleFin v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v α), fun u => ?_,
    fun u hu => evalV_singleFin_ne hu _, 1, rfl, Pi.single i (b : D.host.E), hL b, funext fun j => ?_⟩
  · by_cases e : u = v
    · subst e; rw [evalV_singleFin_self]; exact hα u
    · rw [evalV_singleFin_ne e]; exact zero_mem _
  · change (Pi.single i (pairA D.host.F 0 (singleFin v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v α)) ⊗ₜ[D.host.F] (b : D.host.E)) :
      Fin S.rank → AE D) j = _
    by_cases e : j = i
    · subst e; rw [Pi.single_eq_same, Pi.single_eq_same, one_mul]
    · rw [Pi.single_eq_of_ne e, Pi.single_eq_of_ne e, mul_zero, TensorProduct.tmul_zero]

theorem mem_latV_std (S : HSp D) (L : Lat S) (hL : ∀ x, x ∈ L ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = x i) (v : Pl D)
    (y : Fin S.rank → AE D) : y ∈ latV S L (· = v) ↔ ∀ i, y i ∈ intAt D (· = v) := by
  refine ⟨fun hy i => latV_le_int S L (fun x => (hL x).1) v hy i trivial, fun hy => ?_⟩
  rw [← Finset.univ_sum_single y]
  refine sum_mem fun i _ => ?_
  rw [eq_single (hy i).1]
  refine single_mem_latV S L v i (fun b => (hL _).2 fun j => ?_) (hy i).2
  by_cases e : j = i
  · subst e; exact ⟨b, by rw [Pi.single_eq_same]⟩
  · exact ⟨0, by rw [Pi.single_eq_of_ne e]; rfl⟩

end GlobalTheory.FinPl.Model

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.DoubleCollapse
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

variable {D : D7}

def SplitPt.IsIdele {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (x : kˣ) (a : (AE D)ˣ) : Prop := (a : AE D) = p.sec x + (1 - p.e)

def chrPow (χ : (AE D)ˣ →* Circle) (a : (AE D)ˣ) (e : ℤ) : ℂ := ((χ a ^ e : Circle) : ℂ)

def LiftExact (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k)
    (χ : AddChar k Circle) (hχ : HasConductor χ 1), ∃ e : ℤ, (e = 1 ∨ e = -1) ∧
    ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D),
    CoCpt S → ∀ (vS : Vol S) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om →
    CharUnramAt D χS p.v → CharUnramAt D χT p.v → ∀ (α : Frame p S n') (β : Frame p T n) (P : Pair k n') (Q : Pair k n),
    ∀ a, p.IsIdele q.unit a → ∀ (LS : Lat S) (LT : Lat T) (f₀ f : WO S T → ℂ), Over ψ α β LS LT f₀ (phiOne P Q) f →
    ∀ φ₀, RamAt α P φ₀ → ∀ ε : 𝓀[k]ˣ,
      sOp β Q q (resChar χ hχ q) ε (liftT om vS.μ vS.𝓕 φ₀ f) =
        ((((resCard k : ℝ) ^ (((Fintype.card n : ℝ) - Fintype.card n') / 2) : ℝ) : ℂ) * chrPow χS a e * chrPow χT a (-e)) •
          liftT om vS.μ vS.𝓕 (sOp α P q (resChar χ hχ q) ε φ₀) f

def RamUnitary (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (χ : AddChar k Circle) (hχ : HasConductor χ 1) (ε : 𝓀[k]ˣ) (S : HSp D),
    CoCpt S → ∀ (vS : Vol S) (β : Frame p S n) (P : Pair k n) (φ φ' : GA D S → ℂ), RamAt β P φ → RamAt β P φ' →
      ∫ g in vS.𝓕, sOp β P q (resChar χ hχ q) ε φ g * star (sOp β P q (resChar χ hχ q) ε φ' g) ∂vS.μ =
        (resCard k : ℂ) ^ Fintype.card n * ∫ g in vS.𝓕, φ g * star (φ' g) ∂vS.μ

end GlobalTheory.FinPl

end
end
