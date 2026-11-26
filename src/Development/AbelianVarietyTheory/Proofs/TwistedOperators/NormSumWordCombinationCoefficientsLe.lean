module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftUniqueUpToUnit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SizesEqCount
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruence
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatGlueLatIffDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDiagonalConjEdgeSumAddCharFiniteField
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdCons

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSumWordCombinationCoefficientsLe
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSumWordCombinationCoefficientsLe
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

noncomputable section

namespace GlobalTheory.ArchRec.IoPhase

open GlobalTheory.ConjLiftUnique

theorem isONBasis_of_adapted {n : ℕ} {G B : Mn n} (h : IsAdapted G 1 B) : IsONBasis G 1 B n := by
  obtain ⟨ε, h1, h2⟩ := h
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  have c : Formalism.REAL.Jm ε * (Bᴴ * G) * B = 1 := by rw [Matrix.mul_assoc, h1, hJ]
  have e : Formalism.REAL.Jm ε = 1 := by
    calc Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * (Bᴴ * G) * B * Formalism.REAL.Jm ε := by rw [c, Matrix.one_mul]
      _ = 1 := by rw [Matrix.mul_assoc _ B, ← h2, Matrix.one_mul, c]
  exact ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, by simp [h1, e], by simp⟩

theorem io_eq_smul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {S : D.what₂.Tau → SPar} {M : DSModel W S}
    (hω : IsWeilDatumO ψ V W χV χW ω) (h1 : Formalism.IndefR.FWT.LowSm M) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) {c : CoefA V}
    (hc : c.Is) (pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ)) (ht : ∀ P, IsThetaFunO ψ V W (pt P))
    (hinj : Function.Injective pt) {Δ : PolF D W.rank V.rank}
    {io io' : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank} (hio : IsIoW θ M c ω pt Δ io)
    (hio' : IsIoW θ M c ω pt Δ io') : ∃ a : ℂ, ‖a‖ = 1 ∧ io' = a • io := by
  classical
  let F : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] thetaSub ψ V W := io.compr₂ (pt.codRestrict (thetaSub ψ V W) ht)
  let F' : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] thetaSub ψ V W := io'.compr₂ (pt.codRestrict (thetaSub ψ V W) ht)
  have f1 : ∀ x w, (F x w).1 = pt (io x w) := fun _ _ => rfl
  have f2 : ∀ x w, (F' x w).1 = pt (io' x w) := fun _ _ => rfl
  clear_value F F'
  have hF : Eqv θ ω F := ⟨fun u hu x w => by rw [f1, f1, hio.1 u hu],
    fun τ k hk v u hu w => by rw [f1, f1, hio.2.1 τ k hk v u hu]⟩
  have hF' : Eqv θ ω F' := ⟨fun u hu x w => by rw [f2, f2, hio'.1 u hu],
    fun τ k hk v u hu w => by rw [f2, f2, hio'.2.1 τ k hk v u hu]⟩
  obtain ⟨v₀, w₀, n1, n2, e⟩ := hio.2.2
  obtain ⟨v₁, w₁, n1', n2', e'⟩ := hio'.2.2
  obtain ⟨b, hb⟩ := exists_invForm hω
  obtain ⟨c₁, k1⟩ := exists_const_of_eqv h1 h2 hc hb hF hF w₀ n2
  obtain ⟨c₂, k2⟩ := exists_const_of_eqv h1 h2 hc hb hF' hF' w₀ n2
  obtain ⟨c₃, k3⟩ := exists_const_of_eqv h1 h2 hc hb hF hF' w₀ n2
  obtain ⟨κ, hκ, hk⟩ := exists_phase b hb.symm hb.pos hb.defin (fun v w => F (PiTensorProduct.tprod ℂ v) w)
    (fun v w => F' (PiTensorProduct.tprod ℂ v) w) k1 k2 k3 n1 n1' n2 n2' (l := 1) norm_one
    (Subtype.ext (by rw [one_smul, f1, f2, e, e']))
  have hFF : F' = κ • F := PiTensorProduct.ext (MultilinearMap.ext fun v => LinearMap.ext (hk v))
  refine ⟨κ, hκ, LinearMap.ext fun x => LinearMap.ext fun w => hinj ?_⟩
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, ← f1, ← f2, hFF]
  rfl

theorem ioUniq (D : D7) : IoUniq D := by
  intro i M M' ψ θ χS χT ω hθ hω _ c hc _ BV f hf io io' hio hio'
  obtain ⟨τ₀⟩ : Nonempty D.what₂.Tau := by
    obtain ⟨σ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    by_cases h : ∃ ρ, tauE D ρ = σ
    · exact ⟨h.choose⟩
    · exact ⟨(not_not.1 fun h' => h ((GlobalTheory.PointAtPlace.tauE_cm σ).2 h')).choose⟩
  have hlow := GlobalTheory.HolLowOnce.lowSm_and_lowIrr D _ _ M' fun τ =>
    GlobalTheory.LowSmooth.shape_at M' τ (D.hc τ) (Formalism.IndefR.FWT.rank_Wc i) (GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW (D := D) i τ) rfl
  have hB := fun τ => isONBasis_of_adapted (hf τ).onS
  exact io_eq_smul hω hlow.1 hlow.2 hc _
    (GlobalTheory.GalLift.Vec.theta_pureTensorO hω.std hθ (fun _ => 1) BV (cart M') (onb M') (hf τ₀).theta)
    (GlobalTheory.FockIndep.pureTensorO_injective D ψ θ _ _ _ M' BV f hω.std hθ
      (fun τ => GlobalTheory.GalLift.Vec.isCartanInv_one (hB τ)) hB (hf τ₀).theta (hf τ₀).ne fun τ => (hf τ).vac) hio hio'

theorem ioUniq_of_discreteSeriesCover : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, IoUniq D :=
  fun _ _ => ioUniq

end GlobalTheory.ArchRec.IoPhase

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSumWordCombinationCoefficientsLeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowestKTypeFockMap_unique_of_discreteSeries : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, IoUniq D := by
  first | exact @GlobalTheory.ArchRec.IoPhase.ioUniq_of_discreteSeriesCover | exact GlobalTheory.ArchRec.IoPhase.ioUniq_of_discreteSeriesCover | (intros; apply GlobalTheory.ArchRec.IoPhase.ioUniq_of_discreteSeriesCover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPrimeSmulLatticeHeckeElementLe
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPrimeSmulLatticeHeckeElementLe
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.HeckeConjPart

open Formalism.L2.NTheta GlobalTheory.SplitPlace IsDedekindDomain

variable {D : D7}

theorem le_unif {x : WithZero (Multiplicative ℤ)} (h : x < 1) :
    x ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le'
  obtain ⟨u, rfl⟩ := WithZero.ne_zero_iff_exists.1 hx
  rw [← WithZero.coe_one, WithZero.coe_lt_coe] at h
  rw [WithZero.coe_le_coe]
  rw [← Multiplicative.toAdd_lt, toAdd_one] at h
  rw [← Multiplicative.toAdd_le, toAdd_ofAdd]
  omega

theorem ratio_int {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (he : IsIdemAt e P)
    {ϖ : 𝓞 D.host.E} (hP : ϖ ∈ P.asIdeal) (hP2 : ϖ ∉ P.asIdeal ^ 2) {y : 𝓞 D.host.E} (hy : y ∈ P.asIdeal) :
    ∃ t ∈ intAE D, finPart D e * finPart D (incA D (y : D.host.E)) =
      t * (finPart D e * finPart D (incA D (ϖ : D.host.E))) := by
  obtain ⟨v, π, s, h1, h2, h3, h4, h5⟩ := GlobalTheory.SplitCoord.exists_coord e he.1
  have hu := isUnif he h4 h5 ϖ hP hP2
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := by
    intro h0
    apply hP2
    rw [show ϖ = 0 from RingOfIntegers.coe_eq_zero_iff.1 h0]
    exact zero_mem _
  set φ : D.host.E →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v := (π.comp (finPart D)).comp (incA D) with hφ
  set q : D.host.E := (y : D.host.E) / (ϖ : D.host.E)
  refine ⟨finPart D e * finPart D (incA D q), ?_, ?_⟩
  · rw [h4]
    change Valued.v (φ q) ≤ 1
    rw [map_div₀, map_div₀]
    rcases eq_or_ne y 0 with rfl | hy0
    · simp
    have hn := (he.2 y hy0).1 hy
    rw [map_mul, h4] at hn
    change ¬ Valued.v (φ ((y : D.host.E)⁻¹)) ≤ 1 at hn
    rw [map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ((map_ne_zero φ).2 fun h0 => hy0 (RingOfIntegers.coe_eq_zero_iff.1 h0))))] at hn
    have hϖv : Valued.v (φ ϖ) = _ := hu
    have h6 := le_unif hn
    rw [← hϖv] at h6
    rw [div_le_one₀ (by rw [hϖv]; exact zero_lt_iff.2 WithZero.coe_ne_zero)]
    exact h6
  · have hee : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he.1.1]
    have hq : q * (ϖ : D.host.E) = y := div_mul_cancel₀ _ hϖ0
    calc finPart D e * finPart D (incA D (y : D.host.E))
        = (finPart D e * finPart D e) * (finPart D (incA D q) * finPart D (incA D (ϖ : D.host.E))) := by
          rw [hee, ← map_mul (finPart D) (incA D q), ← map_mul (incA D) q, hq]
      _ = _ := mul_mul_mul_comm _ _ _ _

open scoped Matrix


set_option maxHeartbeats 1000000 in
theorem keeps {V : HSp D} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (he : IsIdemAt e P)
    {ϖ : 𝓞 D.host.E} (hP : ϖ ∈ P.asIdeal) (hP2 : ϖ ∉ P.asIdeal ^ 2) {k : ℕ} {a₀ : GA D V}
    (ha : IsHeckeElt V e (ϖ : D.host.E) k a₀) {x : 𝓞 D.host.E} (hx : x ∈ (Formalism.L2.Col.conjPrime₂ P).asIdeal) :
    ∀ z ∈ LamHat V, finPart D (incA D (x : D.host.E)) • fm V a₀ *ᵥ z ∈ LamHat V := by
  intro z hz
  have hee : e * e = e := he.1.1
  have hint : finPart D (incA D (x : D.host.E)) ∈ intAE D :=
    AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, x, rfl⟩
  have hc := hecke_conj hee ha
  have hce : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have h4 := (lower_iff hce V _ a₀⁻¹).1 hc.2.2.2.1
  rw [inv_inv] at h4
  obtain ⟨t, ht, hteq⟩ := ratio_int he hP hP2 ((Formalism.L2.Col.mem_conjP P x).1 hx)
  have hteq' := congrArg (cf D) hteq
  rw [map_mul, map_mul, map_mul, ← fin_cA, ← fin_cA, ← fin_cA, cA_incA, cA_incA] at hteq'
  have hsx : star ((Formalism.L2.Col.cO D.host.E x : 𝓞 D.host.E) : D.host.E) = (x : D.host.E) := by
    change star (star (x : D.host.E)) = _
    exact star_star _
  rw [hsx] at hteq'
  have h6 := mulVec_parts (finPart D) ((suppAt_iff e V a₀).1 ha.2.1) z
  rw [← fm_eq V a₀] at h6
  rw [h6, RingHom.map_add (f := _), add_smul, smul_sub, smul_add, smul_add]
  have hi1 := idem_mem hee
  have hi2 := idem_mem hce
  refine sub_mem (add_mem (add_mem ?_ ?_) (smul_mem V hint hz))
    (smul_mem V hint (smul_mem V (add_mem hi1 hi2) hz))
  · exact smul_mem V hint (ha.2.2.1 z hz)
  · rw [smul_smul, mul_comm, hteq', mul_smul]
    exact smul_mem V (cf_mem ht) (h4 z hz)

theorem finHom_eq {V : HSp D} (g : GA D V) : (finHom V g).1 = fm V g := rfl

theorem finPart_incA (c : D.host.E) :
    finPart D (incA D c) = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] c := rfl

theorem keeps_one {V : HSp D} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (he : IsIdemAt e P)
    {ϖ : 𝓞 D.host.E} (hP : ϖ ∈ P.asIdeal) (hP2 : ϖ ∉ P.asIdeal ^ 2) {k : ℕ} {a₀ : GA D V}
    (ha : IsHeckeElt V e (ϖ : D.host.E) k a₀) {x : 𝓞 D.host.E} (hx : x ∈ (Formalism.L2.Col.conjPrime₂ P).asIdeal) :
    ∀ y ∈ latGHat V 1, finPart D (incA D (x : D.host.E)) • fm V a₀ *ᵥ y ∈ latGHat V 1 := by
  intro y hy
  rw [GlobalTheory.LevelActionPinned.latGHat_one] at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, hc, z, hz, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨c, hc, finPart D (incA D (x : D.host.E)) • fm V a₀ *ᵥ z, ?_, ?_⟩
    · rw [GlobalTheory.StdFrameCong.pj_latHat_eq] at hz ⊢
      exact keeps he hP hP2 ha hx z hz
    · rw [Matrix.mulVec_smul, smul_comm]
  | zero => rw [Matrix.mulVec_zero, smul_zero]; exact zero_mem _
  | add a b _ _ ha' hb' => rw [Matrix.mulVec_add, smul_add]; exact add_mem ha' hb'
  | neg a _ ha' => rw [Matrix.mulVec_neg, smul_neg]; exact neg_mem ha'

end GlobalTheory.HeckeConjPart

open scoped Matrix


open GlobalTheory.SplitPlace in
theorem GlobalTheory.HeckeConjPart.conj_part : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E)
    (k : ℕ) (g a₀ : GA D V),
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k a₀ →
    (Formalism.L2.Col.conjPrime₂ P).asIdeal • latG V (g * a₀) ≤ latG V g := by
  intro D V P e ϖ k g a₀ he hP hP2 ha
  rw [Submodule.smul_le]
  intro x hx v hv
  have spec := GlobalTheory.MarkCoset.latG_spec D V
  rw [(spec (g * a₀)).1, (spec (g * a₀)).2] at hv
  obtain ⟨y, hy, hyv⟩ := hv
  rw [(spec g).1, (spec g).2]
  refine ⟨finPart D (incA D (x : D.host.E)) • fm V a₀ *ᵥ y, GlobalTheory.HeckeConjPart.keeps_one he hP hP2 ha hx y hy, ?_⟩
  rw [GlobalTheory.HeckeConjPart.finHom_eq] at hyv ⊢
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← fm_mul, hyv]
  funext i
  simp only [finVec, Pi.smul_apply, smul_eq_mul, GlobalTheory.HeckeConjPart.finPart_incA,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPrimeSmulLatticeHeckeElementLeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjPrime_smul_lattice_heckeElement_le : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (k : ℕ) (g a₀ : GA D V),
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k a₀ →
    (Formalism.L2.Col.conjPrime₂ P).asIdeal • latG V (g * a₀) ≤ latG V g := by
  first | exact @GlobalTheory.HeckeConjPart.conj_part | exact GlobalTheory.HeckeConjPart.conj_part | (intros; apply GlobalTheory.HeckeConjPart.conj_part <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluedLatticePrescribedLocalComponents
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluedLatticePrescribedLocalComponents
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom

namespace GlobalTheory.GluedCmp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Algebra

variable {A : Type} [CommRing A] {n k : ℕ} (m : Matrix (Fin n) (Fin k) A) (z : Fin n → A) {e t T : A}

theorem unit_fwd (he : e * e = e) (ht : t * T = 1) (x f : Fin k → A) (a : A) :
    e • (m *ᵥ (x + a • f) + (a * t) • z) = m *ᵥ (e • x + (a * (e * t)) • T • f) + (a * (e * t) * e) • z ∧
      e • (e • x + (a * (e * t)) • T • f) = e • x + (a * (e * t)) • T • f := by
  have h1 : a * (e * t) * e = e * (a * t) := by linear_combination (a * t) * he
  have h2 : a * (e * t) * T = e * a := by linear_combination (a * e) * ht
  rw [h1, smul_smul (a * (e * t)) T f, h2]
  refine ⟨?_, ?_⟩
  · simp only [Matrix.mulVec_add, Matrix.mulVec_smul, smul_add, smul_smul]
  · simp only [smul_add, smul_smul, ← mul_assoc, he]

theorem unit_bwd (he : e * e = e) (ht : t * T = 1) (x f : Fin k → A) (hx : e • x = x) (a : A) :
    m *ᵥ x + (a * e) • z = m *ᵥ ((x - (a * e) • T • f) + (a * e * T) • f) + (a * e * T * t) • z ∧
      e • (m *ᵥ x + (a * e) • z) = m *ᵥ x + (a * e) • z := by
  have h1 : a * e * T * t = a * e := by linear_combination (a * e) * ht
  have h2 : e * (a * e) = a * e := by linear_combination a * he
  refine ⟨?_, ?_⟩
  · rw [h1, smul_smul (a * e) T f, sub_add_cancel]
  · rw [smul_add, ← Matrix.mulVec_smul, hx, smul_smul, h2]

theorem glue_fwd (he : e * e = e) (x f g : Fin k → A) (hg : e • g = g) (a : A) :
    e • (m *ᵥ (x + a • f) + (a * t) • z) = m *ᵥ (e • x - a • (g - e • f)) + a • ((t * e) • z + m *ᵥ g) ∧
      e • (e • x - a • (g - e • f)) = e • x - a • (g - e • f) := by
  have hs : e • (g - e • f) = g - e • f := by rw [smul_sub, hg, smul_smul, he]
  refine ⟨?_, ?_⟩
  · simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, smul_add, smul_sub, smul_smul]
    module
  · rw [smul_sub e (e • x) (a • (g - e • f)), smul_smul e e x, he, smul_comm e a (g - e • f), hs]

theorem glue_bwd (he : e * e = e) (x f g : Fin k → A) (hx : e • x = x) (hg : e • g = g) (a : A) :
    m *ᵥ x + a • ((t * e) • z + m *ᵥ g) = m *ᵥ ((x + a • (g - e • f)) + (a * e) • f) + (a * e * t) • z ∧
      e • (m *ᵥ x + a • ((t * e) • z + m *ᵥ g)) = m *ᵥ x + a • ((t * e) • z + m *ᵥ g) := by
  have h2 : e * (t * e) = t * e := by linear_combination t * he
  refine ⟨?_, ?_⟩
  · simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, smul_add, smul_sub, smul_smul]
    module
  · rw [smul_add e (m *ᵥ x), ← Matrix.mulVec_smul m e x, hx, smul_comm e a, smul_add e ((t * e) • z),
      smul_smul e (t * e) z, h2, ← Matrix.mulVec_smul m e g, hg]

theorem idem_smul_smul (he : e * e = e) (y : Fin n → A) : e • e • y = e • y := by
  rw [smul_smul, he]

end Algebra

variable {D : D7} {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {z : Y.V} {u : D.what₂.Word} {L₀ : Lat X} {x₀ : X.V}

theorem fg_glueLat (h : L₀.FG) : (glueLat Y X ι z u L₀ x₀).FG := by
  unfold glueLat
  refine Submodule.FG.sup ?_ (Submodule.fg_span_singleton _)
  refine Submodule.FG.map _ ?_
  rw [show (Formalism.L2.Herm.crd X).toLinearMap.restrictScalars (𝓞 D.host.E) =
      (((Formalism.L2.Herm.crd X).restrictScalars (𝓞 D.host.E) : X.V ≃ₗ[𝓞 D.host.E] _) : X.V →ₗ[𝓞 D.host.E] _) from rfl,
    Submodule.comap_equiv_eq_map_symm]
  exact h.map _

theorem cmp_unit (hg : IsGlueVec X u L₀ (vA X x₀)) {w : Pl D.host.E}
    (hw : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) (y : Fin Y.rank → EAf D) :
    InCmp (idem w) (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) y ↔
      ∃ x, InCmp (idem w) L₀ x ∧ ∃ a ∈ OA D, y = mA Y X ι *ᵥ x + (a * idem w) • vA Y z := by
  have he := idem_mul_self w
  have ht := inc_inv_mul u
  have het : idem w * inc D (Tu D u)⁻¹ ∈ OA D := (idem_mul_inv_mem_iff u w).2 hw
  have hew := idem_mem w
  unfold InCmp
  constructor
  · rintro ⟨hy, hey⟩
    obtain ⟨x, hx, a, ha, rfl⟩ := (mem_hat_glueLat y).1 hy
    obtain ⟨h1, h2⟩ := unit_fwd (mA Y X ι) (vA Y z) he ht x (vA X x₀) a
    refine ⟨idem w • x + (a * (idem w * inc D (Tu D u)⁻¹)) • inc D (Tu D u) • vA X x₀,
      ⟨add_mem_hat (smul_mem_hat hew hx) (smul_mem_hat (mul_mem ha het) hg.mul_mem), h2⟩,
      a * (idem w * inc D (Tu D u)⁻¹), mul_mem ha het, ?_⟩
    rw [← hey, h1]
  · rintro ⟨x, ⟨hx, hex⟩, a, ha, rfl⟩
    obtain ⟨h1, h2⟩ := unit_bwd (mA Y X ι) (vA Y z) he ht x (vA X x₀) hex a
    refine ⟨?_, h2⟩
    rw [h1]
    exact (mem_hat_glueLat _).2 ⟨_, sub_mem_hat hx (smul_mem_hat (mul_mem ha hew) hg.mul_mem), _,
      mul_mem (mul_mem ha hew) (inc_Tu_mem u), rfl⟩

theorem cmp_glue {w : Pl D.host.E} {g : Fin X.rank → EAf D} (h1 : idem w • g = g)
    (h2 : g - idem w • vA X x₀ ∈ hat L₀) (y : Fin Y.rank → EAf D) :
    InCmp (idem w) (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) y ↔
      ∃ x, InCmp (idem w) L₀ x ∧ ∃ a ∈ OA D,
        y = mA Y X ι *ᵥ x + a • ((inc D (Tu D u)⁻¹ * idem w) • vA Y z + mA Y X ι *ᵥ g) := by
  have he := idem_mul_self w
  have hew := idem_mem w
  unfold InCmp
  constructor
  · rintro ⟨hy, hey⟩
    obtain ⟨x, hx, a, ha, rfl⟩ := (mem_hat_glueLat y).1 hy
    obtain ⟨k1, k2⟩ := glue_fwd (mA Y X ι) (vA Y z) (t := inc D (Tu D u)⁻¹) he x (vA X x₀) g h1 a
    refine ⟨idem w • x - a • (g - idem w • vA X x₀),
      ⟨sub_mem_hat (smul_mem_hat hew hx) (smul_mem_hat ha h2), k2⟩, a, ha, ?_⟩
    rw [← hey, k1]
  · rintro ⟨x, ⟨hx, hex⟩, a, ha, rfl⟩
    obtain ⟨k1, k2⟩ := glue_bwd (mA Y X ι) (vA Y z) (t := inc D (Tu D u)⁻¹) he x (vA X x₀) g hex h1 a
    refine ⟨?_, k2⟩
    rw [k1]
    exact (mem_hat_glueLat _).2 ⟨_, add_mem_hat hx (smul_mem_hat ha h2), _, mul_mem ha hew, rfl⟩

theorem cmp_conj (h : IsLine Y X ι z u) (hg : IsGlueVec X u L₀ (vA X x₀)) (w : Pl D.host.E) (y : Fin Y.rank → EAf D) :
    InCmp (cjA D (idem w)) (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) y ↔
      cjA D (idem w) • y = y ∧ (∃ (x : Fin X.rank → EAf D) (a : EAf D), y = mA Y X ι *ᵥ x + a • vA Y z) ∧
        ∀ y', InCmp (idem w) (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) y' → hA Y y' y ∈ OA D := by
  have hew := idem_mem w
  unfold InCmp
  constructor
  · rintro ⟨hy, hcy⟩
    obtain ⟨x, hx, a, ha, rfl⟩ := (mem_hat_glueLat y).1 hy
    refine ⟨hcy, ⟨x + a • vA X x₀, a * inc D (Tu D u)⁻¹, rfl⟩, ?_⟩
    rintro y' ⟨hy', -⟩
    exact (mem_hat_glueLat_iff_dual h hg _ _).1 hy y' hy'
  · rintro ⟨hcy, ⟨x, a, rfl⟩, hdual⟩
    refine ⟨(mem_hat_glueLat_iff_dual h hg x a).2 ?_, hcy⟩
    intro y'' hy''
    have key : hA Y y'' (mA Y X ι *ᵥ x + a • vA Y z) =
        hA Y (idem w • y'') (mA Y X ι *ᵥ x + a • vA Y z) := by
      conv_lhs => rw [← hcy]
      rw [hA_smul_right, hA_smul_left, cjA_cjA]
    rw [key]
    exact hdual _ ⟨smul_mem_hat hew hy'', idem_smul_smul (idem_mul_self w) y''⟩

theorem isGlued_glueLat : ∀ (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V)
    (z : Y.V), IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V) (f₀ : Pl D.host.E → Fin X.rank → EAf D),
    Submodule.IsLattice D.host.E L₀ → IsGlueVec X u L₀ (vA X x₀) →
    (∀ w : Pl D.host.E, π ∈ w.asIdeal → idem w • f₀ w = f₀ w ∧ f₀ w - idem w • vA X x₀ ∈ hat L₀) →
    IsGlued Y X ι z u π L₀ f₀ (glueLat Y X ι z u L₀ x₀) := by
  intro D u π Y X ι z h L₀ x₀ f₀ hL hg hf
  unfold IsGlued
  refine ⟨fg_glueLat hL.fg, ?_, ?_⟩
  · intro w e he hw y
    obtain rfl := eq_idem he
    exact cmp_unit hg hw y
  · intro w e he hπ
    obtain rfl := eq_idem he
    exact ⟨fun y => cmp_glue (hf w hπ).1 (hf w hπ).2 y, cmp_conj h hg w⟩

end GlobalTheory.GluedCmp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluedLatticePrescribedLocalComponentsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedLattice_prescribed_localComponents : ∀ (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V), IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V) (f₀ : Pl D.host.E → Fin X.rank → EAf D), Submodule.IsLattice D.host.E L₀ → IsGlueVec X u L₀ (vA X x₀) → (∀ w : Pl D.host.E, π ∈ w.asIdeal → idem w • f₀ w = f₀ w ∧ f₀ w - idem w • vA X x₀ ∈ hat L₀) → IsGlued Y X ι z u π L₀ f₀ (glueLat Y X ι z u L₀ x₀) := by
  first | exact @GlobalTheory.GluedCmp.isGlued_glueLat | exact GlobalTheory.GluedCmp.isGlued_glueLat | (intros; apply GlobalTheory.GluedCmp.isGlued_glueLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluedLatticeSelfDualPrimitiveMeet
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluedLatticeSelfDualPrimitiveMeet
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom

namespace GlobalTheory.GlueVecLattice

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {z : Y.V} {u : D.what₂.Word}

theorem vA_flat (x : X.V) (t : D.host.E) :
    vA Y (ι x + t • z) = mA Y X ι *ᵥ vA X x + inc D t • vA Y z := by
  rw [vA_add, vA_smul, mA_mulVec_vA]

theorem mem_of_coords {L₀ : Lat X} {x₀ x : X.V} {t : D.host.E}
    (h1 : t * Tu D u ∈ (algebraMap (𝓞 D.host.E) D.host.E).range)
    (h2 : Formalism.L2.Herm.crd X (x - (t * Tu D u) • x₀) ∈ L₀) : ι x + t • z ∈ glueLat Y X ι z u L₀ x₀ := by
  obtain ⟨a, ha⟩ := h1
  refine (mem_glueLat _).2 ⟨_, h2, a, ?_⟩
  change _ = _ + algebraMap (𝓞 D.host.E) D.host.E a • _
  rw [ha, map_sub, map_smul, smul_add, smul_smul, mul_assoc, mul_inv_cancel₀ (Tu_ne_zero u), mul_one]
  abel

theorem coords_of_mem_hat (h : IsLine Y X ι z u) {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) {x₀ x : X.V}
    {t : D.host.E} (hy : vA Y (ι x + t • z) ∈ hat (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀))) :
    t * Tu D u ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ∧
      Formalism.L2.Herm.crd X (x - (t * Tu D u) • x₀) ∈ L₀ := by
  obtain ⟨x₁, hx₁, a, ha, e⟩ := (mem_hat_glueLat _).1 hy
  rw [vA_flat] at e
  obtain ⟨e1, e2⟩ := flat_inj h e
  have e3 : a = inc D (t * Tu D u) := by
    rw [RingHom.map_mul, e2, mul_assoc, inc_inv_mul, mul_one]
  refine ⟨(inc_mem_iff _).1 (e3 ▸ ha), GlobalTheory.GlueUnique.mem_of_inc_mem_hat hL.fg ?_⟩
  change vA X (x - (t * Tu D u) • x₀) ∈ _
  have e4 : vA X (x - (t * Tu D u) • x₀) = x₁ := by
    rw [sub_eq_add_neg, ← neg_smul, vA_add, vA_smul, RingHom.map_neg, ← e3, e1, neg_smul, add_neg_cancel_right]
  rwa [e4]

theorem mem_iff_coords (h : IsLine Y X ι z u) {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) {x₀ : X.V} (x : X.V)
    (t : D.host.E) : ι x + t • z ∈ glueLat Y X ι z u L₀ x₀ ↔
      t * Tu D u ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ∧
        Formalism.L2.Herm.crd X (x - (t * Tu D u) • x₀) ∈ L₀ :=
  ⟨fun hy => coords_of_mem_hat h hL (vA_mem_hat Y hy), fun hy => mem_of_coords hy.1 hy.2⟩

theorem mem_flatSp (y : Y.V) : y ∈ flatSp Y X ι z ↔ ∃ (x : X.V) (t : D.host.E), y = ι x + t • z := by
  rw [flatSp, Submodule.mem_sup]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, b, hb, rfl⟩
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hb
    exact ⟨x, t, rfl⟩
  · rintro ⟨x, t, rfl⟩
    exact ⟨_, ⟨x, rfl⟩, _, Submodule.mem_span_singleton.2 ⟨t, rfl⟩, rfl⟩

theorem glueLat_fg {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) (x₀ : X.V) : (glueLat Y X ι z u L₀ x₀).FG := by
  refine Submodule.FG.sup (Submodule.FG.map _ ?_) (Submodule.fg_span_singleton _)
  have e : L₀.comap ((Formalism.L2.Herm.crd X).toLinearMap.restrictScalars (𝓞 D.host.E)) =
      L₀.map ((Formalism.L2.Herm.crd X).symm.toLinearMap.restrictScalars (𝓞 D.host.E)) := by
    ext x
    constructor
    · intro hx
      exact ⟨_, hx, (Formalism.L2.Herm.crd X).symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      change Formalism.L2.Herm.crd X ((Formalism.L2.Herm.crd X).symm y) ∈ L₀
      rwa [LinearEquiv.apply_symm_apply]
  rw [e]
  exact hL.fg.map _

theorem span_glueLat {L₀ : Lat X} (hL : Submodule.IsFullLattice D.host.E L₀) (x₀ : X.V) :
    Submodule.span D.host.E (glueLat Y X ι z u L₀ x₀ : Set Y.V) = flatSp Y X ι z := by
  have h1 : ∀ x : X.V, ι x ∈ Submodule.span D.host.E (glueLat Y X ι z u L₀ x₀ : Set Y.V) := by
    intro x
    obtain ⟨y, rfl⟩ := (Formalism.L2.Herm.crd X).symm.surjective x
    have hy : y ∈ Submodule.span D.host.E (L₀ : Set (Fin X.rank → D.host.E)) := (Submodule.IsFullLattice.span_eq_top (self := hL)) ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy =>
      exact Submodule.subset_span ((mem_glueLat _).2 ⟨_, by rwa [LinearEquiv.apply_symm_apply], 0, by simp⟩)
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _)]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smul, map_smul]; exact Submodule.smul_mem _ c ha
  refine le_antisymm (Submodule.span_le.2 fun y hy => ?_) fun y hy => ?_
  · obtain ⟨x, -, a, rfl⟩ := (mem_glueLat y).1 hy
    refine (mem_flatSp _).2 ⟨x + (a : D.host.E) • x₀, a * (Tu D u)⁻¹, ?_⟩
    rw [map_add (f := _), map_smul, smul_add, smul_smul]
    abel
  · obtain ⟨x, t, rfl⟩ := (mem_flatSp y).1 hy
    refine add_mem (h1 x) (Submodule.smul_mem _ t ?_)
    have h2 : (Tu D u)⁻¹ • z + ι x₀ ∈ Submodule.span D.host.E (glueLat Y X ι z u L₀ x₀ : Set Y.V) :=
      Submodule.subset_span ((mem_glueLat _).2 ⟨0, by simp, 1, by simp⟩)
    have h3 := Submodule.smul_mem _ (Tu D u) (sub_mem h2 (h1 x₀))
    rwa [add_sub_cancel_right, smul_smul, mul_inv_cancel₀ (Tu_ne_zero u), one_smul] at h3

theorem isSDIn_glueLat (h : IsLine Y X ι z u) {L₀ : Lat X} (hL : Submodule.IsFullLattice D.host.E L₀) {x₀ : X.V}
    (hg : IsGlueVec X u L₀ (vA X x₀)) : IsSDIn Y (flatSp Y X ι z) (glueLat Y X ι z u L₀ x₀) := by
  refine ⟨glueLat_fg hL.toIsLattice x₀, span_glueLat hL x₀, fun y hy => ?_⟩
  obtain ⟨x, t, rfl⟩ := (mem_flatSp y).1 hy
  have key := mem_hat_glueLat_iff_dual h hg (vA X x) (inc D t)
  rw [← vA_flat] at key
  constructor
  · intro hm x' hx'
    rw [← inc_mem_iff, ← hA_vA]
    exact key.1 (vA_mem_hat Y hm) _ (vA_mem_hat Y hx')
  · intro H
    have h1 := coords_of_mem_hat h hL.toIsLattice (key.2 (hA_mem_of_forall ?_))
    · exact mem_of_coords h1.1 h1.2
    · rintro _ ⟨x', hx', rfl⟩
      change hA Y (vA Y x') _ ∈ _
      rw [hA_vA, inc_mem_iff]
      exact H x' hx'

theorem capX_glueLat (h : IsLine Y X ι z u) {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) (x₀ : X.V) :
    capX Y X ι (glueLat Y X ι z u L₀ x₀) = L₀ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h1 : ι x + (0 : D.host.E) • z ∈ glueLat Y X ι z u L₀ x₀ := by
      rw [zero_smul, add_zero]; exact hx
    have h2 := ((mem_iff_coords h hL x 0).1 h1).2
    rwa [zero_mul, zero_smul, sub_zero] at h2
  · intro hy
    obtain ⟨x, rfl⟩ := (Formalism.L2.Herm.crd X).surjective y
    exact ⟨x, (mem_glueLat (ι x)).2 ⟨x, hy, 0, by simp⟩, rfl⟩

theorem isPrim_glueLat (h : IsLine Y X ι z u) {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) {x₀ : X.V}
    (hg : IsGlueVec X u L₀ (vA X x₀)) : IsPrim Y z (glueLat Y X ι z u L₀ x₀) := by
  intro a
  have e : a • z = ι 0 + a • z := by rw [map_zero, zero_add]
  have hmem (x : Fin X.rank → D.host.E) : (fun i => inc D (x i)) ∈ hat L₀ ↔ x ∈ L₀ :=
    ⟨GlobalTheory.GlueUnique.mem_of_inc_mem_hat hL.fg, inc_mem_hat⟩
  rw [e, mem_iff_coords h hL, ← hmem, ← inc_mem_iff, ← inc_mem_iff]
  change _ ∧ vA X (0 - (a * Tu D u) • x₀) ∈ _ ↔ _
  rw [zero_sub, ← neg_smul, vA_smul, RingHom.map_neg, RingHom.map_mul]
  generalize inc D a = b
  constructor
  · rintro ⟨h1, h2⟩
    have h3 := hg.pair _ h2
    rw [hA_smul_right, RingHom.map_neg, RingHom.map_mul, cjA_inc_Tu] at h3
    have h4 := mul_mem (cjA_mem h1) hg.norm
    rw [RingHom.map_mul, cjA_inc_Tu] at h4
    rw [← cjA_mem_iff]
    convert neg_mem (add_mem h3 h4) using 1
    linear_combination (-(cjA D b)) * inc_inv_mul u
  · intro hb
    refine ⟨mul_mem hb (inc_Tu_mem u), ?_⟩
    rw [← neg_mul, ← smul_smul]
    exact smul_mem_hat (neg_mem hb) hg.mul_mem

theorem glueLat_selfDual_prim_cap : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V),
    IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V), Submodule.IsFullLattice D.host.E L₀ → IsGlueVec X u L₀ (vA X x₀) →
      IsSDIn Y (flatSp Y X ι z) (glueLat Y X ι z u L₀ x₀) ∧ IsPrim Y z (glueLat Y X ι z u L₀ x₀) ∧
        capX Y X ι (glueLat Y X ι z u L₀ x₀) = L₀ :=
  fun _ _ _ _ _ _ h _ x₀ hL hg => ⟨isSDIn_glueLat h hL hg, isPrim_glueLat h hL.toIsLattice hg, capX_glueLat h hL.toIsLattice x₀⟩

end GlobalTheory.GlueVecLattice

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluedLatticeSelfDualPrimitiveMeetStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedLattice_selfDual_primitive_meet : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V), IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V), Submodule.IsFullLattice D.host.E L₀ → IsGlueVec X u L₀ (vA X x₀) → IsSDIn Y (flatSp Y X ι z) (glueLat Y X ι z u L₀ x₀) ∧ IsPrim Y z (glueLat Y X ι z u L₀ x₀) ∧ capX Y X ι (glueLat Y X ι z u L₀ x₀) = L₀ := by
  first
  | exact @GlobalTheory.GlueVecLattice.glueLat_selfDual_prim_cap
  | intro D u Y X ι z h L₀ x₀ hL hg
    exact GlobalTheory.GlueVecLattice.glueLat_selfDual_prim_cap D u Y X ι z h L₀ x₀ hL.toIsLattice hg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FormalDegreeLoweringWeightRatioLe
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FormalDegreeLoweringWeightRatioLe
noncomputable section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

namespace GlobalTheory.SepReal.FormalDegreeRatio

theorem thrStar_lt {N : ℕ} (ε : Fin N → Bool) {M : ℝ} (hNM : (N : ℝ) ≤ M) (hM : 1 ≤ M) :
    ReciprocityTheory.ChartRestriction.DS.thrStar ε + 1 < 1000 * M ^ 3 - 1 := by
  have hp : (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) ≤ M := by
    have : ReciprocityTheory.ChartRestriction.DS.pOf ε ≤ N := by
      delta ReciprocityTheory.ChartRestriction.DS.pOf
      exact (Finset.card_filter_le _ _).trans (by simp)
    exact le_trans (by exact_mod_cast this) hNM
  have hq : (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) ≤ M := by
    have : ReciprocityTheory.ChartRestriction.DS.qOf ε ≤ N := by
      delta ReciprocityTheory.ChartRestriction.DS.qOf
      exact (Finset.card_filter_le _ _).trans (by simp)
    exact le_trans (by exact_mod_cast this) hNM
  have hq0 : (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ M := by
    have : ReciprocityTheory.ChartRestriction.DS.S7.q0 ε ≤ ReciprocityTheory.ChartRestriction.DS.qOf ε := min_le_right _ _
    exact le_trans (by exact_mod_cast this) hq
  have hq00 : (0 : ℝ) ≤ ReciprocityTheory.ChartRestriction.DS.S7.q0 ε := Nat.cast_nonneg _
  have hs : Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ)) ≤ 2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) + 1 := by
    calc Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ))
        ≤ Real.sqrt ((2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) + 1) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) + 1 := Real.sqrt_sq (by linarith)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hp0 : (0 : ℝ) ≤ ReciprocityTheory.ChartRestriction.DS.pOf ε := Nat.cast_nonneg _
  have hqq0 : (0 : ℝ) ≤ ReciprocityTheory.ChartRestriction.DS.qOf ε := Nat.cast_nonneg _
  have h1 : (N : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) ≤ M * M * M := by
    gcongr
  have h2 : 16 * (N : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ 16 * M * M := by
    gcongr
  have hM2 : M ≤ M ^ 2 := by nlinarith
  have hM3 : M ^ 2 ≤ M ^ 3 := by nlinarith
  have hMM : M * M * M = M ^ 3 := by ring
  have hMM2 : 16 * M * M = 16 * M ^ 2 := by ring
  delta ReciprocityTheory.ChartRestriction.DS.thrStar
  have hmax : max ((N : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) + 1)
      (16 * (N : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ))) <
      1000 * M ^ 3 - 2 := by
    refine max_lt ?_ ?_
    · nlinarith
    · nlinarith
  linarith

theorem fdeg_const (N : ℕ) (ε : Fin N → Bool) : ∃ c : ℝ, 0 < c ∧ ∀ (lam : Fin N → ℝ) (h : ℝ),
    Formalism.QuantumDeterminants.IsHCParam lam → Formalism.QuantumDeterminants.GapAtLeast ε lam h → ReciprocityTheory.ChartRestriction.DS.thrStar ε + 1 < h →
    (∃ a, ε a = true) → (∃ a, ε a = false) →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat N → (H →L[ℂ] H)),
      Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) σ (c * Formalism.QuantumDeterminants.fdegHC lam) := by
  obtain ⟨c, hc, hF⟩ := ReciprocityTheory.ChartRestriction.DS.fdCons_muG N ε
  refine ⟨c, hc, fun lam h hlam hgap hh ht hf H _ _ σ hσ => ?_⟩
  have : CompleteSpace H := hσ.1
  have : Nontrivial H := hσ.2.1
  have hp : 1 ≤ ReciprocityTheory.ChartRestriction.DS.pOf ε := by
    obtain ⟨a, ha⟩ := ht
    delta ReciprocityTheory.ChartRestriction.DS.pOf
    exact Finset.card_pos.2 ⟨a, by simpa using ha⟩
  have hq : 1 ≤ ReciprocityTheory.ChartRestriction.DS.qOf ε := by
    obtain ⟨a, ha⟩ := hf
    delta ReciprocityTheory.ChartRestriction.DS.qOf
    exact Finset.card_pos.2 ⟨a, by simpa using ha⟩
  have hq0 : 1 ≤ ReciprocityTheory.ChartRestriction.DS.S7.q0 ε := le_min hp hq
  have h8 : 8 * (N : ℝ) * ReciprocityTheory.ChartRestriction.DS.S7.q0 ε < h := ReciprocityTheory.ChartRestriction.DS.fdc_eight hh
  have hΨ : ∀ μ : Fin N → ℝ, ReciprocityTheory.ChartRestriction.DS.S7.IsHCParam μ → ReciprocityTheory.ChartRestriction.DS.GapAtLeast ε μ h →
      ∃ (T : ReciprocityTheory.ChartRestriction.DS.S7.KType ε (ReciprocityTheory.ChartRestriction.DS.lowK ε μ))
        (Ψ : Matrix (Fin N) (Fin N) ℂ → (T.V →L[ℂ] T.V)), ReciprocityTheory.ChartRestriction.DS.IsPsiFor ε μ T Ψ := by
    intro μ hμ hgμ
    obtain ⟨T⟩ := ReciprocityTheory.ChartRestriction.DS.HW.kType_exists ε μ hμ
    obtain ⟨m, hm⟩ := ReciprocityTheory.ChartRestriction.DS.Lap.LemK.exists_isMu hμ
    exact ⟨T, _, (ReciprocityTheory.ChartRestriction.DS.Lap.Base.psiFor _ _ μ h T m hμ hm hgμ hq0 h8).1⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  have hval := hF lam H σ v hlam hσ h hgap hh hp hq hΨ hv
  obtain ⟨d, hd⟩ := ReciprocityTheory.ChartRestriction.DS.fdcGood_of_isDS hσ
  have := ReciprocityTheory.ChartRestriction.DS.muCD_isHaar ε
  have hs := Measure.haarScalarFactor_pos_of_isHaarMeasure (Formalism.REAL.muG ε) (ReciprocityTheory.ChartRestriction.DS.muCD ε)
  have heq := Measure.isMulLeftInvariant_eq_smul (Formalism.REAL.muG ε) (ReciprocityTheory.ChartRestriction.DS.muCD ε)
  have hc' : (0 : ℝ) < (Measure.haarScalarFactor (Formalism.REAL.muG ε) (ReciprocityTheory.ChartRestriction.DS.muCD ε) : ℝ) := by
    exact_mod_cast hs
  obtain ⟨s, hs0, hEq⟩ : ∃ s : ℝ, 0 < s ∧ Formalism.REAL.muG ε = ENNReal.ofReal s • ReciprocityTheory.ChartRestriction.DS.muCD ε :=
    ⟨_, hc', by rw [ENNReal.ofReal_coe_nnreal]; exact heq⟩
  have hd2 := ReciprocityTheory.ChartRestriction.DS.isFdeg_smul hs0 hd
  rw [← hEq] at hd2
  have e : d / s = c * Formalism.QuantumDeterminants.fdegHC lam := by
    rw [← ReciprocityTheory.ChartRestriction.DS.fdegOf_of_isFdeg' hd2 hv]
    exact hval
  rwa [e] at hd2

theorem isHCParam_sub {N : ℕ} {lam : Fin N → ℝ} (s : Fin N) (hl : Formalism.QuantumDeterminants.IsHCParam lam)
    (hw : ∀ a c, a < c → 2 ≤ lam a - lam c) : Formalism.QuantumDeterminants.IsHCParam (lam - Pi.single s 1) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · have := hw a b hab
    simp only [Pi.sub_apply, Pi.single_apply]
    split_ifs <;> linarith
  · obtain ⟨m, hm⟩ := hl.2 a
    by_cases ha : a = s
    · subst ha
      refine ⟨m - 1, ?_⟩
      simp only [Pi.sub_apply, Pi.single_eq_same]
      push_cast
      linarith
    · refine ⟨m, ?_⟩
      simp only [Pi.sub_apply, Pi.single_apply, if_neg ha]
      linarith

theorem gap_sub {N : ℕ} (ε : Fin N → Bool) (lam : Fin N → ℝ) (s : Fin N) {h : ℝ}
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h) : Formalism.QuantumDeterminants.GapAtLeast ε (lam - Pi.single s 1) (h - 1) := by
  intro a b hab
  have h1 := hg a b hab
  have e : (lam - Pi.single s 1 : Fin N → ℝ) a - (lam - Pi.single s 1 : Fin N → ℝ) b =
      (lam a - lam b) - ((Pi.single s (1 : ℝ) : Fin N → ℝ) a - (Pi.single s (1 : ℝ) : Fin N → ℝ) b) := by
    simp only [Pi.sub_apply]; ring
  have ht : |(Pi.single s (1 : ℝ) : Fin N → ℝ) a - (Pi.single s (1 : ℝ) : Fin N → ℝ) b| ≤ 1 := by
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  have := abs_sub_abs_le_abs_sub (lam a - lam b) ((Pi.single s (1 : ℝ) : Fin N → ℝ) a - (Pi.single s (1 : ℝ) : Fin N → ℝ) b)
  rw [e]
  linarith

theorem fdegHC_le {N : ℕ} (lam : Fin N → ℝ) (s : Fin N) (hw : ∀ a c, a < c → 2 ≤ lam a - lam c) :
    Formalism.QuantumDeterminants.fdegHC lam ≤ 2 ^ (N - 1) * Formalism.QuantumDeterminants.fdegHC (lam - Pi.single s 1) := by
  set lam' := lam - Pi.single s 1 with hlam'
  have hfac : ∀ a b : Fin N, a < b → |lam a - lam b| ≤ (if a = s then (2 : ℝ) else 1) * |lam' a - lam' b| := by
    intro a b hab
    have hne : a ≠ b := hab.ne
    have h2 := hw a b hab
    by_cases ha : a = s
    · subst ha
      have e1 : lam' a = lam a - 1 := by simp [hlam']
      have e2 : lam' b = lam b := by simp [hlam', Pi.single_apply, hne.symm]
      rw [if_pos rfl, e1, e2, abs_of_pos (by linarith), abs_of_pos (by linarith)]
      linarith
    · rw [if_neg ha, one_mul]
      by_cases hb : b = s
      · subst hb
        have e1 : lam' a = lam a := by simp [hlam', Pi.single_apply, ha]
        have e2 : lam' b = lam b - 1 := by simp [hlam']
        rw [e1, e2, abs_of_pos (by linarith), abs_of_pos (by linarith)]
        linarith
      · have e1 : lam' a = lam a := by simp [hlam', Pi.single_apply, ha]
        have e2 : lam' b = lam b := by simp [hlam', Pi.single_apply, hb]
        rw [e1, e2]
  have hcount : ∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), (if a = s then (2 : ℝ) else 1) ≤
      2 ^ (N - 1) := by
    rw [Finset.prod_eq_single s (fun a _ ha => by simp [ha]) (fun h => absurd (Finset.mem_univ s) h)]
    simp only [if_pos rfl, Finset.prod_const]
    apply pow_le_pow_right₀ (by norm_num)
    have hsub : univ.filter (fun b : Fin N => s < b) ⊆ univ.erase s := by
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      simp [hb.ne']
    calc (univ.filter (fun b : Fin N => s < b)).card ≤ (univ.erase s).card := Finset.card_le_card hsub
      _ = N - 1 := by simp [Finset.card_erase_of_mem]
  have hnum : ∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), |lam a - lam b| ≤
      2 ^ (N - 1) * ∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), |lam' a - lam' b| := by
    calc ∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), |lam a - lam b|
        ≤ ∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b),
            ((if a = s then (2 : ℝ) else 1) * |lam' a - lam' b|) :=
          Finset.prod_le_prod₀ (fun a _ => Finset.prod_nonneg fun b _ => abs_nonneg _) fun a _ =>
            Finset.prod_le_prod₀ (fun b _ => abs_nonneg _) fun b hb => hfac a b (Finset.mem_filter.1 hb).2
      _ = (∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), (if a = s then (2 : ℝ) else 1)) *
            ∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), |lam' a - lam' b| := by
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun a _ => ?_
          rw [Finset.prod_mul_distrib]
      _ ≤ 2 ^ (N - 1) * ∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), |lam' a - lam' b| :=
          mul_le_mul_of_nonneg_right hcount (Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun b _ => abs_nonneg _)
  have hD : 0 < ∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) :=
    Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => by
      have hab : a < b := (Finset.mem_filter.1 hb).2
      have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
      linarith
  delta Formalism.QuantumDeterminants.fdegHC
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right hnum hD.le

theorem degRatio_holds : DegRatio := by
  intro n e ε lam ε' mu B hP H H' _ _ _ _ π σ hπ hσ
  obtain ⟨i0, hi0⟩ := hP.neg
  have hε't : ∃ a, ε' a = true := by
    by_contra hne
    push_neg at hne
    have h1 := hP.pos
    have h0 : (univ.filter fun i => ε' i = true) = ∅ := by
      ext i
      simp [hne i]
    rw [h0, Finset.card_empty] at h1
    have : 0 < (univ.filter fun i => ε' i = false).card := Finset.card_pos.2 ⟨i0, by simp [hi0]⟩
    omega
  have hεt : ∃ a, ε a = true := ⟨e none, hP.signs.1⟩
  have hεf : ∃ a, ε a = false := ⟨e (some i0), by rw [hP.signs.2 i0]; exact hi0⟩
  obtain ⟨c, hc, hF⟩ := fdeg_const (n + 1) ε
  obtain ⟨c', -, hF'⟩ := fdeg_const n ε'
  have hM : (1 : ℝ) ≤ (n : ℝ) + 1 := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hthr : ReciprocityTheory.ChartRestriction.DS.thrStar ε + 1 < 1000 * ((n : ℝ) + 1) ^ 3 - 1 :=
    thrStar_lt ε (by push_cast; exact le_refl _) hM
  have hthr' : ReciprocityTheory.ChartRestriction.DS.thrStar ε' + 1 < 1000 * ((n : ℝ) + 1) ^ 3 - 1 :=
    thrStar_lt ε' (by linarith) hM
  refine ⟨⟨c' * Formalism.QuantumDeterminants.fdegHC mu, hF' mu _ hP.hmu hP.gap' (by linarith) hε't ⟨i0, hi0⟩ H' σ hσ⟩,
    c * Formalism.QuantumDeterminants.fdegHC lam, hF lam _ hP.hlam hP.gap (by linarith) hεt hεf H π hπ, fun s K _ _ ρ hρ => ?_⟩
  refine ⟨c * Formalism.QuantumDeterminants.fdegHC (lam - Pi.single s 1),
    hF _ _ (isHCParam_sub s hP.hlam hP.wide) (gap_sub ε lam s hP.gap) hthr hεt hεf K ρ hρ, ?_⟩
  have h2 := fdegHC_le lam s hP.wide
  simp only [Nat.add_sub_cancel] at h2
  calc c * Formalism.QuantumDeterminants.fdegHC lam ≤ c * (2 ^ n * Formalism.QuantumDeterminants.fdegHC (lam - Pi.single s 1)) :=
        mul_le_mul_of_nonneg_left h2 hc.le
    _ = 2 ^ n * (c * Formalism.QuantumDeterminants.fdegHC (lam - Pi.single s 1)) := by ring

end GlobalTheory.SepReal.FormalDegreeRatio
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FormalDegreeLoweringWeightRatioLeStatement
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalDegree_loweringWeight_ratio_le : DegRatio := by
  first | exact @GlobalTheory.SepReal.FormalDegreeRatio.degRatio_holds | exact GlobalTheory.SepReal.FormalDegreeRatio.degRatio_holds | (intros; apply GlobalTheory.SepReal.FormalDegreeRatio.degRatio_holds <;> assumption)
end
end
