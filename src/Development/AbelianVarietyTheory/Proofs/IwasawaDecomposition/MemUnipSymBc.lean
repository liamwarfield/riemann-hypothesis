module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDiagonalConjEdgeSumAddCharFiniteField
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelCharpoly.GaloisClause
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LinearDisjointAlgebraicClosure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitPlaceEqOfPlaceEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemUnipSymBc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymFrame

variable {D : D7}

def EwAt (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  ∀ y ∈ X.B.I.Lf, (1 - X.ew) • y ∈ wLf X w


open Classical in
def epsW (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : Fin D.R.k → VA X.B.I :=
  if EwAt X w then X.bw else fun i => X.bwd (Fin.rev i)

def symVec (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : Fin D.R.r → VA X.B.I :=
  GlobalTheory.SeeConjRead.flagV D.R.rS D.R.k D.R.r X.e0 X.f0 (epsW X w) X.z0

def IsMatIn (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {g : ℕ} (u : Fin D.R.r → VA X.B.I) (x : X.B.I.Gf)
    (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod g)) : Prop :=
  ∀ i, X.B.I.fmat x *ᵥ u i - ∑ j, (((N j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • u j ∈ wLf X w

end GlobalTheory.Mem.SymFrame

end

namespace GlobalTheory.Mem.SymFrame

theorem isMatIn_perm {D : D7} {X : HidaSetting D} {w : HeightOneSpectrum (𝓞 D.host.E)} {g : ℕ}
    (s : Fin D.R.r → VA X.B.I) (x : X.B.I.Gf) (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod g)) (π : Equiv.Perm (Fin D.R.r))
    (hN : IsMatIn X w (fun j => s (π.symm j)) x N) : IsMatIn X w s x (N.submatrix π π) := by
  intro i
  have h1 := hN (π i)
  rw [← Equiv.sum_comp π] at h1
  simpa [Matrix.submatrix_apply] using h1

theorem mem_unipSym_bc {κ κ' : Type} [CommRing κ] [CommRing κ'] (f : κ ≃+* κ') {r ρ k : ℕ} (u : GL (Fin r) κ) :
    Formalism.UG.bc (f : κ →+* κ') u ∈ unipSym κ' r ρ k ↔ u ∈ unipSym κ r ρ k := by
  have e : ∀ i j, ((Formalism.UG.bc (f : κ →+* κ') u : GL (Fin r) κ') : Matrix (Fin r) (Fin r) κ') i j =
      f ((u : Matrix (Fin r) (Fin r) κ) i j) := fun _ _ => rfl
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j ha hb hc => ?_⟩
    · have := h1 hij; rw [e] at this; exact f.injective (this.trans (map_zero f).symm)
    · have := h2 i; rw [e] at this; exact f.injective (this.trans (map_one f).symm)
    · have := h3 i j ha hb hc; rw [e] at this; exact f.injective (this.trans (map_zero f).symm)
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j ha hb hc => ?_⟩
    · show ((Formalism.UG.bc (f : κ →+* κ') u : GL (Fin r) κ') : Matrix (Fin r) (Fin r) κ') i j = 0
      rw [e, h1 hij, map_zero]
    · rw [e, h2 i, map_one]
    · rw [e, h3 i j ha hb hc, map_zero]

theorem edgeSum_bc {κ κ' : Type} [CommRing κ] [CommRing κ'] (f : κ ≃+* κ') {r : ℕ} (Ed : Fin r → Fin r → Prop)
    [DecidableRel Ed] (u : GL (Fin r) κ) : edgeSum Ed (Formalism.UG.bc (f : κ →+* κ') u) = f (edgeSum Ed u) := by
  unfold edgeSum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rfl
  · rw [map_zero]

end GlobalTheory.Mem.SymFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseFrobSet
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.OSplitBig

def sysPol (D : D7) (c : PlE D.host → ℕ → ℂ) (w : PlE D.host) : ℂ[X] :=
  X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV,
    C ((-1 : ℂ) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c w k) * X ^ (D.R.nV - k)

def frobSet (D : D7) (F : Finset (PlE D.host)) : Set (G D.host.E D.nd.Om) :=
  {σ | ∃ w : PlE D.host, w ∉ F ∧ IsSplitPl D.host w ∧
    ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ}

theorem dense_frobSet (D : D7) (h : GlobalTheory.RowTie.ChebSplit D.nd) (F : Finset (PlE D.host)) :
    Dense (frobSet D F) := h F

theorem heckePol_map (D : D7) (L : LocAll (lay0 D)) (i : (withLoc L).nd.Loc) (x : (withLoc L).nd.X i) (v : PlE D.host)
    (hv : SplitOut (withLoc L).nd i v) :
    (heckePol (withLoc L).nd i x v).map (iotaOC (withLoc L) i) =
      sysPol D (GlobalTheory.CoefDuty.ptSys (withLoc L) i x) v := by
  have hS := hv
  obtain ⟨hsp, hl, hSi, hQ⟩ := hv
  have hgen : ∀ k ∈ Finset.Icc 1 D.R.nV,
      GenAt (withLoc L) ((withLoc L).nd.l i) ((withLoc L).nd.Q i) v k := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
    refine ⟨hsp, hl, ?_, hQ, hk1, hk2⟩
    intro hmem
    exact hSi (((withLoc L).nd.S_def i v).2 hmem)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [heckePol, sysPol, Polynomial.map_add (f := _), Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_C]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [GlobalTheory.CoefDuty.ptSys, if_pos (hgen k hk), map_mul, map_pow, map_neg, map_one, map_natCast]
  rfl

end GlobalTheory.OSplitBig

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormVEqAbsNorm
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
open Neutral.B1 hiding G IsPlaceOver

namespace GlobalTheory.ChiLocGal

section General

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]


open Pointwise in
theorem isFrob_conj {A : ValuationSubring Ω} {q : ℕ} {g σ : G E Ω} (hσ : IsFrob (F := E) (g • A) q σ) :
    IsFrob (F := E) A q (g⁻¹ * σ * g) := by
  have hm : ∀ x, g x ∈ g • A ↔ x ∈ A := fun x => ValuationSubring.smul_mem_pointwise_smul_iff
  refine ⟨?_, fun x hx => ?_⟩
  · have h1 : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h1, inv_smul_smul]
  · have h1 := hσ.2 (g x) (by rwa [ValuationSubring.valuation_le_one_iff, hm,
      ← ValuationSubring.valuation_le_one_iff])
    have e : σ (g x) - g x ^ q = g ((g⁻¹ * σ * g) x - x ^ q) := by
      rw [map_sub, map_pow, AlgEquiv.mul_apply, AlgEquiv.mul_apply, mul_inv_apply]
    rwa [e, valuation_lt_one_iff', ← map_inv₀, hm, hm, map_eq_zero_iff _ g.injective,
      ← valuation_lt_one_iff'] at h1

theorem frob_any [IsAlgClosure E Ω] {B : Type} [CommGroup B] {r r' : G E Ω →* B}
    {v : HeightOneSpectrum (𝓞 E)} {A₀ A : ValuationSubring Ω} (h0 : IsPlaceOver A₀ v) (hA : IsPlaceOver A v)
    (h : ∀ σ : G E Ω, IsFrob (F := E) A₀ (normV v) σ → r σ = r' σ) {σ : G E Ω}
    (hσ : IsFrob (F := E) A (normV v) σ) : r σ = r' σ := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver h0 hA
  have e : ∀ f : G E Ω →* B, f (g⁻¹ * σ * g) = f σ := fun f => by
    rw [map_mul, map_mul, map_inv, mul_comm (f g)⁻¹ (f σ), mul_assoc, inv_mul_cancel, mul_one]
  rw [← e r, ← e r']
  exact h _ (isFrob_conj hσ)

theorem locM_eq (P : HeightOneSpectrum (𝓞 E)) (x : (P.adicCompletion E)ˣ) :
    Units.map (Formalism.L2.NC.locM P) x = localIdele E P x := by
  rfl

end General

section Values

variable {E : Type} [Field E] [NumberField E]

theorem val_of_at {χ : HChar E} {ψ : Formalism.L2.NC.HC E} (h : ∀ x, ψ.χ x = χ.1 x) {P : HeightOneSpectrum (𝓞 E)} {α : ℂ}
    (hα : ψ.At P α) : ((χ.val P : ℂˣ) : ℂ) = α := by
  rw [← hα.2 _ (unif_spec P), h, locM_eq]
  rfl

theorem normV_eq_absNorm (P : HeightOneSpectrum (𝓞 E)) : normV P = Ideal.absNorm P.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

theorem val_block {μ η : HChar E} {r : ℕ} {P : HeightOneSpectrum (𝓞 E)} {α z : ℂ}
    (hα : (((μ * η⁻¹).val P : ℂˣ) : ℂ) = α) (hz : z = α⁻¹ * (Real.sqrt (normV P) : ℂ) ^ (-(r : ℤ))) :
    (((GlobalTheory.GalChar.block μ η r).val P : ℂˣ) : ℂ) = z⁻¹ := by
  rw [GlobalTheory.GalChar.block_val, hα, hz, mul_inv, inv_inv, zpow_neg, inv_inv, zpow_natCast, ← normV_eq_absNorm]
  congr 1
  have h0 : (0 : ℝ) ≤ (normV P : ℝ) := Nat.cast_nonneg _
  rw [show ((normV P : ℕ) : ℂ) = ((normV P : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow h0,
    Real.sqrt_eq_rpow, ← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul h0]
  congr 2
  ring

end Values

end GlobalTheory.ChiLocGal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfOfNodupAlg
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutQuot

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

structure AlgWtM where
  d : ℕ
  ρ : Representation ℂ (GQ L n) (Fin d → ℂ)
  alg : IsAlgWeight L n ρ
  irr : ρ.IsIrreducible

structure AutRepM extends AlgWtM L n where
  S : Submodule ℂ (GAf L n → (Fin d → ℂ))
  irrS : NG.IsIrrRep ρ S

variable {L n}

def AlgWtM.toAlgWt (m : AlgWtM L n) : NG.AlgWt L n := ⟨Fin m.d → ℂ, m.ρ, m.alg, m.irr⟩

def AutRepM.toAutRep (m : AutRepM L n) : NG.AutRep L n := ⟨m.toAlgWtM.toAlgWt, m.S, m.irrS⟩

variable (L n)

def AUq : Type := {X : Set (AutRepM L n) // ∃ π : NG.AutRep L n, X = {m | π.Iso m.toAutRep}}

def WtQ : Type := {X : Set (AlgWtM L n) // ∃ a : NG.AlgWt L n, X = {m | a.Iso m.toAlgWt}}

variable {L n}

def clsA (π : NG.AutRep L n) : AUq L n := ⟨{m | π.Iso m.toAutRep}, π, rfl⟩

def clsW (a : NG.AlgWt L n) : WtQ L n := ⟨{m | a.Iso m.toAlgWt}, a, rfl⟩

def AUq.rep (X : AUq L n) : NG.AutRep L n := X.2.choose

def WtQ.rep (X : WtQ L n) : NG.AlgWt L n := X.2.choose

theorem AUq.cls_rep (X : AUq L n) : clsA X.rep = X := Subtype.ext X.2.choose_spec.symm

theorem WtQ.cls_rep (X : WtQ L n) : clsW X.rep = X := Subtype.ext X.2.choose_spec.symm

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def LocAt (π : NG.AutRep L n) (w : HeightOneSpectrum (𝓞 L)) (x : GlobalTheory.LocGL.IrrGL (k := w.adicCompletion L)) : Prop :=
  ∃ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (h : s.w = w),
    IsLocS π.S s σ ∧ HEq (GlobalTheory.LocLanglands.cls σ) x

end


open Classical in
def hwOf (a : NG.AlgWt L n) (τ : L →+* ℂ) : Fin n → ℤ :=
  if h : ∃ lam, a.HWAt τ lam ∧ Antitone lam then h.choose else 0

theorem hwOf_antitone (a : NG.AlgWt L n) (τ : L →+* ℂ) : Antitone (hwOf a τ) := by
  unfold hwOf
  split_ifs with h
  · exact h.choose_spec.2
  · exact fun _ _ _ => le_rfl


open Classical in
def satOf (π : NG.AutRep L n) (w : HeightOneSpectrum (𝓞 L)) : Multiset ℂ :=
  if h : ∃ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ),
      NG.OverPl w v ∧ NG.SatAt π Dv α
  then Finset.univ.val.map h.choose_spec.choose_spec.choose else Multiset.replicate (n / 2) 1

theorem satOf_card (π : NG.AutRep L n) (w : HeightOneSpectrum (𝓞 L)) : Multiset.card (satOf π w) = n / 2 := by
  unfold satOf
  split_ifs <;> simp

theorem infOf_card (lam : Fin n → ℤ) : Multiset.card (NG.infOf lam) = n := by
  simp [NG.infOf]

theorem infOf_nodup_alg {lam : Fin n → ℤ} (hl : Antitone lam) : (NG.infOf lam).Nodup ∧
    ∀ x ∈ NG.infOf lam, ∃ k : ℤ, x = (k : ℂ) + ((n : ℂ) - 1) / 2 := by
  refine ⟨?_, ?_⟩
  · unfold NG.infOf
    refine Multiset.Nodup.map_on (fun i _ j _ hij => ?_) Finset.univ.nodup
    have h1 : ((lam i - (i : ℕ) : ℤ) : ℂ) = ((lam j - (j : ℕ) : ℤ) : ℂ) := by
      push_cast; linear_combination hij
    have h2 : lam i - (i : ℕ) = lam j - (j : ℕ) := by exact_mod_cast h1
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hl (le_of_lt h); have : (i : ℕ) < (j : ℕ) := h; omega
    · have := hl (le_of_lt h); have : (j : ℕ) < (i : ℕ) := h; omega
  · intro x hx
    unfold NG.infOf at hx
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hx
    exact ⟨lam i - (i : ℕ), by push_cast; ring⟩

end GlobalTheory.AutQuot

end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutQuot

open Classical in
def wtOf (D : D7) (π : NG.AutRep D.host.E D.R.nV) : WtQ D.host.E D.R.nV :=
  if h : ∃ b, π.toAlgWt.IsDual b then clsW h.choose else clsW π.toAlgWt

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)


open Classical in
def locOf (π : NG.AutRep D.host.E D.R.nV) (w : PlE D.host) : D.naut.LP w :=
  if h : ∃ x, LocAt π w x then (T.e w).symm (GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w) h.choose)
  else D.naut.lpZero w


end GlobalTheory.AutQuot

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivariantLabelMapTwistCuspidalLabel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivariantLabelMapTwistCuspidalLabel
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.CuspTwist

open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES PI.GreenLabelMapW IntermediateField

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem algebraMap_det_eq_pow {ι : Type} [Fintype ι] [DecidableEq ι] (γ : GL ι K)
    (hγ : Irreducible (γ : Matrix ι ι K).charpoly) {z : AlgebraicClosure K}
    (hz : aeval z (γ : Matrix ι ι K).charpoly = 0) :
    algebraMap K (AlgebraicClosure K) (Matrix.det (γ : Matrix ι ι K)) =
      z ^ ∑ i ∈ Finset.range (Fintype.card ι), Fintype.card K ^ i := by
  have hint : IsIntegral K z := Algebra.IsIntegral.isIntegral z
  have hmin : (γ : Matrix ι ι K).charpoly = minpoly K z :=
    minpoly.eq_of_irreducible_of_monic hγ hz (Matrix.charpoly_monic _)
  have hdeg : (minpoly K z).natDegree = Fintype.card ι := by
    rw [← hmin, Matrix.charpoly_natDegree_eq_dim]
  let pb := IntermediateField.adjoin.powerBasis hint
  have hnorm : Algebra.norm K pb.gen = Matrix.det (γ : Matrix ι ι K) := by
    rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, Matrix.det_eq_sign_charpoly_coeff, hmin]
    have h1 : pb.dim = Fintype.card ι := by
      rw [IntermediateField.adjoin.powerBasis_dim, hdeg]
    have h2 : pb.gen = IntermediateField.AdjoinSimple.gen K z := IntermediateField.adjoin.powerBasis_gen hint
    rw [h1, h2, IntermediateField.minpoly_gen]
  haveI : FiniteDimensional K K⟮z⟯ := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite K⟮z⟯ := Module.finite_of_finite K
  have hfr : Module.finrank K K⟮z⟯ = Fintype.card ι := by
    rw [IntermediateField.adjoin.finrank hint, hdeg]
  have h3 := FiniteField.algebraMap_norm_eq_pow_sum (K := K) (L := K⟮z⟯) (x := pb.gen)
  rw [hnorm, hfr, Nat.card_eq_fintype_card] at h3
  have h5 : ((pb.gen ^ ∑ i ∈ Finset.range (Fintype.card ι), Fintype.card K ^ i : K⟮z⟯) :
      AlgebraicClosure K) = z ^ ∑ i ∈ Finset.range (Fintype.card ι), Fintype.card K ^ i := by
    rw [IntermediateField.coe_pow, IntermediateField.adjoin.powerBasis_gen hint,
      IntermediateField.AdjoinSimple.coe_gen]
  rw [← h5, ← h3]
  rfl

theorem gen_one_pow_eq_det (Cv : LabelConv K) {ι : Type} [Fintype ι] [DecidableEq ι]
    (hι : 1 ≤ Fintype.card ι) (γ : GL ι K) (hγ : Irreducible (γ : Matrix ι ι K).charpoly)
    {z : AlgebraicClosure K} (hz : aeval z (γ : Matrix ι ι K).charpoly = 0) {m : ℕ}
    (hm : Cv.gen (Fintype.card ι) ^ m = z) :
    Cv.gen 1 ^ m = algebraMap K (AlgebraicClosure K) (Matrix.det (γ : Matrix ι ι K)) := by
  have hn := Cv.gen_norm 1 (Fintype.card ι) le_rfl hι
  rw [one_mul, pow_one] at hn
  rw [algebraMap_det_eq_pow γ hγ hz, ← hn, ← hm, ← pow_mul, ← pow_mul,
    Nat.geomSum_eq Fintype.one_lt_card, mul_comm]

theorem twist_clause (Cv : LabelConv K) (hC : CuspParam K Cv) (d : ℕ)
    (τ τ' : FDRep ℂ (GL (Fin d) K)) (x : K) (hd : 1 ≤ d) (hx : x ≠ 0) (hs : Simple τ)
    (hc : IsCuspidal K τ) (hs' : Simple τ') (hc' : IsCuspidal K τ')
    (htr : ∀ (γ : GL (Fin d) K) (m : ℕ),
      Cv.gen 1 ^ m = algebraMap K (AlgebraicClosure K) (Matrix.det (γ : Matrix (Fin d) (Fin d) K)) →
      LinearMap.trace ℂ τ' (τ'.ρ γ) =
        Cv.ι (algebraMap K (AlgebraicClosure K) x) ^ m * LinearMap.trace ℂ τ (τ.ρ γ)) :
    rootsBar K (greenLab Cv d τ') =
      (rootsBar K (greenLab Cv d τ)).map (· * algebraMap K (AlgebraicClosure K) x) := by
  set xb := algebraMap K (AlgebraicClosure K) x with hxb
  have hxb0 : xb ≠ 0 := by
    rw [hxb]; exact (map_ne_zero_iff _ (algebraMap K (AlgebraicClosure K)).injective).2 hx
  obtain ⟨hm, hi, hX, hdeg, hval⟩ := greenLab_spec Cv hC hd hs hc
  have hdeg' : (greenLab Cv d τ).natDegree = d := by rw [hdeg, Fintype.card_fin]
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) (greenLab Cv d τ)
    (by rw [degree_eq_natDegree hm.ne_zero, hdeg']; exact_mod_cast (show d ≠ 0 by omega))
  have hf : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (y : AlgebraicClosure K),
      σ y * xb = σ (y * xb) := fun σ y => by rw [map_mul, hxb, AlgEquiv.commutes]
  have hinj : ∀ r₁ r₂ : AlgebraicClosure K, aeval r₁ (greenLab Cv d τ) = 0 →
      aeval r₂ (greenLab Cv d τ) = 0 → r₁ * xb = r₂ * xb → r₁ = r₂ :=
    fun _ _ _ _ h => mul_right_cancel₀ hxb0 h
  have hint : IsIntegral K (w * xb) := Algebra.IsIntegral.isIntegral _
  have hxq : ∀ i : ℕ, xb ^ (Fintype.card K ^ i) = xb := fun i => by
    rw [hxb, ← map_pow, FiniteField.pow_card_pow]
  have hlab : HasCuspLabel Cv τ' (minpoly K (w * xb)) := by
    refine ⟨minpoly.monic hint, minpoly.irreducible hint, ?_, ?_, ?_⟩
    · intro h
      have h0 := minpoly.aeval K (w * xb)
      rw [h, aeval_X] at h0
      exact mul_ne_zero (root_ne_zero hm hi hX hw) hxb0 h0
    · rw [natDegree_minpoly_eq hm hi hw (fun y => y * xb) hf hinj, hdeg]
    · intro y hy γ hγ z hz m hm'
      obtain ⟨r, hr, rfl⟩ := (conj_roots hm hi hw (fun y => y * xb) hf y).1 hy
      have hι : 1 ≤ Fintype.card (Fin d) := by rw [Fintype.card_fin]; exact hd
      rw [htr γ m (gen_one_pow_eq_det Cv hι γ hγ hz hm'), hval r hr γ hγ z hz m hm',
        mul_left_comm, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      have e : Cv.ι xb ^ (m * Fintype.card K ^ i) = Cv.ι xb ^ m := by
        rw [mul_comm, pow_mul, ← map_pow, hxq i]
      rw [map_mul, mul_pow, e, mul_comm]
  rw [greenLab_eq Cv hC hd hs' hc' hlab]
  exact aroots_eq_map hm hi hw (fun y => y * xb) hf hinj

theorem exists_labelMap_twist_cuspLabel :
    ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv K),
      Formalism.IrreducibleCountingLemmas.TYPES.CuspParam K C → ∃ O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap K C,
        Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O ∧ LabTwLawO O ∧
          ∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) K)), 1 ≤ d → CategoryTheory.Simple τ →
            Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel C τ (O.lab d τ) := by
  intro K _ _ _ Cv hC
  let O : LabelMap K Cv :=
    { lab := greenLab Cv
      lab_iso := greenLab_iso Cv
      lab_spec := fun d τ hd hs hc => by
        obtain ⟨h1, h2, h3, h4, -⟩ := greenLab_spec Cv hC hd hs hc
        exact ⟨h1, h2, h3, by rw [h4, Fintype.card_fin]⟩
      lab_inj := fun d τ τ' hd hs hc hs' hc' h =>
        (hC d hd).2.2 τ τ' (greenLab Cv d τ) hs hc hs' hc' (greenLab_spec Cv hC hd hs hc)
          (by rw [h]; exact greenLab_spec Cv hC hd hs' hc')
      lab_one := fun τ x hs hx htr => greenLab_one Cv hC τ x hs hx htr }
  refine ⟨O, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro d α a hα τ τ' hd hs hc hs' hc' htr
    exact galois_clause Cv hC d α a hα τ τ' hd hs hc hs' hc' htr
  · intro d τ τ' hd hs hc hs' hc' htr
    exact dual_clause Cv hC d τ τ' hd hs hc hs' hc' htr
  · intro d τ τ' x hd hx hs hc hs' hc' htr
    exact twist_clause Cv hC d τ τ' x hd hx hs hc hs' hc' htr
  · intro d τ hd hs hc
    exact greenLab_spec Cv hC hd hs hc

end GlobalTheory.CuspTwist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivariantLabelMapTwistCuspidalLabelStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equivariant_labelMap_twist_cuspidalLabel : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv K), Formalism.IrreducibleCountingLemmas.TYPES.CuspParam K C → ∃ O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap K C, Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O ∧ LabTwLawO O ∧ ∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) K)), 1 ≤ d → CategoryTheory.Simple τ → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel C τ (O.lab d τ) := by
  first | exact @GlobalTheory.CuspTwist.exists_labelMap_twist_cuspLabel | exact GlobalTheory.CuspTwist.exists_labelMap_twist_cuspLabel | (intros; apply GlobalTheory.CuspTwist.exists_labelMap_twist_cuspLabel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceOverSplitPlaceEqChosenOrConjugate
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceOverSplitPlaceEqChosenOrConjugate
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PlaceOverSplit

theorem eq_or_eq_cP : ∀ (D : D7), D.host.F = maximalRealSubfield D.host.E → ∀ (s : SplitPlace D.host.E) (Q : Formalism.L2.DIV.Pl D.host.E), Q.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = s.v.asIdeal → Q = s.w ∨ Q = GlobalTheory.IdemSupport.cP s.w := by
  intro D _ s Q hQ
  rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE (D := D) s.w Q (hQ.trans s.w_under.symm) with e | e
  · exact Or.inl e
  · refine Or.inr (e.trans (HeightOneSpectrum.ext (Ideal.ext fun x => ?_)))
    rw [GlobalTheory.SplitConjPlace.mem_conjPlE, GlobalTheory.IdemSupport.mem_cP]
    have : IsCMField.ringOfIntegersComplexConj D.host.E x = GlobalTheory.IdemSupport.cO D x := by
      apply RingOfIntegers.ext
      rw [IsCMField.coe_ringOfIntegersComplexConj, GlobalTheory.IdemSupport.cO_coe]
      rfl
    rw [this]

end GlobalTheory.PlaceOverSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceOverSplitPlaceEqChosenOrConjugateStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeOver_splitPlace_eq_chosen_or_conjugate : ∀ (D : D7), D.host.F = maximalRealSubfield D.host.E → ∀ (s : SplitPlace D.host.E) (Q : Formalism.L2.DIV.Pl D.host.E), Q.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = s.v.asIdeal → Q = s.w ∨ Q = GlobalTheory.IdemSupport.cP s.w := by
  first | exact @GlobalTheory.PlaceOverSplit.eq_or_eq_cP | exact GlobalTheory.PlaceOverSplit.eq_or_eq_cP | (intros; apply GlobalTheory.PlaceOverSplit.eq_or_eq_cP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricallyConnectedOfAlgClosedInFunctionField
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open scoped TensorProduct

namespace GlobalTheory.GeomConnFn

theorem isConnected_preimage {F : Type} [Field F] [CharZero F] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp F)
    [LocallyOfFiniteType p]
    (h : ∀ a : X.functionField, (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn p) a = 0) →
      a ∈ (GlobalTheory.Cartier.constFn p).range)
    (K : Type) [Field K] [Algebra F K] (U : X.Opens) (hU : IsAffineOpen U) (hx : genericPoint X ∈ U) :
    _root_.IsConnected
      (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap F K))) ⁻¹' (U : Set X)) := by
  let : Algebra F Γ(X, U) := (algX p U).toAlgebra
  let : Algebra F X.functionField := (GlobalTheory.Cartier.constFn p).toAlgebra
  have hft : (algX p U).FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩
      (show U ≤ p ⁻¹ᵁ ⊤ from le_top)).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.surjective)
  have : Algebra.FiniteType F Γ(X, U) := hft
  let j : Γ(X, U) →ₐ[F] X.functionField :=
    { GlobalTheory.Cartier.fnOf U hx with
      commutes' := fun a => RingHom.congr_fun (GlobalTheory.Cartier.fnOf_comp_algX p U hx) a }
  have : IsDomain (K ⊗[F] Γ(X, U)) :=
    GlobalTheory.GeomConn.isDomain_tensor j (GlobalTheory.Cartier.fnOf_injective U hx) (fun a ha => h a ha) K
  have : IsDomain (Γ(X, U) ⊗[F] K) := (Algebra.TensorProduct.comm F Γ(X, U) K).toMulEquiv.isDomain
  have hg : hU.fromSpec ≫ p = Spec.map (CommRingCat.ofHom (algebraMap F Γ(X, U))) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hU
      (show U ≤ p ⁻¹ᵁ ⊤ from le_top)
    rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have h1 : IsIntegral (pullback (hU.fromSpec ≫ p) (Spec.map (CommRingCat.ofHom (algebraMap F K)))) := by
    rw [hg]
    exact IsIntegral.of_isIso (pullbackSpecIso F Γ(X, U) K).inv
  have h2 := IsIntegral.of_isIso
    (pullbackRightPullbackFstIso p (Spec.map (CommRingCat.ofHom (algebraMap F K))) hU.fromSpec).inv
  rw [← hU.range_fromSpec, ← Scheme.Pullback.range_snd]
  exact isConnected_range (Scheme.Hom.continuous _)

theorem geometricallyConnected_of_locallyOfFiniteType {F : Type} [Field F] [CharZero F] {X : Scheme.{0}}
    [IsIntegral X] (p : X ⟶ Sp F) [LocallyOfFiniteType p]
    (h : ∀ a : X.functionField, (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn p) a = 0) →
      a ∈ (GlobalTheory.Cartier.constFn p).range) : GeometricallyConnected p := by
  refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.2 fun K _ _ => ?_⟩
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap F K))) :=
    ⟨fun x => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  obtain ⟨x₀, hx₀⟩ := (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap F K)))).surjective (genericPoint X)
  refine connectedSpace_iff_univ.2 ⟨⟨x₀, trivial⟩, isPreconnected_of_forall x₀ fun y _ => ?_⟩
  obtain ⟨U, hU, hy, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (Opens.mem_top (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap F K))) y))
  have hg := GlobalTheory.Cartier.gen_mem hy
  refine ⟨_, Set.subset_univ _, ?_, hy, (isConnected_preimage p h K U hU hg).isPreconnected⟩
  rw [Set.mem_preimage, hx₀]
  exact hg

end GlobalTheory.GeomConnFn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardFrameConjugateClose
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.StdFrames GlobalTheory.AdIsom GlobalTheory.IdemSupport

namespace GlobalTheory.ConjLt
variable {D : D7}

theorem lt_one_le_exp {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le'
  · obtain ⟨n, rfl⟩ := WithZero.ne_zero_iff_exists.1 hx
    have : (n : WithZero (Multiplicative ℤ)) = WithZero.exp (Multiplicative.toAdd n) := rfl
    rw [this, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [this, WithZero.exp_le_exp]
    omega

theorem cpt_sg_lt_one (Q : Pl D.host.E) (z : EAf D) (h : Valued.v (cpt Q z) < 1) :
    Valued.v (cpt (cP Q) (sg D z)) < 1 := by
  obtain ⟨π, hπ⟩ := Q.intValuation_exists_uniformizer
  set p : D.host.E := (π : D.host.E) with hp
  have hvp : Valued.v (cpt Q (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D p)) = WithZero.exp (-1) := by
    rw [cpt_inc, Formalism.UG.P.levelaf_valued_algebraMap, hp, ← hπ]
    exact Q.valuation_of_algebraMap π
  have hp0 : p ≠ 0 := by
    rintro h0
    rw [h0, map_zero, map_zero, map_zero] at hvp
    exact WithZero.exp_ne_zero hvp.symm
  set a := z * GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D p⁻¹ with ha
  have hza : z = a * GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D p := by
    rw [ha, mul_assoc, ← map_mul, inv_mul_cancel₀ hp0, map_one, mul_one]
  have hva : Valued.v (cpt Q a) ≤ 1 := by
    have e1 : Valued.v (cpt Q a) * WithZero.exp (-1) = Valued.v (cpt Q z) := by
      rw [← hvp, ← Valuation.map_mul, ← map_mul, ← hza]
    have e2 := lt_one_le_exp h
    rw [← e1] at e2
    by_contra hc
    push_neg at hc
    have : WithZero.exp (-1) < Valued.v (cpt Q a) * WithZero.exp (-1) := by
      calc WithZero.exp (-1) = 1 * WithZero.exp (-1) := (one_mul _).symm
        _ < _ := mul_lt_mul_of_pos_right hc (WithZero.exp_pos)
    exact absurd e2 (not_le.2 this)
  have h1 := (cpt_cjA_le_iff Q a).2 hva
  have hs : sg D z = GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D a * GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D (star p) := by
    rw [hza, map_mul]; rfl
  have h2 : Valued.v (cpt (cP Q) (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D (star p))) < 1 := by
    rw [cpt_inc, Formalism.UG.P.levelaf_valued_algebraMap]
    have e : star p = ((cO D π : 𝓞 D.host.E) : D.host.E) := rfl
    rw [e, (cP Q).valuation_lt_one_iff_mem, mem_cP, cO_cO, ← Q.intValuation_lt_one_iff_mem, hπ]
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  rw [hs, map_mul, Valuation.map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' h1) h2

theorem conj_sub_one {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ} (β x : GL (Fin n) A)
    (R U' : Matrix (Fin n) (Fin n) A) (hX : Formalism.UG.cT σ x.val * R * x.val = R)
    (hU : U' * (Formalism.UG.cT σ β.val * R * β.val) = 1) :
    (β⁻¹ * x * β).val - 1 = U' * (Formalism.UG.cT σ (β⁻¹ * x⁻¹ * β).val - 1) * (Formalism.UG.cT σ β.val * R * β.val) := by
  set G := Formalism.UG.cT σ β.val * R * β.val with hG
  set Y := (β⁻¹ * x * β).val with hYdef
  set Yi := (β⁻¹ * x⁻¹ * β).val with hYidef
  have hYYi : Y * Yi = 1 := by
    rw [hYdef, hYidef, ← Units.val_mul]
    rw [show β⁻¹ * x * β * (β⁻¹ * x⁻¹ * β) = 1 by group, Units.val_one]
  have hY : Y = (β⁻¹).val * x.val * β.val := by rw [hYdef, Units.val_mul, Units.val_mul]
  have c1 : ∀ Z : Matrix (Fin n) (Fin n) A, Formalism.UG.cT σ (β⁻¹).val * (Formalism.UG.cT σ β.val * Z) = Z := by
    intro Z
    rw [← Matrix.mul_assoc, ← cT_mul', Units.mul_inv, cT_one', Matrix.one_mul]
  have c2 : ∀ Z : Matrix (Fin n) (Fin n) A, β.val * ((β⁻¹).val * Z) = Z := by
    intro Z
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hUY : Formalism.UG.cT σ Y * G * Y = G := by
    rw [hY, hG, cT_mul', cT_mul']
    simp only [Matrix.mul_assoc, c1, c2]
    rw [show Formalism.UG.cT σ x.val * (R * (x.val * β.val)) = (Formalism.UG.cT σ x.val * R * x.val) * β.val by
        simp only [Matrix.mul_assoc], hX]
  have hGY : G * Y = Formalism.UG.cT σ Yi * G := by
    have := congrArg (fun Z => Formalism.UG.cT σ Yi * Z) hUY
    rw [← this, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← cT_mul', hYYi, cT_one', Matrix.one_mul]
  have e1 : Y = U' * (G * Y) := by rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  calc Y - 1 = U' * (G * Y) - U' * G := by rw [← e1, hU]
    _ = U' * (Formalism.UG.cT σ Yi * G) - U' * G := by rw [hGY]
    _ = U' * (Formalism.UG.cT σ Yi - 1) * G := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.mul_assoc]

theorem frame_mat_sub_one_lt : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∀ (g : GA D V) (Q : Formalism.L2.DIV.Pl D.host.E), (∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * (finE V g)⁻¹ * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) → ∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt (GlobalTheory.IdemSupport.cP Q) ((β⁻¹ * finE V g * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1 := by
  intro D V β Λ N hSD g Q h a b
  obtain ⟨hGi, U', hU'i, hU'⟩ := unimod_of_isSD hSD
  have hX : Formalism.UG.cT (sg D) (finE V g).val * GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM V.gram * (finE V g).val =
      GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM V.gram := GlobalTheory.LevSplit.finE_mem_UA V g
  have hYsub := conj_sub_one (sg D) β (finE V g) _ U' hX hU'
  have hM : ∀ i j, Valued.v (cpt (cP Q) ((Formalism.UG.cT (sg D) (β⁻¹ * (finE V g)⁻¹ * β).val - 1) i j)) < 1 := by
    intro i j
    have e : (Formalism.UG.cT (sg D) (β⁻¹ * (finE V g)⁻¹ * β).val - 1) i j =
        sg D ((β⁻¹ * (finE V g)⁻¹ * β).val j i - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) j i) := by
      simp only [Formalism.UG.cT, Matrix.sub_apply, Matrix.transpose_apply, Matrix.map_apply, map_sub, Matrix.one_apply]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij, if_neg (Ne.symm hij), map_zero]
    rw [e]
    exact cpt_sg_lt_one Q _ (h j i)
  have hint : ∀ x ∈ GlobalTheory.StdFrames.OA D, Valued.v (cpt (cP Q) x) ≤ 1 := fun x hx => (mem_OA x).1 hx (cP Q)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Matrix.sub_apply, hYsub, Matrix.mul_apply, map_sum]
  refine Valuation.map_sum_lt' _ zero_lt_one fun j _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, Valuation.map_mul, Matrix.mul_apply, map_sum]
  refine lt_of_le_of_lt (mul_le_of_le_one_right' (hint _ (hGi j b))) ?_
  refine Valuation.map_sum_lt' _ zero_lt_one fun i _ => ?_
  rw [map_mul, Valuation.map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint _ (hU'i a i))) (hM i j)

end GlobalTheory.ConjLt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameComponentEqOneOffSplitPlaceOfTrivOutside
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameComponentEqOneOffSplitPlaceOfTrivOutside
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FrameOffPlace

theorem swap_one_tmul_apply {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2)
    (ι : E ⊗[F1] FiniteAdeleRing (𝓞 F1) F1 →+* FiniteAdeleRing (𝓞 E) E)
    (hι : ∀ x a, ι (x ⊗ₜ[F1] a) = algebraMap E _ x * GlobalTheory.AdeleBaseChange.adMap F1 E a)
    (a : FiniteAdeleRing (𝓞 F2) F2) (Q : HeightOneSpectrum (𝓞 E)) :
    ι (Algebra.TensorProduct.comm F1 (FiniteAdeleRing (𝓞 F1) F1) E
        ((GlobalTheory.Mem.R3.swapCast h).symm ((1 : E) ⊗ₜ[F2] a))) Q =
      GlobalTheory.AdeleBaseChange.locMap F2 Q (a (Q.under (𝓞 F2))) := by
  subst h
  have e : (GlobalTheory.Mem.R3.swapCast (rfl : F1 = F1)).symm ((1 : E) ⊗ₜ[F1] a) = a ⊗ₜ[F1] (1 : E) := by
    apply (GlobalTheory.Mem.R3.swapCast (rfl : F1 = F1)).injective
    rw [RingEquiv.apply_symm_apply]
    rfl
  rw [e, Algebra.TensorProduct.comm_tmul, hι, map_one, one_mul, GlobalTheory.AdeleBaseChange.adMap_apply]

end GlobalTheory.FrameOffPlace

namespace GlobalTheory.FrameOffPlace


set_option maxHeartbeats 1000000 in
theorem cpt_conj_finE_eq_one : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)), GlobalTheory.Mem.R3.StdFrame hF P → ∀ (s : SplitPlace D.host.E) (κ : Formalism.AUTREP.GAf D.host.E n), TrivOutside {s.v} κ → ∀ (Q : Formalism.L2.DIV.Pl D.host.E), Q.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) ≠ s.v.asIdeal → ∀ (a b : Fin V.rank), GlobalTheory.StdFrames.cpt Q ((β⁻¹ * finE V (P.ψ κ) * β).val a b) = GlobalTheory.StdFrames.cpt Q ((1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b) := by
  classical
  intro D V n hF P β hP s κ hκ Q hQ a b
  obtain ⟨⟨β0, β0', h1, -, hβ⟩, -⟩ := hP
  let v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) := Q.under _
  have hvs : v ∉ ({s.v} : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))) := by
    intro h
    exact hQ (congrArg HeightOneSpectrum.asIdeal (Set.mem_singleton_iff.1 h))
  let f : ReciprocityTheory.Aut.AL D.host.E →+* Q.adicCompletion D.host.E :=
    (GlobalTheory.StdFrames.cpt Q).comp ((Formalism.IndefR.Lev.swapAE D).comp (GlobalTheory.Mem.R3.swapCast hF).symm.toRingHom)
  have hf0 : ∀ c : ReciprocityTheory.Aut.AFplus D.host.E, ReciprocityTheory.Aut.evalAt D.host.E v c = 0 →
      f ((1 : D.host.E) ⊗ₜ c) = 0 := by
    intro c hc
    have e := swap_one_tmul_apply hF (GlobalTheory.StdFrames.toAd D) (GlobalTheory.StdFrames.toAd_spec D) c Q
    have e' : f ((1 : D.host.E) ⊗ₜ c) = GlobalTheory.AdeleBaseChange.locMap _ Q (c (Q.under _)) := e
    rw [e']
    change GlobalTheory.AdeleBaseChange.locMap _ Q (ReciprocityTheory.Aut.evalAt D.host.E v c) = 0
    rw [hc, map_zero]
  have hsurj : Function.Surjective (ReciprocityTheory.Aut.evalAt D.host.E v) := fun c =>
    ⟨⟨Pi.single v c, (Filter.eventually_cofinite_ne v).mono fun w hw => by
      rw [Pi.single_eq_of_ne hw]; exact zero_mem _⟩, by
      change Pi.single v c v = c
      rw [Pi.single_eq_same]⟩
  have hker : ∀ y y' : ReciprocityTheory.Aut.AL D.host.E,
      ReciprocityTheory.Aut.compAt D.host.E v y = ReciprocityTheory.Aut.compAt D.host.E v y' → f y = f y' := by
    intro y y' h
    have hm : y - y' ∈ RingHom.ker
        (Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield D.host.E) D.host.E) (ReciprocityTheory.Aut.evalAt D.host.E v)) := by
      rw [RingHom.mem_ker, map_sub, sub_eq_zero]
      exact h
    rw [Algebra.TensorProduct.lTensor_ker _ hsurj] at hm
    have hle : RingHom.ker (ReciprocityTheory.Aut.evalAt D.host.E v) ≤ (RingHom.ker f).comap
        (Algebra.TensorProduct.includeRight : ReciprocityTheory.Aut.AFplus D.host.E →ₐ[maximalRealSubfield D.host.E] ReciprocityTheory.Aut.AL D.host.E) := by
      intro c hc
      rw [Ideal.mem_comap, RingHom.mem_ker]
      exact hf0 c hc
    have h2 := Ideal.map_le_iff_le_comap.2 hle hm
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h2
    exact h2
  have hK : (κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map f = 1 := by
    have e := hκ v hvs
    ext i j
    have e2 := congrFun (congrFun e i) j
    rw [Matrix.map_apply] at e2 ⊢
    rw [Matrix.one_apply] at e2 ⊢
    split_ifs at e2 ⊢
    · rw [hker _ 1 (e2.trans (map_one _).symm), map_one]
    · rw [hker _ 0 (e2.trans (map_zero _).symm), map_zero]
  let g : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) →+* Q.adicCompletion D.host.E :=
    (GlobalTheory.StdFrames.cpt Q).comp (Formalism.IndefR.Lev.swapAE D)
  have hmain : (Formalism.IndefR.Lev.finE V (P.ψ κ)).val.map (GlobalTheory.StdFrames.cpt Q) = 1 := by
    have e1 : (Formalism.IndefR.Lev.finE V (P.ψ κ)).val = (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (P.ψ κ)).map (Formalism.IndefR.Lev.swapAE D) := rfl
    have e2 : ∀ {k l : Type} (M : Matrix k l (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)),
        (M.map (Formalism.IndefR.Lev.swapAE D)).map (GlobalTheory.StdFrames.cpt Q) = M.map g := fun M => rfl
    have e3 : ((κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.Mem.R3.swapCast hF).symm).map g =
        (κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map f := rfl
    rw [e1, e2, hβ κ, Matrix.map_mul, Matrix.map_mul, e3, hK, Matrix.mul_one, ← Matrix.map_mul, h1,
      Matrix.map_one _ (map_zero g) (map_one g)]
  have e : (β⁻¹ * Formalism.IndefR.Lev.finE V (P.ψ κ) * β).val.map (GlobalTheory.StdFrames.cpt Q) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)).map (GlobalTheory.StdFrames.cpt Q) := by
    have hinv : (β⁻¹).val.map (GlobalTheory.StdFrames.cpt Q) * β.val.map (GlobalTheory.StdFrames.cpt Q) = 1 := by
      rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.map_one _ (map_zero _) (map_one _)]
    calc (β⁻¹ * Formalism.IndefR.Lev.finE V (P.ψ κ) * β).val.map (GlobalTheory.StdFrames.cpt Q)
        = (β⁻¹).val.map (GlobalTheory.StdFrames.cpt Q) * (Formalism.IndefR.Lev.finE V (P.ψ κ)).val.map (GlobalTheory.StdFrames.cpt Q) *
            β.val.map (GlobalTheory.StdFrames.cpt Q) := by
          rw [Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul]
      _ = 1 := by rw [hmain, Matrix.mul_one, hinv]
      _ = _ := (Matrix.map_one _ (map_zero _) (map_one _)).symm
  exact congrFun (congrFun e a) b

end GlobalTheory.FrameOffPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameComponentEqOneOffSplitPlaceOfTrivOutsideStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameComponent_eq_one_off_splitPlace_of_trivOutside : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)), GlobalTheory.Mem.R3.StdFrame hF P → ∀ (s : SplitPlace D.host.E) (κ : Formalism.AUTREP.GAf D.host.E n), TrivOutside {s.v} κ → ∀ (Q : Formalism.L2.DIV.Pl D.host.E), Q.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) ≠ s.v.asIdeal → ∀ (a b : Fin V.rank), GlobalTheory.StdFrames.cpt Q ((β⁻¹ * finE V (P.ψ κ) * β).val a b) = GlobalTheory.StdFrames.cpt Q ((1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b) := by
  first | exact @GlobalTheory.FrameOffPlace.cpt_conj_finE_eq_one | exact GlobalTheory.FrameOffPlace.cpt_conj_finE_eq_one | (intros; apply GlobalTheory.FrameOffPlace.cpt_conj_finE_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitPlaceWPlGw
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FixedPlaceOverType

theorem exists_splitPlace_w_plGw : ∀ (D : D7) (k : Fin 2) (v : D.nd.PlG k), ∃ s : SplitPlace D.host.E, s.w = D.naut.plGw k v :=
  fun D k v => GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw D ⟨k, v⟩

end GlobalTheory.FixedPlaceOverType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyResidualImage
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.ChiOneRead

theorem localIdele_eq {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (u : (P.adicCompletion E)ˣ) :
    Neutral.B1.localIdele E P u = Units.map (Formalism.L2.NC.locM P) u := by
  classical
  apply Units.ext
  rfl

theorem sqrt_zpow (q : ℕ) (r : ℕ) (t nV : ℕ) (h : nV = r + t) :
    ((Real.sqrt q : ℝ) : ℂ) ^ (-(r : ℤ)) = ((q : ℕ) : ℂ) ^ (((((t : ℝ) - 1) / 2 + (1 - (nV : ℝ)) / 2) : ℝ) : ℂ) := by
  subst h
  have e : (((t : ℝ) - 1) / 2 + (1 - ((r + t : ℕ) : ℝ)) / 2) = -(r : ℝ) / 2 := by push_cast; ring
  rw [e]
  rw [show ((q : ℕ) : ℂ) = ((q : ℝ) : ℂ) by norm_cast, ← Complex.ofReal_cpow (Nat.cast_nonneg _),
    ← Complex.ofReal_zpow]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  push_cast; ring

end GlobalTheory.ChiOneRead
end
end
