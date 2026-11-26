module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AmbientH1fOfLocalFiniteness
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PsiAtPsiAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralTateH2Top
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrysOnCondOfEveryDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjFunBaseRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodCoverGalois
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumSelfDualFramesBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepUniqueBaseChange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConditionsEveryLocalisationStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetPointGood
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.SetPtOff

theorem litBurnside_all (D : D7) : LitBurnside (G D.host.E D.nd.Om) := by
  intro l _ a ρ h
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    exact Subsingleton.elim _ _
  · apply GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub ρ
    refine ⟨?_, ?_, ?_⟩
    · intro hb
      have : (Pi.single (⟨0, ha⟩ : Fin a) (1 : CyclotomicNorms.Fbar l) : Fin a → CyclotomicNorms.Fbar l) ∈ (⊤ : Submodule (CyclotomicNorms.Fbar l) (Fin a → CyclotomicNorms.Fbar l)) := trivial
      rw [hb, Submodule.mem_bot] at this
      have h1 := congrFun this ⟨0, ha⟩
      simp at h1
    · intro g x _; trivial
    · intro W' _ hW'
      exact h W' (fun g _ x hx => hW' g x hx)

end GlobalTheory.SetPtOff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeWachModuleExistsProof
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeWachModuleExistsProof
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem wAll_holds : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), WAll D HW F :=
  fun D HW F Cm =>
    GlobalTheory.T.wachHypothesis_crystallineLattices D HW F Cm (GlobalTheory.T.wachModuleLocalConclusions_usedForms D HW F Cm).1 (GlobalTheory.T.wachModuleLocalConclusions_usedForms D HW F Cm).2 (GlobalTheory.crysOnCond_all D HW F)

end GlobalTheory.NLink
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeWachModuleExistsProofStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineLatticeWachModuleExists_proof : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), WAll D HW F := by
  first | exact @GlobalTheory.NLink.wAll_holds | exact GlobalTheory.NLink.wAll_holds | (intros; apply GlobalTheory.NLink.wAll_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFrameMatrixIntegralOfConjugateHalf
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFrameMatrixIntegralOfConjugateHalf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAdjInt

open Formalism.IndefR.Fin.LevelGroupLemmas.Lat Matrix

set_option synthInstance.maxHeartbeats 400000

theorem cA_smul_genE {D : D7} {S T : HSp D} (e : AE D) (c : EAf D) (τ : Fin T.rank → EAf D)
    (σ : Fin S.rank → EAf D) :
    cA D e • genE (S := S) (T := T) c τ σ = genE (sR D (toEAf D e) * c) τ σ := by
  ext i j
  simp only [genE, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mul_liftE, toEAf_cA, mul_assoc]


set_option maxHeartbeats 4000000 in
theorem frMapAdj_int_of_half : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → (∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ u : WO S T, u ∈ latO S T ΛS ΛT (fun _ => True) → IsHalf (cA D e) u → IsIntM (frMapAdj S T βS βT u) := by
  intro D S T ΛS ΛT βS βT hS hT fS fT P e he hP u hu hh
  have hx : cA D e • u = u := Matrix.ext fun i j => hh i j
  rw [← hx]
  clear hx hh
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, _, a, ha, s, hs, t, ht, rfl⟩ := hw
    show IsIntM (frMapAdj S T βS βT (cA D e • genL S T α a s t))
    rw [genL_eq_genE, cA_smul_genE, frMapAdj_genE]
    intro i j
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    have h1 : sR D (sR D (toEAf D e) * (eToEAf D a * ((1 : D.host.E) ⊗ₜ[D.host.F] α))) =
        (toEAf D e * eToEAf D (D.sp.cm.sig a)) * ((1 : D.host.E) ⊗ₜ[D.host.F] α) := by
      rw [map_mul, map_mul, sR_sR, sR_eTo, mul_assoc]
      congr 2
      show (star (1 : D.host.E)) ⊗ₜ[D.host.F] α = _
      rw [star_one]
    rw [h1]
    refine mul_mem (mul_mem (GlobalTheory.IdemIntegral.conj_mem_intAf D e P he hP a ha)
      (Subring.subset_closure (Or.inr ⟨⟨α, fun v => hα v⟩, rfl⟩))) (mul_mem ?_ ?_)
    · exact (fS _).1 (mem_hatL_of_mem hs) i
    · rw [Matrix.vecMul_vecMul]
      have hcol : (fun l => (GE T * (βT : Matrix (Fin T.rank) (Fin T.rank) (EAf D))) l j) =
          GE T *ᵥ (fun i => (βT : Matrix (Fin T.rank) (Fin T.rank) (EAf D)) i j) := by
        funext l; rw [Matrix.mul_apply]; rfl
      show (fun k => sR D (eToEAf D (t k))) ⬝ᵥ
        (fun l => (GE T * (βT : Matrix (Fin T.rank) (Fin T.rank) (EAf D))) l j) ∈ _
      rw [hcol]
      exact hform_int hT ht (col_mem_hatL fT j)
  | zero =>
    rw [smul_zero, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapAdj_zero]
    exact fun _ _ => zero_mem _
  | add x y _ _ hx hy =>
    rw [smul_add, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapAdj_add]
    exact isIntM_add hx hy
  | neg x _ hx =>
    rw [smul_neg, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapAdj_neg]
    exact fun i j => neg_mem (hx i j)

end GlobalTheory.HalfAdjInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFrameMatrixIntegralOfConjugateHalfStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjointFrameMatrix_integral_of_conjugate_half : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → (∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ u : WO S T, u ∈ latO S T ΛS ΛT (fun _ => True) → IsHalf (cA D e) u → IsIntM (frMapAdj S T βS βT u) := by
  first | exact @GlobalTheory.HalfAdjInt.frMapAdj_int_of_half | exact GlobalTheory.HalfAdjInt.frMapAdj_int_of_half | (intros; apply GlobalTheory.HalfAdjInt.frMapAdj_int_of_half <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.UseLoc

section Gen
variable {l : ℕ} [Fact l.Prime]

def incO {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) : ↥(OL LL) →+* ↥(OL LL') where
  toFun x := ⟨IntermediateField.inclusion h x, by
    have := x.2
    exact IsIntegral.map ((IntermediateField.inclusion h).restrictScalars ℤ_[l]) this⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

def incV {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (k : ℕ) : (Fin k → ↥LL.1) →+ (Fin k → ↥LL'.1) :=
  (AddMonoidHom.compLeft (IntermediateField.inclusion h).toRingHom.toAddMonoidHom (Fin k))

def liftQ {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (k : ℕ) :
    (Fin k → ↥LL.1) ⧸ stdG ↥(OL LL) ↥LL.1 k →+ (Fin k → ↥LL'.1) ⧸ stdG ↥(OL LL') ↥LL'.1 k :=
  QuotientAddGroup.lift _ ((QuotientAddGroup.mk' (stdG ↥(OL LL') ↥LL'.1 k).toAddSubgroup).comp (incV h k)) (by
    intro x hx
    obtain ⟨u, rfl⟩ := hx
    exact (QuotientAddGroup.eq_zero_iff _).2 ⟨fun j => incO h (u j), rfl⟩)

theorem liftQ_mk {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (k : ℕ) (v : Fin k → ↥LL.1) :
    liftQ h k (Submodule.Quotient.mk v) = Submodule.Quotient.mk (incV h k v) := rfl

end Gen
end GlobalTheory.UseLoc

namespace GlobalTheory.UseLoc

section AtW
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}

def locOC (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) :
    Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL) :=
  mapM (incO C.le) (Br.locO (D.nbr i w hw) (M.comp (decS D.nd w)))

def chiOC (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (χ : GE D.nd →* (D.nd.O i)ˣ) : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ :=
  (Units.map ((incO C.le).comp (D.nbr i w hw).eO.toRingHom).toMonoidHom).comp
    ((χ.comp (decS D.nd w)).comp (Br.iota D.nbr i w hw))

abbrev repV (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL)) :
    Representation ↥C.LL.1 (Br.G D.nbr i w hw) (Fin k → ↥C.LL.1) :=
  matRep (mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) N)

def latC (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL)) :
    Lattice (O := ↥(OL C.LL)) (repV C N) :=
  stdLatG Subtype.val_injective N

def chiT (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ) :
    Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ :=
  chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) * θ

def embC (HW : HWOf D.loc) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) :=
  ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hA.2.2).emb

end AtW
end GlobalTheory.UseLoc

namespace GlobalTheory.UseLoc

section AtW
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}


open Module in
def SetC (HW : HWOf D.loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL))
    (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
    (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
    (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
    (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ) : Prop :=
  tableLineDegreeTwo.TopHyp (Br.PD D.loc D.nbr i w hw) (embC HW C hA) D.R.t h w' η typ U
                     (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) ∧
    ∀ x, tableLineDegreeTwo.IsFull (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (tableLineDegreeTwo.jTil U w' D.R.t)
      (tableLineDegreeTwo.resPoly (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) D.R.t)
      (repV C (twistM (locOC C (rTwO D.nd i r x)) θ))

end AtW
end GlobalTheory.UseLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRankinSelbergSchurTermFinsuppEulerProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRankinSelbergSchurTermFinsuppEulerProduct
open MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.ZEul

open GlobalTheory.JSW

def partVec {n : ℕ} (l : {l : Fin n → ℕ // Antitone l}) : Fin n → ℤ := fun j => (l.1 j : ℤ)

theorem partVec_injective {n : ℕ} : Function.Injective (partVec (n := n)) := by
  intro a b h
  apply Subtype.ext; funext j
  have := congrFun h j
  simpa [partVec] using this

theorem partVec_valid {n : ℕ} (l : {l : Fin n → ℕ // Antitone l}) :
    (∀ i, 0 ≤ partVec l i) ∧ Antitone (partVec l) :=
  ⟨fun i => Int.natCast_nonneg _, fun a b h => Int.ofNat_le.2 (l.2 h)⟩

theorem mem_range_partVec {n : ℕ} {v : Fin n → ℤ} (hv : (∀ i, 0 ≤ v i) ∧ Antitone v) :
    v ∈ Set.range (partVec (n := n)) :=
  ⟨⟨fun i => (v i).toNat, fun a b h => Int.toNat_le_toNat (hv.2 h)⟩, by
    funext j; simp [partVec, Int.toNat_of_nonneg (hv.1 j)]⟩

theorem rsTerm_partVec (q : ℕ) {n : ℕ} (α β : Fin n → ℂ) (x : ℝ) (l : {l : Fin n → ℕ // Antitone l}) :
    rsTerm q α β x (partVec l) =
      schurAt l.1 α * conj (schurAt l.1 β) * ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, l.1 i) := by
  rw [rsTerm, if_pos (partVec_valid l)]
  simp [partVec]


open Classical in
def sqTerm (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) (v : Fin n → ℤ) : ℝ :=
  if (∀ i, 0 ≤ v i) ∧ Antitone v then
    ‖schurAt (fun i => (v i).toNat) α‖ ^ 2 * (q : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x))
  else 0

theorem sqTerm_nonneg (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) (v : Fin n → ℤ) : 0 ≤ sqTerm q α x v := by
  unfold sqTerm
  split_ifs
  · exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · exact le_rfl

theorem sqTerm_zero (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) : sqTerm q α x 0 = 1 := by
  have hs : schurAt (fun _ : Fin n => 0) α = 1 := by rw [schurAt, schur_zero]; simp
  rw [sqTerm, if_pos ⟨fun i => le_rfl, antitone_const⟩]
  simp [hs]

theorem sqTerm_partVec (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) (l : {l : Fin n → ℕ // Antitone l}) :
    sqTerm q α x (partVec l) = ‖schurAt l.1 α‖ ^ 2 * (q : ℝ) ^ (-(((∑ i, l.1 i : ℕ) : ℝ) * x)) := by
  rw [sqTerm, if_pos (partVec_valid l)]
  simp [partVec]

theorem norm_cpow_pow (q : ℕ) (hq : 0 < q) (x : ℝ) (k : ℕ) :
    ‖((q : ℂ) ^ (-(x : ℂ))) ^ k‖ = (q : ℝ) ^ (-((k : ℝ) * x)) := by
  rw [norm_pow, Complex.norm_natCast_cpow_of_pos hq]
  simp only [Complex.neg_re, Complex.ofReal_re]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q)]
  congr 1; ring

theorem norm_rsTerm_le (q : ℕ) (hq : 0 < q) {n : ℕ} (α β : Fin n → ℂ) (x : ℝ) (v : Fin n → ℤ) :
    ‖rsTerm q α β x v‖ ≤ (sqTerm q α x v + sqTerm q β x v) / 2 := by
  by_cases hv : (∀ i, 0 ≤ v i) ∧ Antitone v
  · rw [rsTerm, if_pos hv, sqTerm, if_pos hv, sqTerm, if_pos hv, norm_mul, norm_mul, Complex.norm_conj,
      norm_cpow_pow q hq]
    have hw : 0 ≤ (q : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    nlinarith [mul_nonneg (sq_nonneg (‖schurAt (fun i => (v i).toNat) α‖ - ‖schurAt (fun i => (v i).toNat) β‖)) hw]
  · rw [rsTerm, if_neg hv, sqTerm, if_neg hv, sqTerm, if_neg hv]; simp

end GlobalTheory.ZEul

namespace GlobalTheory.ZEul

open GlobalTheory.JSW

theorem summable_sqTerm {I : Type} (q : I → ℕ) {n : ℕ} (α : I → Fin n → ℂ) (x : ℝ)
    (h : GlobalTheory.RSPole.eulD q α x ≠ ⊤) :
    Summable fun p : I × {v : Fin n → ℤ // v ≠ 0} => sqTerm (q p.1) (α p.1) x p.2 := by
  set f : I → (Fin n → ℤ) → ℝ≥0∞ := fun i v => ENNReal.ofReal (sqTerm (q i) (α i) x v) with hf
  have hf0 : ∀ i, f i 0 = 1 := fun i => by simp [hf, sqTerm_zero]
  have hloc : ∀ i, ∑' v, f i v = GlobalTheory.RSPole.schurDir (q i) (α i) x := by
    intro i
    rw [← (partVec_injective (n := n)).tsum_eq]
    · rw [GlobalTheory.RSPole.schurDir]
      refine tsum_congr fun l => ?_
      simp only [hf, sqTerm_partVec]
    · intro v hv
      by_cases hval : (∀ j, 0 ≤ v j) ∧ Antitone v
      · exact mem_range_partVec hval
      · exact absurd (by simp [hf, sqTerm, if_neg hval]) hv
  have hE : ∑' l : I →₀ (Fin n → ℤ), l.prod f = GlobalTheory.RSPole.eulD q α x := by
    rw [(GlobalTheory.EulerSum.euler_product_intVec_ennreal n f hf0).2, GlobalTheory.RSPole.eulD]
    exact tprod_congr hloc
  have hinj : Function.Injective fun p : I × {v : Fin n → ℤ // v ≠ 0} => Finsupp.single p.1 p.2.1 := by
    intro p p' hp
    rcases (Finsupp.single_eq_single_iff _ _ _ _).1 hp with ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact Prod.ext h1 (Subtype.ext h2)
    · exact absurd h1 p.2.2
  have hle : ∑' p : I × {v : Fin n → ℤ // v ≠ 0}, f p.1 p.2 ≤ ∑' l : I →₀ (Fin n → ℤ), l.prod f := by
    have hc : (fun p : I × {v : Fin n → ℤ // v ≠ 0} => f p.1 p.2) =
        fun p => (fun l : I →₀ (Fin n → ℤ) => l.prod f) (Finsupp.single p.1 p.2.1) := by
      funext p; simp only; rw [Finsupp.prod_single_index (hf0 p.1)]
    rw [hc]
    exact (by refine' _root_.le_trans _ (_root_.tsum_comp_le_tsum_of_injective hinj _); exact _root_.le_rfl)
  have hfin : ∑' p : I × {v : Fin n → ℤ // v ≠ 0}, f p.1 p.2 ≠ ⊤ := ne_top_of_le_ne_top (hE ▸ h) hle
  refine (ENNReal.summable_toReal hfin).congr fun p => ?_
  simp only [hf]
  exact ENNReal.toReal_ofReal (sqTerm_nonneg _ _ _ _)

theorem hasSum_rsTerm_local (q : ℕ) {n : ℕ} (α β : Fin n → ℂˣ) (x : ℝ)
    (hs : Summable fun v : Fin n → ℤ => ‖rsTerm q (fun j => (α j : ℂ)) (fun j => (β j : ℂ)) x v‖) :
    HasSum (fun v => rsTerm q (fun j => (α j : ℂ)) (fun j => (β j : ℂ)) x v)
      (locL q (Finset.univ.val.map α) ((Finset.univ.val.map β).map (Units.map (starRingEnd ℂ).toMonoidHom))
        (x : ℂ)) := by
  set β' : Fin n → ℂˣ := fun j => Units.map (starRingEnd ℂ).toMonoidHom (β j) with hβ'
  have hconj : ∀ l : Fin n → ℕ, schurAt l (fun j => (β' j : ℂ)) = conj (schurAt l fun j => (β j : ℂ)) := by
    intro l
    rw [schurAt, schurAt, MvPolynomial.eval₂_comp_left, RingHom.ext_int ((starRingEnd ℂ).comp (Int.castRingHom ℂ))
      (Int.castRingHom ℂ)]
    rfl
  have hm : (Finset.univ.val.map β).map (Units.map (starRingEnd ℂ).toMonoidHom) = Finset.univ.val.map β' :=
    Multiset.map_map _ _ _
  rw [hm]
  have hs' : Summable fun l : {l : Fin n → ℕ // Antitone l} =>
      ‖schurAt (padTo le_rfl l.1) (fun i => (α i : ℂ)) * schurAt l.1 (fun j => (β' j : ℂ))‖ *
        ‖(q : ℂ) ^ (-(x : ℂ))‖ ^ (∑ i, l.1 i) := by
    refine (hs.comp_injective partVec_injective).congr fun l => ?_
    simp only [Function.comp, rsTerm_partVec, padTo_self, hconj, norm_mul, norm_pow, Complex.norm_conj]
  have hc := cauchy_locL le_rfl α β' q (x : ℂ) hs'
  rw [← (partVec_injective (n := n)).hasSum_iff]
  · convert hc using 1
    funext l
    simp only [Function.comp, rsTerm_partVec, padTo_self, hconj]
  · intro v hv
    by_cases hval : (∀ j, 0 ≤ v j) ∧ Antitone v
    · exact absurd (mem_range_partVec hval) hv
    · rw [rsTerm, if_neg hval]

theorem hasSum_rsTerm_finsupp : ∀ {I : Type} (q : I → ℕ) {n : ℕ} (α β : I → Fin n → ℂˣ) (x : ℝ), 1 < x → (∀ i, 2 ≤ q i) →
    GlobalTheory.RSPole.eulD q (fun i j => (α i j : ℂ)) x ≠ ⊤ → GlobalTheory.RSPole.eulD q (fun i j => (β i j : ℂ)) x ≠ ⊤ →
    HasSum (fun l : I →₀ (Fin n → ℤ) => l.prod fun i v => GlobalTheory.ZEul.rsTerm (q i) (fun j => (α i j : ℂ)) (fun j => (β i j : ℂ)) x v)
      (∏' i, GlobalTheory.JSW.locL (q i) (Finset.univ.val.map (α i)) ((Finset.univ.val.map (β i)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) := by
  intro I q n α β x _ hq hα hβ
  set f : I → (Fin n → ℤ) → ℂ := fun i v => rsTerm (q i) (fun j => (α i j : ℂ)) (fun j => (β i j : ℂ)) x v with hfdef
  have hf0 : ∀ i, f i 0 = 1 := fun i => rsTerm_zero _ _ _ _
  have hA := summable_sqTerm q (fun i j => (α i j : ℂ)) x hα
  have hB := summable_sqTerm q (fun i j => (β i j : ℂ)) x hβ
  have hsum : Summable fun p : I × {v : Fin n → ℤ // v ≠ 0} => ‖f p.1 p.2‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun p => by
        simpa only [hfdef] using norm_rsTerm_le (q p.1) (by have := hq p.1; omega) (fun j => (α p.1 j : ℂ)) (fun j => (β p.1 j : ℂ)) x p.2.1) ((hA.add hB).div_const 2)
  obtain ⟨hN, -, hE⟩ := GlobalTheory.EulerSum.euler_product_intVec n f hf0 hsum
  have hloc : ∀ i, ∑' v, f i v = locL (q i) (Finset.univ.val.map (α i))
      ((Finset.univ.val.map (β i)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) :=
    fun i => (hasSum_rsTerm_local (q i) (α i) (β i) x (GlobalTheory.EulerSum.summable_norm_local f hsum i)).tsum_eq
  rw [← hE.trans (tprod_congr hloc)]
  exact hN.of_norm.hasSum

end GlobalTheory.ZEul
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRankinSelbergSchurTermFinsuppEulerProductStatement
open MeasureTheory
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_rankinSelbergSchurTerm_finsupp_eulerProduct : ∀ {I : Type} (q : I → ℕ) {n : ℕ} (α β : I → Fin n → ℂˣ) (x : ℝ), 1 < x → (∀ i, 2 ≤ q i) →
    GlobalTheory.RSPole.eulD q (fun i j => (α i j : ℂ)) x ≠ ⊤ → GlobalTheory.RSPole.eulD q (fun i j => (β i j : ℂ)) x ≠ ⊤ →
    HasSum (fun l : I →₀ (Fin n → ℤ) => l.prod fun i v => GlobalTheory.ZEul.rsTerm (q i) (fun j => (α i j : ℂ)) (fun j => (β i j : ℂ)) x v)
      (∏' i, GlobalTheory.JSW.locL (q i) (Finset.univ.val.map (α i)) ((Finset.univ.val.map (β i)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) := by
  first | exact @GlobalTheory.ZEul.hasSum_rsTerm_finsupp | exact GlobalTheory.ZEul.hasSum_rsTerm_finsupp | (intros; apply GlobalTheory.ZEul.hasSum_rsTerm_finsupp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG5Setup
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLinkTameShape

theorem splitL_diagonal {K : Type} [Field K] (a b n : ℕ) (hn : n = a + b) (c : K) (y : Fin n → K) :
    Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL a b n hn ((Matrix.diagonal fun k : Fin n => if (k : ℕ) < a then 1 else c).mulVec y) =
      ((Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL a b n hn y).1, c • (Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL a b n hn y).2) := by
  ext j
  · simp [Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL, Matrix.mulVec_diagonal]
  · simp [Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL, Matrix.mulVec_diagonal]

theorem rhoBarTw_eq (D : D7) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (a : ℤ) : rhoBarTw D.nd ρ π a =
      twistRep (glRep (redRep D.nd i (ρ π))) (Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i a) := by
  have hz : ∀ (u : (D.nd.O i)ˣ) (n : ℤ), IsLocalRing.residue (D.nd.O i) ((u ^ n : (D.nd.O i)ˣ) : D.nd.O i) =
      (IsLocalRing.residue (D.nd.O i) u) ^ n := by
    intro u n
    have := congrArg Units.val (map_zpow (Units.map (IsLocalRing.residue (D.nd.O i)).toMonoidHom) u n)
    rw [Units.val_zpow_eq_zpow_val] at this
    simpa only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] using this
  have hs : ∀ (c : D.nd.O i) (M : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)),
      (c • M).map (IsLocalRing.residue (D.nd.O i)) =
        IsLocalRing.residue (D.nd.O i) c • M.map (IsLocalRing.residue (D.nd.O i)) := fun c M => by
    ext; simp
  refine MonoidHom.ext fun g => LinearMap.ext fun u => funext fun k => ?_
  simp [rhoBarTw, twistRep, glRep, matRep, mapM, twistM, redRep, mapRep, Formalism.MainNotions.SumRepresentations.At.chiEpsBar, rhoO]
  rw [hs, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, hz, map_units_inv]

end GlobalTheory.NLinkTameShape

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenUnitInvariantsTwistedLatticeLeOfKillingExpone
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenUnitInvariantsTwistedLatticeLeOfKillingExpone
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.LengthH0Bound

theorem toNat_div_le (A B : ℕ∞) (r c : ℕ) (h : A ≤ (r : ℕ∞) * (c : ℕ∞) * B) :
    ((A.toNat : ℚ) / (B.toNat : ℚ)) ≤ (r : ℚ) * c := by
  rcases eq_or_ne B ⊤ with hB | hB
  · rw [hB, ENat.toNat_top, Nat.cast_zero, div_zero]; positivity
  obtain ⟨b, rfl⟩ := ENat.ne_top_iff_exists.mp hB
  have h' : A ≤ ((r * c * b : ℕ) : ℕ∞) := by push_cast; exact h
  obtain ⟨a, ha, hle⟩ := ENat.le_natCast_iff.mp h'
  subst ha
  rw [ENat.toNat_coe, ENat.toNat_coe]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [Nat.cast_zero, div_zero]; positivity
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast hle

theorem lenUnit_le_of_kill {O : Type} [CommRing O] [IsDomain O] (k p c : ℕ)
    (hp : algebraMap O (FractionRing O) (p : O) ≠ 0) (W : Submodule O (KOG O k))
    (hW : ∀ x ∈ W, (p : O) ^ c • x = 0) :
    lenUnit (O := O) p ↥W ≤ (k : ℚ) * c := by
  have hlen := length_le_of_killed (LL := FractionRing O) (stdG O (FractionRing O) k) _
    (GlobalTheory.FiniteTwistInvariants.stdG_eq_span k) (p : O) hp c W hW
  exact toNat_div_le _ _ k c hlen

section Bridge

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O)

theorem locM_entry {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O)
    (g : ↥(GK Bw.Kw)) (i j : Fin k) :
    Br.locM Bw M g i j = Br.toLLK Bw (algebraMap O (FractionRing O) (M (Br.ι Bw g) i j)) := by
  rw [Br.toLLK_alg]; rfl

theorem vecS_mulVec' {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O)
    (g : ↥(GK Bw.Kw)) (u : Fin k → FractionRing O) :
    Br.vecS Bw k ((mapM (algebraMap O (FractionRing O)) M (Br.ι Bw g)).mulVec u) =
      (Br.locM Bw M g).mulVec (Br.vecS Bw k u) := by
  funext i
  change Br.toLLK Bw (∑ j, algebraMap O (FractionRing O) (M (Br.ι Bw g) i j) * u j) =
    ∑ j, Br.locM Bw M g i j * Br.toLLK Bw (u j)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, locM_entry]


set_option synthInstance.maxHeartbeats 400000 in
theorem phi_eq_zero {k : ℕ} (z : KOG O k) (hz : Br.phi Bw k z = 0) : z = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  change (Submodule.Quotient.mk (Br.vecS Bw k y) :
    (Fin k → Br.LLw Bw) ⧸ stdG (Br.Ow Bw) (Br.LLw Bw) k) = 0 at hz
  rw [Submodule.Quotient.mk_eq_zero] at hz
  obtain ⟨b, hb⟩ := hz
  rw [Submodule.Quotient.mk_eq_zero]
  refine ⟨fun j => Bw.eO.symm (b j), funext fun j => ?_⟩
  apply (Br.toLLK Bw).injective
  have hbj := congrFun hb j
  simp only [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply] at hbj ⊢
  rw [Br.toLLK_alg, RingEquiv.apply_symm_apply]
  exact hbj


set_option synthInstance.maxHeartbeats 400000 in
theorem actD_phi {Γ : Type} [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) O) (f : ↥Gw →* Γ)
    (gK : ↥(GK Bw.Kw)) (x : KOG O k) :
    actD (Br.lat Bw (M.comp f)) gK (Br.phi Bw k x) = Br.phi Bw k ((WKG M).comp f (Br.ι Bw gK) x) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h := vecS_mulVec' Bw (M.comp f) gK y
  change (Submodule.Quotient.mk (((Br.locM Bw (M.comp f)) gK).mulVec (Br.vecS Bw k y)) :
      (Fin k → Br.LLw Bw) ⧸ stdG (Br.Ow Bw) (Br.LLw Bw) k) =
    Submodule.Quotient.mk (Br.vecS Bw k
      (((mapM (algebraMap O (FractionRing O)) (M.comp f)) (Br.ι Bw gK)).mulVec y))
  rw [h]


set_option synthInstance.maxHeartbeats 400000 in
theorem inv_killed {Γ : Type} [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) O) (f : ↥Gw →* Γ) (p c : ℕ)
    (h : ∀ y : (Fin k → Br.LLw Bw) ⧸ stdG (Br.Ow Bw) (Br.LLw Bw) k,
      (∀ gK, actD (Br.lat Bw (M.comp f)) gK y = y) → ((p : Br.Ow Bw) ^ c) • y = 0) :
    ∀ x ∈ Representation.invariants ((WKG M).comp f), (p : O) ^ c • x = 0 := by
  intro x hx
  have hfix : ∀ gK, actD (Br.lat Bw (M.comp f)) gK (Br.phi Bw k x) = Br.phi Bw k x := by
    intro gK
    rw [actD_phi, hx (Br.ι Bw gK)]
  have hk := h _ hfix
  apply phi_eq_zero Bw
  rw [LinearMap.map_smulₛₗ]
  simp only [map_pow, map_natCast]
  exact hk


include Bw in
theorem natCast_ne_zero : algebraMap O (FractionRing O) ((l : ℕ) : O) ≠ 0 := by
  intro h
  have h2 := congrArg (Br.toLLK Bw) h
  rw [map_natCast, map_natCast, map_zero] at h2
  have hQ : ((l : ℕ) : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  apply hQ
  apply (algebraMap ℚ_[l] (Br.LLw Bw)).injective
  rw [map_natCast, map_zero]
  exact h2

end Bridge


set_option synthInstance.maxHeartbeats 400000 in
theorem main : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (u : HeightOneSpectrum (𝓞 D.host.E)) (hu : u ∈ placesOver D.host.E (D.nd.l i)) (s : ℕ)
    (hs : Good (D.nbr i u hu).Kw s (D.nbr i u hu).LL)
    (hc : ∀ v, Continuous fun g => matRep (Br.locM (D.nbr i u hu) ((WpO D.nd i ρ π).comp (decS D.nd u))) g v) (c : ℕ),
    let S := LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i u hu).Kw s (D.nbr i u hu).LL hs;
    ∀ T : LocLat S.G S.Qp S.LL S.O, T = GlobalTheory.HubX.wLat D i ρ π u hu hc →
    (∀ x : T.V ⧸ T.L.T, (∀ g, actD T.L g x = x) → ((LocalSituation.ell S : S.O) ^ c) • x = 0) →
    (Br.h0W i u ρ π : ℝ) ≤ (D.R.r : ℝ) * c := by
  intro D HW i ρ π u hu s hs hc c S T hT hkill
  subst hT
  have hp : LocalSituation.ell S = D.nd.l i := (D.loc (D.nd.l i)).PD_p _
  have hK := inv_killed (D.nbr i u hu) (WpO D.nd i ρ π) (decS D.nd u) (D.nd.l i) c (fun y hy => by
    have := hkill y hy
    rwa [hp] at this)
  have hq := lenUnit_le_of_kill D.R.r (D.nd.l i) c (natCast_ne_zero (D.nbr i u hu)) _ hK
  exact_mod_cast hq

end GlobalTheory.LengthH0Bound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenUnitInvariantsTwistedLatticeLeOfKillingExponeStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lenUnit_invariants_twistedLattice_le_of_killingExponent : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (u : HeightOneSpectrum (𝓞 D.host.E)) (hu : u ∈ placesOver D.host.E (D.nd.l i)) (s : ℕ)
    (hs : Good (D.nbr i u hu).Kw s (D.nbr i u hu).LL)
    (hc : ∀ v, Continuous fun g => matRep (Br.locM (D.nbr i u hu) ((WpO D.nd i ρ π).comp (decS D.nd u))) g v) (c : ℕ),
    let S := LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i u hu).Kw s (D.nbr i u hu).LL hs;
    ∀ T : LocLat S.G S.Qp S.LL S.O, T = GlobalTheory.HubX.wLat D i ρ π u hu hc →
    (∀ x : T.V ⧸ T.L.T, (∀ g, actD T.L g x = x) → ((LocalSituation.ell S : S.O) ^ c) • x = 0) →
    (Br.h0W i u ρ π : ℝ) ≤ (D.R.r : ℝ) * c := by
  first | exact @GlobalTheory.LengthH0Bound.main | exact GlobalTheory.LengthH0Bound.main | (intros; apply GlobalTheory.LengthH0Bound.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxLengthLocalInvariantsTwistedFractionModIntege
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxLengthLocalInvariantsTwistedFractionModIntege
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.InvariantsKO

open IsDiscreteValuationRing

section DVR

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

noncomputable def divBy (a : O) : O →ₗ[O] KmodO O :=
  (Submodule.mkQ _).comp ((LinearMap.mulLeft O ((algebraMap O (FractionRing O) a)⁻¹)).comp
    (Algebra.linearMap O (FractionRing O)))

theorem divBy_apply (a y : O) : divBy a y =
    Submodule.Quotient.mk ((algebraMap O (FractionRing O) a)⁻¹ * algebraMap O (FractionRing O) y) := rfl

theorem ker_divBy {a : O} (ha : a ≠ 0) : LinearMap.ker (divBy a) = Ideal.span {a} := by
  have h0 : algebraMap O (FractionRing O) a ≠ 0 := by simpa using ha
  ext y
  rw [LinearMap.mem_ker, divBy_apply, Ideal.mem_span_singleton]
  refine (Submodule.Quotient.mk_eq_zero _).trans ⟨?_, ?_⟩
  · rintro ⟨b, hb⟩
    refine ⟨b, IsFractionRing.injective O (FractionRing O) ?_⟩
    have hb' : algebraMap O (FractionRing O) b =
      (algebraMap O (FractionRing O) a)⁻¹ * algebraMap O (FractionRing O) y := hb
    rw [map_mul, hb', mul_inv_cancel_left₀ h0]
  · rintro ⟨b, rfl⟩
    refine ⟨b, ?_⟩
    change algebraMap O (FractionRing O) b =
      (algebraMap O (FractionRing O) a)⁻¹ * algebraMap O (FractionRing O) (a * b)
    rw [map_mul, inv_mul_cancel_left₀ h0]

theorem mem_range_divBy {a : O} (ha : a ≠ 0) (x : KmodO O) (hx : a • x = 0) :
    x ∈ LinearMap.range (divBy a) := by
  have h0 : algebraMap O (FractionRing O) a ≠ 0 := by simpa using ha
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨y, hy⟩ := hx
  refine ⟨y, ?_⟩
  rw [divBy_apply]
  congr 1
  have hy' : algebraMap O (FractionRing O) y = algebraMap O (FractionRing O) a * z := by
    rw [← Algebra.smul_def]; exact hy
  rw [hy', inv_mul_cancel_left₀ h0]

theorem length_le_of_smul_eq_zero {a : O} (ha : a ≠ 0) (P : Submodule O (KmodO O))
    (hP : ∀ x ∈ P, a • x = 0) : Module.length O P ≤ addVal O a := by
  have hle : P ≤ LinearMap.range (divBy a) := fun x hx => mem_range_divBy ha x (hP x hx)
  let f : P →ₗ[O] O ⧸ Ideal.span {a} :=
    (Submodule.quotEquivOfEq _ _ (ker_divBy ha)).toLinearMap.comp
      ((LinearMap.quotKerEquivRange (divBy a)).symm.toLinearMap.comp (Submodule.inclusion hle))
  have hf : Function.Injective f := by
    intro x y hxy
    have := (Submodule.quotEquivOfEq _ _ (ker_divBy ha)).injective hxy
    have := (LinearMap.quotKerEquivRange (divBy a)).symm.injective this
    exact Submodule.inclusion_injective hle this
  calc Module.length O P ≤ Module.length O (O ⧸ Ideal.span {a}) := Module.length_le_of_injective f hf
    _ = addVal O a := Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span a

theorem lenUnit_le_of_smul_eq_zero (l : ℕ) {a : O} (ha : a ≠ 0) (P : Submodule O (KmodO O))
    (hP : ∀ x ∈ P, a • x = 0) : lenUnit (O := O) l P ≤ lenUnit (O := O) l (O ⧸ Ideal.span {a}) := by
  unfold lenUnit
  have hne : Module.length O (O ⧸ Ideal.span {a}) ≠ ⊤ := by
    rw [Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span]
    exact fun h => ha (addVal_eq_top_iff.mp h)
  have h1 : (Module.length O P).toNat ≤ (Module.length O (O ⧸ Ideal.span {a})).toNat :=
    ENat.toNat_le_toNat ((length_le_of_smul_eq_zero ha P hP).trans_eq
      (Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span a).symm) hne
  gcongr

end DVR

end GlobalTheory.InvariantsKO

namespace GlobalTheory.InvariantsKO

open IsDiscreteValuationRing

theorem lenUnit_invariants_le (D : D7) (i : D.nd.Loc) (hls : D.nd.l i ∉ D.host.small)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ) (hn : 0 < n) :
    lenUnit (O := D.nd.O i) (D.nd.l i)
        ↥(Representation.invariants ((Formalism.MainNotions.N.Glob.KOtw D.nd i (n : ℤ)).comp (decS D.nd w))) ≤
      ((1 + padicValNat (D.nd.l i) n : ℕ) : ℚ) := by
  haveI := D.nd.lPrime i
  have hl2 : D.nd.l i ≠ 2 := UpperTheory.Small.ne_two D.host hls
  obtain ⟨g, hgI, hg⟩ := GlobalTheory.PtCore.EpsAll.exists_generator (GlobalTheory.EpsInertia.epsAll D i) w hw
  have hgD : g ∈ Dec (F := D.host.E) (D.nd.plOm.1 w) := Ine_le_Dec _ hgI
  set b : (D.nd.O i)ˣ := Formalism.MainNotions.N.Glob.epsO D.nd i g with hbdef
  have hb : (b : D.nd.O i) = algebraMap ℤ_[D.nd.l i] (D.nd.O i)
      (1 + (D.nd.l i : ℤ_[D.nd.l i]) ^ 1 * ((1 : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i])) := by
    rw [Units.val_one, mul_one, ← UpperTheory.Small.localLevel_eq_one_of_not_mem_smallPrimes D.nd i hls, ← hg]
    rfl
  set a : D.nd.O i := (b : D.nd.O i) ^ n - 1 with hadef
  have hva : addVal (D.nd.O i) a =
      ((1 + padicValNat (D.nd.l i) n : ℕ) : ℕ∞) * addVal (D.nd.O i) ((D.nd.l i : ℕ) : D.nd.O i) := by
    rw [hadef, hb]
    exact Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.addVal_pow_sub_one (O := D.nd.O i) (D.nd.l i) (Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.l_ne_zero D.nd i)
      (Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.l_not_unit D.nd i) 1 le_rfl (fun h => absurd h hl2) 1 n hn
  have ha0 : a ≠ 0 := by
    intro h
    have ht : addVal (D.nd.O i) a = ⊤ := by rw [h]; simp
    rw [hva] at ht
    obtain ⟨e, he0, he⟩ := Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.exists_eO D.nd i
    rw [he] at ht
    exact absurd ht (by rw [← Nat.cast_mul]; exact ENat.coe_ne_top _)
  have hkill : ∀ x ∈ Representation.invariants ((Formalism.MainNotions.N.Glob.KOtw D.nd i (n : ℤ)).comp (decS D.nd w)),
      a • x = 0 := by
    intro x hx
    have hfix := (Representation.mem_invariants _ x).mp hx ⟨g, hgD⟩
    have hfix' : ((b ^ n)⁻¹ : (D.nd.O i)ˣ) • x = x := by
      have e1 : ((Formalism.MainNotions.N.Glob.KOtw D.nd i (n : ℤ)).comp (decS D.nd w)) ⟨g, hgD⟩ x =
          (((b ^ (-(n : ℤ)) : (D.nd.O i)ˣ)) : D.nd.O i) • x := by
        rfl
      rw [e1] at hfix
      rw [Units.smul_def, ← zpow_natCast, ← zpow_neg]
      exact hfix
    rw [hadef, sub_smul, one_smul]
    conv_lhs => rw [← hfix']
    rw [Units.smul_def, smul_smul, ← Units.val_pow_eq_pow_val, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, one_smul, ← Units.smul_def, hfix', sub_self]
  calc lenUnit (O := D.nd.O i) (D.nd.l i) _
      ≤ lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {a}) :=
        lenUnit_le_of_smul_eq_zero (D.nd.l i) ha0 _ hkill
    _ = _ := Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.lenUnit_span D.nd i hva

end GlobalTheory.InvariantsKO

namespace GlobalTheory.InvariantsKO

theorem unbotD_le {m : WithBot ℚ} {c : ℚ} (h : m ≤ (c : WithBot ℚ)) (hc : 0 ≤ c) : m.unbotD 0 ≤ c := by
  cases m with
  | bot => simpa using hc
  | coe a => simpa using h

theorem one_add_padicValNat_le (l : ℕ) [Fact l.Prime] {n t : ℕ} (hn : 0 < n) (hnt : n < t) :
    1 + padicValNat l n ≤ 2 * t := by
  have h1 : l ^ padicValNat l n ≤ n := Nat.le_of_dvd hn (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
  have h2 : 2 ^ padicValNat l n ≤ l ^ padicValNat l n :=
    Nat.pow_le_pow_left (Fact.out : l.Prime).two_le _
  have h3 : padicValNat l n < 2 ^ padicValNat l n := Nat.lt_two_pow_self
  omega

theorem main : ∀ (D : D7) (i : D.nd.Loc) (col : Finset (HeightOneSpectrum (𝓞 D.host.E))), D.nd.l i ∉ D.host.small →
    D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → (∀ u ∈ col, u ∈ placesOver D.host.E (D.nd.l i)) →
    ((h0 D.nd i col : ℚ) : ℝ) ≤ 2 * D.R.t := by
  intro D i col hl2 _ _ hcol
  haveI := D.nd.lPrime i
  have key : h0 D.nd i col ≤ 2 * (D.R.t : ℚ) := by
    unfold h0
    refine unbotD_le ?_ (by positivity)
    apply Finset.max_le
    intro y hy
    obtain ⟨⟨w, n⟩, hp, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hw, hn⟩ := Finset.mem_product.mp hp
    obtain ⟨hn0, hnt⟩ := Finset.mem_Ioo.mp hn
    refine WithBot.coe_le_coe.mpr ((lenUnit_invariants_le D i hl2 w (hcol w hw) n hn0).trans ?_)
    exact_mod_cast one_add_padicValNat_le (D.nd.l i) hn0 hnt
  exact_mod_cast key

end GlobalTheory.InvariantsKO
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxLengthLocalInvariantsTwistedFractionModIntegeStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maxLength_localInvariants_twisted_fractionModInteger_le : ∀ (D : D7) (i : D.nd.Loc) (col : Finset (HeightOneSpectrum (𝓞 D.host.E))), D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → (∀ u ∈ col, u ∈ placesOver D.host.E (D.nd.l i)) → ((h0 D.nd i col : ℚ) : ℝ) ≤ 2 * D.R.t := by
  first | exact @GlobalTheory.InvariantsKO.main | exact GlobalTheory.InvariantsKO.main | (intros; apply GlobalTheory.InvariantsKO.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocFacOfNeg
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.RSCell

def sphZ (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (ν : Fin n → ℤ) : ℂ :=
  if Antitone ν then GlobalTheory.JSW.sphW q α (fun i => (ν i).toNat) else 0

def locFac (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) (ν : Fin n → ℤ) : ℝ≥0∞ :=
  if Antitone ν ∧ ∀ i, 0 ≤ ν i then
    ENNReal.ofReal (‖GlobalTheory.JSW.schurAt (fun i => (ν i).toNat) α‖ ^ 2 *
      (q : ℝ) ^ (-(((∑ i, (ν i).toNat : ℕ) : ℝ) * x)))
  else 0

def cellProd {E : Type} [Field E] [NumberField E] {n : ℕ} (T : Finset (HeightOneSpectrum (𝓞 E)))
    (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin n → ℂ) (x : ℝ)
    (ν : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) : ℝ≥0∞ :=
  ∏ w ∈ ν.support, if h : w ∈ T then 1 else locFac (Ideal.absNorm w.asIdeal) (α ⟨w, h⟩) x (ν w)

def bInt {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (ℓ : Fin a) (F : GA E a → ℂ)
    (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (x : ℝ) (g : GA E a) : ℝ≥0∞ :=
  ‖GlobalTheory.RSTheta.rsPsi ℓ (GlobalTheory.JSW.whit F) (GlobalTheory.JSW.whit F) Φ J η g (g.val ℓ)‖ₑ *
    ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x)

theorem locFac_zero (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) : locFac q α x 0 = 1 := by
  have h : (fun i : Fin n => ((0 : Fin n → ℤ) i).toNat) = fun _ => 0 := funext fun _ => rfl
  rw [locFac, if_pos (show Antitone (0 : Fin n → ℤ) ∧ ∀ i, (0 : ℤ) ≤ (0 : Fin n → ℤ) i from ⟨fun _ _ _ => le_rfl, fun _ => le_rfl⟩), h]
  simp [GlobalTheory.JSW.schurAt, GlobalTheory.JSW.schur_zero]

theorem locFac_of_neg (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) {ν : Fin n → ℤ} {i : Fin n} (h : ν i < 0) :
    locFac q α x ν = 0 := by
  rw [locFac, if_neg fun h' => absurd (h'.2 i) (not_le.2 h)]

end GlobalTheory.RSCell
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BigImageThirdCondition
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut

noncomputable section

namespace GlobalTheory.AdmGThreeRest

theorem litBurnside_host (D : D7) : LitBurnside (G D.host.E D.nd.Om) := by
  intro l _ a ρ h
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    exact Subsingleton.elim _ _
  · apply GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub ρ
    refine ⟨?_, ?_, ?_⟩
    · intro hb
      have : (Pi.single (⟨0, ha⟩ : Fin a) (1 : CyclotomicNorms.Fbar l) : Fin a → CyclotomicNorms.Fbar l) ∈ (⊤ : Submodule (CyclotomicNorms.Fbar l) (Fin a → CyclotomicNorms.Fbar l)) := trivial
      rw [hb, Submodule.mem_bot] at this
      have h1 := congrFun this ⟨0, ha⟩
      simp at h1
    · intro g x _; trivial
    · intro W' _ hW'
      exact h W' (fun g _ x hx => hW' g x hx)

end GlobalTheory.AdmGThreeRest
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumSelfDualFramesBoundStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_sum_self_dual_frames_bound : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → (∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ t : WO S T, IsHalf (cA D e) t → IsIntM (frMapAdj S T βS βT t) → t ∈ latO S T ΛS ΛT (fun _ => True) := by
  first | exact @GlobalTheory.HalfAdjLattice.mem_latO_of_adj_int | exact GlobalTheory.HalfAdjLattice.mem_latO_of_adj_int | (intros; apply GlobalTheory.HalfAdjLattice.mem_latO_of_adj_int <;> assumption)
end
