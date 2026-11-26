module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalUnitaryExchangeUnimodularLatticesIner
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianSeenPrimeConditionHermitianSide
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesEqIffReductionEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddHaarCompletionIntegralMatricesVolOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormMetricEqClassSumMetric
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PairingComplexFormsConstOnRowClasses
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PairingComplexFormsConstOnRowClasses
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df

attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Mem.Df

variable {X : Fields} {n : ℕ}
open Matrix

theorem ufGL_apply_single (γ : UF X.E n) (i j : Fin n) :
    ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E) i j = (γ.1 (Pi.single j 1)) i := by
  simp [ufGL, toGLm, Matrix.GeneralLinearGroup.toLin, LinearMap.GeneralLinearGroup.generalLinearEquiv]

theorem ufGL_unitary (γ : UF X.E n) :
    ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E)ᴴ * (ufGL X.E n γ : Matrix (Fin n) (Fin n) X.E) = 1 := by
  ext j k
  have h := γ.2 (Pi.single j 1) (Pi.single k 1)
  simp only [hStd, LinearMap.mk₂'ₛₗ_apply] at h
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, ufGL_apply_single]
  rw [h]
  simp only [Pi.single_apply, Matrix.one_apply]
  simp [eq_comm]
  split_ifs <;> simp

theorem bc_conj_unitary (hX : X.Ok) (φ : X.E →+* ℂ) (γ : UF X.E n) :
    Formalism.UG.bc (starRingEnd ℂ) (Formalism.UG.bc φ (ufGL X.E n γ)) = inside₂ ℂ n (Formalism.UG.bc φ (ufGL X.E n γ)) := by
  set A := Formalism.UG.bc φ (ufGL X.E n γ)
  have hA : (A : Matrix (Fin n) (Fin n) ℂ) = (ufGL X.E n γ : Matrix (Fin n) (Fin n) X.E).map φ := rfl
  have h1 : ((A : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))ᵀ * (A : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    have := congrArg (fun M => M.map φ) (ufGL_unitary γ)
    simp only [Matrix.map_mul, Matrix.map_one _ φ.map_zero φ.map_one] at this
    rw [← this, hA]
    congr 1
    ext i j
    simp [Matrix.conjTranspose_apply, hX.conjE]
  apply Units.ext
  show (A : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ) = ((A⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ
  have h2 : ((A : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))ᵀ = ((A⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
    calc _ = ((A : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))ᵀ * ((A : Matrix (Fin n) (Fin n) ℂ) * ((A⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) := by
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [← h2, Matrix.transpose_transpose]

theorem map_conj_rhoC (hX : X.Ok) (σ : X.K →+* ℂ) (lam : X.Tau → DomWeight n) (γ : UF X.E n) (p : Pol ℂ X.Tau n) :
    MvPolynomial.map (starRingEnd ℂ) (rhoC σ lam γ p) =
      actP lam (invTrK (embGL (embAt σ X.emb) (ufGL X.E n γ))) (MvPolynomial.map (starRingEnd ℂ) p) := by
  rw [rhoC_apply]
  refine (GlobalTheory.ValCmp.use₂ (starRingEnd ℂ) lam _ p).trans ?_
  congr 2
  funext τ
  exact bc_conj_unitary hX (embAt σ X.emb τ) γ

theorem pairB_rhoC (hX : X.Ok) (σ : X.K →+* ℂ) (lam : X.Tau → DomWeight n) (γ : UF X.E n) (p q : Pol ℂ X.Tau n) :
    pairB lam (MvPolynomial.map (starRingEnd ℂ) (rhoC σ lam γ p)) (rhoC σ lam γ q) =
      pairB lam (MvPolynomial.map (starRingEnd ℂ) p) q := by
  rw [map_conj_rhoC hX σ lam γ p, rhoC_apply]
  exact pairingBInvariantK_holds ℂ X.Tau n lam _ _ q

theorem conj_mul_self_chr {SG : Finset (HeightOneSpectrum (𝓞 X.E))} (σ : X.K →+* ℂ) (Λ : LevFam X.E X.K n SG) (h : ↥Λ.grp) :
    starRingEnd ℂ (σ (Λ.chr h : X.Kˣ)) * σ (Λ.chr h : X.Kˣ) = 1 := by
  obtain ⟨N, hN, hp⟩ := (isOfFinOrder_of_finite h).exists_pow_eq_one
  have h1 : (σ (Λ.chr h : X.Kˣ)) ^ N = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, hp, map_one, Units.val_one, map_one]
  have h2 := Complex.norm_eq_one_of_pow_eq_one h1 hN.ne'
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h2]
  simp

theorem pairB_conj_cls_eq : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (F G : MtCx I a)
    (d d' : (rowS I a).D), (rowS I a).cls d = (rowS I a).cls d' →
    pairB B.wts.sgTrue (MvPolynomial.map (starRingEnd ℂ) (F.1 d)) (G.1 d) =
      pairB B.wts.sgTrue (MvPolynomial.map (starRingEnd ℂ) (F.1 d')) (G.1 d') := by
  intro B X I hX a F G d d' h
  obtain ⟨g, rfl⟩ := ((rowS I a).cls_eq_iff _ _).1 h
  have hF := (F.2 d').2 g
  have hG := (G.2 d').2 g
  letI := (rowS I a).actD
  erw [hF, hG]
  rw [map_conj_smul, LinearMap.map_smul, LinearMap.map_smul, LinearMap.smul_apply]
  rw [pairB_rhoC hX, smul_eq_mul, smul_eq_mul, ← mul_assoc, mul_comm (B.embLL _)]
  have hc := conj_mul_self_chr B.embLL (rowTy I.Ch I.sel (I.tup a) I.Ps).inv g.2
  rw [hc, one_mul]

end GlobalTheory.Mem.Df
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PairingComplexFormsConstOnRowClassesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_complexForms_const_on_row_classes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (F G : MtCx I a) (d d' : (rowS I a).D), (rowS I a).cls d = (rowS I a).cls d' → pairB B.wts.sgTrue (MvPolynomial.map (starRingEnd ℂ) (F.1 d)) (G.1 d) = pairB B.wts.sgTrue (MvPolynomial.map (starRingEnd ℂ) (F.1 d')) (G.1 d') := by
  first | exact @GlobalTheory.Mem.Df.pairB_conj_cls_eq | exact GlobalTheory.Mem.Df.pairB_conj_cls_eq | (intros; apply GlobalTheory.Mem.Df.pairB_conj_cls_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormMetricEqClassSumMetric
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

noncomputable section

namespace GlobalTheory.Mem.Df

set_option maxHeartbeats 1000000

theorem card_stabilizer_eq_of_smul {G α : Type*} [Group G] [MulAction G α] (g : G) (x : α) :
    Nat.card (MulAction.stabilizer G (g • x)) = Nat.card (MulAction.stabilizer G x) :=
  (Nat.card_congr (MulAction.stabilizerEquivStabilizer (rfl : g • x = g • x)).toEquiv).symm

private theorem finset_sum_univ_eq_of_equiv {α β M : Type*} [AddCommMonoid M] (i1 : Fintype α) (i2 : Fintype β) (e : α ≃ β)
    (f : α → M) (g : β → M) (h : ∀ x, f x = g (e x)) :
    @Finset.sum α M _ (@Finset.univ α i1) f = @Finset.sum β M _ (@Finset.univ β i2) g :=
  @Fintype.sum_equiv α β M i1 i2 _ e f g h

theorem ipMt_eq_cSum : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (F G : (I.per l u a).Mt) (F' G' : MtCx I a), SameForm I l u a F' F → SameForm I l u a G' G → I.ipMt l u a F G = cSum I hX a F' G' := by
  intro B X I hOk hP l hX Z u a F G F' G' hF hG
  rw [GlobalTheory.Mem.Col2.IpMt.ipMt_sum I hOk hP l Z u a F G]
  have hd : Disjoint (B.primes X).vGs (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K)) :=
    (GlobalTheory.TopStep.tilOk_of_avoid (mu := I.tup a) l.pr hOk.sel_ok u ⟨hOk.T_mem u, hOk.g_mem⟩).2.2
  have hs : (I.perIn u a).sgT = B.wts.sgTrue := by
    funext τ
    rfl
  rw [hs, GlobalTheory.Mem.Df.cSum_apply]
  refine finset_sum_univ_eq_of_equiv _ _ (GlobalTheory.PeriodOnStep.clEquiv (X := B.fields) (Pr := B.primes X) (R := B.R) B.wts I.Ch I.sel (I.tup a) I.Ps hd) _ _ (fun c => ?_)
  have hFc := hF ((stepX I.Ch I.sel (I.tup a) I.Ps).rep c)
  have hGc := hG ((stepX I.Ch I.sel (I.tup a) I.Ps).rep c)
  have hcls : (rowS I a).cls ((rowS I a).outSec.rep ((GlobalTheory.PeriodOnStep.clEquiv (X := B.fields) (Pr := B.primes X) (R := B.R) B.wts I.Ch I.sel (I.tup a) I.Ps hd) c)) =
      (rowS I a).cls (GlobalTheory.PeriodOnStep.rowPt (X := B.fields) (Pr := B.primes X) (R := B.R) I.Ch I.sel (I.tup a) I.Ps c) :=
    (rowS I a).outSec.spec _
  obtain ⟨g, hg⟩ := ((rowS I a).cls_eq_iff _ _).1 hcls
  have hcard := GlobalTheory.PeriodOnStep.card_stab (X := B.fields) (Pr := B.primes X) (R := B.R) B.wts I.Ch I.sel (I.tup a) I.Ps hd c
  have hpair := GlobalTheory.T.pairing_complexForms_const_on_row_classes I hX a F' G' _ _ hcls
  unfold cTerm
  rw [hpair, ← hg, @card_stabilizer_eq_of_smul (rowS I a).G (rowS I a).D _ (rowS I a).actD g _, ← hcard]
  exact congrArg₂ (fun x y => (((Nat.card ((stepX I.Ch I.sel (I.tup a) I.Ps).Stab c) : ℕ) : ℂ))⁻¹ *
    pairB B.wts.sgTrue (MvPolynomial.map (starRingEnd ℂ) x) y) hFc hGc

end GlobalTheory.Mem.Df

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormMetricEqClassSumMetricStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowFormMetric_eq_classSumMetric : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (F G : (I.per l u a).Mt) (F' G' : MtCx I a), SameForm I l u a F' F → SameForm I l u a G' G → I.ipMt l u a F G = cSum I hX a F' G' := by
  first | exact @GlobalTheory.Mem.Df.ipMt_eq_cSum | exact GlobalTheory.Mem.Df.ipMt_eq_cSum | (intros; apply GlobalTheory.Mem.Df.ipMt_eq_cSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsLiftsHeckeOperatorsCommute
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertPathCardCommLatticePaths
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertPathCardCommLatticePaths
open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory
open Classical

namespace GlobalTheory

theorem inertPath_card_eq_natCard {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
    (hST : ∀ R : ST, R.1 ≠ P) (hSG : ∀ w : SG, w.1 ≠ P) (s t : List ℕ) (d f : DecoSet (E := E) (n := n) (ST := ST) (SG := SG))
    (hf : f.1.f = d.1.f) (hbe : f.1.be = d.1.be) :
    ((d.inertNb P.asIdeal s).filter fun e => f ∈ e.inertNb P.asIdeal t).card =
      Nat.card {Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal s d.1.N Y ∧ IsInertNbr P.asIdeal t Y f.1.N} := by
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr
    { toFun := fun e => ⟨e.1.1.N, e.1.2.lat, e.1.2.uni, ?_, ?_⟩
      invFun := fun Y => ⟨⟨{ N := Y.1, f := d.1.f, be := d.1.be },
          d.2.replN Y.2.1 Y.2.2.1 (fun R => hi_sameAt_inert (hST R) Y.2.2.2.1)
            (fun w => hi_sameAt_inert (hSG w) Y.2.2.2.1)⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have h := (Finset.mem_filter.1 e.2).1
    rw [DecoSet.mem_inertNb P.ne_bot] at h
    exact h.1
  · have h := (Finset.mem_filter.1 e.2).2
    rw [DecoSet.mem_inertNb P.ne_bot] at h
    exact h.1
  · refine Finset.mem_filter.2 ⟨?_, ?_⟩
    · rw [DecoSet.mem_inertNb P.ne_bot]
      exact ⟨Y.2.2.2.1, rfl, rfl⟩
    · rw [DecoSet.mem_inertNb P.ne_bot]
      exact ⟨Y.2.2.2.2, hf, hbe⟩
  · intro e
    have h := Finset.mem_filter.1 e.2
    rw [DecoSet.mem_inertNb P.ne_bot, DecoSet.mem_inertNb P.ne_bot] at h
    exact Subtype.ext (Subtype.ext (Deco.ext rfl h.1.2.1.symm h.1.2.2.symm))
  · intro Y
    rfl

theorem inertPath_card_eq_zero {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) {ST SG : Finset (HeightOneSpectrum (𝓞 E))} (s t : List ℕ)
    (d f : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (h : ¬ (f.1.f = d.1.f ∧ f.1.be = d.1.be)) :
    ((d.inertNb P.asIdeal s).filter fun e => f ∈ e.inertNb P.asIdeal t).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hfe
  rw [DecoSet.mem_inertNb P.ne_bot] at he hfe
  exact h ⟨hfe.2.1.trans he.2.1, hfe.2.2.trans he.2.2⟩

theorem inertPath_card_comm : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}, (∀ R : ST, R.1 ≠ P) → (∀ w : SG, w.1 ≠ P) →
  ∀ (s t : List ℕ) (d f : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)),
    Nonempty ({Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal s d.1.N Y ∧ IsInertNbr P.asIdeal t Y f.1.N} ≃
      {Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal t d.1.N Y ∧ IsInertNbr P.asIdeal s Y f.1.N}) →
    ((d.inertNb P.asIdeal s).filter fun e => f ∈ e.inertNb P.asIdeal t).card =
      ((d.inertNb P.asIdeal t).filter fun e => f ∈ e.inertNb P.asIdeal s).card := by
  intro E _ _ _ n P ST SG hST hSG s t d f ⟨φ⟩
  by_cases hdec : f.1.f = d.1.f ∧ f.1.be = d.1.be
  · rw [inertPath_card_eq_natCard P hST hSG s t d f hdec.1 hdec.2,
      inertPath_card_eq_natCard P hST hSG t s d f hdec.1 hdec.2]
    exact Nat.card_congr φ
  · rw [inertPath_card_eq_zero P s t d f hdec, inertPath_card_eq_zero P t s d f hdec]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertPathCardCommLatticePathsStatement
open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPath_card_comm_latticePaths : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}, (∀ R : ST, R.1 ≠ P) → (∀ w : SG, w.1 ≠ P) →
  ∀ (s t : List ℕ) (d f : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)),
    Nonempty ({Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal s d.1.N Y ∧ IsInertNbr P.asIdeal t Y f.1.N} ≃
      {Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal t d.1.N Y ∧ IsInertNbr P.asIdeal s Y f.1.N}) →
    ((d.inertNb P.asIdeal s).filter fun e => f ∈ e.inertNb P.asIdeal t).card =
      ((d.inertNb P.asIdeal t).filter fun e => f ∈ e.inertNb P.asIdeal s).card := by
  first | exact @GlobalTheory.inertPath_card_comm | exact GlobalTheory.inertPath_card_comm | (intros; apply GlobalTheory.inertPath_card_comm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsLiftsHeckeOperatorsCommute
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

open Formalism.L2.Col Formalism.HermitianLatticesTheory

namespace GlobalTheory.InertSame

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem sameAt_trans {Q : HeightOneSpectrum (𝓞 E)} {A B C : Submodule (𝓞 E) (Sp E n)}
    (h1 : SameAt Q A B) (h2 : SameAt Q B C) : SameAt Q A C := by
  obtain ⟨a, ha, a', ha', h1, h1'⟩ := h1
  obtain ⟨b, hb, b', hb', h2, h2'⟩ := h2
  refine ⟨a * b, fun hm => (Q.isPrime.mem_or_mem hm).elim ha hb, b' * a',
    fun hm => (Q.isPrime.mem_or_mem hm).elim hb' ha', fun x hx => ?_, fun x hx => ?_⟩
  · rw [mul_smul]; exact h1 _ (h2 x hx)
  · rw [mul_smul]; exact h2' _ (h1' x hx)

theorem sameAt_refl (Q : HeightOneSpectrum (𝓞 E)) (A : Submodule (𝓞 E) (Sp E n)) : SameAt Q A A :=
  ⟨1, fun h => Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), 1,
    fun h => Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), fun x hx => by simpa using hx, fun x hx => by simpa using hx⟩

theorem paths_equiv (P : HeightOneSpectrum (𝓞 E)) (hP : conjPrime₂ P = P) (hin : ∃ x : 𝓞 E, cO E x - x ∉ P.asIdeal)
    (X Z : Submodule (𝓞 E) (Sp E n)) (hX : Submodule.IsLattice E X) (hZ : Submodule.IsLattice E Z)
    (hXu : IsUnimodular (hStd E n) X) (hZu : IsUnimodular (hStd E n) Z) (s t : List ℕ) :
    Nonempty ({Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal s X Y ∧ IsInertNbr P.asIdeal t Y Z} ≃
      {Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal t X Y ∧ IsInertNbr P.asIdeal s Y Z}) := by
  by_cases hXZ : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Z
  · obtain ⟨σ, hσX, hσZ, hgood, hsurj, hinj, hrel⟩ := GlobalTheory.T.exists_local_unitary_exchange_unimodular_lattices_inert P hP hin X Z hX hZ hXu hZu hXZ
    have gX : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X X := fun Q _ => sameAt_refl Q X
    have away : ∀ {u : List ℕ} {Y : Submodule (𝓞 E) (Sp E n)}, IsInertNbr P.asIdeal u X Y →
        ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y := fun h Q hQ => hi_sameAt_inert hQ h
    have fwd : ∀ Y : {Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal s X Y ∧ IsInertNbr P.asIdeal t Y Z},
        Submodule.IsLattice E (σ Y.1) ∧ IsUnimodular (hStd E n) (σ Y.1) ∧
          IsInertNbr P.asIdeal t X (σ Y.1) ∧ IsInertNbr P.asIdeal s (σ Y.1) Z := by
      rintro ⟨Y, hl, hu, h1, h2⟩
      obtain ⟨gl, gu, -⟩ := hgood Y hl hu (away h1)
      have r1 := (hrel s X Y hX hXu gX hl hu (away h1)).2 h1
      have r2 := (hrel t Y Z hl hu (away h1) hZ hZu hXZ).2 h2
      rw [hσX] at r1
      rw [hσZ] at r2
      exact ⟨gl, gu, r2.symm, r1.symm⟩
    refine ⟨Equiv.ofBijective (fun Y => ⟨σ Y.1, fwd Y⟩) ⟨?_, ?_⟩⟩
    · rintro ⟨Y, hl, hu, h1, h2⟩ ⟨Y', hl', hu', h1', h2'⟩ he
      have := congrArg Subtype.val he
      exact Subtype.ext (hinj Y Y' hl hu (away h1) hl' hu' (away h1') this)
    · rintro ⟨Y', hl', hu', h1', h2'⟩
      obtain ⟨Y, hl, hu, ha, rfl⟩ := hsurj Y' hl' hu' (away h1')
      refine ⟨⟨Y, hl, hu, ?_, ?_⟩, rfl⟩
      · refine (hrel s X Y hX hXu gX hl hu ha).1 ?_
        rw [hσX]
        exact h2'.symm
      · refine (hrel t Y Z hl hu ha hZ hZu hXZ).1 ?_
        rw [hσZ]
        exact h1'.symm
  · have e1 : IsEmpty {Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal s X Y ∧ IsInertNbr P.asIdeal t Y Z} :=
      ⟨fun Y => hXZ fun Q hQ => sameAt_trans (hi_sameAt_inert hQ Y.2.2.2.1) (hi_sameAt_inert hQ Y.2.2.2.2)⟩
    have e2 : IsEmpty {Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal t X Y ∧ IsInertNbr P.asIdeal s Y Z} :=
      ⟨fun Y => hXZ fun Q hQ => sameAt_trans (hi_sameAt_inert hQ Y.2.2.2.1) (hi_sameAt_inert hQ Y.2.2.2.2)⟩
    exact ⟨Equiv.equivOfIsEmpty _ _⟩

section Ops
variable {K : Type} [Field K] [NumberField K] [StarRing K] {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {S : GSD K}

theorem heckeI_comm_same (c : DecoPts S E n ST SG) (P : HeightOneSpectrum (𝓞 E)) (hP : conjPrime₂ P = P)
    (hin : ∃ x : 𝓞 E, cO E x - x ∉ P.asIdeal) (hST : ∀ R : ST, R.1 ≠ P) (hSG : ∀ w : SG, w.1 ≠ P)
    (s t : List ℕ) : Commute (heckeI c P.asIdeal s).op (heckeI c P.asIdeal t).op := by
  classical
  exact hi_commute c _ _ _ _ (heckeI_op_apply' c _ s) (heckeI_op_apply' c _ t) fun d f =>
    GlobalTheory.T.inertPath_card_comm_latticePaths P hST hSG s t d f (paths_equiv P hP hin d.1.N f.1.N d.2.lat f.2.lat d.2.uni f.2.uni s t)

theorem heckeCommAll_all (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) : HeckeCommAll c S0 :=
  heckeCommAll_of_same c S0 fun P s t => heckeI_comm_same c P.1 P.2.1 P.2.2.1
    (fun R => P.ne_of_mem (Or.inl (Or.inr R.2))) (fun w => P.ne_of_mem (Or.inr w.2)) s t
end Ops

end GlobalTheory.InertSame

namespace GlobalTheory.Mem.R3.Comm

theorem rows_lifts_comm : ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px), B.fields.Ok → I.Ok → ∀ a : I.ι,
  Formalism.L2.Col.HeckeCommAll (rowPts B.wts I.Ch I.sel (I.tup a)) ∅ ∧
    ∀ j : Fin B.R.m, Formalism.L2.Col.HeckeCommAll (liftPts B.wts I.Ch I.sel (I.tup a) (j.1 + 1)) ∅ :=
  fun _ _ _ _ _ _ => ⟨GlobalTheory.InertSame.heckeCommAll_all _ _, fun _ => GlobalTheory.InertSame.heckeCommAll_all _ _⟩
end GlobalTheory.Mem.R3.Comm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsLiftsHeckeOperatorsCommuteStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowsLifts_heckeOperators_commute : ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px), B.fields.Ok → I.Ok → ∀ a : I.ι,
  Formalism.L2.Col.HeckeCommAll (rowPts B.wts I.Ch I.sel (I.tup a)) ∅ ∧
    ∀ j : Fin B.R.m, Formalism.L2.Col.HeckeCommAll (liftPts B.wts I.Ch I.sel (I.tup a) (j.1 + 1)) ∅ := by
  first | exact @GlobalTheory.Mem.R3.Comm.rows_lifts_comm | exact GlobalTheory.Mem.R3.Comm.rows_lifts_comm | (intros; apply GlobalTheory.Mem.R3.Comm.rows_lifts_comm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParahoricCharacterMulOfTame
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParahoricCharacterMulOfTame
noncomputable section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.Mem.LamMul

section Blocks

variable {S : Type*} [CommRing S] {r c : ℕ}

theorem det_eq_of_lower_zero (M : Matrix (Fin (r + c)) (Fin (r + c)) S)
    (h : M.submatrix (Fin.natAdd r) (Fin.castAdd c) = 0) :
    M.det = (M.submatrix (Fin.castAdd c) (Fin.castAdd c)).det * (M.submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
  have e : M.submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (M.submatrix (Fin.castAdd c) (Fin.castAdd c)) (M.submatrix (Fin.castAdd c) (Fin.natAdd r)) 0
        (M.submatrix (Fin.natAdd r) (Fin.natAdd r)) := by
    rw [← h]
    ext (i | i) (j | j) <;> simp
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M, e, Matrix.det_fromBlocks_zero₂₁]

theorem mul_dd_of_lower_zero (M N : Matrix (Fin (r + c)) (Fin (r + c)) S)
    (h : M.submatrix (Fin.natAdd r) (Fin.castAdd c) = 0) :
    (M * N).submatrix (Fin.natAdd r) (Fin.natAdd r) =
      M.submatrix (Fin.natAdd r) (Fin.natAdd r) * N.submatrix (Fin.natAdd r) (Fin.natAdd r) := by
  ext i j
  have h0 : ∀ a, M (Fin.natAdd r i) (Fin.castAdd c a) = 0 := fun a => congrFun (congrFun h i) a
  simp [Matrix.mul_apply, Fin.sum_univ_add, h0]

theorem dd_mod (I : Ideal S) (K K' : Matrix (Fin (r + c)) (Fin (r + c)) S)
    (hK : ∀ i j, K (Fin.natAdd r i) (Fin.castAdd c j) ∈ I) (hK' : ∀ i j, K' (Fin.natAdd r i) (Fin.castAdd c j) ∈ I)
    (hu : IsUnit K.det) (hu' : IsUnit K'.det) :
    IsUnit (Ideal.Quotient.mk I (K.submatrix (Fin.natAdd r) (Fin.natAdd r)).det) ∧
    IsUnit (Ideal.Quotient.mk I (K'.submatrix (Fin.natAdd r) (Fin.natAdd r)).det) ∧
    ((K * K').submatrix (Fin.natAdd r) (Fin.natAdd r)).det -
      (K.submatrix (Fin.natAdd r) (Fin.natAdd r)).det * (K'.submatrix (Fin.natAdd r) (Fin.natAdd r)).det ∈ I := by
  have key : ∀ X : Matrix (Fin (r + c)) (Fin (r + c)) S, (∀ i j, X (Fin.natAdd r i) (Fin.castAdd c j) ∈ I) →
      ((Ideal.Quotient.mk I).mapMatrix X).submatrix (Fin.natAdd r) (Fin.castAdd c) = 0 := by
    intro X hX
    ext i j
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hX i j
  have sub : ∀ X : Matrix (Fin (r + c)) (Fin (r + c)) S, Ideal.Quotient.mk I (X.submatrix (Fin.natAdd r) (Fin.natAdd r)).det =
      (((Ideal.Quotient.mk I).mapMatrix X).submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
    intro X
    rw [RingHom.map_det]
    rfl
  have unit : ∀ X : Matrix (Fin (r + c)) (Fin (r + c)) S, (∀ i j, X (Fin.natAdd r i) (Fin.castAdd c j) ∈ I) →
      IsUnit X.det → IsUnit (Ideal.Quotient.mk I (X.submatrix (Fin.natAdd r) (Fin.natAdd r)).det) := by
    intro X hX hu
    have h1 : IsUnit ((Ideal.Quotient.mk I).mapMatrix X).det := by
      rw [← RingHom.map_det]
      exact hu.map _
    rw [det_eq_of_lower_zero _ (key X hX)] at h1
    rw [sub]
    exact isUnit_of_mul_isUnit_right h1
  refine ⟨unit K hK hu, unit K' hK' hu', ?_⟩
  rw [← Ideal.Quotient.eq, map_mul, sub, sub, sub, map_mul,
    mul_dd_of_lower_zero _ _ (key K hK), Matrix.det_mul]

end Blocks

section Val

variable {F Γ : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (v : Valuation F Γ) (O : Subring F) (ε : Γ)

def redI (hO : ∀ x ∈ O, v x ≤ 1) : Ideal O where
  carrier := {a | v (a : F) ≤ ε}
  add_mem' {a b} ha hb := by
    show v ((a : F) + b) ≤ ε
    exact (v.map_add _ _).trans (max_le ha hb)
  zero_mem' := by
    show v ((0 : O) : F) ≤ ε
    simp
  smul_mem' a b hb := by
    show v ((a : F) * b) ≤ ε
    rw [map_mul]
    exact (mul_le_of_le_one_left' (hO _ a.2)).trans hb

variable {v O ε}

theorem val_eq_one_of_isUnit (hO : ∀ x ∈ O, v x ≤ 1) (hε : ε < 1) (a : O)
    (h : IsUnit (Ideal.Quotient.mk (redI v O ε hO) a)) : v (a : F) = 1 := by
  obtain ⟨b, hb⟩ := h.exists_right_inv
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have h1 : a * b - 1 ∈ redI v O ε hO := by
    apply Ideal.Quotient.eq.1
    simpa using hb
  have h2 : v ((a : F) * b - 1) ≤ ε := by
    have h1' : v (((a * b - 1 : O)) : F) ≤ ε := h1
    simpa using h1'
  have h3 : v ((a : F) * b) = 1 := by
    have e : (a : F) * b = ((a : F) * b - 1) + 1 := by ring
    rw [e, Valuation.map_add_eq_of_lt_right]
    · simp
    · simpa using h2.trans_lt hε
  rw [map_mul] at h3
  refine le_antisymm (hO _ a.2) ?_
  rw [← h3]
  exact mul_le_of_le_one_right' (hO _ b.2)


omit [LinearOrderedCommGroupWithZero Γ] in
theorem exists_lift {n : ℕ} {k : GL (Fin n) F} (hk : k ∈ GLint O n) :
    ∃ K : Matrix (Fin n) (Fin n) O, (k : Matrix (Fin n) (Fin n) F) = K.map O.subtype ∧ IsUnit K.det := by
  let K : Matrix (Fin n) (Fin n) O := fun i j => ⟨(k : Matrix (Fin n) (Fin n) F) i j, hk.1 i j⟩
  let K' : Matrix (Fin n) (Fin n) O := fun i j => ⟨((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j, hk.2 i j⟩
  have e : (k : Matrix (Fin n) (Fin n) F) = K.map O.subtype := by ext i j; rfl
  have e' : ((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = K'.map O.subtype := by ext i j; rfl
  refine ⟨K, e, Matrix.isUnit_det_of_right_inverse (B := K') ?_⟩
  apply Matrix.map_injective (f := O.subtype) Subtype.val_injective
  show (K * K').map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
  rw [Matrix.map_mul, ← e, ← e', ← Units.val_mul, mul_inv_cancel, Matrix.map_one _ (map_zero _) (map_one _)]
  rfl

omit [LinearOrderedCommGroupWithZero Γ] in
theorem det_dd_map {r c : ℕ} (K : Matrix (Fin (r + c)) (Fin (r + c)) O) :
    (bDD (K.map O.subtype)).det = (((K.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : O) : F) := by
  show _ = O.subtype _
  rw [RingHom.map_det]
  rfl

theorem dd_val (hO : ∀ x ∈ O, v x ≤ 1) (hε : ε < 1) {r c : ℕ} {k k' : GL (Fin (r + c)) F}
    (hk : k ∈ GLint O (r + c)) (hk' : k' ∈ GLint O (r + c))
    (hd : ∀ i j, v ((k : Matrix (Fin (r + c)) (Fin (r + c)) F) (Fin.natAdd r i) (Fin.castAdd c j)) ≤ ε)
    (hd' : ∀ i j, v ((k' : Matrix (Fin (r + c)) (Fin (r + c)) F) (Fin.natAdd r i) (Fin.castAdd c j)) ≤ ε) :
    v (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧
    v (bDD (k' : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧
    v ((bDD ((k * k' : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F)).det -
      (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det * (bDD (k' : Matrix (Fin (r + c)) (Fin (r + c)) F)).det) ≤ ε := by
  obtain ⟨K, e, hu⟩ := exists_lift hk
  obtain ⟨K', e', hu'⟩ := exists_lift hk'
  have hK : ∀ i j, K (Fin.natAdd r i) (Fin.castAdd c j) ∈ redI v O ε hO := fun i j => by
    have := hd i j
    rw [e] at this
    exact this
  have hK' : ∀ i j, K' (Fin.natAdd r i) (Fin.castAdd c j) ∈ redI v O ε hO := fun i j => by
    have := hd' i j
    rw [e'] at this
    exact this
  obtain ⟨h1, h2, h3⟩ := dd_mod (redI v O ε hO) K K' hK hK' hu hu'
  have em : ((k * k' : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = (K * K').map O.subtype := by
    rw [Units.val_mul, e, e', Matrix.map_mul]
  rw [em, e, e', det_dd_map, det_dd_map, det_dd_map]
  refine ⟨val_eq_one_of_isUnit hO hε _ h1, val_eq_one_of_isUnit hO hε _ h2, ?_⟩
  have h3' : v (((((K * K').submatrix (Fin.natAdd r) (Fin.natAdd r)).det -
      (K.submatrix (Fin.natAdd r) (Fin.natAdd r)).det * (K'.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : O)) : F) ≤ ε := h3
  simpa using h3'

end Val

section Main

theorem lamJ_mul : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (δ : (P.adicCompletion L)ˣ →* ℂˣ), IsDel P δ → ∀ (r c : ℕ) (k k' : GL (Fin (r + c)) (P.adicCompletion L)), k ∈ parJ (OP P) (piP P : P.adicCompletion L) r c → k' ∈ parJ (OP P) (piP P : P.adicCompletion L) r c → lamJ δ (k * k') = lamJ δ k * lamJ δ k' := by
  intro L _ _ P δ hδ r c k k' hk hk'
  have hO : ∀ x ∈ OP P, Valued.v x ≤ 1 := fun x hx => hx
  have hε : (WithZero.exp (-1 : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hπ : Valued.v (piP P : P.adicCompletion L) = WithZero.exp (-1 : ℤ) := unif_spec P
  have small : ∀ {g : GL (Fin (r + c)) (P.adicCompletion L)}, g ∈ parJ (OP P) (piP P : P.adicCompletion L) r c →
      ∀ i j, Valued.v ((g : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L)) (Fin.natAdd r i) (Fin.castAdd c j)) ≤
        WithZero.exp (-1 : ℤ) := by
    intro g hg i j
    obtain ⟨o, ho, e⟩ := hg.2 i j
    have e' : (g : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L)) (Fin.natAdd r i) (Fin.castAdd c j) =
        (piP P : P.adicCompletion L) * o := e
    rw [e', map_mul, hπ]
    exact mul_le_of_le_one_right' (hO _ ho)
  obtain ⟨ha, hb, hxy⟩ := dd_val hO hε hk.1 hk'.1 (small hk) (small hk')
  unfold lamJ
  set a := (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L))).det with hadef
  set b := (bDD (k' : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L))).det with hbdef
  set x := (bDD ((k * k' : GL (Fin (r + c)) (P.adicCompletion L)) : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L))).det with hxdef
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have hab : Valued.v (a * b) = 1 := by rw [map_mul, ha, hb, one_mul]
  have hx : Valued.v x = 1 := by
    have e : x = (x - a * b) + a * b := by ring
    rw [e, Valuation.map_add_eq_of_lt_right, hab]
    rw [hab]
    exact hxy.trans_lt hε
  have hx0 : x ≠ 0 := fun h => by simp [h] at hx
  have tame := hδ.tame (Units.mk0 x hx0 * (Units.mk0 a ha0 * Units.mk0 b hb0)⁻¹) (by
    show Valued.v _ = 1
    simp [hx, ha, hb]) (by
    have e : x * (a * b)⁻¹ - 1 = (x - a * b) * (a * b)⁻¹ := by field_simp
    simp only [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val]
    rw [e, map_mul, map_inv₀, hab, inv_one, mul_one]
    exact hxy)
  rw [map_mul, map_inv, mul_inv_eq_one, map_mul] at tame
  simp only [chi0, dif_neg hx0, dif_neg ha0, dif_neg hb0, tame, Units.val_mul]

end Main

end GlobalTheory.Mem.LamMul
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParahoricCharacterMulOfTameStatement
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoricCharacter_mul_of_tame : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (δ : (P.adicCompletion L)ˣ →* ℂˣ), IsDel P δ → ∀ (r c : ℕ) (k k' : GL (Fin (r + c)) (P.adicCompletion L)), k ∈ parJ (OP P) (piP P : P.adicCompletion L) r c → k' ∈ parJ (OP P) (piP P : P.adicCompletion L) r c → lamJ δ (k * k') = lamJ δ k * lamJ δ k' := by
  first | exact @GlobalTheory.Mem.LamMul.lamJ_mul | exact GlobalTheory.Mem.LamMul.lamJ_mul | (intros; apply GlobalTheory.Mem.LamMul.lamJ_mul <;> assumption)
end
end
