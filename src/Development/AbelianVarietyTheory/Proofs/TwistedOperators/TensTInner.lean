module

public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocKIntMem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensTInner
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowEvalHH

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def Wsub (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (τ : D.what₂.Tau) :
    Submodule ℂ (X.B.H (X.pl.symm τ)) :=
  ((MP R).sm τ).map ((c τ).toLinearEquiv.toLinearMap)

theorem symm_mem_sm (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (τ : D.what₂.Tau) (y : Wsub R X c τ) :
    (c τ).symm (y : X.B.H (X.pl.symm τ)) ∈ (MP R).sm τ := by
  obtain ⟨w, hw, hwy⟩ := Submodule.mem_map.1 y.2
  have : (c τ).symm (y : X.B.H (X.pl.symm τ)) = w := by
    rw [← hwy]
    exact (c τ).symm_apply_apply w
  rw [this]
  exact hw

def vecOf (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (y : ∀ τ, Wsub R X c τ) : (MP R).Vec :=
  fun τ => ⟨(c τ).symm (y τ : X.B.H (X.pl.symm τ)), symm_mem_sm R X c τ (y τ)⟩

def tensT {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (y : ∀ τ, X.B.H (X.pl.symm τ)) : X.B.Hs :=
  X.B.tens (Equiv.piCongrLeft X.B.H X.pl.symm y)


open Classical in
def evF (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (S : MMap (MP R))
    (y : ∀ τ, Wsub R X c τ) : L2X X :=
  star (if hm : MemLp (fun x => ev (MP R) (vecOf R X c y) S
      (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) 2 (muX X)
    then hm.toLp _ else 0)

end GlobalTheory.RowEvalHH

namespace GlobalTheory.RowEvalHH

theorem tensT_inner {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (a b : ∀ τ, X.B.H (X.pl.symm τ)) :
    ⟪tensT X a, tensT X b⟫_ℂ = ∏ τ, ⟪a τ, b τ⟫_ℂ := by
  unfold tensT
  rw [X.B.tens_spec.1]
  rw [← Equiv.prod_comp X.pl.symm]
  simp only [Equiv.piCongrLeft_apply_apply]

theorem tensT_dense {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) :
    Dense (Submodule.span ℂ (Set.range (tensT X)) : Set X.B.Hs) := by
  have : Set.range (tensT X) = Set.range X.B.tens :=
    (Equiv.piCongrLeft X.B.H X.pl.symm).surjective.range_comp X.B.tens
  rw [this]
  exact X.B.tens_spec.2.2

theorem tensT_w {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) :
    tensT X (fun τ => X.B.w (X.pl.symm τ)) = X.B.tens X.B.w := by
  unfold tensT
  congr 1
  have : (fun τ => X.B.w (X.pl.symm τ)) = (Equiv.piCongrLeft X.B.H X.pl.symm).symm X.B.w := by
    funext τ
    rw [Equiv.piCongrLeft_symm_apply]
  rw [this, Equiv.apply_symm_apply]

end GlobalTheory.RowEvalHH

namespace GlobalTheory.RowEvalHH

theorem Wsub_dense {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (τ : D.what₂.Tau) :
    Dense (Wsub R X c τ : Set (X.B.H (X.pl.symm τ))) := by
  unfold Wsub
  rw [Submodule.map_coe]
  exact (c τ).surjective.denseRange.dense_image (c τ).continuous (Formalism.IndefR.SchurOrthogonalityAlt.sm_dense (MP R) τ)

end GlobalTheory.RowEvalHH
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoThetaMapModelsOfNoPairingCovers
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoThetaMapModelsOfNoPairingCovers
noncomputable section

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

namespace GlobalTheory.ArchRec.NoLiftTransfer

theorem jm_mul_jm (p q : ℕ) : Jm p q * Jm p q = 1 := by
  unfold Jm Formalism.UG.Jpq
  simp [Matrix.fromBlocks_multiply]

theorem conj_trace {p q : ℕ} {Z : Mat p q} (hZ : Z ∈ upq p q) : (starRingEnd ℂ) Z.trace = -Z.trace := by
  have h : Zᴴ * Jm p q + Jm p q * Z = 0 := hZ

  have h2 : Jm p q * Zᴴ * Jm p q + Z = 0 := by
    have h' := congrArg (fun X => Jm p q * X) h
    simpa [mul_add, ← mul_assoc, jm_mul_jm] using h'
  have h3 : (Jm p q * Zᴴ * Jm p q).trace + Z.trace = 0 := by rw [← Matrix.trace_add, h2, Matrix.trace_zero]
  rw [Matrix.trace_mul_comm, ← mul_assoc, jm_mul_jm, one_mul, Matrix.trace_conjTranspose] at h3
  rw [starRingEnd_apply]
  exact eq_neg_of_add_eq_zero_left h3

def invConj {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (u : A → B)
    (hb : Function.Bijective u) (hadd : ∀ x y, u (x + y) = u x + u y)
    (hsmul : ∀ (z : ℂ) x, u (z • x) = conj z • u x) : B →ₛₗ[starRingEnd ℂ] A where
  toFun := (Equiv.ofBijective u hb).symm
  map_add' x y := by
    apply hb.1
    rw [hadd]
    simp only [Equiv.ofBijective_apply_symm_apply]
  map_smul' z x := by
    apply hb.1
    rw [hsmul]
    simp only [Equiv.ofBijective_apply_symm_apply, Complex.conj_conj]

theorem invConj_apply {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (u : A → B)
    (hb : Function.Bijective u) (hadd : ∀ x y, u (x + y) = u x + u y)
    (hsmul : ∀ (z : ℂ) x, u (z • x) = conj z • u x) (x : A) : invConj u hb hadd hsmul (u x) = x :=
  hb.1 ((Equiv.ofBijective u hb).apply_symm_apply (u x))

theorem noLift_of_pairNo : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (ι σ Z : Type) (A : Mn V.rank → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ)) (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] MvPolynomial σ ℂ) (p q : ℕ) (T₁ : GrpData p q) (R₁ : DSRep T₁) (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (l₁ : Ix p q → ℚ) (c₁ : ℚ) (b₁ : Bool) (e₁ : Ix p q ≃ Fin V.rank) (u₁ : kfin M τ → R₁.HK.V), KTie R₁ M τ l₁ c₁ b₁ true e₁ u₁ → Side A pt κ (phiFr (M.fr τ) b₁ e₁) c₁ a₁ → PairNo a₁ R₁ → NoLift M τ A pt := by
  intro D V S M τ ι σ Z A pt κ p q T₁ R₁ a₁ l₁ c₁ b₁ e₁ u₁ hK hS hP

  have hsm : ∀ (z : ℂ) x, u₁ (z • x) = conj z • u₁ x := fun z x => by simpa [cjc] using hK.smul z x
  let w := invConj u₁ hK.bij hK.add hsm
  have hw_right : ∀ y, u₁ (w y) = y := fun y => (Equiv.ofBijective u₁ hK.bij).apply_symm_apply y
  have hw_left : ∀ v, w (u₁ v) = v := fun v => invConj_apply u₁ hK.bij hK.add hsm v
  intro U _ _ Q hQ

  let B : MvPolynomial σ ℂ →ₗ[ℂ] R₁.HK.V →ₛₗ[starRingEnd ℂ] U :=
    { toFun := fun P => (Q (κ.symm P)).comp w
      map_add' := fun P P' => by ext x; simp
      map_smul' := fun z P => by ext x; simp }
  have hB : ∀ P x, B P x = Q (κ.symm P) (w x) := fun _ _ => rfl
  have hinv : PInv a₁ R₁ B := by
    intro Y hY P x
    set t : ℂ := (c₁ : ℂ) * Y.trace with ht_def

    have ht : conj t = -t := by rw [ht_def, map_mul, conj_trace hY, map_ratCast, mul_neg]
    have hX : phiFr (M.fr τ) b₁ e₁ Y ∈ lieAt V τ := by rw [← hK.lie]; exact ⟨Y, hY, rfl⟩
    have hpol : PolDer A pt (phiFr (M.fr τ) b₁ e₁ Y) (κ.symm P) (κ.symm (a₁ Y P + t • P)) :=
      (hS.der Y hY _ _).2 (by simp only [LinearEquiv.apply_symm_apply, ht_def])
    have hvec : VecDer M τ (phiFr (M.fr τ) b₁ e₁ Y) (w x) (w (R₁.HK.act Y x + t • x)) :=
      (hK.der Y hY _ _).2 (by simp only [hw_right, ht_def])
    have h0 := hQ _ hX _ _ _ _ hpol hvec
    have e1 : Q (κ.symm (a₁ Y P + t • P)) (w x) = Q (κ.symm (a₁ Y P)) (w x) + t • Q (κ.symm P) (w x) := by
      rw [map_add (f := _), map_smul, map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    have e2 : Q (κ.symm P) (w (R₁.HK.act Y x + t • x)) =
        Q (κ.symm P) (w (R₁.HK.act Y x)) - t • Q (κ.symm P) (w x) := by
      rw [map_add (f := _), map_add (f := _), map_smulₛₗ, ht, map_smul, neg_smul, sub_eq_add_neg]
    rw [e1, e2] at h0
    rw [hB, hB, ← h0]
    abel
  have hB0 : B = 0 := hP U B hinv
  refine LinearMap.ext fun P => LinearMap.ext fun v => ?_
  have h1 := congrArg (fun F : MvPolynomial σ ℂ →ₗ[ℂ] R₁.HK.V →ₛₗ[starRingEnd ℂ] U => F (κ P) (u₁ v)) hB0
  simpa [hB, hw_left] using h1

end GlobalTheory.ArchRec.NoLiftTransfer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoThetaMapModelsOfNoPairingCoversStatement
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
theorem _root_.GlobalTheory.T.noThetaMap_models_of_noPairing_covers : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (ι σ Z : Type) (A : Mn V.rank → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ)) (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] MvPolynomial σ ℂ) (p q : ℕ) (T₁ : GrpData p q) (R₁ : DSRep T₁) (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (l₁ : Ix p q → ℚ) (c₁ : ℚ) (b₁ : Bool) (e₁ : Ix p q ≃ Fin V.rank) (u₁ : kfin M τ → R₁.HK.V), KTie R₁ M τ l₁ c₁ b₁ true e₁ u₁ → Side A pt κ (phiFr (M.fr τ) b₁ e₁) c₁ a₁ → PairNo a₁ R₁ → NoLift M τ A pt := by
  first | exact @GlobalTheory.ArchRec.NoLiftTransfer.noLift_of_pairNo | exact GlobalTheory.ArchRec.NoLiftTransfer.noLift_of_pairNo | (intros; apply GlobalTheory.ArchRec.NoLiftTransfer.noLift_of_pairNo <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSignCompatibleNumberingDecreasingEnumerati
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSignCompatibleNumberingDecreasingEnumerati
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
namespace GlobalTheory.ArchRec.EnumBlocks

theorem signed_eq {p q : ℕ} {l₁ l₂ : List ℚ} (c : ℚ) (h₁ : l₁.length = p) (h₂ : l₂.length = q) :
    signed l₁ l₂ c = Finset.univ.image fun a : Ix p q => (ofBlocks l₁ l₂ a + c, a.isLeft) := by
  subst h₁ h₂
  ext ⟨x, b⟩
  simp only [signed, Finset.mem_union, List.mem_toFinset, List.mem_map, Prod.mk.injEq, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨y, hy, rfl, rfl⟩ | ⟨y, hy, rfl, rfl⟩)
    · obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hy
      exact ⟨.inl i, by simp [ofBlocks], rfl⟩
    · obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hy
      exact ⟨.inr i, by simp [ofBlocks], rfl⟩
  · rintro ⟨a | a, rfl, rfl⟩
    · exact Or.inl ⟨_, by simp [ofBlocks], rfl, by simp⟩
    · exact Or.inr ⟨_, by simp [ofBlocks], rfl, by simp⟩

theorem sameBlock_iff {p q : ℕ} (a b : Ix p q) : sameBlock a b ↔ b.isLeft = a.isLeft := by
  rcases a with a | a <;> rcases b with b | b <;> simp [sameBlock]

theorem card_filter_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (P : β → Prop) (Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ b, P (e b) ↔ Q b) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card :=
  (Finset.card_equiv e (fun b => by simp [h])).symm

theorem lowK_numbered {n p q : ℕ} {ε : Fin n → Bool} {lamM : Fin n → ℝ} (e : Ix p q ≃ Fin n)
    (hε : ∀ a, ε (e a) = a.isLeft) (R : Ix p q → Ix p q → Prop) (hR : ∀ a b, e a < e b ↔ R a b) (a : Ix p q)
    [DecidableRel R] :
    Formalism.QuantumDeterminants.lowK ε lamM (e a) = lamM (e a) +
      ((((Finset.univ.filter fun b => ¬ sameBlock a b ∧ R a b).card : ℝ) -
        ((Finset.univ.filter fun b => ¬ sameBlock a b ∧ R b a).card : ℝ)) / 2 -
       (((Finset.univ.filter fun b => sameBlock a b ∧ R a b).card : ℝ) -
        ((Finset.univ.filter fun b => sameBlock a b ∧ R b a).card : ℝ)) / 2) := by
  classical
  have hs : ∀ b, ε (e b) = ε (e a) ↔ sameBlock a b := fun b => by rw [hε, hε, sameBlock_iff]
  have hn : ∀ b, ε (e b) ≠ ε (e a) ↔ ¬ sameBlock a b := fun b => not_congr (hs b)
  have n1 := card_filter_equiv e (fun j => e a < j ∧ ε j ≠ ε (e a)) (fun b => ¬ sameBlock a b ∧ R a b)
    fun b => by rw [hR, hn]; exact and_comm
  have n2 := card_filter_equiv e (fun j => j < e a ∧ ε j ≠ ε (e a)) (fun b => ¬ sameBlock a b ∧ R b a)
    fun b => by rw [hR, hn]; exact and_comm
  have c1 := card_filter_equiv e (fun j => e a < j ∧ ε j = ε (e a)) (fun b => sameBlock a b ∧ R a b)
    fun b => by rw [hR, hs]; exact and_comm
  have c2 := card_filter_equiv e (fun j => j < e a ∧ ε j = ε (e a)) (fun b => sameBlock a b ∧ R b a)
    fun b => by rw [hR, hs]; exact and_comm
  simp only [Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply, Formalism.REAL.rhoN, Formalism.REAL.rhoC]
  rw [n1, n2, c1, c2]
  ring

theorem core {n p q : ℕ} {L : Ix p q → ℚ} (hL : Function.Injective L) {c s : ℚ} (hs : s = 1 ∨ s = -1)
    {ε : Fin n → Bool} {lamM : Fin n → ℝ}
    (hE : IsEnum (Finset.univ.image fun a : Ix p q => (s * (L a + c), a.isLeft)) lamM ε) :
    ∃ e : Ix p q ≃ Fin n, IsOrd ε lamM L c (s : ℝ) e := by
  classical
  obtain ⟨hanti, r, hr, hS⟩ := hE
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have hf : Function.Injective fun a : Ix p q => (s * (L a + c), a.isLeft) := fun a b h =>
    hL (add_right_cancel (mul_left_cancel₀ hs0 (congrArg Prod.fst h)))
  have hg : Function.Injective fun i => (r i, ε i) := fun i j h =>
    hanti.injective (by rw [hr, hr, show r i = r j from congrArg Prod.fst h])
  have ex : ∀ a : Ix p q, ∃ i, (r i, ε i) = (s * (L a + c), a.isLeft) := fun a => by
    have : (s * (L a + c), a.isLeft) ∈ Finset.univ.image fun i => (r i, ε i) := by
      rw [← hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 this
    exact ⟨i, hi⟩
  choose f hfi using ex
  have finj : Function.Injective f := fun a b h => hf (by
    show (s * (L a + c), a.isLeft) = (s * (L b + c), b.isLeft)
    rw [← hfi a, ← hfi b, h])
  have fsurj : Function.Surjective f := fun i => by
    have : (r i, ε i) ∈ Finset.univ.image fun a : Ix p q => (s * (L a + c), a.isLeft) := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 this
    exact ⟨a, hg ((hfi a).trans ha)⟩
  let e : Ix p q ≃ Fin n := Equiv.ofBijective f ⟨finj, fsurj⟩
  have he : ∀ a, (r (e a), ε (e a)) = (s * (L a + c), a.isLeft) := hfi
  have hε : ∀ a, ε (e a) = a.isLeft := fun a => congrArg Prod.snd (he a)
  have hr' : ∀ a, r (e a) = s * (L a + c) := fun a => congrArg Prod.fst (he a)
  have hlam : ∀ a, lamM (e a) = (s : ℝ) * ((L a + c : ℚ) : ℝ) := fun a => by
    rw [hr, hr']; push_cast; ring
  have hlt : ∀ a b, e a < e b ↔ s * L b < s * L a := fun a b => by
    have h0 : e a < e b ↔ lamM (e b) < lamM (e a) := ⟨fun h => hanti h, fun h => by
      by_contra hn
      exact absurd (hanti.antitone (not_lt.1 hn)) (not_le.2 h)⟩
    rw [h0, hlam, hlam]
    rw [← Rat.cast_mul, ← Rat.cast_mul, Rat.cast_lt, mul_add, mul_add, add_lt_add_iff_right]
  refine ⟨e, hε, hlam, fun a => ?_⟩
  rcases hs with rfl | rfl
  · rw [lowK_numbered e hε (fun a b => L b < L a) (fun a b => by simpa using hlt a b) a, hlam]
    simp only [blattner, rhoNC]
    push_cast
    ring
  · rw [lowK_numbered e hε (fun a b => L a < L b) (fun a b => by simpa using hlt a b) a, hlam]
    simp only [blattner, rhoNC]
    push_cast
    ring

theorem parOf_eq {p q : ℕ} {l₁ l₂ : List ℚ} (br cj : Bool) (c : ℚ) (h₁ : l₁.length = p) (h₂ : l₂.length = q) :
    parOf br cj l₁ l₂ c = Finset.univ.image fun a : Ix p q =>
      ((if br = cj then 1 else -1 : ℚ) * (ofBlocks l₁ l₂ a + c), a.isLeft) := by
  classical
  unfold parOf dualPar
  rw [signed_eq c h₁ h₂]
  split_ifs
  · simp
  · rw [Finset.image_image]
    refine Finset.image_congr fun a _ => ?_
    simp

theorem exists_isOrd (n p q : ℕ) (l₁ l₂ : List ℚ) (c : ℚ) (br cj : Bool) (ε : Fin n → Bool) (lamM : Fin n → ℝ)
    (h₁ : l₁.length = p) (h₂ : l₂.length = q) (hP : IsParam (ofBlocks l₁ l₂ : Ix p q → ℚ))
    (hE : IsEnum (parOf br cj l₁ l₂ c) lamM ε) :
    ∃ e : Ix p q ≃ Fin n, IsOrd ε lamM (ofBlocks l₁ l₂) c (sg br cj) e := by
  rw [parOf_eq br cj c h₁ h₂] at hE
  have hs : (if br = cj then 1 else -1 : ℚ) = 1 ∨ (if br = cj then 1 else -1 : ℚ) = -1 := by
    split_ifs <;> simp
  have := core hP.1 hs hE
  have hc : (((if br = cj then 1 else -1 : ℚ)) : ℝ) = sg br cj := by
    unfold sg; split_ifs <;> simp
  rwa [hc] at this

end GlobalTheory.ArchRec.EnumBlocks
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSignCompatibleNumberingDecreasingEnumeratiStatement
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
theorem _root_.GlobalTheory.T.exists_signCompatible_numbering_decreasing_enumeration : ∀ (n p q : ℕ) (l₁ l₂ : List ℚ) (c : ℚ) (br cj : Bool) (ε : Fin n → Bool) (lamM : Fin n → ℝ), l₁.length = p → l₂.length = q → IsParam (ofBlocks l₁ l₂ : Ix p q → ℚ) → IsEnum (parOf br cj l₁ l₂ c) lamM ε → ∃ e : Ix p q ≃ Fin n, IsOrd ε lamM (ofBlocks l₁ l₂) c (sg br cj) e := by
  first | exact @GlobalTheory.ArchRec.EnumBlocks.exists_isOrd | exact GlobalTheory.ArchRec.EnumBlocks.exists_isOrd | (intros; apply GlobalTheory.ArchRec.EnumBlocks.exists_isOrd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPartMemCompletedSelfDualLatticeIffSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPartMemCompletedSelfDualLatticeIffSplitPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitRowLat

variable {D : D7}

theorem smul_mem_latHat (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
    ∀ a ∈ intAE D, ∀ y ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)),
      (fun i => a * y i) ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) := by
  intro a ha y hy
  change y ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) at hy
  change _ ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E))
  induction ha using AddSubgroup.closure_induction with
  | mem a ha =>
    obtain ⟨s, hs, o, rfl⟩ := ha
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨t, ht, x, hx, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨s * t, fun v => mul_mem (hs v) (ht v), o • x,
        Λ.smul_mem o hx, ?_⟩
      funext i
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      rfl
    | zero =>
      simp only [Pi.zero_apply, mul_zero]
      exact zero_mem _
    | add u w _ _ hu hw =>
      simp only [Pi.add_apply, mul_add]
      exact add_mem hu hw
    | neg u _ hu =>
      simp only [Pi.neg_apply, mul_neg]
      exact neg_mem hu
  | zero =>
    simp only [zero_mul]
    exact zero_mem _
  | add u w _ _ hu hw =>
    simp only [add_mul]
    exact add_mem hu hw
  | neg u _ hu =>
    simp only [neg_mul]
    exact neg_mem hu

theorem latHat_selfDual (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) (y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    y ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) ↔
      ∀ z ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)),
        hR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram z y ∈ intAE D := by
  obtain ⟨-, -, -, -, hcc, -, -, hG, hdet, -, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have hsum : ∀ w x : Fin V.rank → D.host.E,
      (∑ a, ∑ b, w a * (HSpace.gram V)ᵀ a b * (GlobalTheory.Member.cF D) (x b)) =
        ∑ i, ∑ j, star (x i) * HSpace.gram V i j * w j := by
    intro w x
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.transpose_apply]
    change w b * HSpace.gram V a b * star (x a) = _
    ring
  have hL : ∀ w : Fin V.rank → D.host.E,
      (∀ x ∈ Λ, ∑ a, ∑ b, w a * (HSpace.gram V)ᵀ a b * (GlobalTheory.Member.cF D) (x b) ∈
        (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ↔ w ∈ Λ := by
    intro w
    rw [hΛ.2 w]
    refine forall₂_congr fun x _ => ?_
    rw [FractionalIdeal.mem_one_iff, hsum]
  have hfull : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
      IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
    intro V Λ hΛ
    haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
    refine ⟨?_⟩
    obtain ⟨s, hs⟩ := hΛ.1.fg
    apply eq_top_iff.mpr
    intro y _
    let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
      ∑ i, ∑ j, star (x i) * V.gram i j * y j
    obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
    have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
      exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
    let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
      carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
      zero_mem' := by refine ⟨0, ?_⟩; simp [f]
      add_mem' := by
        rintro x z ⟨b, hb⟩ ⟨c, hc⟩
        refine ⟨b + c, ?_⟩
        change (b : D.host.E) + c = _
        rw [hb, hc]
        simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
      smul_mem' := by
        rintro c x ⟨b, hb⟩
        refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
        simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change star (c : D.host.E) * _ = _
        ring }
    have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
      intro x hx
      obtain ⟨b, hb⟩ := ha x hx
      exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
    have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
      apply (hΛ.2 _).2
      intro x hx
      have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
      obtain ⟨b, hb⟩ := hxP
      refine ⟨b, ?_⟩
      rw [hb]
      dsimp only [f, Pi.smul_apply]
      simp only [smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
      Submodule.subset_span hy
    have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
      (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
    change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
      ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
    rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
    exact this
  have key := GlobalTheory.AdLat.hat_selfDual D.host.F D.host.E V.rank Λ (GlobalTheory.Member.cF D)
    (HSpace.gram V)ᵀ 1 hΛ.1.fg (Submodule.IsFullLattice.span_eq_top (self := hfull V Λ hΛ)) hcc hG hdet one_ne_zero hL
  rw [← GlobalTheory.LatDual.integralTensorAdeles_eq_adelicCompletion_one] at key
  simp only [GlobalTheory.LatDual.hR_eq_hermA]
  constructor
  · intro hy z hz
    change z ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) at hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨t, ht, x, hx, rfl⟩ := hz
      have h1 : (t ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E)) ∈ intAE D :=
        AddSubgroup.subset_closure ⟨t, ht, 1, rfl⟩
      have h2 := (key _).2 (smul_mem_latHat V Λ _ h1 y hy) x hx
      convert h2 using 1
      unfold GlobalTheory.AdLat.hermA
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      have e : GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (GlobalTheory.Member.cF D) (t ⊗ₜ[D.host.F] x b) =
          (t ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E)) *
            GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (GlobalTheory.Member.cF D) (GlobalTheory.AdLat.fv D.host.F x b) := by
        simp [GlobalTheory.AdLat.sg, GlobalTheory.AdLat.fv]
      rw [e]
      ring
    | zero =>
      have : GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y 0 = 0 := by simp [GlobalTheory.AdLat.hermA]
      rw [this]; exact zero_mem _
    | add u w _ _ hu hw =>
      have : GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y (u + w) =
          GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y u +
            GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y w := by
        simp only [GlobalTheory.AdLat.hermA, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
      rw [this]; exact add_mem hu hw
    | neg u _ hu =>
      have : GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y (-u) =
          -GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y u := by
        simp only [GlobalTheory.AdLat.hermA, Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib]
      rw [this]; exact neg_mem hu
  · intro h
    refine (key y).1 fun x hx => h _ ?_
    exact AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩

theorem mem_iff (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) (x : Fin V.rank → AE D) :
    (fun i => finPart D (x i)) ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) ↔
      ∀ z : Fin V.rank → AE D,
        (fun i => finPart D (z i)) ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) →
          finPart D (GlobalTheory.SplitDualLat.form V x z) ∈ intAE D := by
  rw [latHat_selfDual V Λ hΛ]
  constructor
  · intro h z hz
    rw [← GlobalTheory.SplitDualLat.cA_form, GlobalTheory.SplitDualLat.finPart_cA, GlobalTheory.SplitDualLat.finPart_form]
    exact GlobalTheory.SplitDualLat.sigR_mem_intAE (h _ hz)
  · intro h z hz
    obtain ⟨w, rfl⟩ : ∃ w : Fin V.rank → AE D, (fun i => finPart D (w i)) = z := by
      choose s hs using GlobalTheory.SplitDualLat.finPart_surjective (D := D)
      exact ⟨fun i => s (z i), funext fun i => hs _⟩
    rw [← GlobalTheory.SplitDualLat.finPart_form, ← GlobalTheory.SplitDualLat.cA_form, GlobalTheory.SplitDualLat.finPart_cA]
    exact GlobalTheory.SplitDualLat.sigR_mem_intAE (h _ hz)

theorem isInt_iff_le_one {v : FinPl D} (x : Fv D.host.F v) :
    GlobalTheory.SplitHecke.IsInt (GlobalTheory.SplitHecke.Ov D v) x ↔ Valued.v x ≤ 1 := by
  rw [GlobalTheory.SplitHecke.isInt_iff, ← HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · rintro ⟨o, rfl⟩
    exact o.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem conj_mem_latHat_iff : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (β : GL (Fin V.rank) (EAf D)), IsSelfDualC V Λ → Formalism.L2.DIV.IsFrame β Λ → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ y : Fin V.rank → AE D, (fun i => finPart D (cA D e * y i)) ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) ↔ ∀ j, Valued.v (((fun i => rdA φ (cA D (y i))) ᵥ* ((V.gram.map (rdQ φ)) * (frCo φ β).1)) j) ≤ 1 := by
  intro D V Λ β hΛ hβ v φ e he y
  obtain ⟨hπ, -, hQ, -, -⟩ := GlobalTheory.T.splitProjAdeleComponent_chart_properties D v φ e he
  have hcol := GlobalTheory.T.splitPlace_column_mem_completedLattice_iff_frame_integral D V Λ β hΛ hβ v φ e he
  have hmapQ : V.gram.map (rdQ φ) = V.gram.map fun a => rdA φ (incA D a) := by
    ext i j
    simp only [Matrix.map_apply, hQ]
  rw [mem_iff V Λ hΛ, hmapQ]
  constructor
  · intro h j
    choose s hs using hπ.1
    have h1 : (fun k => rdA φ (s ((frCo φ β).1 k j))) = (frCo φ β).1 *ᵥ Pi.single j 1 := by
      funext k
      rw [hs, Matrix.mulVec_single_one]
      rfl
    have h2 := h _ ((hcol fun k => s ((frCo φ β).1 k j)).2 fun i => by
      rw [h1, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      by_cases hi : i = j
      · subst hi; rw [Pi.single_eq_same]; simp
      · rw [Pi.single_eq_of_ne hi]; simp)
    rw [GlobalTheory.SplitDualLat.form_mul, GlobalTheory.SplitDualLat.cA_cA, he.1.1, hπ.2.2.2, GlobalTheory.SplitDualLat.map_form, h1,
      Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, dotProduct_single, mul_one] at h2
    exact (isInt_iff_le_one _).1 h2
  · intro h z hz
    have h1 := smul_mem_latHat V Λ _
      (GlobalTheory.AdIdem.idempotent_mem_intAE D (finPart D e) (by rw [← RingHom.map_mul, he.1.1])) _ hz
    simp only [← RingHom.map_mul] at h1
    have h2 := (hcol z).1 h1
    have h3 := GlobalTheory.SplitDualLat.form_mul V (cA D e) 1 y z
    simp only [one_mul, mul_one, GlobalTheory.SplitDualLat.cA_cA] at h3
    have h4 : (fun k => rdA φ (z k)) = (frCo φ β).1 *ᵥ (((frCo φ β)⁻¹).1 *ᵥ fun k => rdA φ (z k)) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    rw [h3, hπ.2.2.2, GlobalTheory.SplitDualLat.map_form, h4, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      GlobalTheory.SplitHecke.isInt_iff]
    exact sum_mem fun i _ => mul_mem (GlobalTheory.SplitHecke.isInt_iff.1 ((isInt_iff_le_one _).2 (h i)))
      (GlobalTheory.SplitHecke.isInt_iff.1 ((isInt_iff_le_one _).2 (h2 i)))

end GlobalTheory.SplitRowLat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPartMemCompletedSelfDualLatticeIffSplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjPart_mem_completedSelfDualLattice_iff_splitPlace : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (β : GL (Fin V.rank) (EAf D)), IsSelfDualC V Λ → Formalism.L2.DIV.IsFrame β Λ → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ y : Fin V.rank → AE D, (fun i => finPart D (cA D e * y i)) ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) ↔ ∀ j, Valued.v (((fun i => rdA φ (cA D (y i))) ᵥ* ((V.gram.map (rdQ φ)) * (frCo φ β).1)) j) ≤ 1 := by
  first | exact @GlobalTheory.SplitRowLat.conj_mem_latHat_iff | exact GlobalTheory.SplitRowLat.conj_mem_latHat_iff | (intros; apply GlobalTheory.SplitRowLat.conj_mem_latHat_iff <;> assumption)
end
end
