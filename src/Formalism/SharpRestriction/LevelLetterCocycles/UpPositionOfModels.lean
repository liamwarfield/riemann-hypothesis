module

public import Formalism.SharpRestriction.LevelLetterCocycles.ModelKStep
public import Formalism.SharpRestriction.LevelLetterCocycles.PlaceLabelTeichmuller
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.PsiLowerBoundHolds
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantUniformizer
public import Formalism.SharpRestriction.LevelLetterCocycles.EqZeroOfPowDvd
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalShareBounds

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.UpPositionOfModels
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

def DownSlotOfModels : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → modelFR D HW → DownSlotProposition D HW

def UpSlotOfModels : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → modelFR D HW → UpSlotProposition D HW

def MixedSlotOfModels : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → DdRFull D → DiRank D HW F Cm → modelFR D HW → MixedSlotProposition D HW

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.ExpansionFormAll
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def ExpansionFormLetter (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) : Prop :=
  ∀ (c : ZMod n) (y : W.DD T), y ∈ DelS W T → y ∈ letS W T c → (∃ k : ℕ, W.Q ^ k • y ∈ W.N T) →
    (∀ ζ τ, Pt c ζ τ → ∀ (k : ℕ) (hk : W.Q ^ k • y ∈ W.N T) (i : ℤ),
      W.levN T c ζ ⟨W.Q ^ k • y, hk⟩ i ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ ((k : ℤ) - i)) →
    y ∈ W.N T

end Local

def ExpansionFormAll (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K LL : FinExt l) (hG : Good K 1 LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (h' : ℕ), 1 ≤ h' → IsCrys ((D.loc l).PD K) T.ρ →
    (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
    ExpansionFormLetter ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG)

def ExpansionFormHypothesis : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → DdRFull D → DiRank D HW F Cm → ExpansionFormAll D HW

def ModelFLinkStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → ExpansionFormAll D HW → modelFR D HW

theorem modelFStep_of (hL : ModelFLinkStep) (hP : ExpansionFormHypothesis) :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
      DdRFull D → DiRank D HW F Cm → Adm1 D HW F Cm CA CB CK → modelFR D HW :=
  fun D HW F Cm CA CB CK hd hr hA => hL D HW F Cm CA CB CK hA (hP D HW F Cm CA CB CK hA hd hr)

def ModelQLinkStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → modelLR D HW → modelQR D HW

theorem modelQStep_of (hL : ModelQLinkStep) (hM : ModelLStep) : ModelQStep :=
  fun D HW F Cm CA CB CK hA => hL D HW F Cm CA CB CK hA (hM D HW F Cm CA CB CK hA)

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.CylinderCountFamily
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.FamilyStatementsLocal
noncomputable section

namespace Formalism.MainNotions.FamilyNumericLemmas

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Filter Topology

theorem cyl_univ (D : D7) (k : Fin 2) : cyl D k Set.univ = Set.univ := by
  ext t; simp [cyl]

end Formalism.MainNotions.FamilyNumericLemmas
end
end

noncomputable section

namespace Formalism.MainNotions.ArithmeticCylinders

open Formalism.BasicNotions Formalism.MainNotions Filter Topology Polynomial

structure AllRowsAt (D : D7) (Dall Dgood : ℕ) : Type 1 where
  B : Formalism.MainNotions.S.RowsAut
  n_eq : B.I.n = D.R.r
  f_eq : B.I.f = D.R.f
  labAll : ∀ k, Fin Dall → D.nd.PlG k → (ZMod (D.host.g k))[X]
  labAll_label : ∀ k σ v, IsLabel D k (labAll k σ v)
  inc : Fin Dgood → Fin Dall
  eVec : ∀ k, D.nd.PlG k → MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))
  eVec_idem : ∀ k v, eVec k v * eVec k v = eVec k v
  eT : Set (Tup2 D) → B.I.Gf → ℂ
  ReT : Set (Tup2 D) → (B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund)
  ReT_spec : ∀ S, B.I.IsRConvF B.μf B.fund B.R (eT S) (ReT S)
  eT_univ : eT Set.univ = B.e
  ReT_univ : ReT Set.univ = B.Re
  eT_one : ∀ (k : Fin 2) (S : Finset (Tup D k)),
    (eT (cyl D k (S : Set (Tup D k))) 1).re =
      (B.e 1).re * ∑ t ∈ S, ∏ v, wtOf D k (eVec k v) (t v)

variable {D : D7} {Dall Dgood : ℕ}

def AllRowsAt.dimT (A : AllRowsAt D Dall Dgood) (S : Set (Tup2 D)) : ℕ :=
  A.B.I.Dcount A.B.σs A.B.μf A.B.fund A.B.R (A.ReT S)

def TieCountAt (A : AllRowsAt D Dall Dgood) (n₀ : ℕ) (Alev C₃ cb : ℝ) : Prop :=
  ∃ b h : ℝ,
    (∀ (k : Fin 2) (S : Set (Tup D k)),
      Formalism.MainNotions.PlaceDegreeData.HidaSetting A.B.I n₀ Alev b A.B.lam A.B.μf A.B.g (D.host.g (1 - k)) (A.eT (cyl D k S)) ∧
      Formalism.MainNotions.PlaceDegreeData.CountData A.B.I A.B.lam A.B.σ A.B.w A.B.σs A.B.tens A.B.μf A.B.fund A.B.R
        (A.eT (cyl D k S)) (A.ReT (cyl D k S))) ∧
    (∀ v, Formalism.QuantumDeterminants.GapAtLeast (A.B.I.ε v) (A.B.lam v) h) ∧
    C₃ * (A.B.I.n : ℝ) ^ 19 * (A.B.I.f : ℝ) ^ 5 * Real.log (b * A.B.I.rd) ≤ h ∧
    Real.log (A.B.I.f : ℝ) ≤ Real.sqrt (A.B.I.n : ℝ) ∧
    Real.log (Real.log b) ≤ cb * (A.B.I.n : ℝ) * (A.B.I.f : ℝ) * Real.log (A.B.I.n : ℝ) ∧
    0 < A.B.I.Dstar (Formalism.MainNotions.PlaceDegreeData.fdegAll A.B.I A.B.σ A.B.w) A.B.μf A.B.fund A.B.e

variable (D)

def AllRows.toAt {D : D7} (A : AllRows D) : AllRowsAt D D.what₂.Dall D.what₂.Drows where
  B := A.B
  n_eq := A.n_eq
  f_eq := A.f_eq
  labAll := A.labAll
  labAll_label := A.labAll_label
  inc := A.inc
  eVec := A.eVec
  eVec_idem := A.eVec_idem
  eT := A.eT
  ReT := A.ReT
  ReT_spec := A.ReT_spec
  eT_univ := A.eT_univ
  ReT_univ := A.ReT_univ
  eT_one := A.eT_one

end Formalism.MainNotions.ArithmeticCylinders

namespace Formalism.MainNotions.N.CylinderCountFamily

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Formalism.MainNotions.FamilyNumericLemmas Filter Topology Polynomial

end Formalism.MainNotions.N.CylinderCountFamily
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionFree
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

def UnivLinkStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (Fo : FonOf D.loc D.locA HW), HerrClassMapsLocal D HW Fo → dvdR →
    invLiftR D HW → classMapR D HW → frameR D HW → modelFR D HW → u1R D HW → kapPiR D HW →
    u2R D HW → DownSlotProposition D HW → UpSlotProposition D HW → MixedSlotProposition D HW → univR D HW

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionHypothesis
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

def FirstFrameOfModels : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    adm1 D HW F Cm → DdRFull D → DiRank D HW F Cm → modelLR D HW → modelFR D HW → u1R D HW

theorem first_frame_of_models (hL : FirstFrameOfModels) (hML : ModelLStep) :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
      DdRFull D → DiRank D HW F Cm → Adm1 D HW F Cm CA CB CK → modelFR D HW → u1R D HW :=
  fun D HW F Cm CA CB CK hd hr hA hMF => hL D HW F Cm hA.1 hd hr (hML D HW F Cm CA CB CK hA) hMF

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.SecondRankCount
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def SecondRankCount (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) : Prop :=
  ∀ S : Submodule O (LcQ W T π' c),
    finrank O (IIrest W T Pt π' Eπ h' c S) ≤ (finrank K₀ K + 1) * finrank O S

end Local

def SecondRankCountAll (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (h' : ℕ), 1 ≤ h' → IsCrys ((D.loc l).PD K) T.ρ →
      (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
      ∀ c, SecondRankCount ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' c

def SecondRankHypothesis : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → modelLR D HW → SecondRankCountAll D HW

def SecondPropositionOfRank : Prop := ∀ (D : D7) (HW : HWOf D.loc), modelQR D HW → SecondRankCountAll D HW → u2R D HW

theorem second_proposition_of_models (hL : SecondPropositionOfRank) (hQ : ModelQStep) (hR : SecondRankHypothesis) (hML : ModelLStep) : SecondPropositionHypothesis :=
  fun D HW F Cm CA CB CK hA =>
    hL D HW (hQ D HW F Cm CA CB CK hA) (hR D HW F Cm CA CB CK hA (hML D HW F Cm CA CB CK hA))

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.NormOfVOne
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.T2SpaceLatticeVOfGoodSituation
noncomputable section

namespace Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.tableLineDegreeTwo Formalism.MainNotions.LocalSituation TensorProduct

def PGen (S : Sit) : Set S.G :=
  {g | S.W.resΓ g ∈ Subgroup.closure (insert S.W.gamK (S.W.DelF : Set S.W.Gam))}

variable {l : ℕ} [Fact l.Prime]

instance contAddLL (LL : FinExt l) : ContinuousAdd ↥LL.1 :=
  ⟨continuous_induced_rng.2 ((continuous_subtype_val.comp continuous_fst).add
    (continuous_subtype_val.comp continuous_snd))⟩

end Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators
end
end

noncomputable section

namespace Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.tableLineDegreeTwo Formalism.MainNotions.LocalSituation Topology Filter

variable {l : ℕ} [hl : Fact l.Prime]

theorem zetaQ_pow (P : LocPrime l) (j k : ℕ) : P.ζQ (j + k) ^ (l ^ k) = P.ζQ j := by
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, pow_succ', pow_mul, P.ζQ_succ, ih]

theorem chiQ_norm (P : LocPrime l) (h : GQ l) : ‖(P.χQ h : ℚ_[l])‖ = 1 := by
  have hroot : P.ζQ 1 ^ l = 1 := by
    have h0 := zetaQ_pow P 0 1
    rwa [zero_add, P.ζQ_zero, pow_one] at h0
  have hle : ∀ g : GQ l, ‖(P.χQ g : ℚ_[l])‖ ≤ 1 := by
    intro g
    obtain ⟨a, ha, -⟩ := P.χQ_cyc g 1 (P.ζQ 1) (by rwa [pow_one])
    have hA : ‖(a : ℚ_[l])‖ ≤ 1 := by
      have h2 : ‖((a : ℤ) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-((0 : ℕ) : ℤ)) := by
        first
          | exact (Padic.norm_int_le_pow_iff_dvd (a : ℤ) 0).2 (by simp)
          | exact (padicNormE.norm_int_le_pow_iff_dvd (a : ℤ) 0).2 (by simp)
      simpa using h2
    have hl1 : (l : ℝ) ^ (-((1 : ℕ) : ℤ)) ≤ 1 := by
      have h3 : (1 : ℝ) ≤ l := by exact_mod_cast hl.out.one_lt.le
      simp only [Nat.cast_one, zpow_neg, zpow_one]
      first
        | exact inv_le_one_of_one_le₀ h3
        | exact inv_le_one h3
    calc ‖(P.χQ g : ℚ_[l])‖ = ‖((P.χQ g : ℚ_[l]) - a) + a‖ := by rw [sub_add_cancel]
      _ ≤ max ‖(P.χQ g : ℚ_[l]) - a‖ ‖(a : ℚ_[l])‖ := by
        first
          | exact Padic.nonarchimedean _ _
          | exact padicNormE.nonarchimedean _ _
          | exact IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := max_le (ha.trans hl1) hA
  have h1 := hle h
  have h2 := hle h⁻¹
  have hmul : ‖(P.χQ h : ℚ_[l])‖ * ‖(P.χQ h⁻¹ : ℚ_[l])‖ = 1 := by
    rw [← norm_mul, ← Units.val_mul, ← map_mul]
    simp
  exact le_antisymm h1 (by nlinarith [norm_nonneg (P.χQ h : ℚ_[l]), norm_nonneg (P.χQ h⁻¹ : ℚ_[l])])

end Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators
end
end
