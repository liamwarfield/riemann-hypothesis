module

public import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
noncomputable section

namespace Formalism.MainNotions.ElementDenominator

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

section PartI

variable {l : ℕ} [Fact l.Prime]

def colLe (P : LocPrime l) (K LL : FinExt l) {T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)}
    (F : LatHom T₁.L T₂.L) (b : ℝ) : Prop :=
  ∃ m k : ℕ, F.col (P.PD K) = m ∧ lenOl (P.PD K) (O := ↥(OL LL)) = k ∧ (m : ℝ) ≤ b * k

def intersection_update_fsHerm_neg_one (K : FinExt l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL] (τ : ↥K.1 →ₐ[ℚ_[l]] LL) :
    ↥(K0 K) →ₐ[ℚ_[l]] LL :=
  τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)

def deep (up : Bool) (b S : ℕ) : Set ℤ :=
  if up then Set.Icc (b : ℤ) (b + S) else Set.Icc (-((b : ℤ) + S)) (-(b : ℤ))

def boundA (C : ℝ) (l n e r S η m h : ℕ) : ℝ :=
  C * ((n : ℝ) * e + 1) * r *
      ((e : ℝ) * h / l + (e : ℝ) * S + (e : ℝ) * Real.logb l h + 1 + η) +
    (n : ℝ) * e * (e + 1) * m * (C * ((h : ℝ) + 1))

def thmA (P : LocPrime l) (K LL : FinExt l) (C : ℝ) : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (r S η m h : ℕ)
    (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ),
    IsCrys (P.PD K) T₁.ρ → IsCrys (P.PD K) T₂.ρ → F.Onto →
    finrank ↥LL.1 T₂.V = r →
    (∀ τ, JumpsInV (P.PD K) T₁.ρ τ (deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η)) →
    (∀ τ, η < b τ) →
    (∀ τ, ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV (P.PD K) T₂.ρ τ a ≤ m) →
    (∀ τ, JumpsInV (P.PD K) T₁.ρ τ (Set.Icc (-(h : ℤ)) h)) →
    (finrank ↥(K0 K) ↥K.1 = 2 ∨ ∀ τ τ', intersection_update_fsHerm_neg_one K τ = intersection_update_fsHerm_neg_one K τ' → up τ = up τ') →
    colLe P K LL F
      (boundA C l (finrank ℚ_[l] ↥(K0 K)) (finrank ↥(K0 K) ↥K.1) r S η m h)

end PartI

def TheoremBLocal (LT : LocTheory) (C : ℝ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → thmA (LT l) K LL C

def Conclusion1 (D : D7) (C : ℝ) : Prop := TheoremBLocal D.loc C

def H1fGeneratorBoundAll (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL →
    ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) [IsTopologicalAddGroup T.V],
      haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
      letI : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
      FiniteCohomologyGeneratorsBound ((LT l).PD K) T.L

def FontaineRegularity (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)),
    (FiniteDimensional ↥LL.1 ↥(Dcris ((LT l).PD K) T.ρ) ∧
      finrank ↥LL.1 ↥(Dcris ((LT l).PD K) T.ρ) ≤ finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 T.V) ∧
    ∀ τ, FiniteDimensional ↥LL.1 ↥(DdRE ((LT l).PD K) T.ρ τ) ∧
      finrank ↥LL.1 ↥(DdRE ((LT l).PD K) T.ρ τ) ≤ finrank ↥LL.1 T.V

def FontaineStrictExact (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l)
    (T₀ T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L),
    IsSESLat (Qp := ℚ_[l]) ι π → IsCrys ((LT l).PD K) T₁.ρ →
    IsCrys ((LT l).PD K) T₀.ρ ∧ IsCrys ((LT l).PD K) T₂.ρ ∧
    ∀ τ a, multV ((LT l).PD K) T₁.ρ τ a =
      multV ((LT l).PD K) T₀.ρ τ a + multV ((LT l).PD K) T₂.ρ τ a

def CrystallineRestrictionToExtension (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K K' : FinExt l) (hKK : K'.1 ≤ K.1) (hle : GK K ≤ GK K')
    (LL : FinExt l) (T : LocLat ↥(GK K') ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((LT l).PD K') T.ρ →
    IsCrys ((LT l).PD K) (Formalism.MainNotions.LiftingTheory.resLoc (Subgroup.inclusion hle)
      (continuous_subtype_val.subtype_mk _) T).ρ ∧
    ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ),
      multV ((LT l).PD K) (Formalism.MainNotions.LiftingTheory.resLoc (Subgroup.inclusion hle)
        (continuous_subtype_val.subtype_mk _) T).ρ τ a =
      multV ((LT l).PD K') T.ρ (τ.comp (IntermediateField.inclusion hKK)) a

section Herr

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def IsUnitGen (W : LocWach PD LL O v n) (e : W.DD W.one) : Prop :=
  W.N W.one = Submodule.span (LetA O n) {e} ∧ W.φD W.one e = e ∧ ∀ g, W.γD W.one g e = e

def coreHerrExt (W : LocWach PD LL O v n) : Prop :=
  ∀ (T Tp : LocLat G Qp LL O) (ι : LatHom T.L Tp.L) (π : LatHom Tp.L W.one.L),
    IsCrys PD T.ρ → IsCrys PD Tp.ρ →
    ∀ (c : G → T.V) (hc : c ∈ latticeCocycles T.L), Formalism.MainNotions.LiftingTheory.IsExtOf W ι π c →
    ∀ e : W.DD W.one, IsUnitGen W e →
    ∃ u : Oˣ, ∀ (x : W.DD Tp) (a : O), W.map π x = a • e →
      ∀ (y z : W.DD T) (h : (y, z) ∈ W.divisibleCocycles T),
        W.map ι y = W.φD Tp x - x → W.map ι z = W.γ Tp x - x →
        W.cl T ⟨(y, z), h⟩ = ((u : O) * a) •
          Formalism.MainNotions.DeltaInvariantLattices.res W.GKs T (Submodule.Quotient.mk (⟨c, hc⟩ : ↥(latticeCocycles T.L)) : LatticeCohomology T.L)

def coreHerrExtΔ (W : LocWach PD LL O v n) : Prop :=
  W.s = 1 → PD.p ≠ 2 →
  ∀ (T Tp : LocLat G Qp LL O) (ι : LatHom T.L Tp.L) (π : LatHom Tp.L W.one.L),
    IsCrys PD T.ρ → IsCrys PD Tp.ρ →
    ∀ (c : G → T.V) (hc : c ∈ latticeCocycles T.L), Formalism.MainNotions.LiftingTheory.IsExtOf W ι π c →
    ∀ e : W.DD W.one, IsUnitGen W e →
    ∃ u : Oˣ, ∀ (x : W.DD Tp) (a : O), (∀ δ ∈ W.DelF, W.γD Tp δ x = x) → W.map π x = a • e →
      ∀ (y z : W.DD T) (h : (y, z) ∈ W.wachCocyclesDelta T),
        W.map ι y = W.φD Tp x - x → W.map ι z = W.γD Tp W.gamK x - x →
        W.clK T ⟨(y, z), h⟩ = ((u : O) * a) •
          (Submodule.Quotient.mk (⟨c, hc⟩ : ↥(latticeCocycles T.L)) : LatticeCohomology T.L)

end Herr

def HerrClassNaturalExtension (LT : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l)) (HW : HWOf LT) (F : FonOf LT A HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    ((HW l).W K s LL h).ClNat ∧ Formalism.MainNotions.DeltaInvariantLattices.ClKNatG ((HW l).W K s LL h) ∧
      coreHerrExt ((HW l).W K s LL h) ∧ coreHerrExtΔ ((HW l).W K s LL h)

def adm1 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.DeltaInvariantLattices.deltaInvariantLatticeGlobal D HW F Cm

def adm2 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.prop2 D HW F

def adm2b (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.adm20 D HW F

def adm2c (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.adm17 D HW F

def HerrClassMapsLocal (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := HerrClassNaturalExtension D.loc D.locA HW F

def adm3 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.lem3 D HW F

def ArchimedeanSignatureMatching (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CA CB CK : ℝ) : Prop := Formalism.MainNotions.LiftingTheory.LiftTheoremAllCases D HW F CA CB CK

def adm5 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.ConclusionW D HW F

def adm6 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.ConclusionL D HW F

def adm7 (D : D7) : Prop := H1fGeneratorBoundAll D.loc

def adm8 (D : D7) : Prop := FontaineRegularity D.loc

def adm11 (D : D7) : Prop := FontaineStrictExact D.loc

def adm12 (D : D7) : Prop := CrystallineRestrictionToExtension D.loc

def Adm1 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ) : Prop :=
  adm1 D HW F Cm ∧ adm2 D HW F ∧ adm2b D HW F ∧ adm2c D HW F ∧ HerrClassMapsLocal D HW F ∧ adm3 D HW F ∧ ArchimedeanSignatureMatching D HW F CA CB CK ∧ adm5 D HW F ∧ adm6 D HW F ∧
    adm7 D ∧ adm8 D ∧ adm11 D ∧ adm12 D

def IntegralityFromMetric (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK C : ℝ) : Prop := Adm1 D HW F Cm CA CB CK → Conclusion1 D C

def qlExt (l : ℕ) [Fact l.Prime] : FinExt l := ⟨⊥, inferInstance⟩

def orbLen {G LL : Type} [Group G] [Field LL] (I : Subgroup G) (Fr : G) (χ : I →* LLˣ) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ ∀ g h : I, (h : G) = (Fr ^ k)⁻¹ * g * Fr ^ k → χ h = χ g}

def rPrime {G LL : Type} [Group G] [Field LL] (I : Subgroup G) (Fr : G) (Sig : Finset (I →* LLˣ)) :
    ℕ :=
  (Sig ×ˢ Sig).sup fun p => orbLen I Fr (p.1 * p.2⁻¹)

section PartII

variable {l : ℕ} [Fact l.Prime]

def thmT {K₀' K' B BdR : Type} [Field K₀'] [Field K'] [Algebra ℚ_[l] K₀'] [Algebra ℚ_[l] K']
    [Algebra K₀' K'] [IsScalarTower ℚ_[l] K₀' K'] [CommRing B] [CommRing BdR] [Algebra ℚ_[l] B]
    [Algebra ↥(K0 (qlExt l)) B] [IsScalarTower ℚ_[l] ↥(K0 (qlExt l)) B] [Algebra K₀' B]
    [IsScalarTower ℚ_[l] K₀' B] [Algebra ℚ_[l] BdR] [Algebra ↥(K0 (qlExt l)) BdR]
    [Algebra ↥(qlExt l).1 BdR] [IsScalarTower ℚ_[l] ↥(qlExt l).1 BdR]
    [IsScalarTower ↥(K0 (qlExt l)) ↥(qlExt l).1 BdR] [IsScalarTower ℚ_[l] ↥(K0 (qlExt l)) BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower ℚ_[l] K' BdR] [IsScalarTower K₀' K' BdR]
    [IsScalarTower ℚ_[l] K₀' BdR]
    (PC : PotCrysData ↥(GK (qlExt l)) ℚ_[l] ↥(K0 (qlExt l)) ↥(qlExt l).1 K₀' K' B BdR)
    (LL : FinExt l) (C : ℕ) : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK (qlExt l)) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (N η H : ℕ)
    (U : Finset ℤ) (Sig : Finset (PC.Iner →* (↥LL.1)ˣ)) (Fr : ↥(GK (qlExt l))),
    PC.IsPotCrys T₁.ρ → PC.IsPotCrys T₂.ρ → F.Onto →
    PC.IsFrob Fr → FrobStable PC.Iner Fr Sig → 1 ∈ Sig → Sig.card ≤ N → 2 ≤ N →
    PC.InertiaThrough T₁.ρ Sig → PC.InertiaThrough T₂.ρ Sig →
    (∀ u ∈ U, -(η : ℤ) ≤ u ∧ u ≤ H) → (0 : ℤ) ∈ U → U.card ≤ N + 1 → 1 ≤ η → η < H →
    (∀ τ, JumpsInV PC.PD T₁.ρ τ (U : Set ℤ)) → (∀ τ, JumpsInV PC.PD T₂.ρ τ (U : Set ℤ)) →
    C * (H * N ^ 2 + N ^ 3) < l →
    4 * rPrime PC.Iner Fr Sig ≤ N ^ 2 ∧
      F.LiftF PC.PD (C * (N * rPrime PC.Iner Fr Sig + η * (N + rPrime PC.Iner Fr Sig)))

end PartII

def CorollaryALocal (LT : LocTheory) (C : ℕ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K' : FinExt l) (h : (qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal)
    (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (qlExt l))) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((LT l).PD (qlExt l)).actB g (algebraMap ↥(K0 K') (LT l).R.B c) =
        algebraMap ↥(K0 K') (LT l).R.B c')
    (LL : FinExt l), thmT (pc (LT l) h hN hF hS) LL C

def Conclusion2 (D : D7) (C : ℕ) : Prop := CorollaryALocal D.loc C

def adm10 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.adm20 D HW F

def adm13 (D : D7) : Prop := Formalism.MainNotions.LocalSituation.Conclusion5 D

def ArtinSchreierWittOnto : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (x : WCb l), ∃ y : WCb l, frobW l y - y = x

def Adm2 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := adm10 D HW F ∧ adm13 D ∧ adm8 D ∧ adm11 D ∧ adm12 D ∧ ArtinSchreierWittOnto

def HodgeTateFromSandwich (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℕ) : Prop := Adm2 D HW F → Conclusion2 D C

end Formalism.MainNotions.ElementDenominator
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
noncomputable section

namespace Formalism.MainNotions.IdempotentChoiceDepthZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

section Obj51

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))

def IsOrthogonalIdempotentDecomposition (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i) (S : IdempotentChoiceData N i) : Prop :=

  (InR N i r S.eB ∧ InR N i r S.e1 ∧ S.eB * S.eB = S.eB ∧ S.e1 * S.e1 = S.e1 ∧
    S.eB * S.e1 = 0 ∧ S.e1 * S.eB = 0 ∧
    (∀ x, ((S.eB x).map (toK N i)).rank = R.t) ∧ (∀ x, ((S.e1 x).map (toK N i)).rank = 1)) ∧

  (∀ g u, S.e ((mapM (toK N i) (rO N i r π) g).mulVec u) =
      ((mapM (toK N i) (rhoO N i ρ π) g).mulVec (S.e u).1,
        fun c : Fin R.t => toK N i ((chiU N i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i) * (S.e u).2 c)) ∧
  (∀ a, InR' N r S a → ∀ u, S.e (((a S.π').map (toK N i)).mulVec u) =
      (((S.ψρ a).map (toK N i)).mulVec (S.e u).1,
        fun c : Fin R.t => toK N i (S.ψχ c a) * (S.e u).2 c)) ∧
  (∀ A : Matrix (Fin R.r) (Fin R.r) (N.O i), ∃ a, InR' N r S a ∧ S.ψρ a = A) ∧

  (∃ w ∈ placesOver H.E (N.l i), S.g0 ∈ Ine (F := H.E) (N.plOm.1 w)) ∧
  orderOf (PadicInt.toZMod ((cycZ (F := H.E) (Ω := N.Om) (N.l i) S.g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i])) =
    N.l i - 1 ∧

  (InR N i r S.X0 ∧ S.eB * S.X0 = S.X0 ∧ S.X0 * S.eB = S.X0 ∧
    ∀ u, S.e (((S.X0 π).map (toK N i)).mulVec u) =
      (0, fun c : Fin R.t => toK N i ((chiU N i ((c : ℕ) + 1) S.g0 : (N.O i)ˣ) : N.O i) * (S.e u).2 c)) ∧

  ((∀ f ∈ N.T i, (fun x' => f (S.p x')) ∈ S.T') ∧ (∀ c ∈ Finset.Icc 1 R.t, S.rr c ∈ S.T') ∧
    S.T' = Algebra.adjoin (N.O i) ((fun f : N.X i → N.O i => fun x' => f (S.p x')) '' (N.T i : Set _) ∪
      (fun c => S.rr c) '' (Finset.Icc 1 R.t : Set ℕ)) ∧
    (∃ b : Fin R.t.factorial → S.X' → N.O i, (∀ k, b k ∈ S.T') ∧
      ∀ f ∈ S.T', ∃! cf : Fin R.t.factorial → N.T i,
        f = ∑ k, ((fun x' => (cf k : N.X i → N.O i) (S.p x')) : S.X' → N.O i) * b k) ∧
    (∀ x, Nat.card {x' // S.p x' = x} = R.t.factorial)) ∧

  (∀ x', ∏ c ∈ Finset.Icc 1 R.t, (Polynomial.X - Polynomial.C (S.rr c x')) =
    Matrix.det ((Polynomial.X : Polynomial (N.O i)) • (S.eB (S.p x')).map (Polynomial.C (R := N.O i)) -
      (S.X0 (S.p x')).map (Polynomial.C (R := N.O i)) + 1 -
      (S.eB (S.p x')).map (Polynomial.C (R := N.O i)))) ∧

  (S.p S.π' = π ∧ ∀ c ∈ Finset.Icc 1 R.t,
    S.rr c S.π' = ((chiU N i c S.g0 : (N.O i)ˣ) : N.O i)) ∧

  ((∀ x', ((Eel N S x').map (toK N i)).rank = 1) ∧
    (∀ x', Eel N S x' * Eel N S x' = del51 N S x' • Eel N S x') ∧
    (∀ u, S.e (((Eel N S S.π').map (toK N i)).mulVec u) =
      (0, fun c : Fin R.t => if (c : ℕ) = 0 then toK N i (del51 N S S.π') * (S.e u).2 c else 0)) ∧
    IsUnit (del51 N S S.π')) ∧

  CharpolyCoeffsInSubalgebra N i S.T' (fun x' => rO N i r (S.p x'))

end Obj51

end Formalism.MainNotions.IdempotentChoiceDepthZero
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
noncomputable section

open Classical

namespace Formalism.MainNotions.TruncatedSeriesCountingBounds

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def JumpsAt {PD : PeriodData G Qp K₀ K B BdR} (W : LocWach PD LL O v n)
    (T : LocLat G Qp LL O) (i : ZMod n) (Sset : Set ℤ) : Prop :=
  ∀ τ, Formalism.MainNotions.LiftingTheory.Over W τ i → JumpsInV PD T.ρ τ Sset

def lowCount {PD : PeriodData G Qp K₀ K B BdR} [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n)
    (T : LocLat G Qp LL O) (i : ZMod n) (η : ℕ) : ℤ :=
  ∑ τ ∈ Finset.univ.filter (fun τ => Formalism.MainNotions.LiftingTheory.Over W τ i),
    ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV PD T.ρ τ a

def ColLeR (PD : PeriodData G Qp K₀ K B BdR) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (x : ℝ) : Prop :=
  ∃ mm k : ℕ, F.col PD = mm ∧ lenOl PD (O := O) = k ∧ (mm : ℝ) ≤ x * k

def Thick (b η : ℕ) (size : ZMod n → ℕ) (i : ZMod n) : Prop := b ≤ size i ∧ size i ≤ b + η

def HidaSetting (PD : PeriodData G Qp K₀ K B BdR) [Fintype (K →ₐ[Qp] LL)]
    (W : LocWach PD LL O v n) (T₁ T₂ : LocLat G Qp LL O)
    (F : LatHom T₁.L T₂.L) (b w S η m : ℕ) (up : ZMod n → Bool) (size Mi hi : ZMod n → ℕ) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W ∧ Formalism.MainNotions.LiftingTheory.Sur W F ∧
  (∀ i, η < size i) ∧
  (∀ i, JumpsAt W T₁ i (if up i then
      Set.Icc (size i : ℤ) ((size i : ℤ) + S) ∪ Set.Icc (-(η : ℤ)) η
    else Set.Icc (-(size i : ℤ) - S) (-(size i : ℤ)) ∪ Set.Icc (-(η : ℤ)) η)) ∧
  (∀ i, lowCount W T₂ i η ≤ m) ∧
  (∀ i, ¬ Thick b η size i → size i ≤ w) ∧
  Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi hi

def eLift {PD : PeriodData G Qp K₀ K B BdR} (W : LocWach PD LL O v n) (T₁ : LocLat G Qp LL O)
    (Mi hi : ZMod n → ℕ) : ℕ :=
  Formalism.MainNotions.LiftingTheory.ePA PD.p (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi)
    (Formalism.MainNotions.LiftingTheory.jumpSet W T₁ (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Mmax n hi))

def hB (b w S η : ℕ) (size : ZMod n → ℕ) : ℕ :=
  if ∃ i, Thick b η size i then b + η + S else w + S

def Band (l b S η : ℕ) (size : ZMod n → ℕ) (lg C : ℝ) : Prop :=
  ∃ i, ¬ Thick b η size i ∧ (Thick b η size (i + 1) ∨ Thick b η size (i - 1)) ∧
    |(l : ℝ) * size i - b| ≤ C * ((l : ℝ) * η + (l : ℝ) * S + (b : ℝ) / l + size i + (l : ℝ) * lg)

def ThmB (PD : PeriodData G Qp K₀ K B BdR) [Fintype (K →ₐ[Qp] LL)]
    (W : LocWach PD LL O v n) (C : ℝ) : Prop :=
  11 ≤ PD.p →
  ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b w S η m : ℕ) (up : ZMod n → Bool)
    (size Mi hi : ZMod n → ℕ),
    HidaSetting PD W T₁ T₂ F b w S η m up size Mi hi →
    20 * w ≤ b → 20 * η ≤ b → 20 * S ≤ b →
    (∃ i, ¬ Thick b η size i) →
    let l : ℕ := PD.p
    let h : ℕ := hB b w S η size
    let lg : ℝ := Real.logb l (2 * (h : ℝ))
    let band : ℝ := if Band l b S η size lg C then 1 else 0
    let r : ℝ := finrank LL T₂.V
    let e' : ℝ := eLift W T₁ Mi hi
    ((∀ i, up (i + 1) ≠ up i ∧
        ¬ (Thick b η size i ∧ Thick b η size (i + 1) ∧ Thick b η size (i + 2))) →
      ColLeR PD F (C * ((n : ℝ) + 1) * r * ((h : ℝ) / (l : ℝ) ^ 2 + ((w : ℝ) + η) / l + S + 1 + lg +
        η * band) + C * n * m * e')) ∧
    (∀ R : ℕ, 1 ≤ R → (∀ i, up i = up 0) → (∀ i, ¬ ∀ t : ℕ, t < R → Thick b η size (i + t)) →
      ColLeR PD F (C * ((n : ℝ) + 1) * r * ((h : ℝ) / (l : ℝ) ^ 2 + ((w : ℝ) + η) / l +
        (R : ℝ) ^ 2 * (S + 1 + lg) + η * band) + C * n * m * (R : ℝ) ^ 2 * e'))

def Clusters (j : ℕ) (thick : ZMod n → Prop) : Prop :=
  ∀ t, thick t →
    (∀ k : ℕ, 1 ≤ k → k ≤ j → ¬ thick (t - k)) ∨
    (∃ d : ℕ, 1 ≤ d ∧ d ≤ j ∧ thick (t - d) ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ d + j → k ≠ d → ¬ thick (t - k))

end Core

def crisMap {Qp : Type} [Field Qp] (B : Type) [CommRing B] [Algebra Qp B] {LL : Type} [Field LL]
    [Algebra Qp LL] {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] (f : V →ₗ[LL] V') :
    TensorProduct Qp V B →ₗ[LL] TensorProduct Qp V' B :=
  TensorProduct.AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B)

section Lit

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {Bc BdR : Type} [CommRing Bc] [CommRing BdR] [Algebra Qp Bc] [Algebra K₀ Bc] [IsScalarTower Qp K₀ Bc]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

def DcrisExactStrict [TopologicalSpace G] (PD : PeriodData G Qp K₀ K Bc BdR) (LL : Type) [Field LL]
    [Algebra Qp LL] [TopologicalSpace LL] : Prop :=
  Function.Bijective (algebraMap K₀ K) →
  ∀ (V₀ V₁ V₂ : Type) [AddCommGroup V₀] [Module LL V₀] [Module Qp V₀] [IsScalarTower Qp LL V₀]
    [FiniteDimensional LL V₀] [AddCommGroup V₁] [Module LL V₁] [Module Qp V₁]
    [IsScalarTower Qp LL V₁] [FiniteDimensional LL V₁] [AddCommGroup V₂] [Module LL V₂]
    [Module Qp V₂] [IsScalarTower Qp LL V₂] [FiniteDimensional LL V₂]
    (ρ₀ : Representation LL G V₀) (ρ₁ : Representation LL G V₁) (ρ₂ : Representation LL G V₂)
    (ι : V₀ →ₗ[LL] V₁) (π : V₁ →ₗ[LL] V₂)
    [TopologicalSpace V₀] [IsModuleTopology LL V₀] [TopologicalSpace V₁] [IsModuleTopology LL V₁]
    [TopologicalSpace V₂] [IsModuleTopology LL V₂],
    (∀ x, Continuous fun g => ρ₀ g x) → (∀ x, Continuous fun g => ρ₁ g x) →
    (∀ x, Continuous fun g => ρ₂ g x) →
    (∀ g x, ι (ρ₀ g x) = ρ₁ g (ι x)) → (∀ g x, π (ρ₁ g x) = ρ₂ g (π x)) →
    Function.Injective ι → Function.Surjective π → LinearMap.range ι = LinearMap.ker π →
    IsCrys PD ρ₀ → IsCrys PD ρ₁ → IsCrys PD ρ₂ →
    (∀ y ∈ Dcris PD ρ₀, crisMap Bc ι y = 0 → y = 0) ∧
    (∀ x ∈ Dcris PD ρ₁, crisMap Bc π x = 0 → ∃ y ∈ Dcris PD ρ₀, crisMap Bc ι y = x) ∧
    (Dcris PD ρ₁).map (crisMap Bc π) = Dcris PD ρ₂ ∧
    (∀ a : ℤ, (FilCris PD ρ₁ a).map (crisMap Bc π) = FilCris PD ρ₂ a) ∧
    (∀ (a : ℤ), ∀ y ∈ Dcris PD ρ₀, crisMap Bc ι y ∈ FilCris PD ρ₁ a → y ∈ FilCris PD ρ₀ a)

def DdREqDcris [TopologicalSpace G] (PD : PeriodData G Qp K₀ K Bc BdR) (LL : Type) [Field LL]
    [Algebra Qp LL] [TopologicalSpace LL] : Prop :=
  Function.Bijective (algebraMap K₀ K) →
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V) [TopologicalSpace V] [IsModuleTopology LL V],
    (∀ x, Continuous fun g => ρ g x) → IsCrys PD ρ →
    (Dcris PD ρ).map (ιV PD (LL := LL) (V := V)) = DdR PD ρ ∧
    ∀ τ : K →ₐ[Qp] LL, FiniteDimensional LL ↥(DdRE PD ρ τ) ∧
      finrank LL ↥(DdRE PD ρ τ) = finrank LL V ∧
      ∀ a : ℤ, FildR PD ρ τ a =
        (FilCris PD ρ a ⊓ DcrisL PD ρ (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))).map
          (ιV PD (LL := LL) (V := V))

end Lit

section Theory

def TheoremBLocal (LT : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l)) (HW : HWOf LT) (F : FonOf LT A HW) (C : ℝ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL), K.1 ≤ MaximalUnramifiedExtension l →
    ∀ [NeZero (Module.finrank ℚ_[l] ↥(K0 K))] [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)],
      ThmB ((LT l).PD K) ((HW l).W K 1 LL hG) C

def BlochKatoDimensionLocal (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)],
    BlochKatoDim ((LT l).PD K) ↥LL.1

def DcrisExactStrictLocal (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), DcrisExactStrict ((LT l).PD K) ↥LL.1

def DdREqDcrisAll (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), DdREqDcris ((LT l).PD K) ↥LL.1

end Theory

def Conclusion1 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := TheoremBLocal D.loc D.locA HW F C

def adm8 (D : D7) : Prop := BlochKatoDimensionLocal D.loc

def adm9 (D : D7) : Prop := DcrisExactStrictLocal D.loc

def adm15 (D : D7) : Prop := DdREqDcrisAll D.loc

end Formalism.MainNotions.TruncatedSeriesCountingBounds
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingBounds
noncomputable section

namespace Formalism.MainNotions.CrystallineLiftingBounds

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

def adm1 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.wachLatticeFreeLocal D.loc HW D.locA F

def adm2 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p2L D.loc HW D.locA F

def adm3 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p3L D.loc HW D.locA F Cm

def ArchimedeanSignatureMatching (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p4L D.loc HW D.locA F Cm

def adm5 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p5L D.loc HW D.locA F

def adm6 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p6L D.loc HW D.locA F

def adm7 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p7L D.loc HW D.locA F

def adm8 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p8L D.loc HW D.locA F

def adm9 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p9L D.loc HW D.locA F

def adm10 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.wachCharacterisationLocal D.loc HW D.locA F

def adm11 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.gammaSemisimpleLocal D.loc HW D.locA F

def adm12 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p2aL D.loc HW D.locA F

def adm13 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p2bL D.loc HW D.locA F

def adm14 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p2cL D.loc HW D.locA F

def adm15 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p2dL D.loc HW D.locA F

def adm16 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.wachLengthLocal D.loc HW D.locA F

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem invariant_cocycle_le_gamma_cocycle (W : LocWach PD LL O v n) (h1 : W.s = 1) (h2 : PD.p ≠ 2) (T : LocLat G Qp LL O) :
    W.wachCocyclesDelta T ≤ W.divisibleCocycles T := by
  have e := W.gamK_eq_one h1 h2
  intro x hx
  unfold Formalism.BasicNotions.LocWach.wachCocyclesDelta Formalism.BasicNotions.herrZ1Δ at hx
  have hx1 := (Submodule.mem_inf.mp hx).1
  rw [e] at hx1
  exact hx1

def coreResK (W : LocWach PD LL O v n) : Prop :=
  ∀ (h1 : W.s = 1) (h2 : PD.p ≠ 2) (T : LocLat G Qp LL O) (w : ↥(W.wachCocyclesDelta T)),
    Formalism.MainNotions.DeltaInvariantLattices.res W.GKs T (W.clK T w) =
      W.cl T ⟨(w : W.DD T × W.DD T), invariant_cocycle_le_gamma_cocycle W h1 h2 T w.2⟩


variable (PD LL O) in
def coreJumps : Prop :=
  ∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L),
    IsSESLat (Qp := Qp) ι π → IsCrys PD T₀.ρ → IsCrys PD T₁.ρ → IsCrys PD T₂.ρ →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ),
      IsJumpV PD T₁.ρ τ a ↔ IsJumpV PD T₀.ρ τ a ∨ IsJumpV PD T₂.ρ τ a

end Local

def adm17 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    Formalism.MainNotions.LiftingTheory.coreExt ((HW l).W K s LL h)

def adm18 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    Formalism.MainNotions.LiftingTheory.coreExtΔ ((HW l).W K s LL h)

def adm19 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    Formalism.MainNotions.LiftingTheory.coreDss ((HW l).W K s LL h)

def adm20 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K K' : FinExt l) (_hKK : K'.1 ≤ K.1) (hle : GK K ≤ GK K')
    (LL : FinExt l),
    Formalism.MainNotions.LiftingTheory.coreCor ((D.loc l).PD K) ((D.loc l).PD K') ↥LL.1 ↥(OL LL) (Subgroup.inclusion hle)
      (continuous_subtype_val.subtype_mk _)
      (Module.finrank ℚ_[l] ↥K.1 / Module.finrank ℚ_[l] ↥K'.1)

def adm21 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    ((HW l).W K s LL h).ClNat ∧ (s = 1 → l ≠ 2 → ((HW l).W K s LL h).ClKNat)

theorem resK_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL) : coreResK ((HW l).W K s LL h) := by
  intro h1 h2 T w
  exact ((F l).E K s LL h).tie.clK_res (((HW l).W K s LL h).gamK_eq_one h1 h2) T w _ rfl

def adm22 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), FontaineLe ((D.loc l).PD K) ↥LL.1

def adm23 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), coreJumps ((D.loc l).PD K) ↥LL.1 ↥(OL LL)

def admitted (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  adm1 D HW F ∧ adm2 D HW F ∧ adm3 D HW F Cm ∧ ArchimedeanSignatureMatching D HW F Cm ∧ adm5 D HW F ∧ adm6 D HW F ∧ adm7 D HW F ∧ adm8 D HW F ∧
    adm9 D HW F ∧ adm10 D HW F ∧ adm11 D HW F ∧ adm12 D HW F ∧ adm13 D HW F ∧ adm14 D HW F ∧ adm15 D HW F ∧ adm16 D HW F ∧
    adm17 D HW F ∧ adm18 D HW F ∧ adm19 D HW F ∧ adm20 D HW F ∧ adm21 D HW F ∧ adm22 D HW F ∧ adm23 D HW F

def Conclusion1 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.WachKillsQuotients D HW F ∧ Formalism.MainNotions.LiftingTheory.WachKillsCaseB D HW F ∧ Formalism.MainNotions.LiftingTheory.WachKillsCaseA D HW F

def Conclusion2 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CA CB CK : ℝ) : Prop := Formalism.MainNotions.LiftingTheory.LiftTheoremAllCases D HW F CA CB CK

def aux₃ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CA CB CK : ℝ) : Prop := Conclusion1 D HW F ∧ Conclusion2 D HW F CA CB CK

def Stmt (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ) : Prop := admitted D HW F Cm → aux₃ D HW F CA CB CK

end Formalism.MainNotions.CrystallineLiftingBounds
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LatticeVariant
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

namespace Formalism.MainNotions.LatticeVariant

open Formalism.MainNotions.IntegralHeckeForms (HkIdx hkO TwOK T3 IsLatIn sIdx specU)
open Formalism.MainNotions.BlochKatoReduction.Gen (psiAt nval SetHyp PsiOk partA partAT partC partD)

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

abbrev LamO (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (Q : Finset (PlE D.host)) (M : ℕ) : Type :=
  AddMonoidAlgebra (X.O i) (DelQM D.host (X.l i) Q M)

def ConjCl (Q : Finset (PlE D.host)) : Prop := ∀ P ∈ Q, ∀ P', IsConjPl D.host P P' → P' ∈ Q

def DelOn (i : X.Tw) (Q : Finset (PlE D.host)) (M : ℕ) : Prop :=
  ∀ (P : PlE D.host) (hP : P ∈ Q) (A' : ValuationSubring N.Om), IsPlaceOver A' P →
    ∃ σ ∈ Ine (F := D.host.E) A', Multiplicative.toAdd (Y.delU i Q M σ) ⟨P, hP⟩ = 1

variable {Y}

variable (Y)

variable (bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X)






end Formalism.MainNotions.LatticeVariant

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.AutomorphicSideWildInertia
noncomputable section

namespace Formalism.MainNotions.AutomorphicSideWildInertia

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

def ResidualIrreducibleGood (D : D7) : Prop := ResidualIrreducibleRankR D


end Formalism.MainNotions.AutomorphicSideWildInertia
end
end
