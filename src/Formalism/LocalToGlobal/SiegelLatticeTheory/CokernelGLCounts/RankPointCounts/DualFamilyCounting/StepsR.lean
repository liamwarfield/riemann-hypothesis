module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsOrthGen
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsSubDivMemSP

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.StepsR
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section DefsR

variable (D : Formalism.BasicNotions.D7)

def UPair {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    Submodule D.host.E (VS D).V :=
  Submodule.span D.host.E (Set.range F0.fvec ∪ Set.range F'.fl.fvec)

def UUS {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    Submodule (𝓞 D.host.E) (VS D).V :=
  XS D F0 ⊔ Submodule.span (𝓞 D.host.E) {F0.z} ⊔ XS D F'.fl ⊔ Submodule.span (𝓞 D.host.E) {F'.fl.z}

def MMg {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    Submodule (𝓞 D.host.E) (VS D).V :=
  Submodule.span (𝓞 D.host.E)
    (Set.range F0.fvec ∪ Set.range fun b => ((gS D : D.host.E))⁻¹ • (F'.fl.fvec b - F0.fvec b))

def MMof {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    Submodule (𝓞 D.host.E) (VS D).V :=
  ⨅ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E),
    haveI := P.isPrime
    if ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal then Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (MMg D F0 F')
    else Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UUS D F0 F')

def cOne (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K] : ℝ :=
  if hc : ∃ c : ℝ, 0 < c ∧ MassConst K F 1 c then hc.choose else 1

def cMass (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    (j : ℕ) : ℝ :=
  cOne K F * ∏ i ∈ Finset.Icc 2 j, Formalism.HermitianLatticesTheory.massRatioRightSide K i

def IsGlueReps {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V)
    (M : Submodule (𝓞 K) V) (s : Finset (Submodule (𝓞 K) V)) : Prop :=
  (∀ Λ ∈ s, Λ ∈ GlueSet h U M) ∧
  (∀ Λ ∈ GlueSet h U M, ∃! Λ₁, Λ₁ ∈ s ∧ ∃ g ∈ isomFix h U, Formalism.HermitianLatticesTheory.gmap g Λ₁ = Λ) ∧
  (∀ Λ ∈ s, (stabFix h U Λ).Finite)

def cExpl {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : ℝ :=
  cMass D.host.E D.host.F (D.R.k - 1) *
    |(NumberField.discr D.host.F : ℝ)| ^ (-((2 * D.R.rS * (D.R.rS + 1) * (D.R.k - 1) : ℕ) : ℤ)) *
    (∏ i ∈ Finset.Icc D.R.k D.R.r, lValEtaF D.host.E D.host.F i) / Formalism.MainNotions.S.Cnt.massRows D F0 what₂

end DefsR

def HostDict : Prop :=
  ∀ D : Formalism.BasicNotions.D7, Formalism.HermitianLatticesTheory.IsCMUnram D.host.E ∧ IsFixF D.host.E D.host.F ∧ Nondeg (VS D).hT

def RatPair : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ Z : MatZ D, Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        ∃ F' : LFlag (D.sp.Y 0) D.R.rS (Tn u'), F'.zt = F'.fl.z ∧ ZhatL (lf D F0) F' = Z

def PerpDef : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (Z : MatZ D) (F' : LFlag (D.sp.Y 0) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        IsCompl (UPair D F0 F') (orthK (VS D).hT (UPair D F0 F')) ∧
        PosDefOn (VS D).hT (orthK (VS D).hT (UPair D F0 F')) ∧
        finrank D.host.E (UPair D F0 F') = D.R.m ∧
        finrank D.host.E (orthK (VS D).hT (UPair D F0 F')) = D.R.k - 1

def MMChar : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (Z : MatZ D) (F' : LFlag (D.sp.Y 0) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        IsLatIn (UPair D F0 F') (MMof D F0 F') ∧
        ∀ Λ : Submodule (𝓞 D.host.E) (VS D).V,
          (IsRowLat D F0 Λ ∧ F' ∈ EZ (Tn u') F0 Λ Z) ↔ Λ ∈ GlueSet (VS D).hT (UPair D F0 F') (MMof D F0 F')

def RowsGroupoid : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (Z : MatZ D) (F' : LFlag (D.sp.Y 0) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        ∀ s : Finset (Submodule (𝓞 D.host.E) (VS D).V),
          IsGlueReps (VS D).hT (UPair D F0 F') (MMof D F0 F') s →
          nu (Tn u') F0 what₂ Z * Formalism.MainNotions.S.Cnt.massRows D F0 what₂ =
            ∑ Λ ∈ s, ((Nat.card (stabFix (VS D).hT (UPair D F0 F') Λ) : ℕ) : ℝ)⁻¹

def NormMM : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (Z : MatZ D) (F' : LFlag (D.sp.Y 0) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') →
        nM D.host.F (VS D).hT (UPair D F0 F') (MMof D F0 F') =
          |(NumberField.discr D.host.F : ℝ)| ^ (-((2 * D.R.rS * (D.R.rS + 1) : ℕ) : ℤ)) * sqrtAbsNormOfScaledGram (Tn u) (Tn u') Z

def RowsMass : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ →
        Formalism.MainNotions.S.Cnt.massRows D F0 what₂ =
          cMass D.host.E D.host.F D.R.k * ((D.mem u).A.T : ℝ) ^ (D.R.k * finrank ℚ D.host.F) *
            ∏' 𝔭 : {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal},
              (if (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ 𝔭.1 then
                1 - etaF D.host.E D.host.F 𝔭.1 ^ D.R.k * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(D.R.k : ℤ)) else 1)

end Formalism.L2.SG.Pf.Cnt
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SplitAtOf
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

def spanS {K V : Type} [Field K] [AddCommGroup V] [Module K V] (S : Subring K) {ι : Type}
    [Fintype ι] (b : ι → V) : AddSubgroup V where
  carrier := {v | ∃ c : ι → K, (∀ i, c i ∈ S) ∧ v = ∑ i, c i • b i}
  zero_mem' := ⟨0, fun _ => S.zero_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    exact ⟨c + d, fun i => S.add_mem (hc i) (hd i), by
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩
  neg_mem' := by
    rintro x ⟨c, hc, rfl⟩
    exact ⟨-c, fun i => S.neg_mem (hc i), by
      simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]⟩

section Abs

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

def SplitAt (S : Subring K) (π : K) (h : V →ₗ⋆[K] V →ₗ[K] K) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b : ι → V) (e : ι → ℕ) (i₀ : ι),
    (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
    (∀ i, e i₀ ≤ e i) → ∀ ξ ∈ Submodule.span K (Set.range b),
    IsUnitIn S (h ξ ξ * (π ^ e i₀)⁻¹) →
    ∃ c : ι → V, (∀ i j, i ≠ j → h (c i) (c j) = 0) ∧
      (∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹)) ∧ h (c i₀) (c i₀) = h ξ ξ ∧
      Submodule.span K (Set.range c) = Submodule.span K (Set.range b) ∧
      ∀ v, v ∈ spanS S c ↔ v ∈ spanS S b

def ExactAt (S : Subring K) (π : K) (h : V →ₗ⋆[K] V →ₗ[K] K) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b : ι → V) (e : ι → ℕ) (i₀ : ι),
    (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
    (∀ i, e i₀ ≤ e i) → ∀ ξ ∈ Submodule.span K (Set.range b),
    IsUnitIn S (h ξ ξ * (π ^ e i₀)⁻¹) → ∃ X ∈ spanS S b, h X X = h ξ ξ

def RebaseAt (S : Subring K) (π : K) (h : V →ₗ⋆[K] V →ₗ[K] K) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b : ι → V) (e : ι → ℕ) (i₀ : ι),
    (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
    (∀ i, e i₀ ≤ e i) → ∀ X ∈ spanS S b, IsUnitIn S (h X X * (π ^ e i₀)⁻¹) →
    ∃ c : ι → V, (∀ i j, i ≠ j → h (c i) (c j) = 0) ∧
      (∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹)) ∧ c i₀ = X ∧
      Submodule.span K (Set.range c) = Submodule.span K (Set.range b) ∧
      ∀ v, v ∈ spanS S c ↔ v ∈ spanS S b

theorem splitAt_of {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} (hE : ExactAt S π h)
    (hR : RebaseAt S π h) : SplitAt S π h := by
  intro ι _ _ b e i₀ horth hunit hmin ξ hξ hξu
  obtain ⟨X, hX, hXX⟩ := hE ι b e i₀ horth hunit hmin ξ hξ hξu
  have hXu : IsUnitIn S (h X X * (π ^ e i₀)⁻¹) := by rw [hXX]; exact hξu
  obtain ⟨c, hco, hcu, hc0, hsp, hmem⟩ := hR ι b e i₀ horth hunit hmin X hX hXu
  exact ⟨c, hco, hcu, by rw [hc0, hXX], hsp, hmem⟩

end Abs

def ExactVec : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → IsTotPosDef h →
    ∀ P : Ideal (𝓞 K), P.IsMaximal → ∀ π : K, IsUnif (locRing P) π → ExactAt (locRing P) π h

def Rebase : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : Subring K) (π : K)
    (h : V →ₗ⋆[K] V →ₗ[K] K), IsHermSemilocal S → IsUnif S π → h.IsSymm →
    (∀ x, h x x = 0 → x = 0) → RebaseAt S π h

def LocSpan : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ P : Ideal (𝓞 K), P.IsMaximal → ∀ (n : ℕ) (b : Fin n → V)
    (v : V), v ∈ Formalism.HermitianLatticesTheory.loc (K := K) P (Submodule.span (𝓞 K) (Set.range b)) ↔
      v ∈ spanS (locRing P) b

def UnifVal : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ P : Ideal (𝓞 K), P.IsMaximal →
    ∃ π : K, IsUnif (locRing P) π ∧ ∀ a : 𝓞 F, a ≠ 0 →
      IsUnitIn (locRing P)
        (algebraMap F K (a : F) * (π ^ vF (P.comap (algebraMap (𝓞 F) (𝓞 K))) a)⁻¹)

def JordSpan : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (L : Submodule (𝓞 K) V), Submodule.IsFullLattice K L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
    ∀ (n : ℕ) (b : Fin n → V), locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L →
      Submodule.span K (Set.range b) = ⊤

end Formalism.L2.SG.Pf.G3
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscOnto
open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.G5

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

def diagQ (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] {m : ℕ} (𝔭 : Ideal (𝓞 F)) (k : ℕ)
    (a : Fin m → 𝓞 F) : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  Matrix.diagonal fun i => Ideal.Quotient.mk (extP K 𝔭 ^ k) (algebraMap (𝓞 F) (𝓞 K) (a i))

def phiQ (K : Type) {F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
    [Algebra F K] [Fact (IsFixF K F)] {m : ℕ} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F)
    (Y : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  Y + Yᴴ + Yᴴ * diagQ K 𝔭 k a * Y

def kerSet (K : Type) {F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
    [Algebra F K] [Fact (IsFixF K F)] {m : ℕ} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) :
    Set (Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) :=
  {X | Xᴴ * diagQ K 𝔭 k a * X = diagQ K 𝔭 k a ∧ ∃ Y, X = 1 + Y * diagQ K 𝔭 k a}

def PhiCount : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (m : ℕ) (a : Fin m → 𝓞 F), (∀ i, a i ≠ 0) →
    ∀ k : ℕ, 1 ≤ k → ∀ T : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k), Tᴴ = T →
      (∀ i j, T i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) →
      (Nat.card {Y : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k) // phiQ K 𝔭 k a Y = T} : ℝ) =
        (Ideal.absNorm 𝔭 : ℝ) ^ (m ^ 2 * k) * alphaStd K 𝔭 (m - cJof 𝔭 a)

def KerCount : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (m : ℕ) (a : Fin m → 𝓞 F), (∀ i, a i ≠ 0) →
    ∀ k : ℕ, 2 * vJof 𝔭 a + 1 ≤ k → ∀ N : ℕ,
      (∀ T : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k), Tᴴ = T →
        (∀ i j, T i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) →
        Nat.card {Y : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k) // phiQ K 𝔭 k a Y = T} = N) →
      Nat.card (kerSet K 𝔭 k a) = N

def DiscOnto : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → IsTotPosDef h →
    ∀ L : Submodule (𝓞 K) V, Submodule.IsLattice K L → Formalism.HermitianLatticesTheory.IsIntegralLat h L →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h ⊤ L 𝔭 b a →
    ∀ k : ℕ, 2 * vJof 𝔭 a + 1 ≤ k →
      akCount h L 𝔭 k = discAut h ⊤ L 𝔭 * Nat.card (kerSet K 𝔭 k a)

end Formalism.L2.SG.Pf.G5
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueExistsOfOf
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G7

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

def GlueLocal : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ Formalism.HermitianLatticesTheory.IsUnimodular h Λ₀) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → cJ h U M 𝔭 < finrank K (orthK h U) →
      ∃ T : Submodule (𝓞 K) V, (∃ A : Submodule (𝓞 K) V, Submodule.IsLattice K A ∧ locF 𝔭 A = T) ∧
        dualF h 𝔭 T = T ∧ T ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M

end Formalism.L2.SG.Pf.G7
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.BigLineBundleMoriwaki
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G6

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

def ProjInto : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ (X Y : Submodule K V) (hc : IsCompl X Y), (∀ x ∈ X, ∀ y ∈ Y, h x y = 0) →
    ∀ L : Submodule (𝓞 K) V, IsLatIn X L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
    ∀ Λ : Submodule (𝓞 K) V, (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ locF 𝔭 Λ₀ = Λ) →
      dualF h 𝔭 Λ = Λ → Λ ⊓ X.restrictScalars (𝓞 K) = locF 𝔭 L →
      ∀ x ∈ Λ, X.projection Y hc x ∈ locF 𝔭 (dualIn h X L)

def ProjOnto : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ (X Y : Submodule K V) (hc : IsCompl X Y), (∀ x ∈ X, ∀ y ∈ Y, h x y = 0) →
    ∀ L : Submodule (𝓞 K) V, IsLatIn X L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
    ∀ Λ : Submodule (𝓞 K) V, (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ locF 𝔭 Λ₀ = Λ) →
      dualF h 𝔭 Λ = Λ → Λ ⊓ X.restrictScalars (𝓞 K) = locF 𝔭 L →
      ∀ v ∈ locF 𝔭 (dualIn h X L), ∃ x ∈ Λ, X.projection Y hc x = v

def FibCount : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) →
    ∀ M T : Submodule (𝓞 K) V, IsLatIn U M → IsLatIn (orthK h U) T → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
      fibP h U 𝔭 M T ≠ 0 → fibP h U 𝔭 M T = discAut h (orthK h U) T 𝔭

end Formalism.L2.SG.Pf.G6

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.G6

theorem glueLoc_of (hi : ProjInto) (ho : ProjOnto) (hn : FibCount) : GlueLoc := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hcU M T hM hT 𝔭 h𝔭
  refine ⟨fun hne => ⟨?_, hn K F V hK hF h hs hnd U hcU M T hM hT 𝔭 h𝔭 hne⟩,
    fun g hg => fibP_gmap hM 𝔭 T hg⟩
  obtain ⟨⟨Λ, hΛ0, hΛd, hΛU, hΛW⟩⟩ := (Nat.card_ne_zero.mp hne).1
  have oU : ∀ x ∈ U, ∀ y ∈ orthK h U, h x y = 0 := fun x hx y hy => mem_orthK.mp hy x hx
  have oW : ∀ x ∈ orthK h U, ∀ y ∈ U, h x y = 0 := by
    intro x hx y hy
    have e := hs.eq x y
    rw [oU y hy x hx] at e
    simpa using e
  exact discIso_of_proj h hcU hΛU hΛW
    (hi K F V hK hF h hs hnd U (orthK h U) hcU oU M hM 𝔭 h𝔭 Λ hΛ0 hΛd hΛU)
    (ho K F V hK hF h hs hnd U (orthK h U) hcU oU M hM 𝔭 h𝔭 Λ hΛ0 hΛd hΛU)
    (hi K F V hK hF h hs hnd (orthK h U) U hcU.symm oW T hT 𝔭 h𝔭 Λ hΛ0 hΛd hΛW)
    (ho K F V hK hF h hs hnd (orthK h U) U hcU.symm oW T hT 𝔭 h𝔭 Λ hΛ0 hΛd hΛW)

end Formalism.L2.SG.Pf.Cnt
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocFMapSubtype
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G1

open Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem locF_map_subtype (X : Submodule K V) (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (N : Submodule (𝓞 K) X) :
    locF 𝔭 (N.map (X.subtype.restrictScalars (𝓞 K))) =
      (locF 𝔭 N).map (X.subtype.restrictScalars (𝓞 K)) := by
  ext y
  rw [Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF, Submodule.mem_map]
  constructor
  · rintro ⟨t, ht, z, hz, hzy⟩
    have ht0 : t ≠ 0 := fun h0 => ht (h0 ▸ 𝔭.zero_mem)
    have hne : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
      have e : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := rfl
      rw [e, map_ne_zero]
      exact fun h => ht0 (by exact_mod_cast h)
    have hmem : algebraMap (𝓞 F) (𝓞 K) t • y ∈ X := by
      rw [← hzy]; exact z.2
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) y] at hmem
    have hyX : y ∈ X := (X.smul_mem_iff hne).mp hmem
    refine ⟨⟨y, hyX⟩, ?_, rfl⟩
    rw [Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF]
    refine ⟨t, ht, ?_⟩
    have e2 : algebraMap (𝓞 F) (𝓞 K) t • (⟨y, hyX⟩ : X) = z := by
      apply Subtype.ext
      simpa using hzy.symm
    rw [e2]; exact hz
  · rintro ⟨z, hz, rfl⟩
    rw [Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF] at hz
    obtain ⟨t, ht, hz⟩ := hz
    exact ⟨t, ht, _, hz, by simp⟩

variable [FiniteDimensional K V]

theorem exists_basis_in {X : Submodule K V} {L : Submodule (𝓞 K) V} (hL : Cnt.IsLatIn X L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ x : Fin (finrank K X) → V, (∀ i, x i ∈ L) ∧ LinearIndependent K x ∧
      Submodule.span K (Set.range x) = X ∧
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range x)) = locF 𝔭 L := by
  haveI : 𝔭.IsPrime := h𝔭.isPrime
  obtain ⟨hfg, hspan⟩ := hL
  have hLX : ∀ v ∈ L, v ∈ X := fun v hv => hspan ▸ Submodule.subset_span hv
  have hmapN : (L.comap (X.subtype.restrictScalars (𝓞 K))).map
      (X.subtype.restrictScalars (𝓞 K)) = L := by
    rw [Submodule.map_comap_eq]
    refine inf_eq_right.mpr ?_
    intro v hv
    exact ⟨⟨v, hLX v hv⟩, rfl⟩
  have hinj : Function.Injective (X.subtype.restrictScalars (𝓞 K)) := X.injective_subtype
  have hfgN : (L.comap (X.subtype.restrictScalars (𝓞 K))).FG :=
    Submodule.fg_of_fg_map_injective _ hinj (by rw [hmapN]; exact hfg)
  have himg : X.subtype '' ((L.comap (X.subtype.restrictScalars (𝓞 K)) : Submodule (𝓞 K) X) : Set X)
      = (L : Set V) := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hv
      exact ⟨⟨v, hLX v hv⟩, hv, rfl⟩
  have hspanN : Submodule.span K
      ((L.comap (X.subtype.restrictScalars (𝓞 K)) : Submodule (𝓞 K) X) : Set X) = ⊤ := by
    apply Submodule.map_injective_of_injective X.injective_subtype
    rw [Submodule.map_span, himg, hspan, Submodule.map_top, Submodule.range_subtype]
  have hNlat : Submodule.IsFullLattice K (L.comap (X.subtype.restrictScalars (𝓞 K))) :=
    { toIsLattice := Submodule.IsLattice.of_fg K hfgN
      span_eq_top := hspanN }
  obtain ⟨b, hbN, hbloc⟩ := Formalism.HermitianLattices.Ext.L3.LocalSpans.exists_basis_locF hNlat h𝔭
  refine ⟨fun i => (b i : V), fun i => hbN i, ?_, ?_, ?_⟩
  · exact b.linearIndependent.map' X.subtype X.ker_subtype
  · have hx : Set.range (fun i => (b i : V)) = X.subtype '' Set.range b := Set.range_comp _ _
    rw [hx, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  · have hx : Set.range (fun i => (b i : V)) =
        (X.subtype.restrictScalars (𝓞 K)) '' Set.range b := Set.range_comp _ _
    rw [hx, Submodule.span_image, locF_map_subtype, hbloc, ← locF_map_subtype, hmapN]

theorem det_gram_ne_zero [StarRing K] {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V}
    (hnd : Cnt.NondegOn h X) {n : ℕ} {x : Fin n → V} (hli : LinearIndependent K x)
    (hsp : Submodule.span K (Set.range x) = X) : (U0.gram h x).det ≠ 0 := by
  intro hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  have hyX : (∑ i, star (c i) • x i) ∈ X := by
    rw [← hsp]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have key : ∀ j, h (∑ i, star (c i) • x i) (x j) = 0 := by
    intro j
    have hj := congrFun hc j
    simp only [Matrix.vecMul, dotProduct, U0.gram, Matrix.of_apply, Pi.zero_apply] at hj
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smulₛₗ, starRingEnd_apply, star_star, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
    exact hj
  have hall : ∀ z ∈ X, h (∑ i, star (c i) • x i) z = 0 := by
    intro z hz
    rw [← hsp] at hz
    have hle : Submodule.span K (Set.range x) ≤ LinearMap.ker (h (∑ i, star (c i) • x i)) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact key j
    exact hle hz
  have hy0 := hnd _ hyX hall
  have hcoef := Fintype.linearIndependent_iff.mp hli (fun i => star (c i)) hy0
  apply hc0
  funext i
  simpa using hcoef i

end Formalism.L2.SG.Pf.G1
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CardQuotSmulTopCongr
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G2

open Formalism.HermitianLattices.Ext.L3

theorem smul_top_pi {R : Type*} [CommRing R] {κ : Type*} [Fintype κ] [DecidableEq κ]
    {N : κ → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] (J : Ideal R) :
    (J • ⊤ : Submodule R (∀ i, N i)) =
      Submodule.pi Set.univ (fun i => J • (⊤ : Submodule R (N i))) := by
  apply le_antisymm
  · rw [Submodule.smul_le]
    intro r hr n _
    rw [Submodule.mem_pi]
    intro i _
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · intro v hv
    rw [Submodule.mem_pi] at hv
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    have h1 : Pi.single i (v i) ∈ (J • (⊤ : Submodule R (N i))).map (LinearMap.single R N i) :=
      Submodule.mem_map_of_mem (hv i (Set.mem_univ i))
    rw [Submodule.map_smul''] at h1
    exact Submodule.smul_mono le_rfl le_top h1

theorem card_quot_smul_top_congr {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M ≃ₗ[R] N) (J : Ideal R) :
    Nat.card (M ⧸ (J • ⊤ : Submodule R M)) = Nat.card (N ⧸ (J • ⊤ : Submodule R N)) := by
  refine Nat.card_congr (Submodule.Quotient.equiv _ _ f ?_).toEquiv
  rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]

theorem card_quot_quot {A : Type*} [CommRing A] (E J : Ideal A) :
    Nat.card ((A ⧸ E) ⧸ (J • ⊤ : Submodule A (A ⧸ E))) = Nat.card (A ⧸ (E ⊔ J)) := by
  have h1 : (J • ⊤ : Submodule A (A ⧸ E)) = Submodule.map E.mkQ J := by
    conv_lhs => rw [← Submodule.range_mkQ E, LinearMap.range_eq_map, ← Submodule.map_smul'',
      Ideal.smul_eq_mul, Ideal.mul_top]
  rw [h1]
  exact Nat.card_congr (Submodule.quotientQuotientEquivQuotientSup E J).toEquiv

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem two_le_absNorm {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 2 ≤ Ideal.absNorm (extP K 𝔭) := by
  have hc := Formalism.HermitianLattices.Ext.L3.MeanB.comap_extP_pow (K := K) 𝔭 1
  rw [pow_one, pow_one] at hc
  have h1 : extP K 𝔭 ≠ ⊤ := fun h => h𝔭.ne_top (by rw [← hc, h, Ideal.comap_top])
  have h0 : extP K 𝔭 ≠ ⊥ := by
    intro h
    have hne : 𝔭 ≠ ⊥ := fun h' =>
      NumberField.RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.mpr (h' ▸ h𝔭))
    apply hne
    rw [← hc, h]
    ext t
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    constructor
    · intro ht
      have h2 : algebraMap F K (t : F) = 0 := by
        have h3 := congrArg (algebraMap (𝓞 K) K) ht
        rw [map_zero] at h3
        exact h3
      have h4 : (t : F) = 0 := (algebraMap F K).injective (by rw [h2, map_zero])
      exact_mod_cast h4
    · intro ht
      rw [ht, map_zero]
  have ha0 : Ideal.absNorm (extP K 𝔭) ≠ 0 := fun h => h0 (Ideal.absNorm_eq_zero_iff.mp h)
  have ha1 : Ideal.absNorm (extP K 𝔭) ≠ 1 := fun h => h1 (Ideal.absNorm_eq_one_iff.mp h)
  omega

theorem card_pi_quot (𝔭 : Ideal (𝓞 F)) {κ : Type} [Fintype κ] [DecidableEq κ] (e : κ → ℕ) (j : ℕ) :
    Nat.card ((∀ i, 𝓞 K ⧸ extP K 𝔭 ^ e i) ⧸
        (extP K 𝔭 ^ j • ⊤ : Submodule (𝓞 K) (∀ i, 𝓞 K ⧸ extP K 𝔭 ^ e i))) =
      Ideal.absNorm (extP K 𝔭) ^ ∑ i, min (e i) j := by
  rw [smul_top_pi, Nat.card_congr (Submodule.quotientPi
    (fun i => (extP K 𝔭 ^ j • ⊤ : Submodule (𝓞 K) (𝓞 K ⧸ extP K 𝔭 ^ e i)))).toEquiv,
    Nat.card_pi, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hsup : extP K 𝔭 ^ e i ⊔ extP K 𝔭 ^ j = extP K 𝔭 ^ min (e i) j := by
    rcases le_total (e i) j with h | h
    · rw [min_eq_left h, sup_eq_left.mpr (Ideal.pow_le_pow_right h)]
    · rw [min_eq_right h, sup_eq_right.mpr (Ideal.pow_le_pow_right h)]
  rw [card_quot_quot, hsup, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, map_pow]

end Formalism.L2.SG.Pf.G2
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsLocFEq
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def fibS (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (𝔭 : Ideal (𝓞 F)) (M T : Submodule (𝓞 K) V) :
    Set (Submodule (𝓞 K) V) :=
  {Λ | (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ locF 𝔭 Λ₀ = Λ) ∧
    dualF h 𝔭 Λ = Λ ∧
    Λ ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M ∧
    Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 T}

theorem fibP_eq (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (𝔭 : Ideal (𝓞 F)) (M T : Submodule (𝓞 K) V) :
    fibP h U 𝔭 M T = Nat.card (fibS h U 𝔭 M T) := rfl

theorem isLattice_sup {X Y : Submodule K V} (hc : IsCompl X Y) {A B : Submodule (𝓞 K) V}
    (hA : IsLatIn X A) (hB : IsLatIn Y B) : Submodule.IsLattice K (A ⊔ B) := by
  refine ⟨hA.1.sup hB.1, ?_⟩
  intro s hs hli
  exact (LinearIndependent.iff_fractionRing _ _).mp hli
theorem exists_locF_eq {A B : Submodule (𝓞 K) V} (hA : Submodule.IsFullLattice K A)
    (hB : Submodule.IsFullLattice K B) :
    ∃ s : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, ∀ 𝔭 ∉ s, locF 𝔭.1 A = locF 𝔭.1 B := by
  obtain ⟨n, hn, hnA⟩ := LocF.exists_zsmul_le hA.toIsLattice hB
  obtain ⟨m, hm, hmB⟩ := LocF.exists_zsmul_le hB.toIsLattice hA
  have hc : ((n * m : ℤ) : 𝓞 F) ≠ 0 := by
    exact_mod_cast mul_ne_zero hn hm
  obtain ⟨s, hs⟩ := (LocalFactorEquality.finite_vF_ne_zero hc).exists_finset
  refine ⟨s, fun 𝔭 h𝔭 => ?_⟩
  have hv : vF 𝔭.1 ((n * m : ℤ) : 𝓞 F) = 0 := by
    by_contra hne
    exact h𝔭 ((hs 𝔭).2 hne)
  have hnm := LocalizedFibreSets.notMem_of_vF_zero 𝔭.2 hc hv
  have hp := 𝔭.2.isPrime
  have hn' : ((n : ℤ) : 𝓞 F) ∉ 𝔭.1 := fun h1 => hnm (by rw [Int.cast_mul]; exact 𝔭.1.mul_mem_right _ h1)
  have hm' : ((m : ℤ) : 𝓞 F) ∉ 𝔭.1 := fun h1 => hnm (by rw [Int.cast_mul]; exact 𝔭.1.mul_mem_left _ h1)
  have key : ∀ {A B : Submodule (𝓞 K) V} (k : ℤ), ((k : ℤ) : 𝓞 F) ∉ 𝔭.1 → (∀ x ∈ A, k • x ∈ B) →
      locF 𝔭.1 A ≤ locF 𝔭.1 B := by
    intro A B k hk hkA x hx
    obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff hp A x).1 hx
    refine (LocF.mem_locF_iff hp B x).2 ⟨(k : 𝓞 F) * t, fun h1 => (hp.mem_or_mem h1).elim hk ht, ?_⟩
    rw [map_mul, mul_smul, LocF.algebraMap_intCast_smul]
    exact hkA _ htx
  exact le_antisymm (key n hn' hnA) (key m hm' hmB)

private lemma mem_locF_lemma {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (𝔭 : Ideal (𝓞 F))
    (L : Submodule (𝓞 K) W) (x : W) :
    x ∈ locF 𝔭 L ↔ ∃ s ∈ Submonoid.closure
      {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}, s • x ∈ L := Iff.rfl

private lemma algebraMap_ne_zero_of_mem_closure_prime_compl {𝔭 : Ideal (𝓞 F)} {s : 𝓞 K}
    (hs : s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}) :
    algebraMap (𝓞 K) K s ≠ 0 := by
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    have ht0 : t ≠ 0 := fun h0 => ht (h0 ▸ 𝔭.zero_mem)
    have e : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := rfl
    rw [e]
    exact (map_ne_zero _).mpr (by simpa using ht0)
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_ne_zero hx hy

theorem locF_sup_inf {X Y : Submodule K V} (hc : IsCompl X Y) {A B : Submodule (𝓞 K) V}
    (hA : ∀ x ∈ A, x ∈ X) (hB : ∀ x ∈ B, x ∈ Y) {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) :
    locF 𝔭 (A ⊔ B) ⊓ X.restrictScalars (𝓞 K) = locF 𝔭 A := by
  apply le_antisymm
  · rintro x ⟨hx1, hx2⟩
    obtain ⟨s, hs, hsx⟩ := (mem_locF_lemma 𝔭 _ x).mp hx1
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hsx
    have hxX : x ∈ X := hx2
    have hsX : s • x ∈ X := by
      rw [← algebraMap_smul K s x]; exact X.smul_mem _ hxX
    have hbX : b ∈ X := by
      have : b = s • x - a := by rw [← hab]; abel
      rw [this]; exact X.sub_mem hsX (hA a ha)
    have hb0 : b = 0 := by
      have := hc.inf_eq_bot
      have hmem : b ∈ X ⊓ Y := ⟨hbX, hB b hb⟩
      rw [this] at hmem
      exact (Submodule.mem_bot K).mp hmem
    refine (mem_locF_lemma 𝔭 _ x).mpr ⟨s, hs, ?_⟩
    rw [← hab, hb0, add_zero]; exact ha
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := (mem_locF_lemma 𝔭 _ x).mp hx
    refine ⟨(mem_locF_lemma 𝔭 _ x).mpr ⟨s, hs, Submodule.mem_sup_left hsx⟩, ?_⟩
    have hs0 : algebraMap (𝓞 K) K s ≠ 0 := algebraMap_ne_zero_of_mem_closure_prime_compl hs
    have e : x = (algebraMap (𝓞 K) K s)⁻¹ • (s • x) := by
      rw [← algebraMap_smul K s x, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    show x ∈ X
    rw [e]
    exact X.smul_mem _ (hA _ hsx)

theorem dualF_anti (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔭 : Ideal (𝓞 F)) {A B : Submodule (𝓞 K) V} (hAB : A ≤ B) :
    dualF h 𝔭 B ≤ dualF h 𝔭 A := by
  intro x hx
  have hx' : ∀ y ∈ B, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := hx
  change ∀ y ∈ A, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
  exact fun y hy => hx' y (hAB hy)

end Formalism.L2.SG.Pf.G8
end
end
