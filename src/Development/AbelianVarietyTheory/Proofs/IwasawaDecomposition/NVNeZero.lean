module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Formalism.LocalToGlobal.UnitaryNorms.DatumS
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoratedLatticeDiagonalBasePointMul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightDualUniqueness.SelfInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesEqIffReductionEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg

theorem nV_pos (X : Stages) : 0 < X.B.R.nV := by
  have h := X.B.R.m_add_three_le_k
  unfold Ranks.nV Ranks.r
  omega

instance nV_neZero (X : Stages) : NeZero X.B.R.nV := ⟨(nV_pos X).ne'⟩

theorem rkEq (X : Stages) (i : Fin X.toD7.R.m) : X.B.R.nV = (Vc X.toD7 i).rank :=
  (X.toD7.sp.V_rank _ (by omega) i.2).symm

def castGL {R : Type} [CommRing R] {m n : ℕ} (h : m = n) : GL (Fin m) R ≃* GL (Fin n) R :=
  Units.mapEquiv (Matrix.reindexAlgEquiv R R (finCongr h)).toRingEquiv.toMulEquiv

abbrev EA (X : Stages) : Type := X.toD7.host.E ⊗[X.toD7.host.F] Formalism.L2.Herm.Af X.toD7.host.F

abbrev envL (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U))
    (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) :=
  Bridge.envOf (cV i).coef (levEnvOf (Vc X.toD7 i) (L.βV i) (L.datVt i t) (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E))
    ((famR X I hX U Xg tr).A.ok t))

abbrev PresL (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U))
    (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) : Type :=
  Bridge.ClassPres (Bridge.ratF (Vc X.toD7 i)) ((famR X I hX U Xg tr).A.MtCSD i t) X.toD7.what₂.embLL
    (envL X I hX U Xg tr L cV i t).coef.ρ (envL X I hX U Xg tr L cV i t).lev.J (envL X I hX U Xg tr L cV i t).lev.χ

abbrev sgL (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (U : Set I.ι) (t : TupU I U) :
    Finset (Pl X.toD7.host.E) :=
  Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1

def FrameOK (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (U : Set I.ι) (i : Fin X.toD7.R.m) (t : TupU I U)
    (A k : GL (Fin X.B.R.nV) (EA X)) : Prop :=
  (∃ A0 : GL (Fin X.B.R.nV) X.toD7.host.E, A = Formalism.UG.bc (Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E) A0) ∧
    A ∈ Formalism.L2.DIV.St 1 ∧
    (∀ x : GL (Fin X.B.R.nV) (EA X), x ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ↔
      castGL (rkEq X i) (A * x * A⁻¹) ∈ Formalism.L2.DIV.UA X.toD7.sp.cm (Vc X.toD7 i).gram) ∧
    k ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ∧ k ∈ Formalism.L2.DIV.St 1 ∧
    ∀ PP ∈ sgL X I U t, A * k ∈ Formalism.L2.DIV.princAt 1 PP

def ptL (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (U : Set I.ι) (i : Fin X.toD7.R.m) (t : TupU I U)
    (A k : GL (Fin X.B.R.nV) (EA X)) (g : Bridge.Gf (Vc X.toD7 i)) :
    Formalism.L2.Col.DecoSet (E := X.toD7.host.E) (n := X.B.R.nV) (ST := ∅) (SG := sgL X I U t) :=
  Formalism.L2.Col.decoOf ∅ (sgL X I U t)
    (A⁻¹ * castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) (g : GL (Fin (Vc X.toD7 i).rank) _)) * A * k)

def ReadsStd (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U))
    (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X))
    (P : PresL X I hX U Xg tr L cV i t) : Prop :=
  ∀ (f : ((famR X I hX U Xg tr).A.MtCSD i t).Forms) (g : Bridge.Gf (Vc X.toD7 i)),
    P.ext (f : ((famR X I hX U Xg tr).A.MtCSD i t).Cl → ((famR X I hX U Xg tr).A.MtCSD i t).V) g =
      P.coef ((((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res
        (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1))).symm f).1 (ptL X I U i t A k g))

end GlobalTheory.Mem.R3.LiftBrg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtIn

section Cut

variable {G Γ : Type} [Group G] [Group Γ] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

def cutSp (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (Q : Subgroup G) (ch : Q →* ℂˣ)
    {G₀ : Type} [Group G₀] (red : Q →* G₀) (P : Subgroup G₀) (ψ : P →* ℂˣ) : Submodule ℂ (G → W) :=
  Bridge.AdForms ι ρ J χ ⊓
    { carrier := {F | ∀ (κ : Q) (hκ : red κ ∈ P) (h : G), F (h * κ) = ((ch κ * ψ ⟨red κ, hκ⟩ : ℂˣ) : ℂ) • F h}
      add_mem' := fun {F F'} hF hF' κ hκ h => by simp only [Pi.add_apply, hF κ hκ h, hF' κ hκ h, smul_add]
      zero_mem' := fun κ hκ h => by simp
      smul_mem' := fun c F hF κ hκ h => by simp only [Pi.smul_apply, hF κ hκ h]; rw [smul_comm] }

def lvlForm {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G₀ : Type} [Group G₀] [Fintype G₀]
    (r : Representation K G₀ S.Forms) (P : Subgroup G₀) (ψ : P →* Kˣ) (x : Fin (S.lvlDim r P ψ) → K) : S.Forms :=
  S.basis.equivFun.symm ((S.lvlE r P ψ).mulVec x)

end Cut

variable {D : D7}

variable (D) in
def km (n : ℕ) : Formalism.AUTREP.GAf D.host.E n →* GL (Fin n) (EAf D) := (ReciprocityTheory.Aut.GA D.host.E n).subtype

def stdJ {n : ℕ} (Ld : Formalism.L2.DIV.LevDat D.host.E ℂ n) : Subgroup (Formalism.AUTREP.GAf D.host.E n) :=
  (Formalism.L2.DIV.lev D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E) 1 Ld).comap (km D n)

def stdX {n : ℕ} (Ld : Formalism.L2.DIV.LevDat D.host.E ℂ n) : stdJ Ld →* ℂˣ :=
  (Formalism.L2.DIV.levChar D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E) 1 Ld).comp ((km D n).subgroupComap _)

variable (D) in
def datV (n : ℕ) (hr : D.R.r ≤ n) (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg D.R.r ℂ)
    (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Formalism.L2.DIV.LevDat D.host.E ℂ n :=
  datY n D.R.r D.R.t 1 hr Pg Q P (fun _ => chi) xi Frm.A

def UnitFr {V : HSp D} (P : principalLevelFrame.RowPsi V V.rank) : Prop := ∀ κ, finE V (P.ψ κ) = km D V.rank κ

def toGf {V : HSp D} {n : ℕ} (P : principalLevelFrame.RowPsi V n) : Formalism.AUTREP.GAf D.host.E n →* Bridge.Gf V :=
  (finHom V).rangeRestrict.comp P.ψ

def RatIso {V : HSp D} (P : principalLevelFrame.RowPsi V V.rank) (e : ReciprocityTheory.Aut.GQ D.host.E V.rank ≃* Formalism.L2.Theta.GQ V) : Prop :=
  ∀ γ : ReciprocityTheory.Aut.GQ D.host.E V.rank, Bridge.ratF V (e γ) = toGf P γ.1 ∧
    ∀ γ₀ : GL (Fin V.rank) D.host.E,
      (γ.1.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) =
        (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map Algebra.TensorProduct.includeLeftRingHom →
      Bridge.IsRatMat V (e γ) γ₀

def wtRep {V : HSp D} {n : ℕ} (c : CoefA V) (e : ReciprocityTheory.Aut.GQ D.host.E n ≃* Formalism.L2.Theta.GQ V) :
    Representation ℂ (ReciprocityTheory.Aut.GQ D.host.E n) c.W :=
  c.coef.ρ.comp e.toMonoidHom

end GlobalTheory.MtIn

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHostDatumOfPlaceData
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayFieldTopMaximalUnramified
noncomputable section

open Formalism.L2.Host GlobalTheory.Published GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain

namespace GlobalTheory.HilbertInClosure

theorem rayField_top_maximal_unramified : GlobalArtinReciprocity → ∀ (E : Type) [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] (j : E →ₐ[ℚ] Qb) (ι : Qb →+* ℂ) (M : IntermediateField ℚ ℂ),
    IsRayFieldIn (ι.comp j.toRingHom) ⊤ M →
    ∃ _ : NumberField (qb ι M),
      (j.fieldRange ≤ qb ι M ∧
        (∀ σ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ j.fieldRange, σ x = x) → ∀ y ∈ qb ι M, σ y ∈ qb ι M) ∧
        ∀ σ τ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ j.fieldRange, σ x = x) → (∀ x ∈ j.fieldRange, τ x = x) →
          ∀ y ∈ qb ι M, σ (τ y) = τ (σ y)) ∧
      (discr (qb ι M)).natAbs = (discr E).natAbs ^ (Module.finrank ℚ (qb ι M) / Module.finrank ℚ E) ∧
      ∀ (L : Fld) [NumberField L],
        (j.fieldRange ≤ L ∧ (∀ σ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ j.fieldRange, σ x = x) → ∀ y ∈ L, σ y ∈ L) ∧
          ∀ σ τ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ j.fieldRange, σ x = x) → (∀ x ∈ j.fieldRange, τ x = x) →
            ∀ y ∈ L, σ (τ y) = τ (σ y)) →
        (discr L).natAbs = (discr E).natAbs ^ (Module.finrank ℚ L / Module.finrank ℚ E) → L ≤ qb ι M := by
  intro H E _ _ _ j ι M hM
  obtain ⟨hN, h, hst, hc, hd, hmax⟩ := hilbert_qb_aut H E j ι M hM
  have hm : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ GalOf j.fieldRange ↔ ∀ x ∈ j.fieldRange, σ x = x := fun σ =>
    IntermediateField.mem_fixingSubgroup_iff _ _
  exact ⟨hN, ⟨h, fun σ hσ => hst σ ((hm σ).2 hσ), fun σ τ hσ hτ => hc σ ((hm σ).2 hσ) τ ((hm τ).2 hτ)⟩, hd,
    fun L _ hL => hmax L hL.1 fun σ hσ τ hτ => hL.2.2 σ τ ((hm σ).1 hσ) ((hm τ).1 hτ)⟩

end GlobalTheory.HilbertInClosure

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host GlobalTheory.Published GlobalTheory.Mem.HD
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.HostDatumExists

theorem exists_reps (K : Type) [Field K] [NumberField K] {ι : Type} [Finite ι] (n : ι → ℕ) (hn : ∀ i, n i ≠ 0)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) (c : ClassGroup (𝓞 K)) :
    ∃ I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = c ∧
      (∀ i, IsCoprime (I : Ideal (𝓞 K)) (Ideal.span {((n i : ℕ) : 𝓞 K)})) ∧
      ∀ 𝔭 ∈ S, ¬ (I : Ideal (𝓞 K)) ≤ 𝔭.asIdeal := by
  classical
  have := Fintype.ofFinite ι
  set m : Ideal (𝓞 K) := (∏ i, Ideal.span {((n i : ℕ) : 𝓞 K)}) * ∏ 𝔭 ∈ hS.toFinset, 𝔭.asIdeal with hm
  have hm0 : m ≠ ⊥ := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ?_) (Finset.prod_ne_zero_iff.mpr fun 𝔭 _ => 𝔭.ne_bot)
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn i
  obtain ⟨I, hI, hsup⟩ := GlobalTheory.exists_integral_ideal_in_class_coprime K m hm0 c
  refine ⟨I, hI, fun i => ?_, fun 𝔭 h𝔭 hle => 𝔭.isPrime.ne_top ?_⟩
  · rw [Ideal.isCoprime_iff_sup_eq, ← top_le_iff, ← hsup]
    refine sup_le_sup_left (Ideal.le_of_dvd (Dvd.dvd.mul_right ?_ _)) _
    exact Finset.dvd_prod_of_mem (fun i => Ideal.span {((n i : ℕ) : 𝓞 K)}) (Finset.mem_univ i)
  · have h : m ≤ 𝔭.asIdeal :=
      Ideal.le_of_dvd (Dvd.dvd.mul_left
        (Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (𝓞 K) => q.asIdeal) (hS.mem_toFinset.mpr h𝔭)) _)
    exact top_le_iff.mp (hsup ▸ sup_le hle h)

theorem le_of_integral {A B : Formalism.L2.Host.Fld} (h : ∀ x ∈ A, IsIntegral ℤ x → x ∈ B) : A ≤ B := by
  intro x hx
  have : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  have h1 : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ Qb).mpr (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨a, ha, hi⟩ := h1.exists_integral_multiple
  have h2 : a • x ∈ B := h _ (zsmul_mem hx a) hi
  have h3 : x = ((a : Qb))⁻¹ * (a • x) := by
    have : (a : Qb) ≠ 0 := by exact_mod_cast ha
    rw [zsmul_eq_mul, inv_mul_cancel_left₀ this]
  rw [h3]
  exact mul_mem (inv_mem (intCast_mem B a)) h2

end GlobalTheory.HostDatumExists
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTypesOfTypesTrueReal
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Host Formalism.IndefR Formalism.IndefR.Links NumberField IsDedekindDomain

namespace GlobalTheory.HeightCounting

theorem goodTypes_of_typesTrue_real : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → GlobalTheory.Mem.Top.TypesTrue D.ntypes R.C.P R.C.W → GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hL h => GlobalTheory.LiftRows.Inh.goodTypes_of_typesTrue hL h

end GlobalTheory.HeightCounting
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsDeco
noncomputable section

open scoped TensorProduct

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.RowAd

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (X : Stages)

theorem rank_X' : X.toD7.sp.X'.rank = X.B.R.N X.B.R.m - 1 := by
  rw [X.toD7.sp.X'_rank, Formalism.L2.Col.rank_X'_eq]
  rfl

def ptE (h : Bridge.Gf X.toD7.sp.X') :
    GL (Fin (X.B.R.N X.B.R.m - 1)) (X.B.fields.E ⊗[X.B.fields.F] Formalism.L2.Herm.Af X.B.fields.F) :=
  Units.map (Matrix.reindexAlgEquiv (Formalism.IndefR.Lev.EAf X.toD7) (Formalism.IndefR.Lev.EAf X.toD7) (finCongr (rank_X' X))).toMonoidHom
    (Formalism.UG.bc (Formalism.IndefR.Lev.swapAE X.toD7) h.1)

variable {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) {U : Set I.ι}

def decoAd (t : TupU I U) (h : Bridge.Gf X.toD7.sp.X') : (Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).D :=
  Formalism.L2.Col.decoOf (F := X.B.fields.F) (E := X.B.fields.E) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) (ptE X h)

def ReadsDeco (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (cX : CoefA X.toD7.sp.X') {J : Subgroup (Bridge.Gf X.toD7.sp.X')}
    {χ : J →* ℂˣ} (t : TupU I U)
    (P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ J χ) : Prop :=
  ∃ m : ((famR X I hX U Xg tr).A.MtildeCSD t).V →ₛₗ[X.toD7.what₂.embLL] cX.W,
    ∀ (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) (h : Bridge.Gf X.toD7.sp.X'),
      P.ext (f : _ → _) h = m ((((Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f).1
        (decoAd X I t h))

end GlobalTheory.Mem.R3.RowAd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GEquivIntL
noncomputable section

open NumberField IsDedekindDomain Formalism.AUTREP Formalism.UG ReciprocityTheory.Aut

namespace GlobalTheory.SatInd

section Field

variable {K : Type} [Field K]

theorem antiJ_map (g : K →+* K) (n : ℕ) : (antiJ K n).map g = antiJ K n := by
  ext i j
  simp only [antiJ, Matrix.map_apply]
  split_ifs <;> simp

theorem cT_map (g σ σ' : K →+* K) (hg : ∀ x, g (σ x) = σ' (g x)) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) : cT σ' (M.map g) = (cT σ M).map g := by
  ext i j
  simp [cT, hg]

def guMap (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)) (n : ℕ) :
    GU σ n →* GU σ' n :=
  ((bc (n := Fin n) (g : K →+* K)).comp (GU σ n).subtype).codRestrict (GU σ' n) (fun y => by
    have hy : cT σ ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * antiJ K n *
        ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = antiJ K n := y.2
    show cT σ' (((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map (g : K →+* K)) * antiJ K n *
        ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map (g : K →+* K) = antiJ K n
    rw [cT_map (g : K →+* K) σ σ' hg, ← antiJ_map (g : K →+* K) n]
    rw [← Matrix.map_mul, ← Matrix.map_mul, hy])

theorem guMap_val (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)) {n : ℕ}
    (y : GU σ n) :
    (((guMap g hg n y : GU σ' n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map g := rfl

end Field

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

def gEquiv (D D' : InertDatum L n v w) : w.adicCompletion L ≃+* w.adicCompletion L :=
  D.e.symm.trans D'.e

theorem gEquiv_e (D D' : InertDatum L n v w) (y) : gEquiv D D' (D.e y) = D'.e y := by
  simp [gEquiv]

theorem gEquiv_comm (D D' : InertDatum L n v w) :
    ∀ x, gEquiv D D' (D.σw x) = D'.σw (gEquiv D D' x) := by
  intro x
  obtain ⟨y, rfl⟩ := D.e.surjective x
  rw [← D.comm, gEquiv_e, gEquiv_e, D'.comm]

theorem gEquiv_intL (D D' : InertDatum L n v w) :
    ∀ x, x ∈ intL (w.adicCompletion L) ↔ gEquiv D D' x ∈ intL (w.adicCompletion L) := by
  intro x
  obtain ⟨y, rfl⟩ := D.e.surjective x
  rw [gEquiv_e, ← D.integ, ← D'.integ]

end GlobalTheory.SatInd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasSatGLLocRep
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CuspRep.UnrSat

open GlobalTheory.CuspRep GlobalTheory.LFun GlobalTheory.PRep

theorem exists_hasSatGL_locRep : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E]
    [NumberField.IsTotallyComplex E] (a : ℕ) (π : GlobalTheory.CuspRep.CuspSub E a) (v : HeightOneSpectrum (𝓞 E)),
    GlobalTheory.LGrp.IsSpherical (π.locRep v) (GlobalTheory.LFun.KGL v (n := a)) → ∃ B : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL v (π.locRep v) B := by
  intro hF E _ _ _ a π v hs
  obtain ⟨σ, hσ, hadm⟩ := LocEx.exists_isLocComp hF E a π v
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hs
  obtain ⟨y, hy0, hy⟩ := LocSph.exists_fixed_of_mem_iSup ((finRep E a).comp (locGL E a v)) σ.ρ σ.irred
    (fun f : LocSph.Maps π v σ => f.1) (fun f => f.2.2) (KGL v (n := a) : Set _) x.1 (fun e => hx0 (Subtype.ext e))
    (fun k hk => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hx k hk))
    (by rw [LocSph.iSup_range_eq π v σ hσ]; exact x.2)
  have hsph : GlobalTheory.LGrp.IsSpherical σ.ρ (KGL v (n := a)) :=
    (Submodule.ne_bot_iff _).2 ⟨y, GlobalTheory.LGrp.mem_fixed.2 hy, hy0⟩
  have hfin : FiniteDimensional ℂ (fixed σ.ρ (KGL v (n := a))) :=
    hadm.2 _ (SatCompare.isOpen_isCompact_KGL v a).1 (SatCompare.isOpen_isCompact_KGL v a).2
  obtain ⟨B, hB⟩ := SatCompare.exists_hasSatGL ⟨σ.smooth, σ.irred⟩ hfin hsph
  exact ⟨B, HeightCounting.Blocks.hasSatGL_locRep hσ hB⟩

end GlobalTheory.CuspRep.UnrSat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfMulJ0Decoration
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfMulJ0Decoration
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TopCh

theorem decoRaw_mul_levelIwahori_reduction {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E)
    {n : ℕ} [NeZero n] (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (g z : GL (Fin n) (AfE F E)) (hz : z ∈ J0 hc n ST) :
    decoRaw ST SG (g * z) = (decoRaw ST SG g).act 1 (redG hc n ST SG ⟨z, hz⟩)⁻¹ := by
  have h := decoRaw_rawSm hc ST SG 1 (⟨z, hz⟩⁻¹ : J0 hc n ST) g
  rw [map_one, map_inv] at h
  have e : Formalism.UG.bc (iA F E) ((1 : URat hc n) : GL (Fin n) E) * g *
      (((⟨z, hz⟩⁻¹ : J0 hc n ST) : J0 hc n ST) : GL (Fin n) (AfE F E))⁻¹ = g * z := by
    simp
  rw [e] at h
  exact h

set_option trace.Meta.synthInstance true in
theorem isPtOf_mul_J0 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (g z : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q) (h : GLG (E := E) (n := n) (SG := SG)), (IsPtOf hc g p → IsPtOf hc (g * z) p' → ((∃ hz : z ∈ J0 hc n ST, redG hc n ST SG ⟨z, hz⟩ = h⁻¹) ↔ p'.deco = ((1, h) : UF E n × GLG (E := E) (n := n) (SG := SG)) • p.deco)) ∧ (Q = ∅ → IsPtOf hc g p → ∀ hz : z ∈ J0 hc n ST, redG hc n ST SG ⟨z, hz⟩ = h⁻¹ → IsPtOf hc (g * z) (((1, h, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p)) ∧ (Q = ∅ → g ∈ UAd hc n → ∃ q : DecoF E n ST SG Q, IsPtOf hc g q) := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q g z p p' h
  refine ⟨fun hp hp' => ⟨?_, fun he => ?_⟩, fun hQ hp hz hr => ?_, fun hQ hg => ?_⟩
  · rintro ⟨hz, hr⟩
    apply Subtype.ext
    have h1 := decoRaw_mul_levelIwahori_reduction hc ST SG g z hz
    rw [hr, inv_inv, (near_of_isPtOf hp 0).deco, (near_of_isPtOf hp' 0).deco] at h1
    exact h1
  · have hx : decoRaw ST SG (g * z) = (decoRaw ST SG g).act 1 h := by
      rw [(near_of_isPtOf hp 0).deco, (near_of_isPtOf hp' 0).deco, he]
      rfl
    obtain ⟨hJ, hr⟩ := mem_congruence_of_action hc ST SG hp'.uni hp.uni h hx
    have e : (g * z)⁻¹ * g = z⁻¹ := by group
    have hz : z ∈ J0 hc n ST := by
      have h1 := inv_mem hJ
      rwa [e, inv_inv] at h1
    refine ⟨hz, ?_⟩
    have e' : (⟨(g * z)⁻¹ * g, hJ⟩ : J0 hc n ST) = (⟨z, hz⟩ : J0 hc n ST)⁻¹ := Subtype.ext e
    rw [e', map_inv] at hr
    rw [← hr, inv_inv]
  · refine (GlobalTheory.Mem.Col2.PtDeco.isPtOf_iff_decoRaw F E hc n ST SG Q (g * z) _ hQ).2
      ⟨mul_mem hp.uni (congruence_le_adelic_unitary hc n ST hz), ?_⟩
    have h1 := decoRaw_mul_levelIwahori_reduction hc ST SG g z hz
    rw [hr, inv_inv, (near_of_isPtOf hp 0).deco] at h1
    exact h1.symm
  · obtain ⟨q, hq⟩ := exists_near (ST := ST) (SG := SG) (Q := Q) hc 0 hg
    exact ⟨q, (GlobalTheory.Mem.Col2.PtDeco.isPtOf_iff_decoRaw F E hc n ST SG Q g q hQ).2 ⟨hg, hq.deco.symm⟩⟩

end GlobalTheory.Mem.Col2.TopCh

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfMulJ0DecorationStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPtOf_mul_J0_decoration : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (g z : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q) (h : GLG (E := E) (n := n) (SG := SG)), (IsPtOf hc g p → IsPtOf hc (g * z) p' → ((∃ hz : z ∈ J0 hc n ST, redG hc n ST SG ⟨z, hz⟩ = h⁻¹) ↔ p'.deco = ((1, h) : UF E n × GLG (E := E) (n := n) (SG := SG)) • p.deco)) ∧ (Q = ∅ → IsPtOf hc g p → ∀ hz : z ∈ J0 hc n ST, redG hc n ST SG ⟨z, hz⟩ = h⁻¹ → IsPtOf hc (g * z) (((1, h, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p)) ∧ (Q = ∅ → g ∈ UAd hc n → ∃ q : DecoF E n ST SG Q, IsPtOf hc g q) := by
  exact @GlobalTheory.Mem.Col2.TopCh.isPtOf_mul_J0
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightContragredientExistsUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightContragredientExistsUnique
namespace GlobalTheory.WtDual

section alg

open NumberField ReciprocityTheory.Aut Formalism.AUTREP

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

local notation3 "L⁺" => maximalRealSubfield L

theorem exists_finite_place : Nonempty (IsDedekindDomain.HeightOneSpectrum (𝓞 L⁺)) := by
  obtain ⟨I, hbot, htop⟩ := Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top.mp
    (NumberField.RingOfIntegers.not_isField L⁺)
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I htop.ne
  exact ⟨⟨M, hM.isPrime, fun h => by
    rw [h] at hIM
    exact hbot.ne' (le_bot_iff.mp hIM)⟩⟩

theorem nontrivial_finiteAdeles : Nontrivial (AFplus L) := by
  obtain ⟨v⟩ := exists_finite_place L
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have := congrArg (evalAt L v) h
  rw [map_zero, map_one] at this
  exact zero_ne_one this

theorem nontrivial_adeles : Nontrivial (AL L) := by
  haveI := nontrivial_finiteAdeles L
  exact Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left _ _ _
    (algebraMap (L⁺) (AFplus L)).injective

theorem includeLeft_injective :
    Function.Injective (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) := by
  haveI := nontrivial_adeles L
  exact (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L).injective

variable {L n}

theorem mem_rationalUnitaryGroup_of_matrix_match (γ : GQ L n) (γ₀ : GL (Fin n) L)
    (hm : (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom)) : γ₀ ∈ GQ0 L n := by
  have hγ : ((γ : GAf L n) : GL (Fin n) (AL L)) ∈ (GQ0 L n).map (Matrix.GeneralLinearGroup.map
      (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L)) := γ.2
  obtain ⟨γ₁, h₁, he⟩ := hγ
  have hmat : (γ₀ : Matrix (Fin n) (Fin n) L) = (γ₁ : Matrix (Fin n) (Fin n) L) := by
    ext i j
    apply includeLeft_injective L
    have e1 := congrFun (congrFun hm i) j
    have e2 := congrArg (fun g : GL (Fin n) (AL L) => (g : Matrix (Fin n) (Fin n) (AL L)) i j) he
    simp only [Matrix.map_apply] at e1 e2
    rw [← e1, ← e2]
    rfl
  rw [show γ₀ = γ₁ from Units.ext hmat]
  exact h₁

theorem match_inv (γ : GQ L n) (γ₀ : GL (Fin n) L)
    (h : (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom)) :
    ((((γ⁻¹ : GQ L n) : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      ((γ₀⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) := by
  have hm : ((γ : GAf L n) : GL (Fin n) (AL L)) =
      Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) γ₀ :=
    Units.ext h
  have : (((γ⁻¹ : GQ L n) : GAf L n) : GL (Fin n) (AL L)) =
      Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) γ₀⁻¹ := by
    rw [map_inv, ← hm]
    rfl
  rw [this]
  rfl

theorem inv_entry (γ₀ : GL (Fin n) L) (hγ : γ₀ ∈ GQ0 L n) (k l : Fin n) :
    ((γ₀⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) k l =
      (IsCMField.complexConj L : L →+* L) ((γ₀ : Matrix (Fin n) (Fin n) L) l k) := by
  have h1 : ((γ₀⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      conjT (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L) :=
    Units.inv_eq_of_mul_eq_one_right hγ
  rw [h1]
  rfl

theorem isAlgWeight_dual (a : Formalism.L2.NG.AlgWt L n) : IsAlgWeight L n a.ρ.dual := by
  obtain ⟨hfd, ι, _, _, b, P, hP⟩ := a.alg
  refine ⟨inferInstance, ι, inferInstance, inferInstance, b.dualBasis,
    fun i j => MvPolynomial.rename
      (fun p : (L →+* ℂ) × Fin n × Fin n => (ComplexEmbedding.conjugate p.1, p.2.2, p.2.1)) (P j i), ?_⟩
  intro γ γ₀ h
  have hinv := hP γ⁻¹ γ₀⁻¹ (match_inv γ γ₀ h)
  have hγ := mem_rationalUnitaryGroup_of_matrix_match γ γ₀ h
  have e : LinearMap.toMatrix b.dualBasis b.dualBasis (a.ρ.dual γ) =
      Matrix.transpose (LinearMap.toMatrix b b (a.ρ γ⁻¹)) := by
    rw [Representation.dual_apply, LinearMap.toMatrix_transpose]
  rw [e, hinv]
  ext i j
  change MvPolynomial.eval (fun p : (L →+* ℂ) × Fin n × Fin n =>
      p.1 (((γ₀⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)) (P j i) =
    MvPolynomial.eval (fun p : (L →+* ℂ) × Fin n × Fin n => p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2))
      (MvPolynomial.rename (fun p : (L →+* ℂ) × Fin n × Fin n =>
        (ComplexEmbedding.conjugate p.1, p.2.2, p.2.1)) (P j i))
  rw [MvPolynomial.eval_rename]
  refine congrArg (fun f => MvPolynomial.eval f (P j i)) (funext fun p => ?_)
  simp only [Function.comp_apply]
  rw [inv_entry γ₀ hγ, ComplexEmbedding.conjugate_coe_eq]
  exact IsCMField.complexEmbedding_complexConj L p.1 _

end alg

end GlobalTheory.WtDual

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.WtDual

theorem dual_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : ρ.IsIrreducible) : ρ.dual.IsIrreducible := by
  have hnt : Nontrivial V := by
    by_contra hs
    rw [not_nontrivial_iff_subsingleton] at hs
    obtain ⟨S, T, hST⟩ := (hρ : IsSimpleOrder _).toNontrivial.exists_pair_ne
    exact hST (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  have hntD : Nontrivial (Module.Dual ℂ V) := inferInstance
  refine { toNontrivial := ⟨⟨⊥, ⊤, fun h => ?_⟩⟩, eq_bot_or_eq_top := fun U => ?_ }
  · have h1 := congrArg Subrepresentation.toSubmodule h
    exact (bot_ne_top : (⊥ : Submodule ℂ (Module.Dual ℂ V)) ≠ ⊤) h1
  · let C : Subrepresentation ρ :=
      { toSubmodule := U.toSubmodule.dualCoannihilator
        apply_mem_toSubmodule := fun g v hv => by
          rw [Submodule.mem_dualCoannihilator] at hv ⊢
          intro φ hφ
          have h2 := hv _ (U.apply_mem_toSubmodule g⁻¹ hφ)
          simp [Representation.dual_apply] at h2
          exact h2 }
    rcases hρ.eq_bot_or_eq_top C with hC | hC
    · right
      apply Subrepresentation.toSubmodule_injective
      have hC' : U.toSubmodule.dualCoannihilator = ⊥ := congrArg Subrepresentation.toSubmodule hC
      show U.toSubmodule = ⊤
      rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := U.toSubmodule), hC', Submodule.dualAnnihilator_bot]
    · left
      apply Subrepresentation.toSubmodule_injective
      have hC' : U.toSubmodule.dualCoannihilator = ⊤ := congrArg Subrepresentation.toSubmodule hC
      show U.toSubmodule = ⊥
      rw [eq_bot_iff]
      intro φ hφ
      rw [Submodule.mem_bot]
      ext v
      have hv : v ∈ U.toSubmodule.dualCoannihilator := by rw [hC']; exact Submodule.mem_top
      exact (Submodule.mem_dualCoannihilator _).1 hv φ hφ

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def dualWt (a : NG.AlgWt L n) : NG.AlgWt L n where
  W := Module.Dual ℂ a.W
  ρ := a.ρ.dual
  alg := isAlgWeight_dual a
  irr := by
    haveI := a.alg.1
    exact dual_isIrreducible a.ρ a.irr

theorem isDual_dualWt (a : NG.AlgWt L n) : a.IsDual (dualWt a) := by
  refine ⟨Module.Dual.eval ℂ a.W, ?_, ?_⟩
  · intro h0
    have hnt : Nontrivial a.W := by
      by_contra hs
      rw [not_nontrivial_iff_subsingleton] at hs
      obtain ⟨S, T, hST⟩ := (a.irr : IsSimpleOrder _).toNontrivial.exists_pair_ne
      exact hST (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
    obtain ⟨x, hx⟩ := exists_ne (0 : a.W)
    obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ a.W, f x ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hx ((Module.forall_dual_apply_eq_zero_iff ℂ x).mp hc)
    have h1 := LinearMap.congr_fun (LinearMap.congr_fun h0 x) f
    simp only [Module.Dual.eval_apply, LinearMap.zero_apply] at h1
    exact hf h1
  · intro γ x (y : Module.Dual ℂ a.W)
    show y (a.ρ γ⁻¹ (a.ρ γ x)) = y x
    rw [Representation.inv_self_apply]

theorem isDual_iff_iso (a b b' : NG.AlgWt L n) (hab : a.IsDual b) : a.IsDual b' ↔ b.Iso b' := by
  haveI := a.alg.1; haveI := b.alg.1; haveI := b'.alg.1
  haveI := a.irr; haveI := b.irr; haveI := b'.irr
  constructor
  · rintro ⟨C, hC0, hC⟩
    obtain ⟨B, hB0, hB⟩ := hab
    exact PI.UnitaryGroupMassFormula.AlgWtDualUniq.dual_unique (ρa := a.ρ) B hB hB0 C hC hC0
  · rintro ⟨T, hT⟩
    obtain ⟨B, hB0, hB⟩ := hab
    refine ⟨B.compl₂ T.symm.toLinearMap, fun h => hB0 ?_, fun γ x y => ?_⟩
    · ext x y
      have := LinearMap.congr_fun (LinearMap.congr_fun h x) (T y)
      simpa using this
    · have e : T.symm (b'.ρ γ y) = b.ρ γ (T.symm y) := by
        apply T.injective
        rw [hT]
        simp
      simp only [LinearMap.compl₂_apply, LinearEquiv.coe_coe]
      rw [e, hB]

theorem isDual_of_iso {a a' b : NG.AlgWt L n} (h : a.Iso a') (hab : a.IsDual b) : a'.IsDual b := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨B, hB0, hB⟩ := hab
  refine ⟨B.comp T.symm.toLinearMap, fun h => hB0 ?_, fun γ x y => ?_⟩
  · ext x y
    have := LinearMap.congr_fun (LinearMap.congr_fun h (T x)) y
    simpa using this
  · have e : T.symm (a'.ρ γ x) = a.ρ γ (T.symm x) := by
      apply T.injective
      rw [hT]
      simp
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [e, hB]

theorem hwAt_of_iso {a a' : NG.AlgWt L n} (h : a.Iso a') {τ : L →+* ℂ} {lam : Fin n → ℤ} (hw : a.HWAt τ lam) :
    a'.HWAt τ lam := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨ι, hfin, hdec, b, P, hP, v, hv0, hv⟩ := hw
  refine ⟨ι, hfin, hdec, b.map T, P, fun γ γ₀ hm => ?_, v, hv0, hv⟩
  rw [← hP γ γ₀ hm]
  ext i j
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, Module.Basis.map_apply, Module.Basis.map_repr,
    LinearEquiv.trans_apply, ← hT, LinearEquiv.symm_apply_apply]

end GlobalTheory.WtDual

theorem GlobalTheory.algWt_contragredient : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n),
    ∃ b : NG.AlgWt L n, a.IsDual b ∧ (∀ b', a.IsDual b' ↔ b.Iso b') ∧
      ∀ a' : NG.AlgWt L n, a.Iso a' → a'.IsDual b ∧ ∀ τ lam, a.HWAt τ lam → a'.HWAt τ lam := by
  intro L _ _ _ n a
  have hd := GlobalTheory.WtDual.isDual_dualWt a
  exact ⟨GlobalTheory.WtDual.dualWt a, hd, fun b' => GlobalTheory.WtDual.isDual_iff_iso a _ b' hd,
    fun a' h => ⟨GlobalTheory.WtDual.isDual_of_iso h hd, fun τ lam hw => GlobalTheory.WtDual.hwAt_of_iso h hw⟩⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightContragredientExistsUniqueStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algWeight_contragredient_exists_unique : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n), ∃ b : NG.AlgWt L n, a.IsDual b ∧ (∀ b', a.IsDual b' ↔ b.Iso b') ∧ ∀ a' : NG.AlgWt L n, a.Iso a' → a'.IsDual b ∧ ∀ τ lam, a.HWAt τ lam → a'.HWAt τ lam := by
  first | exact @GlobalTheory.algWt_contragredient | exact GlobalTheory.algWt_contragredient | (intros; apply GlobalTheory.algWt_contragredient <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelFamilyCharacterExponent
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelFamilyCharacterExponent
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TopCh

theorem levFam_chr_exp : ∀ {X : Fields} {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 X.E))} (Λ : LevFam X.E X.K n SG), ∃ m : ℕ, 0 < m ∧ ∀ h, Λ.chr h ^ m = 1 := by
  intro X n SG Λ
  have : ∀ w : SG, Finite (𝓞 X.E ⧸ w.1.asIdeal) := fun w => Ideal.finiteQuotientOfFreeOfNeBot _ w.1.ne_bot
  have : Finite ↥Λ.grp := inferInstance
  refine ⟨Nat.card ↥Λ.grp, Nat.card_pos, fun h => ?_⟩
  rw [← map_pow, pow_card_eq_one', map_one]

end GlobalTheory.Mem.Col2.TopCh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelFamilyCharacterExponentStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelFamily_character_exponent : ∀ {X : Fields} {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 X.E))} (Λ : LevFam X.E X.K n SG), ∃ m : ℕ, 0 < m ∧ ∀ h, Λ.chr h ^ m = 1 := by
  first | exact @GlobalTheory.Mem.Col2.TopCh.levFam_chr_exp | exact GlobalTheory.Mem.Col2.TopCh.levFam_chr_exp | (intros; apply GlobalTheory.Mem.Col2.TopCh.levFam_chr_exp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPrimesAwayLevelAndTypePrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPrimesAwayLevelAndTypePrimes
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TwistPrimes

open GlobalTheory.Mem.LevTwist ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1

theorem twist_primes_away : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → (I.Q I.mu0 = ∅) ∧ ∀ (u : B.Word) (a : I.ι), ∀ P ∈ I.Q a, (P ∉ (B.primes X).vT u ∧ P ∉ (B.primes X).vGs ∧ conjPrime₂ P ∉ (B.primes X).vT u ∧ conjPrime₂ P ∉ (B.primes X).vGs ∧ conjPrime₂ P ∉ I.Q a) ∧ X.piT u ∉ P.asIdeal ∧ (B.T u : 𝓞 B.host.F) ∉ (P.under (𝓞 B.host.F)).asIdeal := by
  intro B X I h
  refine ⟨I.twistPrimes_reference_tuple_eq_empty, fun u a P hP => ?_⟩
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  have hg := good_of_mem h (I.Q_subset_SQ a hP)
  have hS := hg.2.2.2
  have hu : (conjPrime₂ P).under (𝓞 B.host.F) = P.under (𝓞 B.host.F) := (under_eq_iff B.host P _).2 (Or.inr rfl)
  have hT : ∀ R : HeightOneSpectrum (𝓞 B.host.E), R.under (𝓞 B.host.F) = P.under (𝓞 B.host.F) →
      ((B.primes X).T u : 𝓞 B.host.E) ∉ R.asIdeal := fun R hR hm => hS (by
    rw [← hR, (ReadTwist.plc_under_eq_iff (F := B.host.F) R (hPr.T_prime u)).2 hm]
    exact h.T_mem u)
  have hpi : ∀ R : HeightOneSpectrum (𝓞 B.host.E), R.under (𝓞 B.host.F) = P.under (𝓞 B.host.F) →
      (B.primes X).piT u ∉ R.asIdeal := fun R hR hm => hT R hR (by
    rw [← hPr.piT_norm u]; exact Ideal.mul_mem_right _ _ hm)
  have h0 : (B.primes X).piT u ≠ 0 := fun e => by
    have := hPr.piT_norm u
    rw [e, zero_mul] at this
    exact (hPr.T_prime u).ne_zero (Nat.cast_eq_zero.1 this.symm)
  have hvT : ∀ R : HeightOneSpectrum (𝓞 B.host.E), R.under (𝓞 B.host.F) = P.under (𝓞 B.host.F) →
      R ∉ (B.primes X).vT u := fun R hR hm => hpi R hR ((mem_divs h0 _).1 hm)
  have hvG : ∀ R : HeightOneSpectrum (𝓞 B.host.E), R.under (𝓞 B.host.F) = P.under (𝓞 B.host.F) →
      R ∉ (B.primes X).vGs := fun R hR hm => hS (by rw [← hR]; exact plc_mem h hm)
  refine ⟨⟨hvT P rfl, hvG P rfl, hvT _ hu, hvG _ hu, fun hc => ?_⟩, hpi P rfl, fun hm => hT P rfl ?_⟩
  · have e := (good_of_mem h (I.Q_subset_SQ a hc)).1
    rw [hu, hg.1] at e
    exact conjP_ne B.host ((GoodPlace.goodPl_under_iff _ B.host _ P).1 hg.2).1 e.symm
  · rw [← map_natCast (algebraMap (𝓞 B.host.F) (𝓞 B.host.E))]
    exact hm

end GlobalTheory.Mem.Col2.TwistPrimes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPrimesAwayLevelAndTypePrimesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPrimes_away_level_and_type_primes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → (I.Q I.mu0 = ∅) ∧ ∀ (u : B.Word) (a : I.ι), ∀ P ∈ I.Q a, (P ∉ (B.primes X).vT u ∧ P ∉ (B.primes X).vGs ∧ conjPrime₂ P ∉ (B.primes X).vT u ∧ conjPrime₂ P ∉ (B.primes X).vGs ∧ conjPrime₂ P ∉ I.Q a) ∧ X.piT u ∉ P.asIdeal ∧ (B.T u : 𝓞 B.host.F) ∉ (P.under (𝓞 B.host.F)).asIdeal := by
  first | exact @GlobalTheory.Mem.Col2.TwistPrimes.twist_primes_away | exact GlobalTheory.Mem.Col2.TwistPrimes.twist_primes_away | (intros; apply GlobalTheory.Mem.Col2.TwistPrimes.twist_primes_away <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockValAe
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockValAe
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

namespace GlobalTheory.BlockVal

private theorem block_val_mul_sqrt_normV_zpow_neg_eq_mul_inv {E : Type} [Field E] [NumberField E]
    (μ η : _root_.Formalism.L2.Host.HChar E) (r : ℕ) (v : HeightOneSpectrum (𝓞 E)) :
    (((_root_.GlobalTheory.GalChar.block μ η r).val v : ℂˣ) : ℂ) * (Real.sqrt (_root_.Formalism.ConjugateSelfDual.normV v) : ℂ) ^ (-(r : ℤ)) =
      (((μ * η⁻¹).val v : ℂˣ) : ℂ) := by
  have hval : (((_root_.GlobalTheory.GalChar.block μ η r).val v : ℂˣ) : ℂ) =
      (((μ * η⁻¹).val v : ℂˣ) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((((r : ℝ) / 2 : ℝ)) : ℂ) :=
    _root_.GlobalTheory.GalChar.block_val μ η r v
  have hN : (_root_.Formalism.ConjugateSelfDual.normV v : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := by
    unfold _root_.Formalism.ConjugateSelfDual.normV
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hne : Ideal.absNorm v.asIdeal ≠ 0 := by
    have := _root_.GlobalTheory.GalChar.absNorm_ne_zero v
    exact_mod_cast this
  have hpos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hne)
  set N : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hNdef
  have hpow : (N : ℂ) ^ ((((r : ℝ) / 2 : ℝ)) : ℂ) = ((Real.sqrt N ^ r : ℝ) : ℂ) := by
    rw [← Complex.ofReal_cpow hpos.le, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul hpos.le]
    congr 2
    ring
  have hs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  rw [hval, hN]
  have hcast : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) = (N : ℂ) := by simp [hNdef]
  rw [hcast, hpow, zpow_neg, zpow_natCast, Complex.ofReal_pow, mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast hs)), mul_one]

theorem _root_.GlobalTheory.BlockVal.block_val_ae : ∀ {E : Type} [Field E] [NumberField E] {K : Type} [Field K] (ε : K →+* ℂ)
    (μ η : _root_.Formalism.L2.Host.HChar E),
    _root_.GlobalTheory.GalChar.AlmostIn ε μ → η.ValuesIn (1 / 2) ε → ∀ {r : ℕ}, Odd r →
    ∀ (μH ηH : _root_.Formalism.L2.NC.HC E),
    μH.χ = (μ : _root_.Neutral.B1.Ideles E →* ℂˣ) → ηH.χ = (η : _root_.Neutral.B1.Ideles E →* ℂˣ) → ∀ᶠ v in Filter.cofinite,
    (μH * ηH⁻¹).At v ((((_root_.GlobalTheory.GalChar.block μ η r).val v : ℂˣ) : ℂ) *
      (Real.sqrt (_root_.Formalism.ConjugateSelfDual.normV v) : ℂ) ^ (-(r : ℤ))) ∧
    ∃ y : K, ε y = (((_root_.GlobalTheory.GalChar.block μ η r).val v : ℂˣ) : ℂ)⁻¹ := by
  intro E _ _ K _ ε μ η hμ hη r hr μH ηH hμH hηH
  have hχ : (μH * ηH⁻¹).χ = ((μ * η⁻¹ : _root_.Formalism.L2.Host.HChar E) : _root_.Neutral.B1.Ideles E →* ℂˣ) := by
    change μH.χ * ηH.χ⁻¹ = _
    rw [hμH, hηH]
    rfl
  have hblock := _root_.GlobalTheory.GalChar.AlmostIn.block hμ hη hr
  unfold _root_.GlobalTheory.GalChar.AlmostIn at hblock
  filter_upwards [hblock, _root_.GlobalTheory.GalChar.unr_ae (μ * η⁻¹)] with v hv hunr
  refine ⟨?_, ?_⟩
  · rw [block_val_mul_sqrt_normV_zpow_neg_eq_mul_inv]
    exact (_root_.GlobalTheory.HeckeUnifVal.at_val_and_unr_iff (μ * η⁻¹) (μH * ηH⁻¹) hχ v).1 hunr
  · obtain ⟨y, hy⟩ := hv
    exact ⟨y⁻¹, by rw [map_inv₀, hy]⟩

end GlobalTheory.BlockVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockValAeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_block_val_at_and_exists_inv_eq : ∀ {E : Type} [Field E] [NumberField E] {K : Type} [Field K] (ε : K →+* ℂ) (μ η : HChar E), AlmostIn ε μ → η.ValuesIn (1 / 2) ε → ∀ {r : ℕ}, Odd r → ∀ (μH ηH : Formalism.L2.NC.HC E), μH.χ = (μ : Ideles E →* ℂˣ) → ηH.χ = (η : Ideles E →* ℂˣ) → ∀ᶠ v in Filter.cofinite, (μH * ηH⁻¹).At v ((((block μ η r).val v : ℂˣ) : ℂ) * (Real.sqrt (normV v) : ℂ) ^ (-(r : ℤ))) ∧ ∃ y : K, ε y = (((block μ η r).val v : ℂˣ) : ℂ)⁻¹ := by
  first | exact @GlobalTheory.BlockVal.block_val_ae | exact GlobalTheory.BlockVal.block_val_ae | (intros; apply GlobalTheory.BlockVal.block_val_ae <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalCondMoveDecoratedLattice
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.TC.ChTw.Match

variable {B : Base} {X : PreX B.toPre}

def LocalCondMoveDecoratedLattice (u : B.Word) (n : ℕ) (s : GA B n) (h : GLG (E := B.fields.E) (n := n) (SG := (B.primes X).vGs)) : Prop :=
  s ∈ Formalism.L2.Herm.UstdAf B.sp.cm n ∧ Formalism.L2.Herm.Carries s (stdLat B.fields.E n) (stdLat B.fields.E n) ∧
  (∀ (P : (B.primes X).vT u) (r j : Fin n), r.1 + 1 = n →
    HasRes P.1 (adAt B.host.F P.1 ((s⁻¹ : GA B n).1 r j)) (if j = r then 1 else 0)) ∧
  ∀ (w : (B.primes X).vGs) (r j : Fin n), HasRes w.1 (adAt B.host.F w.1 ((s⁻¹ : GA B n).1 r j)) ((h w).1 r j)

def LocCQ (Q : Finset (HeightOneSpectrum (𝓞 B.fields.E))) (n : ℕ) (s : GA B n) (θ : GLQ B.fields.E n Q) : Prop :=
  ∀ (P : Q) (r j : Fin n), adAt B.host.F P.1 ((s : Matrix (Fin n) (Fin n) _) r j) =
    algebraMap B.host.E _ ((((θ P)⁻¹ : ↥(GLint B.fields.E n P.1)).1) (Pi.single j 1) r)

end GlobalTheory.Mem.Col2.TC.ChTw.Match
end
end
