module

public import Formalism.AdmissibleDesigns.ExistsWildInertiaCyclotomicGenerator
public import Formalism.AdmissibleDesigns.SelfGood
public import Formalism.AdmissibleDesigns.HigherColumnInvariantsBound

@[expose] public section

section -- merged from Formalism.AdmissibleDesigns.DisplayForms
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Finset Classical

namespace Formalism.MainNotions.N.K.Topo

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
  (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem topoHyps
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (u : ℤ_[D.nd.l i]ˣ)
    (hcyc : ((cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) g0 : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) =
      1 + (D.nd.l i : ℤ_[D.nd.l i]) ^ D.nd.s0 i * (u : ℤ_[D.nd.l i])) :
    letI := fracTopology (D.nd.O i); letI := rTopology (D.nd.O i) Dd.R';
    Function.Injective (algebraMap ℤ_[D.nd.l i] (D.nd.O i)) ∧ PadicCoeff (D.nd.l i) (D.nd.O i) ∧
      FracTop (D.nd.O i) ∧ IsFGTop (D.nd.O i) Dd.R' ∧ IsCycG (D.nd.l i) (epsU D.nd i) ∧
      (Continuous fun g : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) => uElt Dd.r Dd.χ g) ∧
      (∀ v, IsPlaceOver (Formalism.MainNotions.N.K.Av (D := D) v) v) ∧
      (D.nd.l i ≠ 2 ∨ InfinitePlace.nrRealPlaces D.host.E = 0) ∧
      1 ≤ D.nd.s0 i ∧ (D.nd.l i = 2 → 2 ≤ D.nd.s0 i) ∧
      ((epsU D.nd i g0 : (D.nd.O i)ˣ) : D.nd.O i) - 1 =
        ((D.nd.l i : ℕ) : D.nd.O i) ^ D.nd.s0 i * ((yU i u : (D.nd.O i)ˣ) : D.nd.O i) ∧
      (∀ w ∈ Formalism.MainNotions.N.K.rowsN i dc, (Formalism.MainNotions.N.K.Aw i dc w).valuation ((D.nd.l i : ℕ) : D.nd.Om) < 1 ∧
        IsPlaceOver (Formalism.MainNotions.N.K.Aw i dc w) (Formalism.MainNotions.N.K.plOf i dc w)) := by
  refine ⟨?_, padicCoeff_O i, fracTop_O i, fgTop_RD i r π g0 eB e₁ s Dd hD, ?_, uElt_cont i r π g0 eB e₁ s Dd hD hc,
    av_over, ?_, one_le_localLevel i, restNLevelExponent_of_two i, ?_, rows_over i dc⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    have h1 : algebraMap ℤ_[D.nd.l i] (D.nd.O i)
        ((PadicInt.unitCoeff h0 : ℤ_[D.nd.l i]) * (D.nd.l i : ℤ_[D.nd.l i]) ^ x.valuation) = 0 := by
      rw [← PadicInt.unitCoeff_spec h0]
      exact hx
    rw [map_mul, map_pow, map_natCast] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact ((PadicInt.unitCoeff h0).isUnit.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i))).ne_zero h
    · exact (padicCoeff_O i).p_ne (pow_eq_zero_iff'.mp h).1
  · apply isCyc_eps <;> assumption
  · apply l_or_noReal <;> assumption
  · have h2 : ((epsU D.nd i g0 : (D.nd.O i)ˣ) : D.nd.O i) = algebraMap ℤ_[D.nd.l i] (D.nd.O i)
        ((cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) g0 : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) := rfl
    rw [h2, hcyc]
    simp [yU]

end Formalism.MainNotions.N.K.Topo

end
end

section -- merged from Formalism.AdmissibleDesigns.BlockTwistedCyclotomic
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.ShaT

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K
open Formalism.MainNotions.N.K.QS Formalism.RepresentationBoundsCohomology.FIN
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Gen

variable {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]

def selRep2 (ρ : Representation R G M) {V VS : Type} (J : V → Subgroup G) (JS : VS → Subgroup G)
    (D : ℕ → Subgroup G) (F : ∀ w, Submodule R (H1z (resRep ρ (D w)))) (P : Finset ℕ) : Submodule R (H1z ρ) :=
  (lcH1 ρ ⊓ (⨅ v, unrH1 ρ (J v)) ⊓ ⨅ v, unrH1 ρ (JS v)) ⊓ ⨅ w ∈ P, (F w).comap (resH1 ρ (D w))

def Fsha (ρ : Representation R G M) (D : ℕ → Subgroup G) (Iq : ∀ w, Subgroup (D w)) (qs : Finset ℕ) (w : ℕ) :
    Submodule R (H1z (resRep ρ (D w))) :=
  if w ∈ qs then unrH1 (resRep ρ (D w)) (Iq w) else ⊥

def RepIso {M' : Type} [AddCommGroup M'] [Module R M'] (ρ : Representation R G M) (ρ' : Representation R G M') :
    Prop :=
  ∃ φ : M ≃ₗ[R] M', ∀ g m, φ (ρ g m) = ρ' g (φ m)

end Gen

def CoefChange (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] (ψ : G →* ℤ_[l]ˣ) {V VS : Type} (J : V → Subgroup G)
    (JS : VS → Subgroup G) (D : ℕ → Subgroup G) (Iq : ∀ w, Subgroup (D w)) (qs P : Finset ℕ),
    let ψO : G →* Oˣ := (Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp ψ
    let ρO := Formalism.GaloisCohomology.scalRep (KO O) ψO
    let ρZ := Formalism.GaloisCohomology.scalRep (Formalism.GaloisCohomology.QZ l) ψ
    Module.length O ↥(selRep2 ρO J JS D (Fsha ρO D Iq qs) P) ≤
      Module.length O (O ⧸ Ideal.span {((l : ℕ) : O)}) * Module.length ℤ_[l] ↥(selRep2 ρZ J JS D (Fsha ρZ D Iq qs) P)

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

def Pall : Finset ℕ := rowsN i dc ∪ qsN i dc ∪ univ.image (colIdx i dc)

def cycE : GE D.nd →* ℤ_[D.nd.l i]ˣ := cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i)

def qzE (e : ℕ) : Representation ℤ_[D.nd.l i] (GE D.nd) (Formalism.GaloisCohomology.QZ (D.nd.l i)) :=
  Formalism.GaloisCohomology.scalRep (Formalism.GaloisCohomology.QZ (D.nd.l i)) (cycE i ^ (-(e : ℤ)))

def koE (e : ℕ) : Representation (D.nd.O i) (GE D.nd) (KO (D.nd.O i)) :=
  Formalism.GaloisCohomology.scalRep (KO (D.nd.O i)) ((Units.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i)).toMonoidHom).comp
    (cycE i ^ (-(e : ℤ))))

def selZ (e : ℕ) : Submodule ℤ_[D.nd.l i] (H1z (qzE i e)) :=
  selRep2 (qzE i e) (Io i) (IS i) (decs D.host.E (Aw i dc)) (Fsha (qzE i e) (decs D.host.E (Aw i dc)) (I i dc) (qsN i dc))
    (Pall i dc)

def BlockTwistedCyclotomic (c : Fin (D.R.t + 1)) : Prop :=
  RepIso (uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ) (koE i ((c : ℕ) - 1))

def ZlSha (e : ℕ) : Prop :=
  Module.length ℤ_[D.nd.l i] ↥(selZ i dc e) ≤ Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ)

end Rec

end Formalism.MainNotions.N.K.ShaT

end
end

section -- merged from Formalism.AdmissibleDesigns.TrCMemZ1D
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TB

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR

section Core

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {A T' G : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]

def TBClause (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (Dw : Subgroup G) (ℓ cB cT deg : ℕ)
    (Hc F : Submodule O (H1z (resRep (uRep O (M := M) r χ) Dw))) : Prop :=
  F ≤ Hc ∧ cT ≤ cB ∧
    (∀ ψ : Ymod r χ E →ₗ[O] M, (∀ g ∈ Dw, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y) →
      ∀ z : coZ1s (resRep (uRep O (M := M) r χ) Dw),
        (∀ g : Dw, (z : Dw → M) g = ψ (yY r χ E (g : G))) →
        ((ℓ : O) ^ cT) • (Submodule.mkQ _ z : H1z (resRep (uRep O (M := M) r χ) Dw)) ∈ F) ∧
    Module.length O (↥(Hc ⊓ divBy F ((ℓ : O) ^ cT)) ⧸
        F.comap (Hc ⊓ divBy F ((ℓ : O) ^ cT)).subtype) ≤
      Module.length O (O ⧸ Ideal.span {(ℓ : O)}) * (cT : ℕ∞) * ((deg : ℕ∞) + 1)

def YLoc (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (Dw : Subgroup G) [TopologicalSpace Dw] : Prop :=
  ∀ ψ : Ymod r χ E →ₗ[O] M, (∀ g ∈ Dw, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y) →
    IsLocallyConstant fun g : Dw => ψ (yY r χ E (g : G))

end Core

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    (O : Type) [CommRing O] [Algebra O LL]

structure TwLat (e : ℕ) where
  V : Type
  [acg : AddCommGroup V]
  [mLL : Module LL V]
  [mQ : Module Qp V]
  [tQ : IsScalarTower Qp LL V]
  [mO : Module O V]
  [tO : IsScalarTower O LL V]
  [top : TopologicalSpace V]
  [cadd : ContinuousAdd V]
  [csm : ContinuousConstSMul LL V]
  [imt : IsModuleTopology LL V]
  [fd : FiniteDimensional LL V]
  ρ : Representation LL G V
  L : Lattice (O := O) ρ
  cont : ∀ x, Continuous fun g => ρ g x
  mat : IsMatLat (ρ := ρ) L.T (epsTw PD e)

attribute [instance] TwLat.acg TwLat.mLL TwLat.mQ TwLat.tQ TwLat.mO TwLat.tO TwLat.top TwLat.cadd TwLat.csm
  TwLat.imt TwLat.fd

structure YtLat where
  V : Type
  [acg : AddCommGroup V]
  [mLL : Module LL V]
  [mQ : Module Qp V]
  [tQ : IsScalarTower Qp LL V]
  [mO : Module O V]
  [tO : IsScalarTower O LL V]
  [top : TopologicalSpace V]
  [cadd : ContinuousAdd V]
  [csm : ContinuousConstSMul LL V]
  [imt : IsModuleTopology LL V]
  [fd : FiniteDimensional LL V]
  ρ : Representation LL G V
  L : Lattice (O := O) ρ
  cont : ∀ x, Continuous fun g => ρ g x
  p : V →ₗ[LL] LL
  p_inv : ∀ g v, p (ρ g v) = p v
  p_int : ∀ v ∈ L.T, p v ∈ Set.range (algebraMap O LL)
  e₀ : V
  e₀_mem : e₀ ∈ L.T
  p_e₀ : p e₀ = 1

attribute [instance] YtLat.acg YtLat.mLL YtLat.mQ YtLat.tQ YtLat.mO YtLat.tO YtLat.top YtLat.cadd YtLat.csm
  YtLat.imt YtLat.fd

variable {PD LL O}

def YtCrys (Y : YtLat (G := G) (Qp := Qp) LL O) (J : (K →ₐ[Qp] LL) → Set ℤ) : Prop :=
  IsCrys PD Y.ρ ∧ ∀ τ, JumpsInV PD Y.ρ τ (J τ)

end Local

section Transport

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {O' : Type} [CommRing O'] (σ : O' ≃+* O)
    {A T' GG : Type} [Ring A] [Algebra O' A] [CommRing T'] [Algebra T' A] [Group GG]
    {M : Type} [AddCommGroup M] [Module A M] [Module O' M] [SMulCommClass A O' M]
    (r : GG →* A) (χ : GG →* T'ˣ) (E : A) (Dw : Subgroup GG) (eG : Dw ≃* G)


variable (PD LL O M) in
structure CoefDict (e : ℕ) where
  Ce : TwLat PD LL O e
  u : M ≃+ (Ce.V ⧸ Ce.L.T)
  u_smul : ∀ (a : O') (m : M), u (a • m) = σ a • u m
  u_act : ∀ (g : Dw) (m : M), u (uElt r χ (g : GG) • m) = actD Ce.L (eG g) (u m)

def PsiExt {e : ℕ} (Y : YtLat (G := G) (Qp := Qp) LL O) (Cd : CoefDict PD LL O σ M r χ Dw eG e) : Prop :=
  ∀ ψ : Ymod r χ E →ₗ[O'] M, (∀ g ∈ Dw, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y) →
    ∃ φ : Y.V →ₗ[O] (Cd.Ce.V ⧸ Cd.Ce.L.T),
      (∀ g, ∀ y ∈ Y.L.T, Y.p y = 0 → φ (Y.ρ g y) = actD Cd.Ce.L g (φ y)) ∧
      ∀ g : Dw, φ (Y.ρ (eG g) Y.e₀ - Y.e₀) = Cd.u (ψ (yY r χ E (g : GG)))

variable {σ r χ E Dw eG}

def trC {e : ℕ} (Cd : CoefDict PD LL O σ M r χ Dw eG e) (z : Dw → M) : G → Cd.Ce.V ⧸ Cd.Ce.L.T :=
  fun g => Cd.u (z (eG.symm g))

theorem trC_hf {e t cB : ℕ} {I : Subgroup G} {J : (K →ₐ[Qp] LL) → Set ℤ}
    (hTB : Formalism.MainNotions.N.TBAt PD (O := O) I J t cB) (het : e < t)
    (Y : YtLat (G := G) (Qp := Qp) LL O) (hY : YtCrys (PD := PD) Y J)
    (Cd : CoefDict PD LL O σ M r χ Dw eG e) (hψ : PsiExt σ r χ E Dw eG Y Cd)
    (ψ : Ymod r χ E →ₗ[O'] M) (hψe : ∀ g ∈ Dw, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y)
    (z : Dw → M) (hz : ∀ g : Dw, z g = ψ (yY r χ E (g : GG))) :
    ((PD.p : O) ^ cB) • trC Cd z ∈ HfD PD Cd.Ce.L := by
  obtain ⟨φ, hφ1, hφ2⟩ := hψ ψ hψe
  have hfun : trC Cd z = fun g => φ (Y.ρ g Y.e₀ - Y.e₀) := by
    funext g
    have h := hφ2 (eG.symm g)
    rw [MulEquiv.apply_symm_apply] at h
    rw [h]
    simp only [trC, hz]
  rw [hfun]
  exact hTB.1 Y.V Y.ρ Y.L Y.cont hY.1 hY.2 Y.p Y.p_inv Y.p_int Y.e₀ Y.e₀_mem Y.p_e₀ e het
    Cd.Ce.V Cd.Ce.ρ Cd.Ce.L Cd.Ce.cont Cd.Ce.mat φ hφ1

theorem trC_mem_Z1D {e : ℕ} (Cd : CoefDict PD LL O σ M r χ Dw eG e) [TopologicalSpace Dw]
    (heG : Continuous eG.symm) (z : coZ1s (resRep (uRep O' (M := M) r χ) Dw))
    (hz : IsLocallyConstant (z : Dw → M)) (c : O) : c • trC Cd (z : Dw → M) ∈ divisibleCocycles Cd.Ce.L := by
  apply Submodule.smul_mem
  show IsLocallyConstant (trC Cd (z : Dw → M)) ∧ ∀ g h, trC Cd (z : Dw → M) (g * h) =
    trC Cd (z : Dw → M) g + actD Cd.Ce.L g (trC Cd (z : Dw → M) h)
  refine ⟨(hz.comp_continuous heG).comp Cd.u, fun g h => ?_⟩
  have hc : (z : Dw → M) (eG.symm g * eG.symm h) = (z : Dw → M) (eG.symm g) +
      resRep (uRep O' (M := M) r χ) Dw (eG.symm g) ((z : Dw → M) (eG.symm h)) := z.2 _ _
  simp only [trC, map_mul]
  rw [hc, map_add (f := _)]
  congr 1
  have hu := Cd.u_act (eG.symm g) ((z : Dw → M) (eG.symm h))
  rw [MulEquiv.apply_symm_apply] at hu
  exact hu

end Transport

section Record

open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

abbrev Dw (n : ℕ) : Subgroup (GE D.nd) := (Aw i dc n).decompositionSubgroup D.host.E

abbrev Mc (c : Fin (D.R.t + 1)) : Type := blockRestrictedRepresentationType (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R) Dd.ρk c

abbrev ρc (c : Fin (D.R.t + 1)) (n : ℕ) : Representation (D.nd.O i) (Dw i dc n) (Mc i Dd c) :=
  resRep (uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ) (Dw i dc n)

def Hc (c : Fin (D.R.t + 1)) (n : ℕ) : Submodule (D.nd.O i) (H1z (ρc i dc Dd c n)) :=
  Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (ρc i dc Dd c n)

def Fc (c : Fin (D.R.t + 1)) (n : ℕ) : Submodule (D.nd.O i) (H1z (ρc i dc Dd c n)) :=
  if (c : ℕ) = 1 then
    Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (ρc i dc Dd c n) ⊓
      unrH1 (ρc i dc Dd c n) ((Ine (F := D.host.E) (Aw i dc n)).subgroupOf (Dw i dc n))
  else ⊥

def TBTarget (cB : ℕ) : Prop :=
  ∀ n ∈ rowsN i dc, ∀ c : Fin (D.R.t + 1), 1 ≤ (c : ℕ) →
    TBClause (Mc i Dd c) Dd.r Dd.χ Dd.E (Dw i dc n) (D.nd.l i) cB cB (Formalism.MainNotions.N.locDeg D.host.E (plOf i dc n))
      (Hc i dc Dd c n) (Fc i dc Dd c n)

theorem mem_plSet {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    w ∈ plSet i dc := by
  simp only [plSet, Finset.mem_union]
  exact Or.inl ((dc.cover w).2 hw)

theorem Dw_idx {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    Dw i dc (idx i dc w) = Dec (F := D.host.E) (D.nd.plOm.1 w) := by
  have hm := mem_plSet i dc hw
  have hpl : plOf i dc (idx i dc w) = w := by
    simp [plOf, idx, hm]
  simp only [Dw, Aw, hpl, ReciprocityTheory.Gal.Dec]

def eW {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    ↥(Dw i dc (idx i dc w)) ≃* Br.G D.nbr i w hw :=
  (MulEquiv.subgroupCongr (Dw_idx i dc hw)).trans (D.nbr i w hw).e

def Jr {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) :
    (Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) → Set ℤ :=
  fun τ => {a | IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r π))) τ a}

def selfO {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    D.nd.O i ≃+* ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL) :=
  (D.nbr i w hw).eO

def TBDict : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.row →
    ∀ c : Fin (D.R.t + 1), 1 ≤ (c : ℕ) →
      ∃ (Y : YtLat (G := Br.G D.nbr i w hw) (Qp := ℚ_[D.nd.l i]) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
          ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL))
        (Cd : CoefDict (Br.PD D.loc D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
          ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL) (selfO i hw) (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w))
          (eW i dc hw) ((c : ℕ) - 1)),
        YtCrys (PD := Br.PD D.loc D.nbr i w hw) Y (Jr i r π (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)) ∧
        PsiExt (selfO i hw) Dd.r Dd.χ Dd.E (Dw i dc (idx i dc w)) (eW i dc hw) Y Cd ∧
        YLoc (O := D.nd.O i) (Mc i Dd c) Dd.r Dd.χ Dd.E (Dw i dc (idx i dc w))

end Record

end Formalism.MainNotions.N.K.TB

end
end
