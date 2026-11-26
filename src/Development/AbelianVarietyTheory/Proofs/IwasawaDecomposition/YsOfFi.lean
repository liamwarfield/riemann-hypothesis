module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelGroupWithCharacterAtTypePlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueCharacterArtinTameGaloisEqTameValue

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.YsOfFi
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.HeightCounting.SerCopy

def NoOff (D : D7) : Prop := ∀ i j b, ¬ (1 ≤ j ∧ j ≤ D.R.m) → Subsingleton (D.nexp.Fm i j b)

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def HkAd (R : RealDat3 D A3 Ks) (Sb : Finset (PlE D.host))
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (Fin (R.nW (idxOf D j)) → D.what₂.LL)) : Prop :=
  ∀ j k P α Rr, 1 ≤ j → j ≤ D.R.m → HkDat R Sb (idxOf D j) k P α Rr → ∀ x : Fin (R.nW (idxOf D j)) → D.what₂.LL,
    (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) (hL j k P x)) =
      hkNorm R (idxOf D j) k P • Mult.heckeOn (R.MW (idxOf D j) (sg0 D A3.A)) Rr
        ((R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) x))

variable {R : RealDat3 D A3 Ks} {cG : G0 R.Pg D.R.r ≃* G0g D.nd}

def ysOf {kKs : Ks →+* ↥D.LL0} {hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x} {cf Rw low Pq hL eig θ}
    (Bs : SideB D cf Rw low Pq (ratDatR R cG kKs hk) hL eig θ) : NExpRealS R cG (ratDatR R cG kKs hk) where
  fi := fun i => SideTies.fiOf R (idxOf D ((i : ℕ) + 1)) i (idxOf_succ D i)
  geq := fun i g => congrArg (fun y => cG (R.eG y)) (SideTies.fiOf_eG R _ i (idxOf_succ D i) g)
  rho := Bs.rho
  chi := Bs.chiL
  eF := Bs.eF
  bsup := fun i j b h1 h2 => ⟨1, one_ne_zero, fun x hx => by
    rw [one_smul]; exact (Bs.bsup i j b h1 h2 x).1 hx, fun x hx => by
    rw [one_smul]; exact (Bs.bsup i j b h1 h2 x).2 hx⟩
  act := Bs.act

theorem ysOf_fi {kKs : Ks →+* ↥D.LL0} {hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x}
    {cf Rw low Pq hL eig θ} (Bs : SideB D cf Rw low Pq (ratDatR R cG kKs hk) hL eig θ) (i x) : HEq (((ysOf Bs).fi i).e x) x :=
  SideTies.fiOf_heq _ _ _ _ x

variable {S : RatDat D.ntw}


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure PreTie (YS : NExpRealS R cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW j σ).Vec) (X : NExpTied D)
    (hF : D.host.F = maximalRealSubfield D.host.E)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) : Type 1 where
  Dat : D.ntw.Tw → ℕ → Bool → Type
  th : ∀ i j b, Dat i j b → D.nexp.Fm i j b
  lev : ∀ i j b, Dat i j b → Finset (PlE D.host)
  thPsi : ∀ i j b k (_ : Finset (PlE D.host)) (_ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), Dat i j b →
    Set (D.ntw.Ok i k ⊗[D.ntw.O i] D.nexp.Fm i j b)
  h1 : ∀ i j b k (d : Dat i j b), thPsi i j b k ∅ 1 d = {(1 : D.ntw.Ok i k) ⊗ₜ[D.ntw.O i] th i j b d}
  thU : ∀ i j b (Q : Finset (PlE D.host)) (M : ℕ), Dat i j b →
    D.nexp.Fm i j b ⊗[D.ntw.O i] AddMonoidAlgebra (D.ntw.O i) (DelQM D.host (D.ntw.l i) Q M)
  thP : ∀ i j b k Q ψ, D.nexp.MtV i j b k Q ψ →ₗ[D.ntw.Ok i k] (D.ntw.Ok i k ⊗[D.ntw.O i] D.nexp.Fm i j b)
  MtLat : ∀ i j b k Q ψ, Submodule (D.ntw.Ok i k) (D.nexp.MtV i j b k Q ψ)
  h2 : ∀ i j b k Q ψ, (MtLat i j b k Q ψ).FG
  h3 : ∀ i j b k Q ψ,
    Submodule.span (FractionRing (D.ntw.Ok i k)) (MtLat i j b k Q ψ : Set (D.nexp.MtV i j b k Q ψ)) = ⊤
  ρ : Setup D.ntw
  good : ρ.Good
  pin : RealPin R cG ρ
  vec : ∀ j, FWT.IsChosenExtremalVector R.toRealDat j (sg0 D A3.A) (v₀ j _)
  ν : D.ntw.Tw → Fin D.R.m → Bool → ℂ
  scalar : ∀ i j b, IsScalar YS v₀ good i j b (ν i j b)
  tie : Comparison₂ good (Y := keepEx D Dat th lev thPsi h1 thU thP MtLat h2 h3) fun i j b => realRd YS v₀ good i j b (ν i j b)
  hecke : ∀ i j b, HeckeTie (realRd YS v₀ good i j b (ν i j b))
  bad : ∀ i, ρ.bad i = normProd (D.ntw.S0 i)
  ch : ∀ i P, IsSplitPl D.host P → (P ∈ ρ.ch i ↔ P ∈ Set.range Pq)
  join : ∀ PV : ∀ j : Fin D.R.m, principalLevelFrame.RowPsi (Vc D j) D.R.nV, (∀ j, GlobalTheory.MtRead.IdFrame hF (PV j)) →
    ∀ i (j : Fin D.R.m) b k Q ψ (hA : NX.AdmTw D i k Q ψ), TwOK i k Q ψ →
      ∃ ω : (X.mtV i (j.1 + 1) b k Q ψ (by omega) (by omega) hA).W →ₛₗ[ρ.ek i b k] PolF D (Wc D j).rank (Vc D j).rank,
        Function.Injective ω ∧ ∀ f g, (tie i j b).rdV k Q ψ f ((finHom _).rangeRestrict ((PV j).ψ g)) =
          ω (((X.mtV i (j.1 + 1) b k Q ψ (by omega) (by omega) hA).real f).1 g)

namespace PreTie

variable {YS : NExpRealS R cG S} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW j σ).Vec} {X : NExpTied D} {hF Pq}
  (p : PreTie YS v₀ X hF Pq)

abbrev ex : NExp D.R D.host D.what₂ D.LL0 D.nd D.ntw := keepEx D p.Dat p.th p.lev p.thPsi p.h1 p.thU p.thP p.MtLat p.h2 p.h3

theorem hU : ∀ i j b M (d : p.Dat i j b), 1 ≤ j → j ≤ D.R.m →
    p.thU i j b ∅ M d = p.th i j b d ⊗ₜ[D.ntw.O i] (1 : AddMonoidAlgebra (D.ntw.O i) (DelQM D.host (D.ntw.l i) ∅ M)) := by
  intro i j b M d h1 h2
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
  exact (p.tie i ⟨n, h2⟩ b).thU_empty M d

def nth : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw p.ex :=
  { D.nth with datPhi := fun _ _ _ _ => 0, datP := fun _ _ _ _ => 0 }

end PreTie

end GlobalTheory.HeightCounting.SerCopy

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BadPlacesSubOfAdmissibleTwist
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp.BadV

theorem unr_of_twist {R : Ranks} {H : Host R} {S : Set ℕ} {ξ : HChar H.E} (hξ : Chr.IsTwist H S ξ) {p : ℕ} (hp : p.Prime)
    (hS : p ∈ S) (u : HeightOneSpectrum (𝓞 H.E)) (hu : OverP H p u) : ξ.UnrAt u := by
  by_contra hn
  obtain ⟨-, h1, -, h2⟩ := hξ.2.2.2 u hn
  have h3 : ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 H.E) ∈ u.asIdeal := Ideal.absNorm_mem _
  by_cases e : Ideal.absNorm u.asIdeal = p
  · exact h2 (e ▸ hS)
  · obtain ⟨a, b, hab⟩ : IsCoprime ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 H.E) (p : 𝓞 H.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes h1 hp).2 e)
    exact u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ h3) (Ideal.mul_mem_left _ _ hu)))

theorem not_unr_of_delta {R : Ranks} {H : Host R} {p : ℕ} {δ : HChar H.E} (hδ : IsDelta (H := H) p δ)
    (u : HeightOneSpectrum (𝓞 H.E)) (hu : OverP H p u) : ¬ δ.UnrAt u := by
  intro hn
  have h15 := (hδ.ine u hu 1).1 fun y hy => by rw [pow_one]; exact hn y hy
  exact absurd h15 (by decide)

theorem unr_of_mul_left {L : Type} [Field L] [NumberField L] {χ χ' : HChar L} {u : HeightOneSpectrum (𝓞 L)}
    (h : χ.UnrAt u) (h' : (χ * χ').UnrAt u) : χ'.UnrAt u := fun y hy => by
  have e : χ.loc u y * χ'.loc u y = 1 := h' y hy
  simpa only [h y hy, one_mul] using e

theorem unr_of_mul_right {L : Type} [Field L] [NumberField L] {χ χ' : HChar L} {u : HeightOneSpectrum (𝓞 L)}
    (h : χ'.UnrAt u) (h' : (χ * χ').UnrAt u) : χ.UnrAt u := fun y hy => by
  have e : χ.loc u y * χ'.loc u y = 1 := h' y hy
  simpa only [h y hy, mul_one] using e

end GlobalTheory.LevCmp.BadV
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelByPlacesParahoricAtConductorPlaceTameCharac
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelByPlacesParahoricAtConductorPlaceTameCharac
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.LevParaLoc

theorem locM_eq_one_of_ne {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s s' : SplitPlace L)
    {κ : GAf L n} (hκ : TrivOutside {s.v} κ) (h : s'.v ≠ s.v) : NX.locM s' κ = 1 :=
  GlobalTheory.LevGChar.locM_triv s' (B := {s.v}ᶜ) (by rwa [compl_compl]) (by simpa using h)

theorem intLift_one {L : Type} [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : NX.intLift v 1 = 1 := by
  unfold NX.intLift
  rw [dite_eq_left (v.adicCompletionIntegers (maximalRealSubfield L)).one_mem]
  rfl

theorem intLift_zero {L : Type} [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : NX.intLift v 0 = 0 := by
  unfold NX.intLift
  rw [dite_eq_left (v.adicCompletionIntegers (maximalRealSubfield L)).zero_mem]
  rfl

end GlobalTheory.LevParaLoc

namespace GlobalTheory.LevParaLoc

theorem redMat_one {L : Type} [Field L] [NumberField L] [IsCMField L] {r : ℕ}
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {R : Type} [CommRing R]
    (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R) :
    NX.redMat v red (1 : Matrix (Fin r) (Fin r) (v.adicCompletion (maximalRealSubfield L))) = 1 := by
  refine Matrix.ext fun a b => ?_
  show red (NX.intLift v ((1 : Matrix (Fin r) (Fin r) _) a b)) = (1 : Matrix (Fin r) (Fin r) R) a b
  by_cases hab : a = b
  · subst hab; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, intLift_one, map_one]
  · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne hab, intLift_zero, map_zero]

open Classical in
theorem gVal_one (D : D7) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (kv : Σ k : Fin 2, D.nd.PlG k) (s : SplitPlace D.host.E)
    (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1))
    (τ : (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) :
    NX.gVal D i k b kv s red τ 1 = 1 := by
  have htop : NX.topR (Nat.le_add_right D.R.r D.R.t : D.R.r ≤ D.R.nV)
      (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))) = 1 :=
    Matrix.submatrix_one _ (Fin.castLE_injective _)
  have hgl : NX.glOf (1 : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) = 1 :=
    Units.ext (NX.glOf_val _ (by simp))
  have hpsi : NX.psiUTot D i b 1 = 1 := by
    unfold NX.psiUTot
    rw [dite_eq_left (one_mem _)]
    have e : (⟨1, one_mem _⟩ : D.nexp.U) = 1 := rfl
    rw [e, map_one, Units.val_one]
  have hd : red (NX.intLift s.v (NX.detT D.R.r
      (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))))) = 1 := by
    rw [GlobalTheory.LevGChar.detT_one', intLift_one, map_one]
  unfold NX.gVal
  rw [htop, redMat_one, hgl, Pi.mulSingle_one, hpsi, map_one, one_mul]
  split_ifs with h
  · have hu : h.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, hd]; rfl)
    rw [hu, map_one, Units.val_one, map_one]
  · exact absurd (hd ▸ isUnit_one) h

theorem resRep_one {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) :
    NX.resRep s s.w 1 - 1 ∈ s.w.asIdeal := by
  have hu := GlobalTheory.LevGChar.i_resRep s 1 (map_one _)
  show Valued.v (s.i (((NX.resRep s s.w 1 - 1 : 𝓞 L)) : L)) < 1
  have e : s.i (((NX.resRep s s.w 1 - 1 : 𝓞 L)) : L) = s.i ((NX.resRep s s.w 1 : 𝓞 L) : L) - 1 := by
    push_cast; rw [map_sub, map_one]
  rw [e]
  exact hu

end GlobalTheory.LevParaLoc

namespace GlobalTheory.LevParaLoc

theorem mem_iff (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e₀ : ℤ) (W₀ : Type) [AddCommGroup W₀]
    [Module (FractionRing (D.ntw.O i)) W₀]
    (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀)
    (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (M : NX.MtVReal D i j b k Q ψ e₀ W₀ ρ₀ τ) (P : PlE D.host)
    (hP : P ∈ M.QP ∨ P ∈ M.DP) (hG : ∀ kv, (M.sp (NX.pG D kv)).v ≠ (M.sp P).v)
    (hQ : ∀ P'' ∈ M.QP, (M.sp P'').v = (M.sp P).v → P'' = P)
    (hD : ∀ P'' ∈ M.DP, (M.sp P'').v = (M.sp P).v → P'' = P)
    (κ : GAf D.host.E D.R.nV) (hκ : TrivOutside {(M.sp P).v} κ) :
    κ ∈ M.J ↔ NG.ParaRT (M.sp P) D.R.r ((M.sp P).loc _ κ) := by
  have hpar : ((∀ P'' ∈ M.QP, NX.InParah (M.sp P'').v D.R.r (NX.locM (M.sp P'') κ)) ∧
      (∀ P'' ∈ M.DP, NX.InParah (M.sp P'').v D.R.r (NX.locM (M.sp P'') κ))) ↔
      NX.InParah (M.sp P).v D.R.r (NX.locM (M.sp P) κ) := by
    constructor
    · rintro ⟨h1, h2⟩
      rcases hP with h | h
      exacts [h1 P h, h2 P h]
    · intro h
      refine ⟨fun P'' hP'' => ?_, fun P'' hP'' => ?_⟩
      · by_cases hv : (M.sp P'').v = (M.sp P).v
        · rw [hQ P'' hP'' hv]; exact h
        · rw [locM_eq_one_of_ne _ _ hκ hv]; exact NX.inParah_one _ _
      · by_cases hv : (M.sp P'').v = (M.sp P).v
        · rw [hD P'' hP'' hv]; exact h
        · rw [locM_eq_one_of_ne _ _ hκ hv]; exact NX.inParah_one _ _
  have hg : ∀ kv, NX.InLevG (M.sp (NX.pG D kv)).v D.R.r (NX.locM (M.sp (NX.pG D kv)) κ) := fun kv => by
    rw [locM_eq_one_of_ne _ _ hκ (hG kv)]; exact NX.inLevG_one _ _
  rw [M.J_mem κ]
  constructor
  · rintro ⟨hU, -, h1, h2⟩
    exact ⟨(GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff _ hκ).2 hU, (hpar.1 ⟨h1, h2⟩).2⟩
  · rintro ⟨hGL, hll⟩
    exact ⟨(GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff _ hκ).1 hGL, hg,
      hpar.2 ⟨fun a b => (GlobalTheory.HeckeScalarSph.mem_GLint_iff.1 hGL).1 a b, hll⟩⟩

theorem levelPara_loc : ∀ (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e₀ : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀] (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀) (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) (M : NX.MtVReal D i j b k Q ψ e₀ W₀ ρ₀ τ) (ek : NX.Kk D i k →+* ℂ) (P : PlE D.host) (ξ : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), (P ∈ M.QP ∨ P ∈ M.DP) → ¬ (P ∈ M.QP ∧ P ∈ M.DP) → (∀ kv, (M.sp (NX.pG D kv)).v ≠ (M.sp P).v) → (∀ P'' ∈ M.QP, (M.sp P'').v = (M.sp P).v → P'' = P) → (∀ P'' ∈ M.DP, (M.sp P'').v = (M.sp P).v → P'' = P) → (∀ P'' ∈ M.QP, ∀ u : 𝓞 D.host.E, u - 1 ∈ P''.asIdeal → NX.tameVal ψ P'' e₀ u = 1) → (∀ P'' ∈ M.DP, ∀ u : 𝓞 D.host.E, u - 1 ∈ P''.asIdeal → NX.tameVal (D.ntw.delta i) P'' (if b then e₀ else -e₀) u = 1) → (P ∈ M.QP → ∀ (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))ˣ) (a : 𝓞 D.host.E), a ∉ P.asIdeal → Valued.v (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) = 1 → Valued.v ((y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) - (M.sp P).i (a : D.host.E)) < 1 → ((ξ y : ℂˣ) : ℂ) = ek (NX.ofOk D i k (NX.tameVal ψ P e₀ a).1)) → (P ∈ M.DP → ∀ (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))ˣ) (a : 𝓞 D.host.E), a ∉ P.asIdeal → Valued.v (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) = 1 → Valued.v ((y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) - (M.sp P).i (a : D.host.E)) < 1 → ((ξ y : ℂˣ) : ℂ) = ek (NX.ofO0 D i k (NX.tameVal (D.ntw.delta i) P (if b then e₀ else -e₀) a).1)) → NG.LevelPara M.J (cx ek M.χ) (M.sp P) D.R.r ξ := by
  intro D i j b k Q ψ e₀ W₀ _ _ ρ₀ τ M ek P ξ hP hPn hG hQ hD hψ hδ hξQ hξD
  refine ⟨fun κ hκ => mem_iff D i j b k Q ψ e₀ W₀ ρ₀ τ M P hP hG hQ hD κ hκ, ?_⟩
  intro κ h hκ u hu
  have hpara := (mem_iff D i j b k Q ψ e₀ W₀ ρ₀ τ M P hP hG hQ hD κ hκ).1 h
  have hUm : κ ∈ Umax D.host.E D.R.nV := ((M.J_mem κ).1 h).1
  have hx : NX.InParah (M.sp P).v D.R.r (NX.locM (M.sp P) κ) :=
    ⟨fun a b => (GlobalTheory.HeckeScalarSph.mem_GLint_iff.1 hpara.1).1 a b, hpara.2⟩
  have hv1 : Valued.v (NX.detT D.R.r (NX.locM (M.sp P) κ)) = 1 :=
    GlobalTheory.LevGChar.i_detT_one _ D.R.r _ (NX.locM (M.sp P) κ⁻¹)
      (by rw [← GlobalTheory.LevGChar.locM_mul, mul_inv_cancel, GlobalTheory.LevGChar.locM_one])
      (fun a b => GlobalTheory.LevGChar.locM_int _ (inv_mem hUm) a b) hx
  have hu' : (u : (M.sp P).v.adicCompletion (maximalRealSubfield D.host.E)) =
      NX.detT D.R.r (NX.locM (M.sp P) κ) := hu
  have hw : (M.sp P).w = P := M.sp_w P (by rcases hP with h | h; exacts [Or.inl h, Or.inr (Or.inl h)])
  have hclose : Valued.v ((u : (M.sp P).v.adicCompletion (maximalRealSubfield D.host.E)) -
      (M.sp P).i ((NX.resRep (M.sp P) P (NX.detT D.R.r (NX.locM (M.sp P) κ)) : 𝓞 D.host.E) : D.host.E)) < 1 := by
    have := GlobalTheory.LevGChar.i_resRep (M.sp P) _ hv1
    rw [hw] at this
    rw [hu', ← Valuation.map_neg, neg_sub]
    exact this
  have hnm := GlobalTheory.LevGChar.resRep_not_mem (M.sp P) P (NX.detT D.R.r (NX.locM (M.sp P) κ))
  have hvu : Valued.v (u : (M.sp P).v.adicCompletion (maximalRealSubfield D.host.E)) = 1 := by rw [hu']; exact hv1
  have hGp : ∏ kv, NX.gVal D i k b kv (M.sp (NX.pG D kv)) (M.redG kv) (τ kv) (NX.locM (M.sp (NX.pG D kv)) κ) = 1 :=
    Finset.prod_eq_one fun kv _ => by rw [locM_eq_one_of_ne _ _ hκ (hG kv)]; exact gVal_one _ _ _ _ _ _ _ _
  have offQ : ∀ P'' ∈ M.QP, P'' ≠ P → NX.ofOk D i k (NX.tameVal ψ P'' e₀
      (NX.resRep (M.sp P'') P'' (NX.detT D.R.r (NX.locM (M.sp P'') κ)))).1 = 1 := by
    intro P'' hP'' hne
    have hv : (M.sp P'').v ≠ (M.sp P).v := fun e => hne (hQ P'' hP'' e)
    have hw'' : (M.sp P'').w = P'' := M.sp_w P'' (Or.inl hP'')
    rw [locM_eq_one_of_ne _ _ hκ hv, GlobalTheory.LevGChar.detT_one']
    have h1 := resRep_one (M.sp P'')
    rw [hw''] at h1
    rw [hψ P'' hP'' _ h1, Units.val_one, map_one]
  have offD : ∀ P'' ∈ M.DP, P'' ≠ P → NX.ofO0 D i k (NX.tameVal (D.ntw.delta i) P'' (if b then e₀ else -e₀)
      (NX.resRep (M.sp P'') P'' (NX.detT D.R.r (NX.locM (M.sp P'') κ)))).1 = 1 := by
    intro P'' hP'' hne
    have hv : (M.sp P'').v ≠ (M.sp P).v := fun e => hne (hD P'' hP'' e)
    have hw'' : (M.sp P'').w = P'' := M.sp_w P'' (Or.inr (Or.inl hP''))
    rw [locM_eq_one_of_ne _ _ hκ hv, GlobalTheory.LevGChar.detT_one']
    have h1 := resRep_one (M.sp P'')
    rw [hw''] at h1
    rw [hδ P'' hP'' _ h1, Units.val_one, map_one]
  apply Units.ext
  rw [cx_apply, M.chi_eq κ h, hGp, one_mul]
  rcases hP with hPQ | hPD
  · have hPD : P ∉ M.DP := fun h' => hPn ⟨hPQ, h'⟩
    rw [Finset.prod_eq_single_of_mem P hPQ offQ,
      Finset.prod_eq_one (fun P'' hP'' => offD P'' hP'' (fun e => hPD (e ▸ hP''))), mul_one]
    exact (hξQ hPQ u _ hnm hvu hclose).symm
  · have hPQ : P ∉ M.QP := fun h' => hPn ⟨h', hPD⟩
    rw [Finset.prod_eq_single_of_mem P hPD offD,
      Finset.prod_eq_one (fun P'' hP'' => offQ P'' hP'' (fun e => hPQ (e ▸ hP''))), one_mul]
    exact (hξD hPD u _ hnm hvu hclose).symm

end GlobalTheory.LevParaLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelByPlacesParahoricAtConductorPlaceTameCharacStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelByPlaces_parahoric_at_conductorPlace_tameCharacter : ∀ (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e₀ : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀] (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀) (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) (M : NX.MtVReal D i j b k Q ψ e₀ W₀ ρ₀ τ) (ek : NX.Kk D i k →+* ℂ) (P : PlE D.host) (ξ : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), (P ∈ M.QP ∨ P ∈ M.DP) → ¬ (P ∈ M.QP ∧ P ∈ M.DP) → (∀ kv, (M.sp (NX.pG D kv)).v ≠ (M.sp P).v) → (∀ P'' ∈ M.QP, (M.sp P'').v = (M.sp P).v → P'' = P) → (∀ P'' ∈ M.DP, (M.sp P'').v = (M.sp P).v → P'' = P) → (∀ P'' ∈ M.QP, ∀ u : 𝓞 D.host.E, u - 1 ∈ P''.asIdeal → NX.tameVal ψ P'' e₀ u = 1) → (∀ P'' ∈ M.DP, ∀ u : 𝓞 D.host.E, u - 1 ∈ P''.asIdeal → NX.tameVal (D.ntw.delta i) P'' (if b then e₀ else -e₀) u = 1) → (P ∈ M.QP → ∀ (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))ˣ) (a : 𝓞 D.host.E), a ∉ P.asIdeal → Valued.v (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) = 1 → Valued.v ((y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) - (M.sp P).i (a : D.host.E)) < 1 → ((ξ y : ℂˣ) : ℂ) = ek (NX.ofOk D i k (NX.tameVal ψ P e₀ a).1)) → (P ∈ M.DP → ∀ (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))ˣ) (a : 𝓞 D.host.E), a ∉ P.asIdeal → Valued.v (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) = 1 → Valued.v ((y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) - (M.sp P).i (a : D.host.E)) < 1 → ((ξ y : ℂˣ) : ℂ) = ek (NX.ofO0 D i k (NX.tameVal (D.ntw.delta i) P (if b then e₀ else -e₀) a).1)) → NG.LevelPara M.J (cx ek M.χ) (M.sp P) D.R.r ξ := by
  first | exact @GlobalTheory.LevParaLoc.levelPara_loc | exact GlobalTheory.LevParaLoc.levelPara_loc | (intros; apply GlobalTheory.LevParaLoc.levelPara_loc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EnlargedBaseLb2Descent
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up.HkCopy

theorem exists_units_copy {T T' Q Q' : Type} {O : T → Type} {O' : T' → Type} [c : ∀ i, CommRing (O i)]
    [c' : ∀ i, CommRing (O' i)] (hT : T = T') (hO : HEq O O') (hc : HEq c c') (hQ : Q = Q')
    (f : ∀ (i : T) (_b : Bool) (_P : Q), (O i)ˣ) :
    ∃ f' : ∀ (i : T') (_b : Bool) (_P : Q'), (O' i)ˣ,
      ∀ (i : T) (i' : T') (b : Bool) (P : Q) (P' : Q'), HEq i i' → HEq P P' → HEq (f' i' b P') (f i b P) := by
  subst hT; cases hO; cases hc; subst hQ
  exact ⟨f, fun i i' b P P' hi hP => by cases hi; cases hP; rfl⟩

theorem plE_eq {R R' : Ranks} (hR : R = R') {H : Host R} {H' : Host R'} (hH : HEq H H') : PlE H = PlE H' := by
  subst hR; cases hH; rfl

theorem exists_cHk_copy {D D' : D7} (h : GlobalTheory.TwistChoice.SameExport D D')
    (f : ∀ (i : D.ntw.Tw) (_b : Bool) (_P : PlE D.host), (D.ntw.O i)ˣ) :
    ∃ f' : ∀ (i : D'.ntw.Tw) (_b : Bool) (_P : PlE D'.host), (D'.ntw.O i)ˣ,
      ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw) (b : Bool) (P : PlE D.host) (P' : PlE D'.host), HEq i i' → HEq P P' →
        HEq (f' i' b P') (f i b P) :=
  exists_units_copy (eq_of_heq h.set.Tw) h.set.O h.set.crO (plE_eq h.gal.R h.gal.host) f

end GlobalTheory.HeightCounting.Up.HkCopy
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellPlacesMembershipTwist
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.TwTameCell

theorem tameAt_mul {L : Type} [Field L] [NumberField L] {χ χ' : HChar L} {v : HeightOneSpectrum (𝓞 L)}
    (h : χ.TameAt v) (h' : χ'.TameAt v) : (χ * χ').TameAt v := fun y hy hy1 => by
  change χ.loc v y * χ'.loc v y = 1
  rw [h y hy hy1, h' y hy hy1, mul_one]

theorem tameAt_one {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) : (1 : HChar L).TameAt v :=
  fun _ _ _ => rfl

end GlobalTheory.TwTameCell

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNontrivialAddCharZmodEqOfNeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNontrivialAddCharZmodEqOfNeOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory

theorem exists_nontrivial_addChar_eq_of_ne (p : ℕ) [Fact p.Prime] (Pr : Prop) (φ : AddChar (ZMod p) ℂ) (h : Pr → φ ≠ 1) :
    ∃ ψ' : AddChar (ZMod p) ℂ, ψ' ≠ 1 ∧ (Pr → ψ' = φ) := by
  by_cases hP : Pr
  · exact ⟨φ, h hP, fun _ => rfl⟩
  · refine ⟨ZMod.stdAddChar, ?_, fun h' => absurd h' hP⟩
    intro h1
    have hprim := ZMod.isPrimitive_stdAddChar p
    apply hprim (a := 1) one_ne_zero
    rw [AddChar.mulShift_one, h1]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNontrivialAddCharZmodEqOfNeOneStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nontrivial_addChar_zmod_eq_of_ne_one : ∀ (p : ℕ) [Fact p.Prime] (Pr : Prop) (φ : AddChar (ZMod p) ℂ), (Pr → φ ≠ 1) →
    ∃ ψ' : AddChar (ZMod p) ℂ, ψ' ≠ 1 ∧ (Pr → ψ' = φ) := by
  first | exact @GlobalTheory.exists_nontrivial_addChar_eq_of_ne | exact GlobalTheory.exists_nontrivial_addChar_eq_of_ne | (intros; apply GlobalTheory.exists_nontrivial_addChar_eq_of_ne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlacesSameRealPlaceNatCastMem
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlacesSameRealPlaceNatCastMem
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory

theorem split_places_same_natCast_mem : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s s' : SplitPlace L) (n : ℕ), s.v = s'.v →
    ((n : ℕ) : 𝓞 L) ∈ s.w.asIdeal → ((n : ℕ) : 𝓞 L) ∈ s'.w.asIdeal := by
  intro L _ _ _ s s' n hv hn
  have e : ((n : ℕ) : 𝓞 L) = algebraMap (𝓞 (NumberField.maximalRealSubfield L)) (𝓞 L) (n : 𝓞 (NumberField.maximalRealSubfield L)) := (map_natCast _ n).symm
  rw [e] at hn ⊢
  have h1 : ((n : ℕ) : 𝓞 (NumberField.maximalRealSubfield L)) ∈ s.v.asIdeal := by
    rw [← s.w_under]; exact Ideal.mem_comap.mpr hn
  rw [hv] at h1
  rw [← s'.w_under] at h1
  exact Ideal.mem_comap.mp h1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlacesSameRealPlaceNatCastMemStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaces_same_realPlace_natCast_mem : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s s' : SplitPlace L) (n : ℕ), s.v = s'.v →
    ((n : ℕ) : 𝓞 L) ∈ s.w.asIdeal → ((n : ℕ) : 𝓞 L) ∈ s'.w.asIdeal := by
  first | exact @GlobalTheory.split_places_same_natCast_mem | exact GlobalTheory.split_places_same_natCast_mem | (intros; apply GlobalTheory.split_places_same_natCast_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratorNotMemTwistPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratorNotMemTwistPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.Mem.PdNotType

theorem pD_not_type : ∀ (D : D7) (i : D.ntw.Tw) (P : PlE D.host) (k : Fin 2), P ∈ D.ntw.pD i →
    ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  intro D i P k hP
  intro hg
  have hPs : P ∈ (D.ntw.pD i : Set (HeightOneSpectrum (𝓞 D.host.E))) := hP
  rw [D.ntw.pD_eq i] at hPs
  have hPg : P ∈ placesOver D.host.E (D.host.g k) := by
    simpa [placesOver] using hg
  split_ifs at hPs
  · exact GlobalTheory.InertialTypes.not_mem_placesOver_of_ne D.host.pde'_prime (D.host.g_prime k) (D.host.pde_ne_g k).2 hPs hPg
  · exact GlobalTheory.InertialTypes.not_mem_placesOver_of_ne D.host.pde_prime (D.host.g_prime k) (D.host.pde_ne_g k).1 hPs hPg

end GlobalTheory.Mem.PdNotType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratorNotMemTwistPlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generator_not_mem_twist_place : ∀ (D : D7) (i : D.ntw.Tw) (P : PlE D.host) (k : Fin 2), P ∈ D.ntw.pD i →
    ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  first | exact @GlobalTheory.Mem.PdNotType.pD_not_type | exact GlobalTheory.Mem.PdNotType.pD_not_type | (intros; apply GlobalTheory.Mem.PdNotType.pD_not_type <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHeckeOfSideRead
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp.ValQ

theorem tameVal_eq_locK (hGAR : GlobalTheory.Published.GlobalArtinReciprocity) (D : D7) (i : D.ntw.Tw) (k : ℕ)
    (e : NX.Kk D i k →+* ℂ) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (χ : HChar D.host.E)
    (hR : ReadsHecke e ψ χ) (hopen : IsOpen (ψ.ker : Set (G D.host.E D.nd.Om)))
    (hord : ∀ σ, ∃ N : ℕ, ψ σ ^ (D.ntw.l i ^ N) = 1) (P' : PlE D.host)
    (hl : ((D.ntw.l i : ℕ) : 𝓞 D.host.E) ∉ P'.asIdeal) (a : 𝓞 D.host.E) (y : D.host.Eˣ)
    (ha : a ∉ P'.asIdeal) (hy : (y : D.host.E) = (a : D.host.E)) :
    e (NX.ofOk D i k (NX.tameVal ψ P' 1 a).1) = ((χ.locK P' y : ℂˣ) : ℂ) := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  obtain ⟨art, hart, hH⟩ := hR
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver D.nd.Om P'
  obtain ⟨hq2, hq1⟩ := GlobalTheory.TameValChar.two_le_normV_and_not_mem P'
  obtain ⟨ϖ, hϖ1, hϖ2⟩ : ∃ ϖ0 : 𝓞 D.host.E, ϖ0 ∈ P'.asIdeal ∧ ϖ0 ∉ P'.asIdeal ^ 2 := by
    have hlt := Ideal.pow_succ_lt_pow (P := P'.asIdeal) P'.ne_bot 1
    rw [pow_one] at hlt
    obtain ⟨x, hx, hx'⟩ := SetLike.exists_of_lt hlt
    exact ⟨x, hx, hx'⟩
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap D.host.E D.nd.Om (ϖ : D.host.E))
    (show 0 < normV P' - 1 by omega)
  have hxu : IsUnitAt P' (atFin P' y) := by
    show Valued.v (((y : D.host.E) : P'.adicCompletion D.host.E)) = 1
    rw [hy, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem _).2 ha
  obtain ⟨σ, hσI, hσart, hσval⟩ := GlobalTheory.TameRecip.exists_ine_of_unit hGAR D.host.E D.nd.Om art hart
    P' A hA ϖ hϖ1 hϖ2 π hπ (atFin P' y) a hxu (by simp [atFin, hy])
  have hTR : NX.TameRep P' 1 σ a := ⟨A, hA, hσI, ϖ, π, hϖ1, hϖ2, hπ, by simpa using hσval⟩
  have hI : ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P' → ∀ σ ∈ Ine (F := D.host.E) A,
      ∃ N : ℕ, ψ σ ^ (D.ntw.l i ^ N) = 1 := fun _ _ σ _ => hord σ
  rw [GlobalTheory.TameResRead.tameVal_eq_of_tameRep ψ P' 1 (D.ntw.l i) hopen hl hI σ a ha hTR]
  have h1 := hH _ σ hσart.symm
  exact (congrArg (fun z : ℂˣ => (z : ℂ)) h1).symm

end GlobalTheory.LevCmp.ValQ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedTupleFiniteOrderPartUnramifiedAtTypePrime
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedTupleFiniteOrderPartUnramifiedAtTypePrime
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.TwistUnr

theorem nat_not_mem_of_ne {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (Q : HeightOneSpectrum (𝓞 E)) (hq' : ((q : ℕ) : 𝓞 E) ∈ Q.asIdeal) : ((p : ℕ) : 𝓞 E) ∉ Q.asIdeal := by
  intro hp'
  have hc : IsCoprime (p : 𝓞 E) (q : 𝓞 E) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  apply Q.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact Q.asIdeal.add_mem (Q.asIdeal.mul_mem_left a hp') (Q.asIdeal.mul_mem_left b hq')

theorem unrAt_xiTw : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (v : B.places.Pl) (Q : HeightOneSpectrum (𝓞 B.host.E)) (k : Fin 2),
    ((B.host.g k : ℕ) : 𝓞 B.host.E) ∈ Q.asIdeal → Q ∉ T.Q v → (T.xiTw f v).UnrAt Q := by
  intro B f T v Q k hg hQ
  have hp : B.host.pde.Prime := B.toPre.level_prime _ B.host.pde_level.1
  have hp' : B.host.pde'.Prime := B.toPre.level_prime _ B.host.pde_level.2
  have h1 := nat_not_mem_of_ne hp (B.host.g_prime k) (B.host.pde_ne_g k).1 Q hg
  have h2 := nat_not_mem_of_ne hp' (B.host.g_prime k) (B.host.pde_ne_g k).2 Q hg
  have hψ : (T.psi v).UnrAt Q := ((T.psi_is v).ram Q).2 hQ
  unfold TwDat.xiTw
  split_ifs
  · exact GlobalTheory.Plug.TwistLevels.unrAt_mul (f.isDel'.unr Q h2) hψ
  · exact GlobalTheory.Plug.TwistLevels.unrAt_mul (f.isDel.unr Q h1) hψ

end GlobalTheory.TwistUnr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedTupleFiniteOrderPartUnramifiedAtTypePrimeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedTuple_finiteOrderPart_unramified_at_typePrimes : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (v : B.places.Pl) (Q : HeightOneSpectrum (𝓞 B.host.E)) (k : Fin 2),
    ((B.host.g k : ℕ) : 𝓞 B.host.E) ∈ Q.asIdeal → Q ∉ T.Q v → (T.xiTw f v).UnrAt Q := by
  first | exact @GlobalTheory.TwistUnr.unrAt_xiTw | exact GlobalTheory.TwistUnr.unrAt_xiTw | (intros; apply GlobalTheory.TwistUnr.unrAt_xiTw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalDatumCharactersNeOneAtFixedElementResidu
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalDatumCharactersNeOneAtFixedElementResidu
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.HeightCounting

theorem theta_xiRed_ne_one : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ), SideB D cf Rw low Pq S hL eig θ →
    2 ≤ D.R.r → D.ntw.Tw → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), θ kv.1 (Multiplicative.ofAdd (NX.xiRed D kv)) ≠ 1 := by
  classical
  intro D cf Rw low Pq S hL eig θ Bs hr i kv h1
  haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
  obtain ⟨θ', hθ', hψ⟩ := Bs.exp.psiU_gen i true
  have hu : Formalism.L2.NX.tvAt (p := fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) hr kv ∈ D.nexp.U := by
    rw [Bs.exp.U_eq]; exact Formalism.L2.NX.tvAt_mem hr _
  have hu' : Formalism.L2.NX.tvAt (p := fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) hr kv ∈ Formalism.IndefR.NX.U D.nd :=
    Formalism.L2.NX.tvAt_mem hr _
  have e := Bs.psiU i true _ hu hu'
  have e2 : psiUOf D.nd (NX.xiRed D) θ ⟨_, hu'⟩ = θ kv.1 (Multiplicative.ofAdd (NX.xiRed D kv)) :=
    psiXi_tvAt (p := fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) (NX.xiRed D) (fun kv => θ kv.1) hr kv
  have e3 : D.nexp.psiU i true ⟨_, hu⟩ = θ' kv (Multiplicative.ofAdd 1) :=
    (hψ ⟨_, hu⟩).trans (Formalism.L2.NX.stdVal_tvAt θ' hr kv)
  rw [e2, h1, e3] at e
  refine Formalism.L2.NX.char_one_ne (θ' kv) (hθ' hr kv) (Units.ext (e.trans ?_))
  exact map_one (readLL0 S i true)

end GlobalTheory.HeightCounting
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalDatumCharactersNeOneAtFixedElementResiduStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalDatum_characters_ne_one_at_fixedElement_residues : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ), SideB D cf Rw low Pq S hL eig θ →
    2 ≤ D.R.r → D.ntw.Tw → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), θ kv.1 (Multiplicative.ofAdd (NX.xiRed D kv)) ≠ 1 := by
  first | exact @GlobalTheory.HeightCounting.theta_xiRed_ne_one | exact GlobalTheory.HeightCounting.theta_xiRed_ne_one | (intros; apply GlobalTheory.HeightCounting.theta_xiRed_ne_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellQPlacesOfAdmissibleTwist
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.TameUnitOne

open _root_.Formalism.L2.NX

theorem tameVal_eq_one {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {M : Type}
    [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (e : ℤ) (m : ℕ)
    (hopen : IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω))) (hm : ((m : ℕ) : 𝓞 E) ∉ P.asIdeal)
    (hI : ∀ A : ValuationSubring Ω, Formalism.ConjugateSelfDual.IsPlaceOver A P → ∀ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A, ∃ N : ℕ, φ σ ^ (m ^ N) = 1)
    (u : 𝓞 E) (hu1 : u - 1 ∈ P.asIdeal) : NX.tameVal φ P e u = 1 := by
  have hu : u ∉ P.asIdeal := fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by
    have := P.asIdeal.sub_mem h hu1
    simpa using this))
  have hAC : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω P
  obtain ⟨hq2, -⟩ := GlobalTheory.TameValChar.two_le_normV_and_not_mem P
  obtain ⟨ϖ, hϖ1, hϖ2⟩ : ∃ ϖ : 𝓞 E, ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 := by
    have hlt := Ideal.pow_succ_lt_pow (P := P.asIdeal) P.ne_bot 1
    rw [pow_one] at hlt
    obtain ⟨x, hx, hx'⟩ := SetLike.exists_of_lt hlt
    exact ⟨x, hx, hx'⟩
  have hϖne : algebraMap E Ω (ϖ : E) ≠ 0 := by
    intro h
    apply hϖ2
    have h' : ((ϖ : E)) = 0 := (map_eq_zero _).1 h
    rw [show ϖ = 0 from RingOfIntegers.coe_eq_zero_iff.1 h']
    exact zero_mem _
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (ϖ : E)) (show 0 < Formalism.ConjugateSelfDual.normV P - 1 by omega)
  have hπne : π ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hπ
    exact hϖne hπ.symm
  have hv : A.valuation ((1 : Formalism.ConjugateSelfDual.G E Ω) π / π - algebraMap E Ω (u : E)) < 1 := by
    rw [AlgEquiv.one_apply, div_self hπne]
    have h1 := (hA (u - 1)).2 hu1
    have e1 : (1 : Ω) - algebraMap E Ω (u : E) = -(algebraMap E Ω (((u - 1 : 𝓞 E)) : E)) := by
      push_cast
      ring
    rw [e1, Valuation.map_neg]
    exact h1
  have hT := GlobalTheory.TameResRead.tameRep_zpow hA (one_mem _) hϖ1 hϖ2 hπ hu hv e
  rw [GlobalTheory.TameResRead.tameVal_eq_of_tameRep φ P e m hopen hm hI _ u hu hT, one_zpow, map_one]

end GlobalTheory.TameUnitOne

namespace GlobalTheory.LevCmp

end GlobalTheory.LevCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceEqOfCmFieldPlaceEq
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceEqOfCmFieldPlaceEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.SplitByCompl

theorem eq_of_w_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s s' : SplitPlace L),
    s.w = s'.w → s = s' := by
  intro L _ _ _ s s' h
  have hv : s.v = s'.v := HeightOneSpectrum.ext (by rw [← s'.w_under, ← s.w_under, h])
  obtain ⟨v, si⟩ := s
  obtain ⟨v', si'⟩ := s'
  dsimp only at hv
  subst hv
  obtain ⟨i, hi, -, hix⟩ := GlobalTheory.SplitCompl.exists_ringEquiv L ⟨v, si⟩
  obtain ⟨i', hi', -, hix'⟩ := GlobalTheory.SplitCompl.exists_ringEquiv L ⟨v, si'⟩
  dsimp only at hix hix'
  generalize hw : SplitPlace.w ⟨v, si⟩ = w at i hix hi
  generalize hw' : SplitPlace.w ⟨v, si'⟩ = w' at i' hix' hi'
  have hww : w = w' := hw.symm.trans (h.trans hw')
  subst hww
  have e : (i' : v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L) = i :=
    DFunLike.coe_injective ((HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield L) v).equalizer
      hi' hi (funext fun y => by
        have h1 := hix (algebraMap _ L y)
        have h2 := hix' (algebraMap _ L y)
        rw [AlgHom.commutes] at h1 h2
        exact h2.trans h1.symm))
  have e' : ∀ x, i' x = i x := fun x =>
    congrArg (fun f : v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L => f x) e
  have hs : si = si' := AlgHom.ext fun x => i.injective (by rw [hix, ← e', hix'])
  rw [hs]

end GlobalTheory.SplitByCompl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceEqOfCmFieldPlaceEqStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_eq_of_cmFieldPlace_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s s' : SplitPlace L), s.w = s'.w → s = s' := by
  first | exact @GlobalTheory.SplitByCompl.eq_of_w_eq | exact GlobalTheory.SplitByCompl.eq_of_w_eq | (intros; apply GlobalTheory.SplitByCompl.eq_of_w_eq <;> assumption)
end
end
