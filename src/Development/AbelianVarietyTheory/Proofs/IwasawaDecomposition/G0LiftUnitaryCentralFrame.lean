module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAgreeRealOfReadGalois
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrivOutsideListProd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodRowCuspParam
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefImPartOnPolydiscOfPuncturedCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionBarycentreCellNextStage

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.G0LiftUnitaryCentralFrame
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

noncomputable section

namespace GlobalTheory.BlockLiftFrame

open ReciprocityTheory.Aut GlobalTheory.CenFrame

section Local

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem exists_isCompOf (s : SplitPlace L) {κ : Formalism.AUTREP.GAf L n} (hκ : κ ∈ Umax L n) :
    ∃ y : GL (Fin n) (Os s), IsCompOf s κ y := by
  obtain ⟨y, hy⟩ := GlobalTheory.TSetDoubleCoset.loc_mem_GLint s hκ
  refine ⟨y, fun a c => ?_⟩
  rw [← hy]
  rfl

theorem isCompOf_one_of_not_mem (s : SplitPlace L) {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))}
    (h : s.v ∉ T) {x : Formalism.AUTREP.GAf L n} (hx : TrivOutside T x) : IsCompOf s x 1 := by
  have e : s.loc n x = 1 := by
    apply Units.ext
    refine Matrix.ext fun a b => ?_
    have hc : compAt L s.v (((x : GA L n).1 : Matrix (Fin n) (Fin n) (AL L)) a b - (1 : Matrix (Fin n) (Fin n) (AL L)) a b) = 0 := by
      have := congrFun (congrFun (hx s.v h) a) b
      rw [Matrix.map_apply] at this
      rw [map_sub, this, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    have h0 := GlobalTheory.SplitProj.proj_eq_zero_of_compAt_eq_zero L s _ hc
    rw [map_sub, sub_eq_zero] at h0
    show s.proj (((x : GA L n).1 : Matrix (Fin n) (Fin n) (AL L)) a b) =
      (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b
    rw [h0, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  intro a c
  rw [e]
  by_cases hac : a = c <;> simp [Matrix.one_apply, hac]

theorem isBlockDiagonal_reduction_of_blockLift_splitPlace (s : SplitPlace L) {r p : ℕ} [NeZero p] (γ : GL (Fin r) (ZMod p)) {κ : Formalism.AUTREP.GAf L n}
    {y : GL (Fin n) (Os s)} (hy : IsCompOf s κ y) (hl : GlobalTheory.PendOf.IsLiftAt s r p γ (s.loc n κ)) {k : Type} [CommRing k]
    (φ : Os s →+* k) (hφ : IsResidue s φ) (i : ZMod p →+* k) :
    GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity (Formalism.UG.bc i γ) (Matrix.GeneralLinearGroup.map φ y) := by
  intro a b
  have hl' := hl a b
  have hyab := hy a b
  show φ (y.val a b) = _
  by_cases hab : a.val < r ∧ b.val < r
  · rw [dite_eq_left hab] at hl' ⊢
    show φ (y.val a b) = i ((γ : Matrix (Fin r) (Fin r) (ZMod p)) ⟨a.val, hab.1⟩ ⟨b.val, hab.2⟩)
    set m : ℕ := ((γ : Matrix (Fin r) (Fin r) (ZMod p)) ⟨a.val, hab.1⟩ ⟨b.val, hab.2⟩).val with hm
    have h0 : φ (y.val a b - (m : Os s)) = 0 := by
      rw [hφ.ker]
      push_cast
      rw [hyab]
      exact hl'
    rw [map_sub, sub_eq_zero, map_natCast] at h0
    rw [h0, ← map_natCast i m, hm, ZMod.natCast_zmod_val]
  · rw [dite_eq_right hab] at hl' ⊢
    have h1 : ((y.val a b : Os s) : s.v.adicCompletion (maximalRealSubfield L)) = if a = b then 1 else 0 := by
      rw [hyab]; exact hl'
    split_ifs at h1 ⊢ with hab'
    · have h2 : y.val a b = 1 := Subtype.ext (by simpa using h1)
      rw [h2, map_one]
    · have h2 : y.val a b = 0 := Subtype.ext (by simpa using h1)
      rw [h2, map_zero]

end Local

theorem not_mem_gPl_of_twist (D : D7) {Q : Finset (Pl D.host.E)} (hQ : IsTwistPlaces D.host.g Q) (s : SplitPlace D.host.E)
    (hs : s.w ∈ Q) : s.v ∉ GlobalTheory.PendOf.gPl D := by
  rintro ⟨kv, hov⟩
  obtain ⟨q, hq, hcard, -, hqg⟩ := (hQ s.w hs).1
  have hg : (D.host.g kv.1 : 𝓞 D.host.E) ∈ s.w.asIdeal := by
    have h0 : (D.host.g kv.1 : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal := D.naut.plGw_over kv.1 kv.2
    have h1 : ((D.host.g kv.1 : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal := by
      rw [← hov, Ideal.mem_comap, map_natCast]; exact h0
    rw [← s.w_under, Ideal.mem_comap, map_natCast] at h1
    exact h1
  exact GlobalTheory.LevelTypePlace.not_two_primes s.w.asIdeal (D.host.g_prime kv.1) hq (hqg kv.1).symm hg
    (GlobalTheory.LevelTypePlace.natCast_mem_of_card s.w hcard hq.ne_zero)

theorem exists_blockLift (D : D7) {Q Pg : Finset (Pl D.host.E)} (hQ : IsTwistPlaces D.host.g Q) {G : Type} [Group G]
    (eG : G ≃* G0 Pg D.R.r) (cG : G0 Pg D.R.r ≃* G0g D.nd)
    (hgrp : ∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ Pg)
      (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1),
      (∀ kv, ((plg kv : Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧
      ∀ g kv, eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((eG.trans cG) g kv)) :
    ∃ L : G0g D.nd → Formalism.AUTREP.GAf D.host.E D.R.nV,
      GlobalTheory.PendOf.IsTypeGroupBlockLift D D.R.nV L ∧ (∀ g, L g ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV) ∧
      ∀ g (s' : SplitPlace D.host.E) (φ : Os s' →+* kP s'.w), IsResidue s' φ →
        (s'.w ∈ Q → ∃ y, IsCompOf s' (L g) y ∧ Matrix.GeneralLinearGroup.map φ y = 1) ∧
        ∀ hP : s'.w ∈ Pg, ∃ y, IsCompOf s' (L g) y ∧
          GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity (eG ((eG.trans cG).symm g) ⟨s'.w, hP⟩) (Matrix.GeneralLinearGroup.map φ y) := by
  obtain ⟨plg, iso, hpl, hg⟩ := hgrp
  obtain ⟨L, hL, hU⟩ := GlobalTheory.LiftStandardGroup.main D D.R.nV (by unfold Ranks.nV; omega)
  refine ⟨L, hL, hU, fun g s' φ hφ => ⟨fun hs => ?_, fun hP => ?_⟩⟩
  · exact ⟨1, isCompOf_one_of_not_mem s' (not_mem_gPl_of_twist D hQ s' hs) (hL g).1, map_one _⟩
  · obtain ⟨y, hy⟩ := exists_isCompOf s' (hU g)
    refine ⟨y, hy, ?_⟩
    have hkv : plg (plg.symm ⟨s'.w, hP⟩) = ⟨s'.w, hP⟩ := plg.apply_symm_apply _
    have key : ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (PP : Pg), plg kv = PP →
        ∃ i : ZMod (D.host.g kv.1) →+* kP PP.1, eG ((eG.trans cG).symm g) PP = Formalism.UG.bc i (g kv) := by
      intro kv PP hPP
      subst hPP
      exact ⟨iso kv, by rw [hg, MulEquiv.apply_symm_apply]⟩
    obtain ⟨i, hi⟩ := key _ _ hkv
    rw [hi]
    have hw : s'.w = D.naut.plGw (plg.symm ⟨s'.w, hP⟩).1 (plg.symm ⟨s'.w, hP⟩).2 := by
      rw [← hpl, hkv]
    haveI : NeZero (D.host.g (plg.symm ⟨s'.w, hP⟩).1) := ⟨(D.host.g_prime _).ne_zero⟩
    exact isBlockDiagonal_reduction_of_blockLift_splitPlace s' (g _) hy ((hL g).2 _ s' hw) φ hφ i

end GlobalTheory.BlockLiftFrame

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeqRationalDataOfEigen
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.RowTriple.Lay.EigCopy


theorem eigTrue_congr {D : D7} {cf : CharFrame D} {Rw Rw' : RowSide D} {Sb : Finset (PlE D.host)}
    {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0} (h : Rw.locR = Rw'.locR) (hT : GlobalTheory.TwInputs.EigTrue D cf Rw Sb eig) :
    GlobalTheory.TwInputs.EigTrue D cf Rw' Sb eig := by
  unfold GlobalTheory.TwInputs.EigTrue at hT ⊢
  rw [← h]
  exact hT


end GlobalTheory.RowTriple.Lay.EigCopy
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueNeZeroOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
namespace GlobalTheory.ResThree

theorem two_ne_zero_one (g : ℕ) (hg : 3 ≤ g) : (2 : ZMod g) ≠ 0 ∧ (2 : ZMod g) ≠ 1 := by
  constructor
  · intro h
    have h' : ((2 : ℕ) : ZMod g) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  · intro h
    have h' : ((2 : ℕ) : ZMod g) = ((1 : ℕ) : ZMod g) := by exact_mod_cast h
    rw [ZMod.natCast_eq_natCast_iff'] at h'
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
    omega

end GlobalTheory.ResThree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFinEMemDivisorStandard
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitReductionStandardFrameConjStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.CenFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_split_reduction_standard_frame_conj : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), R3.StdFrame hF P → IsBaseFrame V β Λ 1 → ∀ s : ReciprocityTheory.Aut.SplitPlace D.host.E, ∃ (φ : Os s →+* kP s.w) (b : GL (Fin n) (kP s.w)), IsResidue s φ ∧ FrameRed hn P β s φ b := by
  first | exact @GlobalTheory.FrameRedSplit.frameRed_exists | exact GlobalTheory.FrameRedSplit.frameRed_exists | (intros; apply GlobalTheory.FrameRedSplit.frameRed_exists <;> assumption)
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

noncomputable section

namespace GlobalTheory.FrameInt

theorem exists_split (D : D7) (PP : HeightOneSpectrum (𝓞 D.host.E)) (h : ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP) :
    ∃ s : ReciprocityTheory.Aut.SplitPlace D.host.E, s.w = PP := by
  refine GlobalTheory.RowUnitProof.exists_splitPlace_eq D PP ?_
  by_contra hs
  refine h fun c hc => ?_
  by_contra hn
  exact hs ⟨c, hc, fun y hy hm => hn ⟨y, hm, hy.trans (GlobalTheory.TypePlaces.star_eq_conj D _).symm⟩⟩

theorem frame_of {D : D7} {T : Type} (L : LevCh D T) {μ0 : T} (hL : L.Is μ0)
    (hF : D.host.F = maximalRealSubfield D.host.E) (k : Fin D.R.m) (P : principalLevelFrame.RowPsi (Vc D k) D.R.nV)
    (hP : R3.StdFrame hF P) (s : T) :
    (∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV, Formalism.IndefR.Lev.finE (Vc D k) (P.ψ κ) ∈ Formalism.L2.DIV.St (L.βV k)) ∧
    ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q s → ∃ (s' : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin D.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w = PP ∧ GlobalTheory.CenFrame.IsResidue s' φ ∧
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV D k) P (L.βV k) s' φ b := by
  have hβ : IsBaseFrame (Vc D k) (L.βV k) (L.ΛV k) 1 := by
    obtain ⟨c, hc⟩ := hL.βV k
    rwa [one_pow] at hc
  refine ⟨fun κ hκ => ?_, fun PP h => ?_⟩
  · have h1 := (hP.2 κ).1 hκ
    exact (GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hβ h1.1).2 h1
  · have hn : ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP :=
      h.elim (fun h => GlobalTheory.TypePlaces.not_isConjPl L.C.P L.Pg hL.Pg PP h PP h) fun h => (hL.Q_pl s PP h).2 PP h
    obtain ⟨s', hs'⟩ := exists_split D PP hn
    obtain ⟨φ, b, h1, h2⟩ := GlobalTheory.T.exists_split_reduction_standard_frame_conj D (Vc D k) D.R.nV (GlobalTheory.FrameBlockDiagonal.rankV D k) hF P (L.βV k) (L.ΛV k) hP hβ s'
    exact ⟨s', φ, b, hs', h1, h2⟩

end GlobalTheory.FrameInt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeElementInvLatticeClausesOfFrameConj
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeElementInvLatticeClausesOfFrameConj
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

namespace GlobalTheory.Mem.R3.LiftBrg.EtaInvLat

theorem mat_mul_mem {R : Type} [CommRing R] (I : Subring R) {m : Type} [Fintype m]
    {A B : Matrix m m R} (hA : ∀ i j, A i j ∈ I) (hB : ∀ i j, B i j ∈ I) :
    ∀ i j, (A * B) i j ∈ I := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)

theorem mulVec_mem {R : Type} [CommRing R] (I : Subring R) {m : Type} [Fintype m]
    {A : Matrix m m R} {y : m → R} (hA : ∀ i j, A i j ∈ I) (hy : ∀ j, y j ∈ I) :
    ∀ i, (A *ᵥ y) i ∈ I := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hy k)

theorem conj_mulVec_mem {R : Type} [CommRing R] (I : Subring R) {m : Type} [Fintype m]
    {C N Ci : Matrix m m R} (hC : ∀ i j, C i j ∈ I) (hCi : ∀ i j, Ci i j ∈ I) (s : R)
    (hN : ∀ i j, s * N i j ∈ I) {y : m → R} (hy : ∀ j, y j ∈ I) (a : m) :
    s * ((C * N * Ci) *ᵥ y) a ∈ I := by
  have h : s * ((C * N * Ci) *ᵥ y) a = ((C * (s • N) * Ci) *ᵥ y) a := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mulVec]
    simp [Pi.smul_apply, smul_eq_mul]
  rw [h]
  refine mulVec_mem I (mat_mul_mem I (mat_mul_mem I hC (fun i j => ?_)) hCi) hy a
  simpa [Matrix.smul_apply, smul_eq_mul] using hN i j

end GlobalTheory.Mem.R3.LiftBrg.EtaInvLat

namespace GlobalTheory.Mem.R3.LiftBrg.EtaInvLat


set_option maxHeartbeats 2000000 in
theorem eta_inv_lat : ∀ {D : D7} (V : HSp D) (n : ℕ) [NeZero n] (h : n = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (Ut : Formalism.L2.Col.MhlUnif Pb) (d : ℕ) (e : Formalism.L2.Theta.AE D) (C : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (α : GA D V), Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → (∀ z : Formalism.IndefR.Lev.EAf D, Formalism.UG.prV v z = 0 → swapAE D (finPart D e) * z = 0) → (∀ y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, y ∈ Formalism.L2.NTheta.LamHat V ↔ ∀ j, swapAE D (y j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → C ∈ Formalism.L2.DIV.St 1 → α ∈ GfC V → castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)) = C * ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) * C⁻¹ →
    (∀ y ∈ Formalism.L2.NTheta.LamHat V, (fun a => finPart D e * (finMat D.sp.cm.sig V.gram α⁻¹).mulVec y a) ∈ Formalism.L2.NTheta.LamHat V) ∧
    (∀ y ∈ Formalism.L2.NTheta.LamHat V, ∃ z ∈ Formalism.L2.NTheta.LamHat V, (fun a => finPart D e * (finPart D (incA D ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E)) * y a)) =
      fun a => finPart D e * (finMat D.sp.cm.sig V.gram α⁻¹).mulVec z a) := by
  intro D V n _ h v Pb Ut d e C α hI hV hL hC hα hg
  subst h
  rw [GlobalTheory.Mem.R3.LiftBrg.StdFrame.castGL_rfl] at hg
  have hee : e * e = e := hI.1.1
  have hεI : swapAE D (finPart D e) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    (GlobalTheory.IdemSupport.mem_intAE_iff _).1 (GlobalTheory.SplitPlace.idem_mem hee)
  have hiA : ∀ x : 𝓞 D.host.E, Formalism.L2.Col.iA D.host.F D.host.E (algebraMap (𝓞 D.host.E) D.host.E x) ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := fun x => Formalism.L2.Col.iA_mem x
  have hπ0 : algebraMap (𝓞 D.host.E) D.host.E Ut.π ≠ 0 := by
    rw [← map_zero (algebraMap (𝓞 D.host.E) D.host.E)]
    exact (IsFractionRing.injective (𝓞 D.host.E) D.host.E).ne Ut.hπ0
  have hsπ0 : star (algebraMap (𝓞 D.host.E) D.host.E Ut.π) ≠ 0 := star_ne_zero.mpr hπ0
  have hπinv : swapAE D (finPart D e) * Formalism.L2.Col.iA D.host.F D.host.E (algebraMap (𝓞 D.host.E) D.host.E Ut.π)⁻¹ ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    have h1 := not_not.mp ((hI.2 Ut.π Ut.hπ0).not.mp Ut.hπP)
    have h2 := (GlobalTheory.IdemSupport.mem_intAE_iff _).1 h1
    rw [map_mul, map_mul] at h2
    exact h2
  have hstar : star (algebraMap (𝓞 D.host.E) D.host.E Ut.π) =
      algebraMap (𝓞 D.host.E) D.host.E (Formalism.L2.Col.cO D.host.E Ut.π) := rfl
  have hCC := (Formalism.L2.Col.rll_mem_St_iff _ C).1 hC
  obtain ⟨η, hη⟩ : ∃ η : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D),
      η = ((Formalism.L2.Col.mhlEta D.sp.cm V.rank v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm V.rank) : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) :=
    ⟨_, rfl⟩
  rw [← hη] at hg
  have hprη : ∀ i j, Formalism.UG.prV v ((Units.val η) i j) =
      Formalism.UG.prV v (Formalism.L2.Col.iA D.host.F D.host.E (if i = j then Formalism.L2.Col.mhlDiag V.rank Ut.π d i else 0)) := by
    intro i j
    have := congrArg (fun g : GL (Fin V.rank) (D.host.E ⊗[D.host.F] HeightOneSpectrum.adicCompletion D.host.F v) => (Units.val g) i j) (Formalism.L2.Col.rll_put_self (F := D.host.F) (E := D.host.E) V.rank v
      ((Formalism.UG.bc (Formalism.UG.prV v)) ((Formalism.UG.bc (Formalism.L2.Col.iA D.host.F D.host.E)) (Formalism.L2.Col.mhlD V.rank Ut.hπ0 d))))
    rw [hη]
    exact this
  have hV' : ∀ a b : Formalism.IndefR.Lev.EAf D, Formalism.UG.prV v a = Formalism.UG.prV v b →
      swapAE D (finPart D e) * a = swapAE D (finPart D e) * b := by
    intro a b hab
    have h0 := hV (a - b) (by
      rw [map_sub, sub_eq_zero]
      exact hab)
    rw [mul_sub] at h0
    exact sub_eq_zero.mp h0
  have hεη : ∀ i j, swapAE D (finPart D e) * (Units.val η) i j =
      swapAE D (finPart D e) * Formalism.L2.Col.iA D.host.F D.host.E (if i = j then Formalism.L2.Col.mhlDiag V.rank Ut.π d i else 0) :=
    fun i j => hV' _ _ (hprη i j)
  have hεηi : ∀ i j, swapAE D (finPart D e) * (Units.val η⁻¹) i j =
      swapAE D (finPart D e) * Formalism.L2.Col.iA D.host.F D.host.E (if i = j then (Formalism.L2.Col.mhlDiag V.rank Ut.π d i)⁻¹ else 0) :=
    fun i j => hV' _ _ (by rw [hη]; exact Formalism.L2.Col.mhl_prV_eta_inv _ _ _ _ _ _)
  have hN1 : ∀ i j, swapAE D (finPart D e) * (Units.val η⁻¹) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro i j
    rw [hεηi]
    split_ifs with hij
    · simp only [Formalism.L2.Col.mhlDiag]
      split_ifs
      · rw [Formalism.L2.Col.mhlA, _root_.mul_inv_rev, inv_inv, map_mul, mul_left_comm]
        exact Subring.mul_mem _ (hstar ▸ hiA _) hπinv
      · rw [inv_one, map_one, mul_one]
        exact hεI
    · rw [map_zero, mul_zero]
      exact Subring.zero_mem _
  have hN2 : ∀ i j, (swapAE D (finPart D e) * Formalism.L2.Col.iA D.host.F D.host.E (star (algebraMap (𝓞 D.host.E) D.host.E Ut.π))) *
      (Units.val η) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro i j
    rw [mul_right_comm, hεη]
    split_ifs with hij
    · simp only [Formalism.L2.Col.mhlDiag]
      split_ifs
      · rw [Formalism.L2.Col.mhlA, mul_assoc, ← map_mul, mul_assoc, inv_mul_cancel₀ hsπ0, mul_one]
        exact Subring.mul_mem _ hεI (hiA _)
      · rw [map_one, mul_one]
        exact Subring.mul_mem _ hεI (hstar ▸ hiA _)
    · rw [map_zero, mul_zero, zero_mul]
      exact Subring.zero_mem _
  have hT : ∀ (β : GA D V) (w : Fin V.rank → GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) (a : Fin V.rank),
      swapAE D ((finMat D.sp.cm.sig V.gram β *ᵥ w) a) =
        ((Units.val (Formalism.UG.bc (swapAE D) (finHom V β))) *ᵥ (fun b => swapAE D (w b))) a := by
    intro β w a
    rw [RingHom.map_mulVec]
    rfl
  have hgi : Formalism.UG.bc (swapAE D) (finHom V α⁻¹) = C * η⁻¹ * C⁻¹ := by
    rw [map_inv, map_inv, hg]
    group
  have hinv : finMat D.sp.cm.sig V.gram α⁻¹ * finMat D.sp.cm.sig V.gram α = 1 := by
    show Units.val (finHom V α⁻¹) * Units.val (finHom V α) = 1
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · rw [hL] at hy ⊢
    intro a
    show swapAE D (finPart D e * _) ∈ _
    rw [map_mul, hT, hgi, Units.val_mul, Units.val_mul]
    exact conj_mulVec_mem _ hCC.1 hCC.2 _ hN1 hy a
  · refine ⟨fun a => finPart D e * (finMat D.sp.cm.sig V.gram α *ᵥ
      (fun b => finPart D (incA D ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E)) * y b)) a, ?_, ?_⟩
    · rw [hL] at hy ⊢
      intro a
      show swapAE D (finPart D e * _) ∈ _
      rw [map_mul, hT, hg, Units.val_mul, Units.val_mul]
      have hw : (fun b => swapAE D (finPart D (incA D ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E)) * y b)) =
          (Formalism.L2.Col.iA D.host.F D.host.E (star (algebraMap (𝓞 D.host.E) D.host.E Ut.π))) • (fun b => swapAE D (y b)) := by
        funext b
        rw [map_mul]
        rfl
      rw [hw, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc]
      exact conj_mulVec_mem _ hCC.1 hCC.2 _ hN2 hy a
    · have hz : (fun a => finPart D e * (finMat D.sp.cm.sig V.gram α *ᵥ
          (fun b => finPart D (incA D ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E)) * y b)) a) =
          finPart D e • (finMat D.sp.cm.sig V.gram α *ᵥ
          (fun b => finPart D (incA D ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E)) * y b)) := rfl
      rw [hz, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      funext a
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc (finPart D e) (finPart D e), ← map_mul, hee]

end GlobalTheory.Mem.R3.LiftBrg.EtaInvLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeElementInvLatticeClausesOfFrameConjStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeElementInv_latticeClauses_of_frameConj : ∀ {D : D7} (V : HSp D) (n : ℕ) [NeZero n] (h : n = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (Ut : Formalism.L2.Col.MhlUnif Pb) (d : ℕ) (e : Formalism.L2.Theta.AE D) (C : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (α : GA D V), Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → (∀ z : Formalism.IndefR.Lev.EAf D, Formalism.UG.prV v z = 0 → swapAE D (finPart D e) * z = 0) → (∀ y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, y ∈ Formalism.L2.NTheta.LamHat V ↔ ∀ j, swapAE D (y j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → C ∈ Formalism.L2.DIV.St 1 → α ∈ GfC V → castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)) = C * ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) * C⁻¹ →
    (∀ y ∈ Formalism.L2.NTheta.LamHat V, (fun a => finPart D e * (finMat D.sp.cm.sig V.gram α⁻¹).mulVec y a) ∈ Formalism.L2.NTheta.LamHat V) ∧
    (∀ y ∈ Formalism.L2.NTheta.LamHat V, ∃ z ∈ Formalism.L2.NTheta.LamHat V, (fun a => finPart D e * (finPart D (incA D ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E)) * y a)) =
      fun a => finPart D e * (finMat D.sp.cm.sig V.gram α⁻¹).mulVec z a) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.EtaInvLat.eta_inv_lat | exact GlobalTheory.Mem.R3.LiftBrg.EtaInvLat.eta_inv_lat | (intros; apply GlobalTheory.Mem.R3.LiftBrg.EtaInvLat.eta_inv_lat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BarycentricSubdivisionStarStepCells
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BarycentricSubdivisionStarStepCells
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan

section Helpers

variable {X : Type} [AddCommGroup X]

theorem inRCone_append_left {b a : ℕ} (v : Fin b → LinearMap.BilinForm ℤ X) (u : Fin a → LinearMap.BilinForm ℤ X)
    {β : LinearMap.BilinForm ℤ X} (h : InRCone v β) : InRCone (Fin.append v u) β :=
  inRCone_trans (fun k => by simpa using inRCone_self (Fin.append v u) (Fin.castAdd a k)) h

theorem inRCone_cons_of {n m : ℕ} (β₀ : LinearMap.BilinForm ℤ X) {F : Fin m → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} (h : InRCone F β) : InRCone (Fin.cons β₀ F : Fin (m + 1) → _) β :=
  inRCone_trans (fun k => by simpa using inRCone_self (Fin.cons β₀ F : Fin (m + 1) → _) k.succ) h

theorem inRCone_cons_mono {n m : ℕ} (β₀ : LinearMap.BilinForm ℤ X) {F : Fin m → LinearMap.BilinForm ℤ X}
    {δ : Fin n → LinearMap.BilinForm ℤ X} (h : ∀ k, InRCone F (δ k)) :
    ∀ k, InRCone (Fin.cons β₀ F : Fin (m + 1) → _) ((Fin.cons β₀ δ : Fin (n + 1) → _) k) := by
  intro k
  refine Fin.cases ?_ (fun k => ?_) k
  · simpa using inRCone_self (Fin.cons β₀ F : Fin (m + 1) → _) 0
  · simpa using inRCone_cons_of (n := n) β₀ (h k)

theorem inRCone_comp_of {m m' : ℕ} {G : Fin m → LinearMap.BilinForm ℤ X} (s : Fin m' ↪ Fin m) {c : Fin m → ℝ}
    (hc : ∀ j, 0 ≤ c j) {β : LinearMap.BilinForm ℤ X} (hβ : toReal β = ∑ j, c j • toReal (G j))
    (h0 : ∀ j, j ∉ Set.range s → c j = 0) : InRCone (fun l => G (s l)) β := by
  refine ⟨fun l => c (s l), fun l => hc _, ?_⟩
  rw [hβ]
  symm
  exact Fintype.sum_of_injective s s.injective _ _ (fun j hj => by rw [h0 j hj, zero_smul]) fun l => rfl

theorem coeff_eq_zero_of_apply {m : ℕ} {G : Fin m → LinearMap.BilinForm ℤ X} {c : Fin m → ℝ} (hc : ∀ j, 0 ≤ c j)
    {β : LinearMap.BilinForm ℤ X} (hβ : toReal β = ∑ j, c j • toReal (G j)) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ)
    (hG : ∀ j, 0 ≤ h (G j)) (h0 : h β = 0) (j : Fin m) (hj : h (G j) ≠ 0) : c j = 0 := by
  have e := apply_eq_of_toReal_eq hβ h
  rw [h0, Int.cast_zero] at e
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ c j * (h (G j) : ℝ) := fun j _ => mul_nonneg (hc j) (by exact_mod_cast hG j)
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 e.symm j (Finset.mem_univ _)
  exact (mul_eq_zero.1 this).resolve_right (by exact_mod_cast hj)

theorem exists_faceCut {m : ℕ} (G : Fin m → LinearMap.BilinForm ℤ X) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ)
    (hG : ∀ j, 0 ≤ h (G j)) : ∃ (m' : ℕ) (s : Fin m' ↪ Fin m), IsFaceCut G s h := by
  classical
  let S := Finset.univ.filter fun j => h (G j) = 0
  refine ⟨S.card, (S.orderEmbOfFin rfl).toEmbedding, hG, fun j => ?_⟩
  have : Set.range (S.orderEmbOfFin rfl).toEmbedding = (S : Set (Fin m)) := by
    simp [Finset.range_orderEmbOfFin]
  rw [this]
  simp [S]

end Helpers

section Reduce

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X]

theorem reduce_of_not_mem {m n : ℕ} {G : Fin m → LinearMap.BilinForm ℤ X} {γ : Fin n → LinearMap.BilinForm ℤ X}
    (hG : IsCell bar φ G) (hγ : IsCell bar φ γ) (hcov : ∀ k, InRCone G (γ k)) {β₀ : LinearMap.BilinForm ℤ X}
    (hb : β₀ ∈ balForms bar X) (hp : ∀ y, 0 ≤ β₀ y y) (hin : InRCone G β₀) (hnin : ¬ InRCone γ β₀) :
    ∃ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut G s h ∧ 0 < h β₀ ∧
      ∀ k, InRCone (fun l => G (s l)) (γ k) := by
  obtain ⟨h, hh1, hh2, hh3⟩ := GlobalTheory.T.exists_intLinearForm_cutting_subcell O bar φ X m n G γ hG hγ hcov
  obtain ⟨m', s, hs⟩ := exists_faceCut G h hh1
  refine ⟨m', s, h, hs, ?_, fun k => ?_⟩
  · rcases (hin.apply_nonneg h hh1).eq_or_lt with e | e
    · exact (hnin (hh3 β₀ hb hp hin e.symm)).elim
    · exact e
  · obtain ⟨c, hc, e⟩ := hcov k
    exact inRCone_comp_of s hc e fun j hj =>
      coeff_eq_zero_of_apply hc e h hh1 (hh2 k) j fun h0 => hj ((hs.2 j).1 h0)

theorem reduce_of_mem {m n n' : ℕ} {G : Fin m → LinearMap.BilinForm ℤ X} {δ : Fin n → LinearMap.BilinForm ℤ X}
    (hG : IsCell bar φ G) (hδ : IsCell bar φ δ) (hcov : ∀ k, InRCone G (δ k)) {β₀ : LinearMap.BilinForm ℤ X}
    (hin : InRCone δ β₀) {s : Fin n' ↪ Fin n} {h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (hcut : IsFaceCut δ s h)
    (hpos : 0 < h β₀) :
    ∃ (m' : ℕ) (s' : Fin m' ↪ Fin m) (h' : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut G s' h' ∧ 0 < h' β₀ ∧
      ∀ k, InRCone (fun l => G (s' l)) (δ (s k)) := by
  obtain ⟨h₁, hh1, hh2, hh3⟩ := GlobalTheory.T.exists_intLinearForm_cutting_subcell O bar φ X m n G δ hG hδ hcov
  set K : ℤ := 1 + ∑ j, |h (G j)| with hK
  have hKj : ∀ j, |h (G j)| < K := fun j => by
    have := Finset.single_le_sum (f := fun j => |h (G j)|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
    linarith
  let h' : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := K • h₁ + h
  have hv : ∀ β, h' β = K * h₁ β + h β := fun β => rfl
  have hnn : ∀ j, 0 ≤ h' (G j) := fun j => by
    rw [hv]
    rcases (hh1 j).eq_or_lt with e | e
    · rw [← e, mul_zero, zero_add]
      exact (hh3 _ (hG.mem j) (hG.nonneg j) (inRCone_self G j) e.symm).apply_nonneg h hcut.1
    · have h1 : 1 ≤ h₁ (G j) := e
      have := hKj j
      have h2 : -K < h (G j) := by have := neg_abs_le (h (G j)); linarith
      have hK0 : 0 < K := lt_of_le_of_lt (abs_nonneg _) (hKj j)
      have h3 : K ≤ K * h₁ (G j) := le_mul_of_one_le_right hK0.le h1
      linarith
  obtain ⟨m', s', hs'⟩ := exists_faceCut G h' hnn
  have hz : ∀ β, InRCone δ β → h₁ β = 0 := fun β hβ => by
    obtain ⟨c, _, e⟩ := hβ
    have := apply_eq_of_toReal_eq e h₁
    simp only [hh2, Int.cast_zero, mul_zero, Finset.sum_const_zero] at this
    exact_mod_cast this
  refine ⟨m', s', h', hs', by rw [hv, hz β₀ hin, mul_zero, zero_add]; exact hpos, fun k => ?_⟩
  obtain ⟨c, hc, e⟩ := hcov (s k)
  have h0 : h' (δ (s k)) = 0 := by
    rw [hv, hz _ (inRCone_self δ _), mul_zero, zero_add]
    exact (hcut.2 _).2 ⟨k, rfl⟩
  exact inRCone_comp_of s' hc e fun j hj => coeff_eq_zero_of_apply hc e h' hnn h0 j fun h0 => hj ((hs'.2 j).1 h0)

end Reduce

theorem baryStep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ lab φ : InvFun (𝓞 E)) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → IsTwInv H lab → IsCarrierDim H.bar q ψ lab → IsTwInv H φ → IsBaryStage H.bar q ψ lab φ (i + 1) → ∃ φ' : InvFun (𝓞 E), IsTwInv H φ' ∧ IsBaryStage H.bar q ψ lab φ' i := by
  intro E _ _ _ H q ψ lab φ i hdom hψ hψt hlt hcar hφt hst
  obtain ⟨w, hwt, hw⟩ := GlobalTheory.T.markedFormIndicator_zeroOne_barycentres_polyFan E H q ψ lab i hdom hψ hψt hlt hcar
  obtain ⟨hφp, hφs, hφc⟩ := hst
  have hcen : IsCentreSet H.bar q φ w := by
    intro X _ _ _ _ hX
    obtain ⟨h1, h2, h3, h4, -⟩ := hw X hX
    refine ⟨h1, h2, fun m γ hγ β hβ hp β' hβ' hp' hw1 hw2 hc hc' => ?_⟩
    obtain ⟨b, a, v, u, -, hv, hcov, -, -, hvl, hoff, -⟩ := hφc X hX m γ hγ
    have inv : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → InRCone γ β → InRCone v β := by
      intro β hβ hp hw1 hc
      by_contra hn
      have := hoff β hβ hp (inRCone_trans hcov hc) hn
      rw [h3 β hβ hp hw1] at this
      exact lt_irrefl _ this
    exact h4 b v hv hvl β hβ hp β' hβ' hp' hw1 hw2 (inv β hβ hp hw1 hc) (inv β' hβ' hp' hw2 hc')
  obtain ⟨φ', hp', ht', hsub, hs1, hs2, hs3⟩ := GlobalTheory.T.exists_starSubdivision_invariant_polyhedral_fan E H q φ w hdom hφp hφt hwt hcen
  refine ⟨φ', ht', hp', hsub.trans hφs, fun X _ _ _ _ hX n γ' hγ' => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw X hX
  have hnat : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℕ, lab.evalZ β = n :=
    fun β hβ hp => ⟨_, hcar X hX β hβ hp⟩
  have core : ∀ (b a : ℕ) (v : Fin b → LinearMap.BilinForm ℤ X) (u : Fin a → LinearMap.BilinForm ℤ X),
      IsCell H.bar φ (Fin.append v u) → IsCell H.bar ψ v → Function.Injective (fun j => lab.evalZ (u j)) →
      (∀ j, ((i + 1 : ℕ) : ℝ) < lab.evalZ (u j)) →
      (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) →
      (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v u) β → ¬ InRCone v β →
        ((i + 1 : ℕ) : ℝ) < lab.evalZ β) →
      (∀ (d : Fin b → ℤ) (c : Fin a → ℤ), ∑ j, c j • u j = ∑ k, d k • v k → c = 0) →
      ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone (Fin.append v u) β₀ →
      ∀ (m' : ℕ) (s : Fin m' ↪ Fin (b + a)) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
        IsFaceCut (Fin.append v u) s h → 0 < h β₀ →
      ∃ (b' a' : ℕ) (v' : Fin b' → LinearMap.BilinForm ℤ X) (u' : Fin a' → LinearMap.BilinForm ℤ X),
        IsCell H.bar φ' (Fin.append v' u') ∧ IsCell H.bar ψ v' ∧
        (∀ k, InRCone (Fin.append v' u') ((Fin.cons β₀ fun j => Fin.append v u (s j) : Fin (m' + 1) → _) k)) ∧
        Function.Injective (fun j => lab.evalZ (u' j)) ∧ (∀ j, (i : ℝ) < lab.evalZ (u' j)) ∧
        (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone v' β → lab.evalZ β ≤ i) ∧
        (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v' u') β → ¬ InRCone v' β →
          (i : ℝ) < lab.evalZ β) ∧
        ∀ (d : Fin b' → ℤ) (c : Fin a' → ℤ), ∑ j, c j • u' j = ∑ k, d k • v' k → c = 0 := by
    intro b a v u hγ hv hinj hlu hvl hoff hind β₀ hb0 hp0 hw0 hin0
    exact GlobalTheory.T.starSubdivision_barycentre_cell_next_stage (𝓞 E) H.bar ψ lab φ' w i X b a v u hv hinj hlu hvl hoff hind hnat
      (fun m' s h hh => GlobalTheory.T.polyFan_face_cut_by_intLinearForm_isCell E H q ψ hψ X hX (hdom X) b v hv m' s h hh) h5
      (fun β hβ hp β' hβ' hp' hw1 hw2 hc hc' => (hcen X hX).2.2 _ _ hγ β hβ hp β' hβ' hp' hw1 hw2 hc hc')
      (fun β₀ hb0 hp0 β hβ hp hin c₀ c hc₀ hc e =>
        GlobalTheory.T.carrierDim_le_of_add_cell_generators (𝓞 E) H.bar q ψ lab hcar X hX b v hv β₀ hb0 hp0 β hβ hp hin c₀ c hc₀ hc e)
      β₀ hb0 hp0 hw0 (h3 β₀ hb0 hp0 hw0) hin0
      (fun m' s h hh hpos => hs2 X hX _ _ hγ β₀ hb0 hp0 hw0 hin0 m' s h hh hpos)
  rcases hs3 X hX n γ' hγ' with ⟨m, γ, hγ, hno, hcov'⟩ | ⟨m, δ, β₀, m', s, h, hδ, hb0, hp0, hw0, hin0, hcut, hpos, hcov'⟩
  · obtain ⟨b, a, v, u, hG, hv, hcov, hinj, hlu, hvl, hoff, hind⟩ := hφc X hX m γ hγ
    by_cases hc : ∃ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) ∧ w.evalZ β₀ = 1 ∧ InRCone (Fin.append v u) β₀
    · obtain ⟨β₀, hb0, hp0, hw0, hin0⟩ := hc
      have hnin : ¬ InRCone γ β₀ := fun hh => by
        have := hno β₀ hb0 hp0 hh
        rw [hw0] at this
        exact one_ne_zero this
      obtain ⟨m', s, h, hcut, hpos, hsub'⟩ := reduce_of_not_mem hG hγ hcov hb0 hp0 hin0 hnin
      obtain ⟨b', a', v', u', r1, r2, r3, r4, r5, r6, r7, r8⟩ :=
        core b a v u hG hv hinj hlu hvl hoff hind β₀ hb0 hp0 hw0 hin0 m' s h hcut hpos
      exact ⟨b', a', v', u', r1, r2, fun j => inRCone_trans r3 (inRCone_cons_of (n := 0) β₀
        (inRCone_trans hsub' (hcov' j))), r4, r5, r6, r7, r8⟩
    · push_neg at hc
      have hw0 : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v u) β → w.evalZ β = 0 :=
        fun β hβ hp hin => (h1 β hβ hp).resolve_right fun e => hc β hβ hp e hin
      refine ⟨b, a, v, u, hs1 X hX _ _ hG hw0, hv, fun j => inRCone_trans hcov (hcov' j), hinj,
        fun j => ?_, fun β hβ hp hin => ?_, fun β hβ hp hin hn => ?_, hind⟩
      · have := hlu j; push_cast at this ⊢; linarith
      · obtain ⟨k, hk⟩ := hnat β hβ hp
        have hle := hvl β hβ hp hin
        rw [hk] at hle ⊢
        have hle' : k ≤ i + 1 := by exact_mod_cast hle
        rcases hle'.lt_or_eq with hl | hl
        · exact_mod_cast Nat.lt_succ_iff.1 hl
        · obtain ⟨β₁, hb1, hp1, hw1, hin1⟩ := h5 b v hv β hβ hp hin (by rw [hk, hl])
          exact absurd (inRCone_append_left v u hin1) (hc β₁ hb1 hp1 hw1)
      · have := hoff β hβ hp hin hn; push_cast at this ⊢; linarith
  · obtain ⟨b, a, v, u, hG, hv, hcov, hinj, hlu, hvl, hoff, hind⟩ := hφc X hX m δ hδ
    obtain ⟨m'', s', h', hcut', hpos', hsub'⟩ := reduce_of_mem hG hδ hcov hin0 hcut hpos
    obtain ⟨b', a', v', u', r1, r2, r3, r4, r5, r6, r7, r8⟩ :=
      core b a v u hG hv hinj hlu hvl hoff hind β₀ hb0 hp0 hw0 (inRCone_trans hcov hin0) m'' s' h' hcut' hpos'
    exact ⟨b', a', v', u', r1, r2, fun j => inRCone_trans r3 (inRCone_trans (inRCone_cons_mono β₀ hsub') (hcov' j)),
      r4, r5, r6, r7, r8⟩

end GlobalTheory.PolFan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BarycentricSubdivisionStarStepCellsStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.barycentricSubdivision_star_step_cells : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ lab φ : InvFun (𝓞 E)) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → IsTwInv H lab → IsCarrierDim H.bar q ψ lab → IsTwInv H φ → IsBaryStage H.bar q ψ lab φ (i + 1) → ∃ φ' : InvFun (𝓞 E), IsTwInv H φ' ∧ IsBaryStage H.bar q ψ lab φ' i := by
  first | exact @GlobalTheory.PolFan.baryStep | exact GlobalTheory.PolFan.baryStep | (intros; apply GlobalTheory.PolFan.baryStep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjParahoricBlockLift
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjParahoricBlockLift
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

noncomputable section

namespace GlobalTheory.ParahLift

section Core

variable {K : Type} [CommRing K]

theorem pl_blkDiag_mem {m r : ℕ} {x : GL (Fin r) K} {M : GL (Fin m) K} (hM : GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity x M) :
    M ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
  intro i j hij
  have hj : j.val < r := by
    unfold Formalism.L2.DIV.blk2 at hij; split_ifs at hij with h1 h2 <;> omega
  have hi : ¬ i.val < r := by
    unfold Formalism.L2.DIV.blk2 at hij; split_ifs at hij with h1 h2 <;> omega
  have hne : i ≠ j := fun h => hi (h ▸ hj)
  show M.val i j = 0
  rw [hM i j, dite_eq_right (fun h => hi h.1), if_neg hne]

theorem pl_blkOf_eq {m r t : ℕ} (hm : m = r + t) (a : Fin m) :
    Formalism.L2.DIV.blkOf r t a = Formalism.L2.DIV.blk2 r a := by
  have ha := a.2
  unfold Formalism.L2.DIV.blkOf Formalism.L2.DIV.blk2
  split_ifs with h
  · rfl
  · have : (a.val - r) / t = 0 := Nat.div_eq_of_lt (by omega)
    omega

theorem pl_blockTri_eq {m r t : ℕ} (hm : m = r + t) :
    Formalism.L2.DIV.blockTri (κ := K) (n := m) (Formalism.L2.DIV.blkOf r t) = Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
  have : (Formalism.L2.DIV.blkOf r t : Fin m → ℕ) = Formalism.L2.DIV.blk2 r := funext (pl_blkOf_eq hm)
  rw [this]

theorem pl_core {m r t : ℕ} (hm : m = r + t) (hr : r ≤ m) {b M : GL (Fin m) K} {x : GL (Fin r) K}
    (hb : b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) (hM : GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity x M) :
    b * M * b⁻¹ ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ∧
    Formalism.L2.DIV.upperLeftBlock hr (b * M * b⁻¹) = Formalism.L2.DIV.upperLeftBlock hr b * x * (Formalism.L2.DIV.upperLeftBlock hr b)⁻¹ ∧
    Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 (b * M * b⁻¹) = 1 := by
  have hM2 := pl_blkDiag_mem hM
  have hbinv := (Formalism.L2.DIV.blockTri (κ := K) (Formalism.L2.DIV.blk2 r)).inv_mem hb
  have hbM := (Formalism.L2.DIV.blockTri (κ := K) (Formalism.L2.DIV.blk2 r)).mul_mem hb hM2
  have hall := (Formalism.L2.DIV.blockTri (κ := K) (Formalism.L2.DIV.blk2 r)).mul_mem hbM hbinv
  have hE := pl_blockTri_eq (K := K) hm
  refine ⟨hE ▸ hall, ?_, ?_⟩
  · have hMr : Formalism.L2.DIV.upperLeftBlock hr M = x := by
      apply Units.ext
      ext i j
      rw [Formalism.L2.DIV.upper_block_val_submatrix hr hM2, Matrix.submatrix_apply, hM, dite_eq_left ⟨i.2, j.2⟩]
      rfl
    unfold Formalism.L2.DIV.upperLeftBlock at hMr ⊢
    rw [Formalism.L2.DIV.extendMatrixByIdentityAlongIndices_mul _ hbM hbinv, Formalism.L2.DIV.extendMatrixByIdentityAlongIndices_mul _ hb hM2, Formalism.L2.DIV.extendOne_inv _ hb, hMr]
  · have hb' : b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) := hE ▸ hb
    have hM' : M ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) := hE ▸ hM2
    have hbinv' : b⁻¹ ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) := hE ▸ hbinv
    have hbM' := (Formalism.L2.DIV.blockTri (κ := K) (Formalism.L2.DIV.blkOf r t)).mul_mem hb' hM'
    have hdM : Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 M = 1 := by
      apply Units.ext
      rw [Formalism.L2.DIV.diag_block_det_val 1 hM', Units.val_one]
      have hsub : (M.val.submatrix (Subtype.val : {a : Fin m // Formalism.L2.DIV.blkOf r t a = 1} → Fin m) (Subtype.val : {a : Fin m // Formalism.L2.DIV.blkOf r t a = 1} → Fin m)) = 1 := by
        ext a c
        have ha : ¬ a.1.val < r := fun h => by
          have h2 := a.2
          simp [Formalism.L2.DIV.blkOf, h] at h2
        rw [Matrix.submatrix_apply, hM, dite_eq_right (fun h => ha h.1), Matrix.one_apply]
        by_cases hac : a = c
        · subst hac; simp
        · rw [if_neg hac, if_neg (fun h => hac (Subtype.ext h))]
      show (M.val.submatrix (Subtype.val : {a : Fin m // Formalism.L2.DIV.blkOf r t a = 1} → Fin m) (Subtype.val : {a : Fin m // Formalism.L2.DIV.blkOf r t a = 1} → Fin m)).det = 1
      rw [hsub, Matrix.det_one]
    rw [Formalism.L2.DIV.diag_block_det_mul hbM' hbinv', Formalism.L2.DIV.diag_block_det_mul hb' hM', hdM, mul_one]
    unfold Formalism.L2.DIV.dBlk
    rw [Formalism.L2.DIV.extendOne_inv _ hb', mul_inv_cancel]

theorem pl_core_cast {n m r t : ℕ} (hn : n = m) (hm : m = r + t) (hr : r ≤ m) (hr' : r ≤ n) {b M : GL (Fin m) K}
    {X : GL (Fin n) K} {x : GL (Fin r) K}
    (hb : b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) (hM : GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity x M)
    (hX : ∀ a c : Fin m, X.val (Fin.cast hn.symm a) (Fin.cast hn.symm c) = (b * M * b⁻¹).val a c) :
    X ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ∧
    Formalism.L2.DIV.upperLeftBlock hr' X = Formalism.L2.DIV.upperLeftBlock hr b * x * (Formalism.L2.DIV.upperLeftBlock hr b)⁻¹ ∧
    Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 X = 1 := by
  subst hn
  have hXe : X = b * M * b⁻¹ := Units.ext (Matrix.ext fun a c => hX a c)
  subst hXe
  exact pl_core hm hr hb hM

theorem pl_one_cast {n m : ℕ} (hn : n = m) {b Y : GL (Fin m) K} {X : GL (Fin n) K} (hY : Y = 1)
    (hX : ∀ a c : Fin m, X.val (Fin.cast hn.symm a) (Fin.cast hn.symm c) = (b * Y * b⁻¹).val a c) : X = 1 := by
  subst hn; subst hY
  apply Units.ext
  ext a c
  have h := hX a c
  rw [mul_one, mul_inv_cancel] at h
  exact h

end Core

end GlobalTheory.ParahLift

namespace GlobalTheory.ParahLift

section LevFn

open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
  {LL : Type} [CommRing LL]

theorem pl_levFn_eq_one (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Ld : Formalism.L2.DIV.LevDat E LL n)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hP : Ld.P.chi = 1)
    (hg : ∀ PP ∈ Ld.Pg, ∀ c ∈ Finset.range Ld.s,
      Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf Ld.r Ld.t) (c + 1) (Formalism.L2.DIV.redFn β PP x) = 1)
    (hq : ∀ PP ∈ Ld.Q, Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 Ld.r) 1 (Formalism.L2.DIV.redFn β PP x) = 1) :
    Formalism.L2.DIV.levFn β Ld x = 1 := by
  unfold Formalism.L2.DIV.levFn
  rw [Finset.prod_eq_one (fun PP hPP => Finset.prod_eq_one (fun c hc => by rw [hg PP hPP c hc, map_one])),
    Finset.prod_eq_one (fun PP hPP => by rw [hq PP hPP, map_one])]
  have h1 : Formalism.L2.DIV.ext1 Ld.P.H Ld.P.chi (Formalism.L2.DIV.rTup β Ld x) = 1 := by
    unfold Formalism.L2.DIV.ext1
    split_ifs
    · rw [hP]; rfl
    · rfl
  rw [h1, mul_one, mul_one]

end LevFn

theorem exists_conj_parahoric_lift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (k : Fin D.R.m) (s : T)
  (P : Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc D k) D.R.nV) (L : G0g D.nd → Formalism.AUTREP.GAf D.host.E D.R.nV),
  (∀ g, L g ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV) →
  (∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV, Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc D k) (P.ψ κ) ∈ Formalism.L2.DIV.St (R.βV k)) →
  (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q s → ∃ (s' : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin D.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w = PP ∧ GlobalTheory.CenFrame.IsResidue s' φ ∧
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV D k) P (R.βV k) s' φ b ∧ (PP ∈ R.Pg → b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 D.R.r))) →
  (∀ g (s' : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w), GlobalTheory.CenFrame.IsResidue s' φ →
      (s'.w ∈ R.Q s → ∃ y, GlobalTheory.CenFrame.IsCompOf s' (L g) y ∧ Matrix.GeneralLinearGroup.map φ y = 1) ∧
      ∀ hP : s'.w ∈ R.Pg, ∃ y, GlobalTheory.CenFrame.IsCompOf s' (L g) y ∧
        GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity (R.eG ((R.eG.trans cG).symm g) ⟨s'.w, hP⟩) (Matrix.GeneralLinearGroup.map φ y)) →
  ∃ c : G, ∀ g : G,
    Formalism.IndefR.Lev.IsLevelLift (Formalism.IndefR.Links.Vc D k) (R.βV k) (R.datVt k s) (R.eG g) (P.ψ (L ((R.eG.trans cG) (c * g * c⁻¹)))) ∧
    Formalism.IndefR.Lev.levChi (Formalism.IndefR.Links.Vc D k) (R.βV k) (Formalism.IndefR.Lev.flagL (R.datVt k s)) (P.ψ (L ((R.eG.trans cG) (c * g * c⁻¹)))) = 1 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R cG k s P L H1 H2 H3 H4
  have hn : (Formalism.IndefR.Links.Vc D k).rank = D.R.nV := GlobalTheory.FrameBlockDiagonal.rankV D k
  have hm : D.R.nV = D.R.r + D.R.t := rfl
  have hr : D.R.r ≤ D.R.nV := Nat.le_add_right _ _
  have hr' : D.R.r ≤ (Formalism.IndefR.Links.Vc D k).rank := hn ▸ hr
  have hA : ∀ PP : ↥R.Pg, ∃ b : GL (Fin D.R.nV) (Formalism.L2.DIV.kP PP.1), b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 D.R.r) ∧
      ∀ h : G0g D.nd, ∃ M : GL (Fin D.R.nV) (Formalism.L2.DIV.kP PP.1),
        GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity (R.eG ((R.eG.trans cG).symm h) PP) M ∧
        ∀ a c, (Formalism.L2.DIV.redFn (R.βV k) PP.1 (Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc D k) (P.ψ (L h)))).val
          (Fin.cast hn.symm a) (Fin.cast hn.symm c) = (b * M * b⁻¹).val a c := by
    rintro ⟨PP, hPP⟩
    obtain ⟨s', φ, b, hw, hres, hfr, hb⟩ := H3 PP (Or.inl hPP)
    subst hw
    refine ⟨b, hb hPP, fun h => ?_⟩
    obtain ⟨y, hy, hbd⟩ := (H4 h s' φ hres).2 hPP
    exact ⟨_, hbd, hfr (L h) (H1 h) y hy⟩
  have hB : ∀ PP ∈ R.Q s, ∀ h : G0g D.nd,
      Formalism.L2.DIV.redFn (R.βV k) PP (Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc D k) (P.ψ (L h))) = 1 := by
    intro PP hPP h
    obtain ⟨s', φ, b, hw, hres, hfr, -⟩ := H3 PP (Or.inr hPP)
    subst hw
    obtain ⟨y, hy, h1⟩ := (H4 h s' φ hres).1 hPP
    exact pl_one_cast hn h1 (hfr (L h) (H1 h) y hy)
  choose bf hbf Mf hMd hMe using hA
  refine ⟨R.eG.symm (fun PP => (Formalism.L2.DIV.upperLeftBlock hr (bf PP))⁻¹), fun g => ?_⟩
  set c := R.eG.symm (fun PP => (Formalism.L2.DIV.upperLeftBlock hr (bf PP))⁻¹) with hc
  set h := (R.eG.trans cG) (c * g * c⁻¹) with hh
  have hsymm : (R.eG.trans cG).symm h = c * g * c⁻¹ := MulEquiv.symm_apply_apply _ _
  have hx : ∀ PP : ↥R.Pg, R.eG ((R.eG.trans cG).symm h) PP =
      (Formalism.L2.DIV.upperLeftBlock hr (bf PP))⁻¹ * R.eG g PP * Formalism.L2.DIV.upperLeftBlock hr (bf PP) := by
    intro PP
    rw [hsymm, map_mul, map_mul, map_inv, hc, MulEquiv.apply_symm_apply]
    simp only [Pi.mul_apply, Pi.inv_apply, inv_inv]
  have hcore : ∀ PP : ↥R.Pg,
      Formalism.L2.DIV.redFn (R.βV k) PP.1 (Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc D k) (P.ψ (L h))) ∈
        Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf D.R.r D.R.t) ∧
      Formalism.L2.DIV.upperLeftBlock hr' (Formalism.L2.DIV.redFn (R.βV k) PP.1 (Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc D k) (P.ψ (L h)))) =
        R.eG g PP ∧
      Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf D.R.r D.R.t) 1
        (Formalism.L2.DIV.redFn (R.βV k) PP.1 (Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc D k) (P.ψ (L h)))) = 1 := by
    intro PP
    obtain ⟨h1, h2, h3⟩ := pl_core_cast hn hm hr hr' (hbf PP) (hMd PP h) (hMe PP h)
    refine ⟨h1, ?_, h3⟩
    rw [h2, hx PP]
    group
  have hSt := H2 (L h) (H1 h)
  refine ⟨⟨P.into _, Formalism.L2.DIV.mem_parLev.2 ⟨GlobalTheory.LevFinCong.finE_mem_UA _ _, hSt, fun PP hPP => (hcore ⟨PP, hPP⟩).1,
    fun PP hPP => ?_⟩, ?_⟩, ?_⟩
  · rw [hB PP hPP h]; exact Subgroup.one_mem _
  · funext PP
    exact (hcore PP).2.1
  · unfold Formalism.IndefR.Lev.levChi
    rw [pl_levFn_eq_one _ _ _ rfl, Units.val_one]
    · intro PP hPP c' hc'
      have hc0 : c' = 0 := by
        have : c' < 1 := Finset.mem_range.1 hc'
        omega
      subst hc0
      exact (hcore ⟨PP, hPP⟩).2.2
    · intro PP hPP
      rw [hB PP hPP h]
      exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _

end GlobalTheory.ParahLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjParahoricBlockLiftStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_parahoric_block_lift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (k : Fin D.R.m) (s : T)
  (P : Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc D k) D.R.nV) (L : G0g D.nd → Formalism.AUTREP.GAf D.host.E D.R.nV),
  (∀ g, L g ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV) →
  (∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV, Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc D k) (P.ψ κ) ∈ Formalism.L2.DIV.St (R.βV k)) →
  (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q s → ∃ (s' : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin D.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w = PP ∧ GlobalTheory.CenFrame.IsResidue s' φ ∧
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV D k) P (R.βV k) s' φ b ∧ (PP ∈ R.Pg → b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 D.R.r))) →
  (∀ g (s' : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w), GlobalTheory.CenFrame.IsResidue s' φ →
      (s'.w ∈ R.Q s → ∃ y, GlobalTheory.CenFrame.IsCompOf s' (L g) y ∧ Matrix.GeneralLinearGroup.map φ y = 1) ∧
      ∀ hP : s'.w ∈ R.Pg, ∃ y, GlobalTheory.CenFrame.IsCompOf s' (L g) y ∧
        GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity (R.eG ((R.eG.trans cG).symm g) ⟨s'.w, hP⟩) (Matrix.GeneralLinearGroup.map φ y)) →
  ∃ c : G, ∀ g : G,
    Formalism.IndefR.Lev.IsLevelLift (Formalism.IndefR.Links.Vc D k) (R.βV k) (R.datVt k s) (R.eG g) (P.ψ (L ((R.eG.trans cG) (c * g * c⁻¹)))) ∧
    Formalism.IndefR.Lev.levChi (Formalism.IndefR.Links.Vc D k) (R.βV k) (Formalism.IndefR.Lev.flagL (R.datVt k s)) (P.ψ (L ((R.eG.trans cG) (c * g * c⁻¹)))) = 1 := by
  first | exact @GlobalTheory.ParahLift.exists_conj_parahoric_lift | exact GlobalTheory.ParahLift.exists_conj_parahoric_lift | (intros; apply GlobalTheory.ParahLift.exists_conj_parahoric_lift <;> assumption)
end
end
