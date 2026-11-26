module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.Columns.MtHeckeSum
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
public import Formalism.LocalToGlobal.IndefiniteReal.BridgeColPts
public import Formalism.LocalToGlobal.Columns.InputsGenus
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AutConjTranslatesDetCharacterMarkings
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCompletedSelfDualLatticeIffIntegralStdFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCompletedSelfDualLatticeIffIntegralStdFrame
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

namespace GlobalTheory.Mem.SDFrameStd

theorem lamHat_iff_int : ∀ {D : D7} (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V 1 Λ 1 → ∀ y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, y ∈ Formalism.L2.NTheta.LamHat V ↔ ∀ j, swapAE D (y j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D V Λ hβ y
  obtain ⟨c, hf, -, -, h1, h2⟩ := hβ
  have hset : (Λ : Set (Fin V.rank → D.host.E)) = L0c D V := by
    ext x
    constructor
    · intro hx
      have := h2 x hx
      simpa using this
    · intro hx
      have := h1 x hx
      simpa using this
  have e1 : y ∈ Formalism.L2.NTheta.LamHat V ↔ (fun i => GlobalTheory.LevSplit.swp D.host.F D.host.E (y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    rw [← GlobalTheory.LevSplit.latHat_iff Λ y, hset]
  rw [e1, hf]
  simp only [inv_one, Units.val_one, one_mulVec]
  rfl

end GlobalTheory.Mem.SDFrameStd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCompletedSelfDualLatticeIffIntegralStdFrameStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedSelfDualLattice_iff_integral_stdFrame : ∀ {D : D7} (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V 1 Λ 1 → ∀ y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, y ∈ Formalism.L2.NTheta.LamHat V ↔ ∀ j, swapAE D (y j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.Mem.SDFrameStd.lamHat_iff_int | exact GlobalTheory.Mem.SDFrameStd.lamHat_iff_int | (intros; apply GlobalTheory.Mem.SDFrameStd.lamHat_iff_int <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesUnder
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtIn.Under

theorem not_both {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : q ≠ p) (h1 : (p : 𝓞 E) ∈ P.asIdeal) (h2 : (q : 𝓞 E) ∈ P.asIdeal) : False := by
  have hc : IsCoprime (q : 𝓞 E) (p : 𝓞 E) := Nat.Coprime.cast ((Nat.coprime_primes hq hp).2 hne)
  obtain ⟨x, y, hxy⟩ := hc
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hxy ▸ P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ h2) (P.asIdeal.mul_mem_left _ h1)))

theorem q_mem {D : D7} {P : Pl D.host.E} {q : ℕ} (h : Nat.card (kP P) = q) : (q : 𝓞 D.host.E) ∈ P.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← h]
  have := card_nsmul_eq_zero' (G := kP P) (x := 1)
  rwa [nsmul_one] at this

theorem places_under : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) → ∀ (i : Fin D.R.m) (t : T) (PP : Pl D.host.E), PP ∈ L.Pg ∨ PP ∈ L.Q t → ∀ v, NG.OverPl PP v → v ∈ gPl D ∪ qPl D (L.C.mu0 i * L.xiH t) := by
  intro D T L μ0 hL hPg i t PP hPP v hv
  by_cases hg : v ∈ gPl D
  · exact Or.inl hg
  rcases hPP with hP | hQ
  · obtain ⟨k, w, rfl⟩ := (hPg _).1 hP
    exact absurd ⟨_, hv, k, D.naut.plGw_over k w⟩ hg
  · refine Or.inr ⟨hg, PP, hv, fun hu => ?_⟩
    obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := hL.Q_pl t PP hQ
    have hm : (L.C.mu0 i).UnrAt PP := (L.C.isMu0 i).unr PP fun l hl =>
      not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
    have hx : (L.xiH t).UnrAt PP := by
      intro x hx
      have h1 : (L.C.mu0 i).loc PP x * (L.xiH t).loc PP x = 1 := hu x hx
      rwa [hm x hx, one_mul] at h1
    exact (hL.Q_ram t PP).2 (Or.inl hQ) hx

end GlobalTheory.MtIn.Under

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdSideUnique
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Col Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.StdUnique

theorem closed_eq_univ {D : D7} (V : HSp D) (C : Set (GA D V)) (hC : IsClosed C) (hQ : ∀ γ ∈ GQ V, γ ∈ C)
    (hf : ∀ h, ∀ k ∈ GfC V, h ∈ C → h * k ∈ C) (h : GA D V) : h ∈ C := by
  obtain ⟨e, he⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  have hfin : ∀ h : GA D V, (e h).2 = 1 → h ∈ GinfC V := fun h H =>
    MonoidHom.mem_ker.2 (Units.ext ((he h).1.symm.trans (by rw [H]; rfl)))
  have hinf : ∀ h : GA D V, (e h).1 = 1 → h ∈ GfC V := fun h H =>
    MonoidHom.mem_ker.2 (Units.ext ((he h).2.symm.trans (by rw [H]; rfl)))
  have hu : e.symm ((e h).1, 1) ∈ C := by
    by_contra hn
    obtain ⟨γ, hγ, k, hk, hU, -⟩ := GlobalTheory.RealApprox.weak_approx_real V _ (hfin _ (by rw [e.apply_symm_apply])) Cᶜ
      hC.isOpen_compl hn
    exact hU (hf γ k hk (hQ γ hγ))
  have hk : e.symm (1, (e h).2) ∈ GfC V := hinf _ (by rw [e.apply_symm_apply])
  have := hf _ _ hk hu
  rwa [← map_mul, Prod.mk_mul_mk, mul_one, one_mul, Prod.mk.eta, e.symm_apply_apply] at this

variable {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is)
include hc

theorem bot_or_top (U : Submodule ℂ c.W) (hU : ∀ γ ∈ GQ V, ∀ w ∈ U, c.ρ γ w ∈ U) : U = ⊥ ∨ U = ⊤ := by
  refine hc.2.2.2.2 U fun h => ?_
  rintro _ ⟨w, hw, rfl⟩
  refine closed_eq_univ V {h | c.ρ h w ∈ U} (U.closed_of_finiteDimensional.preimage (hc.2.2.1 w))
    (fun γ hγ => hU γ hγ w hw) (fun h k hk H => ?_) h
  show c.ρ (h * k) w ∈ U
  rw [map_mul, hc.1 k hk, mul_one]
  exact H


omit hc in
theorem exists_ratMat (γ : GQ V) : ∃ γE, Bridge.IsRatMat V γ γE := by
  obtain ⟨γ, ⟨g, -, hg⟩⟩ := γ
  exact ⟨g, hg.symm⟩

omit hc

end GlobalTheory.Mem.StdUnique

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjUniformizerIsUniformizerConjPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjUniformizerIsUniformizerConjPrime
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

namespace GlobalTheory.Mem.UnifConj

theorem conj_unif_isUnif : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (Pb : Formalism.L2.DIV.Pl E) (Ut : Formalism.L2.Col.MhlUnif Pb), Formalism.L2.Col.cO E Ut.π ∈ (Formalism.L2.Col.conjPrime₂ Pb).asIdeal ∧ Formalism.L2.Col.cO E Ut.π ∉ (Formalism.L2.Col.conjPrime₂ Pb).asIdeal ^ 2 := by
  intro E _ _ _ Pb Ut
  refine ⟨(Formalism.L2.Col.mem_conjP Pb _).2 (by rw [Formalism.L2.Col.cO_cO]; exact Ut.hπ), ?_⟩
  intro h
  have h2 : Ut.π ∈ Pb.asIdeal ^ 2 := by
    have h1 : Formalism.L2.Col.cO E Ut.π ∈ (Pb.asIdeal ^ 2).comap (Formalism.L2.Col.cO E) :=
      Ideal.le_comap_pow (Formalism.L2.Col.cO E) 2 h
    rw [Ideal.mem_comap, Formalism.L2.Col.cO_cO] at h1
    exact h1
  have hle : Pb.asIdeal ≤ Pb.asIdeal ^ 2 := by
    intro p hp
    obtain ⟨t, ht⟩ := Ut.hcπ p hp
    have hcp : Ut.c * p ∈ Pb.asIdeal ^ 2 := by
      rw [ht]; exact Ideal.mul_mem_right t _ h2
    obtain ⟨a, e, he, hae⟩ := Pb.isMaximal.exists_inv Ut.hc
    have hee : e * e ∈ Pb.asIdeal ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul he he
    have hp' : p = a * (a * Ut.c + 2 * e) * (Ut.c * p) + (e * e) * p := by
      linear_combination (-(p) * (a * Ut.c + e + 1)) * hae
    rw [hp']
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hcp) (Ideal.mul_mem_right _ _ hee)
  have hlt : Pb.asIdeal ^ 2 < Pb.asIdeal ^ 1 :=
    Ideal.pow_right_strictAnti Pb.asIdeal Pb.ne_bot Pb.isPrime.ne_top (by norm_num)
  rw [pow_one] at hlt
  exact hlt.not_ge hle

end GlobalTheory.Mem.UnifConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjUniformizerIsUniformizerConjPrimeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_uniformizer_isUniformizer_conjPrime : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (Pb : Formalism.L2.DIV.Pl E) (Ut : Formalism.L2.Col.MhlUnif Pb), Formalism.L2.Col.cO E Ut.π ∈ (Formalism.L2.Col.conjPrime₂ Pb).asIdeal ∧ Formalism.L2.Col.cO E Ut.π ∉ (Formalism.L2.Col.conjPrime₂ Pb).asIdeal ^ 2 := by
  first | exact @GlobalTheory.Mem.UnifConj.conj_unif_isUnif | exact GlobalTheory.Mem.UnifConj.conj_unif_isUnif | (intros; apply GlobalTheory.Mem.UnifConj.conj_unif_isUnif <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftResidueTwistCharacterEqResChar
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftResidueTwistCharacterEqResChar
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Mem.LevResXi

theorem xiR_eq_map_resChar : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)),
    I.Ok → ValsIn I → LevOf X I U L → ∀ (t : TupU I U) (PP : HeightOneSpectrum (𝓞 X.B.fields.E)), PP ∈ Formalism.L2.Col.QE I.sel t.1 →
      ∀ c : (𝓞 X.B.fields.E ⧸ PP.asIdeal)ˣ, L.xiR t PP c = Units.map X.toD7.what₂.embLL.toMonoidHom
        (Formalism.L2.DIV.resChar (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) PP c) := by
  intro X px I U L hI hV hL t PP hPP c
  have hQ : PP ∈ L.Q t := by
    rw [hL.Q t]
    change PP ∈ Formalism.L2.Col.QE I.sel (I.tup (ixOf I U t))
    rw [tup_ixOf]
    exact hPP
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (c : 𝓞 X.B.fields.E ⧸ PP.asIdeal)
  have hn : b ∉ PP.asIdeal := fun hm => c.ne_zero (hb ▸ Ideal.Quotient.eq_zero_iff_mem.2 hm)
  have h0 : (b : X.B.fields.E) ≠ 0 := fun e => hn ((RingOfIntegers.coe_eq_zero_iff.1 e) ▸ zero_mem _)
  have h1 := hL.is.xiR t PP hQ b (Units.mk0 _ h0) c rfl hb.symm
  have ht : ∀ P, (I.xi (ixOf I U t)).TameAt P := fun P => hL.xiH t ▸ hL.is.xi_tame t P
  have h2 := GlobalTheory.NormOneUnit.resChar_eq (hI.xi_reads (ixOf I U t)) ht PP c b (Units.mk0 _ h0) rfl hb
  rw [tup_ixOf] at h2
  rw [hL.xiH t] at h1
  refine Units.ext ?_
  rw [h1]
  exact h2.symm

end GlobalTheory.Mem.LevResXi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftResidueTwistCharacterEqResCharStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftResidueTwistCharacter_eq_resChar : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)),
    I.Ok → ValsIn I → LevOf X I U L → ∀ (t : TupU I U) (PP : HeightOneSpectrum (𝓞 X.B.fields.E)), PP ∈ Formalism.L2.Col.QE I.sel t.1 →
      ∀ c : (𝓞 X.B.fields.E ⧸ PP.asIdeal)ˣ, L.xiR t PP c = Units.map X.toD7.what₂.embLL.toMonoidHom
        (Formalism.L2.DIV.resChar (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) PP c) := by
  first | exact @GlobalTheory.Mem.LevResXi.xiR_eq_map_resChar | exact GlobalTheory.Mem.LevResXi.xiR_eq_map_resChar | (intros; apply GlobalTheory.Mem.LevResXi.xiR_eq_map_resChar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsDetAtUnram
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.DetUnit

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem det_mem_intAE (V : HSp D) (g : GA D V)
    (h : ∀ y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V),
      finMat D.sp.cm.sig V.gram g *ᵥ y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V)) :
    finPart D (Formalism.L2.Theta.mt V g).det ∈ intAE D := by
  obtain ⟨L, hL, hfg, hsp⟩ := GlobalTheory.SplitHeckeLabel.exists_coord_lattice V
  have hd : finPart D (Formalism.L2.Theta.mt V g).det = (finMat D.sp.cm.sig V.gram g).det :=
    RingHom.map_det (finPart D) (Formalism.L2.Theta.mt V g)
  rw [hd, GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers]
  rw [← hL] at h
  exact GlobalTheory.DetTranslate.det_mem_int D.host.F L _ hfg hsp h

theorem part_mem_intAE {e d : AE D} (he : e * e = e) (hd : finPart D d ∈ intAE D) :
    finPart D (e * d + (1 - e)) ∈ intAE D := by
  have h1 : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he])
  have h2 : finPart D (1 - e) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul]; congr 1; linear_combination he)
  rw [RingHom.map_add (f := _), RingHom.map_mul]
  exact add_mem (GlobalTheory.SplitHeckeLabel.mul_mem_intA h1 hd) h2

theorem exists_isDetAt_unram : ∀ (D : D7) (V : HSp D) (ε : AF D.host.F) (e : AE D), IsSplitIdem D e → e + cA D e = algebraMap (AF D.host.F) (AE D) ε → ∀ g ∈ KsphC V ∅, ∃ x, IsDetAt e V g x ∧ ∀ χ : (AE D)ˣ →* Circle, UnramAt ε χ → χ x = 1 := by
  intro D V ε e he hε g hg
  obtain ⟨h1, h0, -⟩ := he
  have hm : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hd : (Formalism.L2.Theta.mt V g).det * (Formalism.L2.Theta.mt V g⁻¹).det = 1 := by
    rw [← Matrix.det_mul, hm, Matrix.det_one]
  have hf : finMat D.sp.cm.sig V.gram g * finMat D.sp.cm.sig V.gram g⁻¹ = 1 := by
    change (finHom V g).1 * (finHom V g⁻¹).1 = 1
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have i1 := det_mem_intAE V g fun y hy => (hg.2.1 y).1 hy
  have i2 := det_mem_intAE V g⁻¹ fun y hy => (hg.2.1 _).2 (by rw [Matrix.mulVec_mulVec, hf, Matrix.one_mulVec]; exact hy)
  generalize (Formalism.L2.Theta.mt V g⁻¹).det = d' at hd i2
  have hx : (e * (Formalism.L2.Theta.mt V g).det + (1 - e)) * (e * d' + (1 - e)) = 1 := by
    linear_combination e * e * hd + (2 - (Formalism.L2.Theta.mt V g).det - d') * h1
  refine ⟨⟨_, _, hx, (mul_comm _ _).trans hx⟩, rfl, fun χ hχ => hχ _ ?_ (part_mem_intAE h1 i1) (part_mem_intAE h1 i2)⟩
  rw [← hε]
  change (e + cA D e) * (e * (Formalism.L2.Theta.mt V g).det + (1 - e) - 1) = e * (Formalism.L2.Theta.mt V g).det + (1 - e) - 1
  linear_combination ((Formalism.L2.Theta.mt V g).det - 1) * h1 + ((Formalism.L2.Theta.mt V g).det - 1) * h0

end GlobalTheory.Mem.DetUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrimeIdempotentMulEqZeroOfVanishingAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrimeIdempotentMulEqZeroOfVanishingAtPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
noncomputable section

namespace GlobalTheory.IdemSupp

variable {D : D7}

def singleL (v : HeightOneSpectrum (𝓞 D.host.F)) : Fv D.host.F v →ₗ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F where
  toFun y := singleV D.host.F v y
  map_add' x y := by
    have h := GlobalTheory.IdemModTwo.singleV_sub (D := D) v (x + y) y
    rw [add_sub_cancel_right] at h
    rw [h, sub_add_cancel]
  map_smul' c y := by
    rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, GlobalTheory.IdemModTwo.singleV_mul (D := D), AlgHom.commutes]

theorem pl_mul_eq (v : HeightOneSpectrum (𝓞 D.host.F)) (z : Formalism.IndefR.Lev.EAf D) :
    swapAE D (finPart D (GlobalTheory.IdemModTwo.pl D v)) * z =
      TensorProduct.map (LinearMap.id : D.host.E →ₗ[D.host.F] D.host.E) (singleL (D := D) v) (Formalism.UG.prV v z) := by
  change ((1 : D.host.E) ⊗ₜ[D.host.F] singleV D.host.F v 1) * z = _
  induction z using TensorProduct.induction_on with
  | zero => rw [mul_zero, map_zero, map_zero]
  | tmul x a =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    change _ = x ⊗ₜ[D.host.F] singleV D.host.F v (evalV D.host.F v a)
    rw [mul_comm, GlobalTheory.IdemModTwo.singleV_mul (D := D), mul_one]
  | add x y hx hy => simp only [mul_add, hx, hy, map_add (f := _)]

theorem idem_mul_eq_zero : ∀ {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (e : Formalism.L2.Theta.AE D), Formalism.L2.Col.IsOver v Pb → Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → ∀ z : Formalism.IndefR.Lev.EAf D, Formalism.UG.prV v z = 0 → swapAE D (finPart D e) * z = 0 := by
  intro D v Pb e hov he z hz
  have hov' := Formalism.L2.Col.IsOver.conj D.sp.cm hov
  have hsp := GlobalTheory.GridIdem.splitAt_under he
  have hu : (Formalism.L2.Col.conjPrime₂ Pb).under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hov'.symm
  rw [hu] at hsp
  rw [← hsp.pl_mul, map_mul, map_mul, mul_comm (swapAE D _), mul_assoc, pl_mul_eq, hz, map_zero, mul_zero]

end GlobalTheory.IdemSupp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrimeIdempotentMulEqZeroOfVanishingAtPlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjPrimeIdempotent_mul_eq_zero_of_vanishing_at_place : ∀ {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (e : Formalism.L2.Theta.AE D), Formalism.L2.Col.IsOver v Pb → Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → ∀ z : Formalism.IndefR.Lev.EAf D, Formalism.UG.prV v z = 0 → swapAE D (finPart D e) * z = 0 := by
  first | exact @GlobalTheory.IdemSupp.idem_mul_eq_zero | exact GlobalTheory.IdemSupp.idem_mul_eq_zero | (intros; apply GlobalTheory.IdemSupp.idem_mul_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleTwistRamifiedIffChosenPrimeOrConjHost
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.Col2.RamQ

theorem not_unr_iff_under_mem (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hI : I.Ok) (a : I.ι)
    (PP : HeightOneSpectrum (𝓞 X.B.host.E)) :
    ¬ (I.xi a).UnrAt PP ↔ PP.under (𝓞 X.B.host.F) ∈ Qprime (I.tup a : Chr X.B.fields.F X.B.fields.E X.B.fields.K) := by
  obtain ⟨htw, hq, -⟩ := GlobalTheory.Mem.ReadTwist.isTwist_of_reads X.B.R X.B.host X.B.fields.K X.B.embLL I.S (I.tup a) (I.xi a)
    (hI.xi_reads a)
  rw [hq]
  refine ⟨fun h => ⟨PP, rfl, h⟩, ?_⟩
  rintro ⟨P, hP, hn⟩ hu
  apply hn
  intro x hx
  have h1 := GlobalTheory.Mem.Chr.twist_pow_units_of_under_eq X.B.R X.B.host I.S (I.xi a) htw P PP hP 1
    (fun y hy => by rw [pow_one]; exact hu y hy) x hx
  simpa using h1

theorem tupleTwist_ramified_iff_chosenPrime_or_conj_host (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hI : I.Ok) (a : I.ι)
    (PP : HeightOneSpectrum (𝓞 X.B.host.E)) :
    ¬ (I.xi a).UnrAt PP ↔ PP ∈ I.Q a ∨ ∃ PP' ∈ I.Q a, Formalism.IndefR.Lev.IsConjPl (D := X.toD7) PP' PP := by
  classical
  rw [not_unr_iff_under_mem X px I hI a PP]
  have hf := Formalism.L2.DIV.auxiliary_primes_finite X.B.fields.F X.B.fields.E X.B.fields.K (I.tup a : Chr X.B.fields.F X.B.fields.E X.B.fields.K)
    (I.tup a).2.1.1.1.1.2
  have hsel : ∀ v, (I.sel v).under (𝓞 X.B.fields.F) = v := fun v => HeightOneSpectrum.ext (hI.sel_ok v)
  have memQ : ∀ v ∈ Qprime (I.tup a : Chr X.B.fields.F X.B.fields.E X.B.fields.K), I.sel v ∈ I.Q a := fun v hv => by
    unfold ColIn.Q
    rw [Formalism.L2.Col.QE, dite_eq_left hf]
    exact Finset.mem_image_of_mem _ (hf.mem_toFinset.2 hv)
  have under_of_mem : ∀ P ∈ I.Q a, P.under (𝓞 X.B.host.F) ∈ Qprime (I.tup a : Chr X.B.fields.F X.B.fields.E X.B.fields.K) :=
    fun P hP => by
      obtain ⟨v, hv, hs, -⟩ := ColIn.exists_of_mem_Q I hP
      rw [← hs, hsel]
      exact hv
  constructor
  · intro hv
    have key : ∀ Q P : Pl X.toD7.host.E, Q.under (𝓞 X.toD7.host.F) = P.under (𝓞 X.toD7.host.F) →
        Q = P ∨ Q = Formalism.DivisionValues.conjPl P := fun Q P h => GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq h
    have e : PP.under (𝓞 X.B.host.F) = (I.sel (PP.under (𝓞 X.B.host.F))).under (𝓞 X.B.fields.F) := (hsel _).symm
    rcases key PP (I.sel (PP.under (𝓞 X.B.host.F))) e with h | h
    · left
      rw [h]
      exact memQ _ hv
    · right
      exact ⟨_, memQ _ hv, GlobalTheory.GoodPrimes.isConjPl_iff.2 h⟩
  · rintro (h | ⟨PP', h, hc⟩)
    · exact under_of_mem _ h
    · have e : PP'.under (𝓞 X.B.host.F) = PP.under (𝓞 X.B.host.F) := GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc
      rw [← e]
      exact under_of_mem _ h

theorem ram_iff : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), I.Ok → ∀ (a : I.ι) (PP : Pl X.toD7.host.E),
    ¬ (I.xi a).UnrAt PP ↔ PP ∈ I.Q a ∨ ∃ PP' ∈ I.Q a, Formalism.IndefR.Lev.IsConjPl (D := X.toD7) PP' PP :=
  fun X px I hI a PP => tupleTwist_ramified_iff_chosenPrime_or_conj_host X px I hI a PP

end GlobalTheory.Mem.Col2.RamQ

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericUnipotentCharacterAtSideEqThetaSide
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericUnipotentCharacterAtSideEqThetaSide
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

theorem star_mul_self_of_pow (D : D7) (ζ : (↥D.LL0)ˣ) (n : ℕ) (hn : n ≠ 0) (h : ζ ^ n = 1) :
    star ((ζ : ↥D.LL0) : D.what₂.LL) * ((ζ : ↥D.LL0) : D.what₂.LL) = 1 := by
  apply D.what₂.embLL.injective
  rw [map_mul, map_one, D.starLL_cx]
  have hp : ((ζ : ↥D.LL0) : D.what₂.LL) ^ n = 1 := by
    have e := congrArg (fun u : (↥D.LL0)ˣ => ((u : ↥D.LL0) : D.what₂.LL)) h
    simpa using e
  have hz : (D.what₂.embLL ((ζ : ↥D.LL0) : D.what₂.LL)) ^ n = 1 := by
    rw [← map_pow, hp, map_one]
  have hn1 : ‖D.what₂.embLL ((ζ : ↥D.LL0) : D.what₂.LL)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz hn
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn1]
  simp

theorem readT_false_eq (D : D7) (T : TwR D.LL0 D.nd) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0)
    (i : T.Tw) (x : ↥D.LL0) : readT D T i false x = readT D T i true ⟨star (x : D.what₂.LL), hstar x⟩ := by
  simp only [readT, RingHom.comp_apply, Bool.false_eq_true, if_false, if_true]
  rw [T.restX_coefficientEmbedding_conj i x ⟨star (x : D.what₂.LL), hstar x⟩ rfl]

theorem readT_false_mul_true (D : D7) (T : TwR D.LL0 D.nd) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0)
    (i : T.Tw) (ζ : (↥D.LL0)ˣ) (n : ℕ) (hn : n ≠ 0) (h : ζ ^ n = 1) :
    readT D T i false (ζ : ↥D.LL0) * readT D T i true (ζ : ↥D.LL0) = 1 := by
  rw [readT_false_eq D T hstar, ← map_mul]
  have e : (⟨star ((ζ : ↥D.LL0) : D.what₂.LL), hstar _⟩ : ↥D.LL0) * (ζ : ↥D.LL0) = 1 :=
    Subtype.ext (star_mul_self_of_pow D ζ n hn h)
  rw [e, map_one]

theorem mul_pow_g_eq_one (g : ℕ) (m : Multiplicative (ZMod g)) : m ^ g = 1 := by
  rw [← ofAdd_toAdd m, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]

theorem psiUT_eq_thSide : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd),
    (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    (∀ i b (u : Formalism.IndefR.NX.U D.nd), psiUT D T In.θ i b u = psiUOf D.nd (NX.xiRed D)
      (thSide D.host.g (fun k => (Units.map (readT D T i true).toMonoidHom).comp (In.θ k)) b) u) ∧
    (2 ≤ D.R.r → ∀ i k, (Units.map (readT D T i true).toMonoidHom).comp (In.θ k) ≠ 1) := by
  intro D S In T hstar
  refine ⟨fun i b u => ?_, fun _ i k h => ?_⟩
  · simp only [psiUT, MonoidHom.comp_apply, psiUOf_apply, map_prod]
    refine Finset.prod_congr rfl fun kv _ => ?_
    cases b
    · simp only [thSide, Bool.false_eq_true, if_false, MonoidHom.inv_apply, MonoidHom.comp_apply]
      apply Units.ext
      rw [Units.coe_map, Units.val_inv_eq_inv_val, Units.coe_map]
      refine eq_inv_of_mul_eq_one_left ?_
      exact readT_false_mul_true D T hstar i _ (D.host.g kv.1) (D.host.g_prime kv.1).ne_zero
        (by rw [← map_pow, mul_pow_g_eq_one, map_one])
    · rfl
  · apply In.θ_ne k
    refine MonoidHom.ext fun x => Units.ext ?_
    apply (readT D T i true).injective
    have e := congrArg (fun u : (FractionRing (T.O i))ˣ => (u : FractionRing (T.O i))) (DFunLike.congr_fun h x)
    simpa using e

end GlobalTheory.HeightCounting.FormsStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericUnipotentCharacterAtSideEqThetaSideStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericUnipotentCharacterAtSide_eq_thetaSide : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd),
    (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    (∀ i b (u : Formalism.IndefR.NX.U D.nd), psiUT D T In.θ i b u = psiUOf D.nd (NX.xiRed D)
      (thSide D.host.g (fun k => (Units.map (readT D T i true).toMonoidHom).comp (In.θ k)) b) u) ∧
    (2 ≤ D.R.r → ∀ i k, (Units.map (readT D T i true).toMonoidHom).comp (In.θ k) ≠ 1) := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.psiUT_eq_thSide | exact GlobalTheory.HeightCounting.FormsStep.psiUT_eq_thSide | (intros; apply GlobalTheory.HeightCounting.FormsStep.psiUT_eq_thSide <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftFormLevelSplitsAtOffLevelSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftFormLevelSplitsAtOffLevelSplitPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

namespace GlobalTheory.Mem.R3.LiftBrg.LevSplitAt

set_option maxHeartbeats 4000000

theorem lev_split_at : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hV : ValsIn I) (hL : LevOf X I U L) (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (x : (famR X I hX U Xg tr).A.ok t × ℕ) (j : Bridge.Gf (Vc X.toD7 i)) (hj : j ∈ (envL X I hX U Xg tr L cV i t).lev.J),
    ∃ j₁ ∈ (envL X I hX U Xg tr L cV i t).lev.J, ∃ j₂ ∈ (envL X I hX U Xg tr L cV i t).lev.J,
      (envL X I hX U Xg tr L cV i t).isLoc x j₁ ∧ j = j₁ * j₂ ∧
      ∀ l, (envL X I hX U Xg tr L cV i t).isLoc x l → Commute j₂ l := by
  intro X px I hX U Xg tr L hI hV hL cV i t x j hj
  classical
  set L' := L.datVt i t with hL'
  set P : Formalism.L2.DIV.Pl X.toD7.host.E := (x.1.1.1 : Formalism.L2.DIV.Pl X.toD7.host.E) with hPdef
  have hoffP : P ∈ Formalism.L2.DIV.offSet ∅ (sgL X I U t) ∅ := x.1.2
  obtain ⟨hPc, hPn, hPq⟩ := hoffP

  obtain ⟨c, hβ⟩ := hL.is.βV i
  rw [one_pow] at hβ

  have hPg : ∀ PP ∈ (flag1L L').Pg, PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 := by
    intro PP hPP
    rw [show (flag1L L').Pg = L.Pg from rfl, hL.Pg] at hPP
    exact Finset.mem_union.2 (Or.inl hPP)
  have hQ : ∀ PP ∈ (flag1L L').Q, PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 := by
    intro PP hPP
    rw [show (flag1L L').Q = L.Q t from rfl, hL.Q t] at hPP
    have e4 : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel t.1 := by
      simp only [ColIn.Q, tup_ixOf]
    rw [e4] at hPP
    exact Finset.mem_union.2 (Or.inr hPP)
  have hoff : ∀ PP, PP ∈ (flag1L L').Pg ∨ PP ∈ (flag1L L').Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := by
    intro PP hPP
    have hm : PP ∈ sgL X I U t := hPP.elim (hPg PP) (hQ PP)
    refine ⟨fun e => hPn ?_, fun hc => hPq PP ?_ ?_⟩
    · subst e; simp [hm]
    · simp [hm]
    · rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq, GlobalTheory.SplitHeckeAdj.eq_conj_of_isConjPl hc, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]

  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt P hPc
  have hpi : IsPrimeIdem P e (e + cA X.toD7 e) := Or.inl ⟨he, rfl⟩
  have h01 := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents (Vc X.toD7 i)).2.2.1 P e _ hpi
  have hff := h01.1
  have hcf := h01.2.1
  have h1 : ((1 : ℕ) : 𝓞 X.toD7.host.E) ∉ P.asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  obtain ⟨-, -, hsp⟩ := (GlobalTheory.LevSplit.lev_split (Vc X.toD7 i) (L.βV i) (L.ΛV i) 1 (flag1L L') hβ).2 P e _ hpi h1 hoff
  obtain ⟨g, hg, hgj⟩ := GlobalTheory.SplitHeckeAdj.fin_lift (Vc X.toD7 i) j
  have hj' : GlobalTheory.SplitHeckeAdj.fin (Vc X.toD7 i) g ∈ (levEnv (Vc X.toD7 i) (L.βV i) L').J := by rw [hgj]; exact hj
  obtain ⟨k₁, h₁, k₂, h₂, s₁, s₂, hk⟩ := hsp g ((GlobalTheory.SplitHeckeAdj.mem_J (Vc X.toD7 i) (L.βV i) L' hg).1 hj')
  refine ⟨GlobalTheory.SplitHeckeAdj.fin (Vc X.toD7 i) k₁, (GlobalTheory.SplitHeckeAdj.mem_J (Vc X.toD7 i) (L.βV i) L' h₁.1).2 h₁,
    GlobalTheory.SplitHeckeAdj.fin (Vc X.toD7 i) k₂, (GlobalTheory.SplitHeckeAdj.mem_J (Vc X.toD7 i) (L.βV i) L' h₂.1).2 h₂, ⟨e, k₁, he, h₁.1, s₁, rfl⟩,
    by rw [← hgj, hk, map_mul], ?_⟩
  intro l hl
  obtain ⟨a, ha, rfl⟩ := GlobalTheory.SplitHeckeAdj.loc_supp (Vc X.toD7 i) hl he
  exact (GlobalTheory.SplitHeckeAdj.commute_compl (Vc X.toD7 i) _ hff hcf ha s₂).symm.map (GlobalTheory.SplitHeckeAdj.fin (Vc X.toD7 i))

end GlobalTheory.Mem.R3.LiftBrg.LevSplitAt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftFormLevelSplitsAtOffLevelSplitPlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftFormLevel_splits_at_offLevel_splitPlace : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hV : ValsIn I) (hL : LevOf X I U L) (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (x : (famR X I hX U Xg tr).A.ok t × ℕ) (j : Bridge.Gf (Vc X.toD7 i)) (hj : j ∈ (envL X I hX U Xg tr L cV i t).lev.J),
    ∃ j₁ ∈ (envL X I hX U Xg tr L cV i t).lev.J, ∃ j₂ ∈ (envL X I hX U Xg tr L cV i t).lev.J,
      (envL X I hX U Xg tr L cV i t).isLoc x j₁ ∧ j = j₁ * j₂ ∧
      ∀ l, (envL X I hX U Xg tr L cV i t).isLoc x l → Commute j₂ l := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.LevSplitAt.lev_split_at | exact GlobalTheory.Mem.R3.LiftBrg.LevSplitAt.lev_split_at | (intros; apply GlobalTheory.Mem.R3.LiftBrg.LevSplitAt.lev_split_at <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TransportedClassSetPresentationReadsEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TransportedClassSetPresentationReadsEquivariant
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Mem.TransportRead

theorem transport_ext_eq : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {S : Formalism.L2.Col.GSD K} {G Γ G' Γ' : Type}
    [Group G] [Group Γ] [Group G'] [Group Γ'] {ι : Γ →* G} {J : Subgroup G} (A : Bridge.AdPts S ι J) (h : S.Ok)
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (χ : J →* ℂˣ)
    (coef : S.V →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => coef (S.bV i))
    (hspan : Submodule.span ℂ (Set.range fun i => coef (S.bV i)) = ⊤)
    (hpair : ∀ x x', inner ℂ (coef x) (coef x') = σ (S.pair x x')) (hK1 : ∀ k : J, (k : G) ∈ A.K1 → χ k = 1)
    (hgl : ∀ (γ : Γ) (k : J) (v : S.V), coef (S.ρ (A.gl (γ, k)) v) = ((χ k)⁻¹ : ℂˣ) • ρ γ (coef v))
    {ι' : Γ' →* G'} {ρ' : Γ' →* Module.End ℂ W} {J' : Subgroup G'} {χ' : J' →* ℂˣ}
    (eG : G ≃* G') (eΓ : Γ ≃* Γ') (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ)) (hρ : ∀ γ, ρ' (eΓ γ) = ρ γ)
    (hJ : J' = J.map eG.toMonoidHom) (hχ : ∀ (k : J) (hk : eG k ∈ J'), χ' ⟨eG k, hk⟩ = χ k)
    (f : (S.toCSD h).Forms) (g : G'),
    ((Bridge.classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).transport eG eΓ hι hρ hJ hχ).ext (f : S.Cl → S.V) g =
      coef ((((S.res h).symm f : S.EqFun) : S.D → S.V) (A.q (eG.symm g))) := by
  intro K _ _ _ S G Γ G' Γ' _ _ _ _ ι J A h W _ _ σ ρ χ coef hli hspan hpair hK1 hgl ι' ρ' J' χ' eG eΓ hι hρ hJ hχ f g
  set P' := (Bridge.classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).transport eG eΓ hι hρ hJ hχ with hP'
  have hJ' : ∀ x, x ∈ J' ↔ eG.symm x ∈ J := fun x => by subst hJ; exact Subgroup.mem_map_equiv
  have hspec := P'.dec_spec g
  set γ' := P'.decG g
  set c := P'.decC g
  set k' := P'.decK g
  have hy : P'.y c = eG (A.y c) := rfl
  have hc : P'.coef = coef := rfl
  let k'' : J := ⟨eG.symm (k' : G'), (hJ' _).1 k'.2⟩
  have hg : eG.symm g = ι (eΓ.symm γ') * A.y c * (k'' : G) := by
    have e : ι (eΓ.symm γ') = eG.symm (ι' γ') := by
      rw [MulEquiv.eq_symm_apply, ← hι, MulEquiv.apply_symm_apply]
    rw [e, hspec, hy]
    simp only [map_mul, MulEquiv.symm_apply_apply, k'']
  have hq : A.q (eG.symm g) = A.gl (eΓ.symm γ', k''⁻¹) • S.outSec.rep c := by
    rw [hg, A.q_mul, A.q_y]
  set φ := (S.res h).symm f with hφ
  have hφc : ((φ : S.EqFun) : S.D → S.V) (S.outSec.rep c) = (f : S.Cl → S.V) c := by
    have := Formalism.L2.Col.GSD.resOf_apply S h S.outSec φ c
    rw [← this]
    show (((S.res h) φ).1 : S.Cl → S.V) c = (f : S.Cl → S.V) c
    rw [hφ, LinearEquiv.apply_symm_apply]
  have hk : k' = ⟨eG (k'' : G), by simp only [k'', MulEquiv.apply_symm_apply]; exact k'.2⟩ :=
    Subtype.ext (by simp only [k'', MulEquiv.apply_symm_apply])
  rw [hq, φ.2, hφc, hgl]
  show (χ' k' : ℂ) • ρ' γ' (P'.coef ((f : S.Cl → S.V) c)) = _
  rw [hc, hk, hχ]
  have hγ : ρ' γ' = ρ (eΓ.symm γ') := by rw [← hρ, MulEquiv.apply_symm_apply]
  rw [hγ, map_inv, inv_inv, Units.smul_def]

end GlobalTheory.Mem.TransportRead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TransportedClassSetPresentationReadsEquivariantStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transportedClassSetPresentation_reads_equivariant : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {S : Formalism.L2.Col.GSD K} {G Γ G' Γ' : Type}
    [Group G] [Group Γ] [Group G'] [Group Γ'] {ι : Γ →* G} {J : Subgroup G} (A : Bridge.AdPts S ι J) (h : S.Ok)
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (χ : J →* ℂˣ)
    (coef : S.V →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => coef (S.bV i))
    (hspan : Submodule.span ℂ (Set.range fun i => coef (S.bV i)) = ⊤)
    (hpair : ∀ x x', inner ℂ (coef x) (coef x') = σ (S.pair x x')) (hK1 : ∀ k : J, (k : G) ∈ A.K1 → χ k = 1)
    (hgl : ∀ (γ : Γ) (k : J) (v : S.V), coef (S.ρ (A.gl (γ, k)) v) = ((χ k)⁻¹ : ℂˣ) • ρ γ (coef v))
    {ι' : Γ' →* G'} {ρ' : Γ' →* Module.End ℂ W} {J' : Subgroup G'} {χ' : J' →* ℂˣ}
    (eG : G ≃* G') (eΓ : Γ ≃* Γ') (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ)) (hρ : ∀ γ, ρ' (eΓ γ) = ρ γ)
    (hJ : J' = J.map eG.toMonoidHom) (hχ : ∀ (k : J) (hk : eG k ∈ J'), χ' ⟨eG k, hk⟩ = χ k)
    (f : (S.toCSD h).Forms) (g : G'),
    ((Bridge.classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).transport eG eΓ hι hρ hJ hχ).ext (f : S.Cl → S.V) g =
      coef ((((S.res h).symm f : S.EqFun) : S.D → S.V) (A.q (eG.symm g))) := by
  first | exact @GlobalTheory.Mem.TransportRead.transport_ext_eq | exact GlobalTheory.Mem.TransportRead.transport_ext_eq | (intros; apply GlobalTheory.Mem.TransportRead.transport_ext_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamRdefEqSgTrue
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.RowWeight

lemma isWtOfPar_eq {N n : ℕ} (h : N = n) {lam : DomWeight N} {S : SPar} (hS : Bridge.IsWtOfPar lam S)
    (hs : ∀ x ∈ S, x.2 = true) (c' : Fin n → ℚ) (hc' : StrictAnti c') (hm' : ∀ i, (c' i, true) ∈ S) (i : Fin N) :
    (lam.w i : ℚ) = c' (Fin.cast h i) - rhoVec n (Fin.cast h i) := by
  subst h
  obtain ⟨hcard, c, hc, hm, hw⟩ := hS
  have key : ∀ d : Fin N → ℚ, StrictAnti d → (∀ i, (d i, true) ∈ S) → Set.range d = {x | (x, true) ∈ S} := by
    intro d hd hdm
    have h1 : Finset.univ.image (fun i => (d i, true)) = S := by
      refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
        exact hdm i
      · rw [Finset.card_image_of_injective _ (fun x y h => hd.injective (Prod.ext_iff.mp h).1), hcard]
        simp
    ext x
    rw [← h1]
    simp
  have hm2 : ∀ i, (c i, true) ∈ S := fun i => by
    obtain ⟨s, hs'⟩ := hm i
    have : s = true := hs _ hs'
    rwa [this] at hs'
  have e : c = c' := (hc.range_inj hc').1 ((key c hc hm2).trans (key c' hc' hm').symm)
  rw [hw, e]
  rfl

lemma sgHC_mem {R : Ranks} (P : HCParam R) (n : ℕ) (hn : n < R.N R.m - 1) :
    ∃ x, GlobalTheory.ForcedWeights.entry P x = (Formalism.L2.Col.RowPar.of P).sgHC n - Formalism.L2.Col.RowPar.sh R := by
  have hk := R.m_add_three_le_k
  unfold Ranks.N at hn
  by_cases h1 : n < R.k - 1
  · refine ⟨.inl ⟨n, h1⟩, ?_⟩
    rw [Formalism.L2.Col.RowPar.sgHC_lo _ h1, Formalism.L2.Col.RowPar.vb_lo _ h1]
    simp [GlobalTheory.ForcedWeights.entry]
  · obtain ⟨B, ρ, hρ, rfl⟩ : ∃ B ρ, ρ < R.t + 1 ∧ n = R.k - 1 + B * (R.t + 1) + ρ := by
      refine ⟨(n - (R.k - 1)) / (R.t + 1), (n - (R.k - 1)) % (R.t + 1), Nat.mod_lt _ (by omega), ?_⟩
      have := Nat.div_add_mod (n - (R.k - 1)) (R.t + 1)
      rw [Nat.mul_comm] at this
      omega
    have hBm : B < R.m := by
      apply Nat.lt_of_mul_lt_mul_right (a := R.t + 1)
      omega
    rcases ρ with _ | ρ
    · refine ⟨.inr (.inl ⟨B, hBm⟩), ?_⟩
      rw [Nat.add_zero, Formalism.L2.Col.RowPar.sgHC_b, Formalism.L2.Col.RowPar.bAt_of _ hBm]
      simp [GlobalTheory.ForcedWeights.entry]
    · refine ⟨.inr (.inr (⟨B, hBm⟩, ⟨ρ, by omega⟩)), ?_⟩
      rw [Formalism.L2.Col.RowPar.sgHC_e _ B (ρ + 1) (by omega) (by omega), Formalism.L2.Col.RowPar.eAt_of _ hBm]
      simp only [GlobalTheory.ForcedWeights.entry]
      push_cast
      ring

lemma sgHC_strictAnti {R : Ranks} (P : HCParam R) :
    StrictAnti fun i : Fin (R.N R.m - 1) => (Formalism.L2.Col.RowPar.of P).sgHC i.1 - Formalism.L2.Col.RowPar.sh R := by
  intro i j hij
  have h := Formalism.L2.Col.anti_sub_rho (N := R.N R.m - 1) (Formalism.L2.Col.RowPar.of P).sgHC
    (fun _ hn => Formalism.L2.Col.RowPar.sgHC_step P hn) hij.le
  have h2 : (i.1 : ℚ) < (j.1 : ℚ) := by exact_mod_cast (show i.1 < j.1 from hij)
  simp only [rhoVec] at h ⊢
  linarith

theorem lamRdef_eq (D : D7) (h : D.sp.X'.rank = D.R.N D.R.m - 1) (τ : D.what₂.Tau) (i : Fin D.sp.X'.rank) :
    (Bridge.lamRdef (Ptw D) τ).w i = (Formalism.L2.Col.RowPar.of (D.hc τ)).sgTrue.w (Fin.cast h i) := by
  have hF := GlobalTheory.ForcedWeights.lamRForced D τ
  rw [GlobalTheory.ForcedWeights.dpar_eq] at hF
  have h1 := isWtOfPar_eq h hF (fun x hx => by
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
      rfl) _ (sgHC_strictAnti (D.hc τ)) (fun a => by
      obtain ⟨x, hx⟩ := sgHC_mem (D.hc τ) a.1 a.2
      exact Finset.mem_image.2 ⟨x, Finset.mem_univ _, by rw [hx]⟩) i
  rw [← Formalism.L2.Col.RowPar.sgTrue_eq] at h1
  exact_mod_cast h1

theorem lamRdef_eq_sgTrue : ∀ (X : Stages) (τ : X.B.fields.Tau) (i : Fin X.toD7.sp.X'.rank), (Bridge.lamRdef (Ptw X.toD7) τ).w i = (X.B.wts.sgTrue τ).w (Fin.cast (RowAd.rank_X' X) i) :=
  fun X τ i => lamRdef_eq X.toD7 (RowAd.rank_X' X) τ i

end GlobalTheory.Mem.R3.RowWeight
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeAlgebraCompUnitaryGroupAntidiagTransportMem
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeAlgebraCompUnitaryGroupAntidiagTransportMem
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

noncomputable section

namespace GlobalTheory.SatInd

section HeckeTransport

theorem hecke_comp_of_inverse {G G' : Type} [Group G] [Group G'] (φ : G →* G') (ψ : G' →* G)
    (hψφ : ∀ y, ψ (φ y) = y) {K : Subgroup G} {K' : Subgroup G'} (hφK : ∀ a ∈ K, φ a ∈ K')
    (hψK : ∀ a ∈ K', ψ a ∈ K) (h' : G' → ℂ) (hh : h' ∈ Formalism.UG.Hecke ℂ K') :
    (fun y => h' (φ y)) ∈ Formalism.UG.Hecke ℂ K := by
  classical
  have hh' : Formalism.UG.IsBiInv K' h' ∧ Formalism.UG.FinDosetSupp K' h' := hh
  obtain ⟨hbi, S', hS'⟩ := hh'
  show Formalism.UG.IsBiInv K (fun y => h' (φ y)) ∧ Formalism.UG.FinDosetSupp K (fun y => h' (φ y))
  refine ⟨fun a b y => ?_, S'.image ψ, fun y hy => ?_⟩
  · show h' (φ ((a : G) * y * b)) = h' (φ y)
    rw [map_mul, map_mul]
    exact hbi ⟨φ a, hφK a a.2⟩ ⟨φ b, hφK b b.2⟩ (φ y)
  · obtain ⟨s, hs, a, b, e⟩ := hS' (φ y) hy
    refine ⟨ψ s, Finset.mem_image_of_mem _ hs, ⟨ψ a, hψK a a.2⟩, ⟨ψ b, hψK b b.2⟩, ?_⟩
    show y = ψ a * ψ s * ψ b
    rw [← map_mul, ← map_mul, ← e, hψφ]

end HeckeTransport

section KUTransport

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem guMap_mem_KU (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x))
    (hint : ∀ x, x ∈ intL K → g x ∈ intL K) (n : ℕ) (a : GU σ n) (ha : a ∈ KU σ n) :
    guMap g hg n a ∈ KU σ' n := by
  simp only [KU, Subgroup.mem_subgroupOf, intPts, Subgroup.mem_inf, MonoidHom.mem_range] at ha ⊢
  obtain ⟨-, b, hb⟩ := ha
  refine ⟨(guMap g hg n a).2, ?_⟩
  let gi : intL K →+* intL K :=
    ((g : K →+* K).comp (intL K).subtype).codRestrict (intL K) (fun x => hint x x.2)
  refine ⟨bc (n := Fin n) gi b, ?_⟩
  apply Units.ext
  ext i j
  have hij := congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K) i j) hb
  simp only [bc, Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at hij ⊢
  rw [guMap_val, Matrix.map_apply, ← hij]
  rfl

theorem guMap_symm_guMap (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x))
    (hg' : ∀ x, g.symm (σ' x) = σ (g.symm x)) (n : ℕ) (y : GU σ n) :
    guMap g.symm hg' n (guMap g hg n y) = y := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [guMap_val, guMap_val]
  simp

theorem guMap_hecke_comap : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)), (∀ x, x ∈ intL K ↔ g x ∈ intL K) → ∀ (n : ℕ) (h' : GU σ' n → ℂ), h' ∈ Hecke ℂ (KU σ' n) → (fun y => h' (guMap g hg n y)) ∈ Hecke ℂ (KU σ n) := by
  intro K _ _ g σ σ' hg hint n h' hh
  have hg' : ∀ x, g.symm (σ' x) = σ (g.symm x) := by
    intro x
    apply g.injective
    rw [RingEquiv.apply_symm_apply, hg, RingEquiv.apply_symm_apply]
  have hint' : ∀ x, x ∈ intL K → g.symm x ∈ intL K := by
    intro x hx
    rw [hint (g.symm x), RingEquiv.apply_symm_apply]
    exact hx
  exact hecke_comp_of_inverse (guMap g hg n) (guMap g.symm hg' n) (guMap_symm_guMap g hg hg' n)
    (fun a ha => guMap_mem_KU g hg (fun x => (hint x).1) n a ha)
    (fun a ha => guMap_mem_KU g.symm hg' hint' n a ha) h' hh

end KUTransport

end GlobalTheory.SatInd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeAlgebraCompUnitaryGroupAntidiagTransportMemStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeAlgebra_comp_unitaryGroupAntidiagTransport_mem : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)), (∀ x, x ∈ intL K ↔ g x ∈ intL K) → ∀ (n : ℕ) (h' : GU σ' n → ℂ), h' ∈ Hecke ℂ (KU σ' n) → (fun y => h' (guMap g hg n y)) ∈ Hecke ℂ (KU σ n) := by
  first | exact @GlobalTheory.SatInd.guMap_hecke_comap | exact GlobalTheory.SatInd.guMap_hecke_comap | (intros; apply GlobalTheory.SatInd.guMap_hecke_comap <;> assumption)
end
end
