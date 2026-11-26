module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplitting
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestSupportFamiliesStaircaseCosets

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepDepthLatticeMulVecMemCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepDepthLatticeMulVecMemCompletion
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.ShiftRowMul

variable {D : D7}

theorem latV_at_le_all {S : HSp D} {Λ : Lat S} {v : GlobalTheory.FinPl.Pl D} {y : Fin S.rank → AE D}
    (hy : y ∈ latV S Λ (· = v)) : y ∈ latV S Λ (fun _ => True) := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul at *
  refine AddSubgroup.closure_mono ?_ hy
  rintro _ ⟨α, hα, -, a, ha, x, hx, rfl⟩
  exact ⟨α, hα, fun _ h => (h trivial).elim, a, ha, x, hx, rfl⟩

theorem smul_mem_of_idLat {n : ℕ} {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hI : I ≠ 0)
    {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {c : D.host.E} (hc : c ∈ I⁻¹) {x : Fin n → D.host.E}
    (hx : x ∈ idLat I Λ) : c • x ∈ Λ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, y, hy, rfl⟩ := hx
    have h1 : c * t ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
      rw [← inv_mul_cancel₀ hI]; exact FractionalIdeal.mul_mem_mul hc ht
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    rw [smul_smul, ← hr, algebraMap_smul]
    exact Λ.smul_mem r hy
  | zero => rw [smul_zero]; exact zero_mem _
  | add x x' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | smul r x _ h =>
    rw [← algebraMap_smul D.host.E r x, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]
    exact Λ.smul_mem r h

theorem smul_mem_latV {S : HSp D} {Λ : Lat S} {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {v : GlobalTheory.FinPl.Pl D}
    {s : AE D} (hs : s ∈ GlobalTheory.SeeSaw.idV (D.host.AA⁻¹ * I⁻¹) v) {z : Fin S.rank → AE D}
    (hz : z ∈ latA S (idLat I Λ) (fun _ => True)) : s • z ∈ latV S Λ (· = v) := by
  have hAA : D.host.AA ≠ 0 := GlobalTheory.HostAAPartition.host_AA_ne_zero D
  induction hs using AddSubgroup.closure_induction with
  | mem s hs =>
    obtain ⟨β, hβ, hβv, b, hb, rfl⟩ := hs
    by_cases hI : I = 0
    · subst hI
      rw [_root_.inv_zero, mul_zero, FractionalIdeal.mem_zero_iff] at hb
      subst hb
      rw [TensorProduct.tmul_zero, zero_smul]; exact zero_mem _
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨α, hα, -, a, ha, x, hx, rfl⟩ := hz
      have hba : b * a ∈ I⁻¹ := by
        have := FractionalIdeal.mul_mem_mul hb ha
        rwa [mul_comm D.host.AA⁻¹, mul_assoc, inv_mul_cancel₀ hAA, mul_one] at this
      refine AddSubgroup.subset_closure ⟨β * α, GlobalTheory.FinPl.LatMem.intAf_mul' hβ hα,
        fun w hw => by rw [map_mul, hβv w hw, zero_mul], 1, rfl, (b * a) • x, smul_mem_of_idLat hI hba hx, ?_⟩
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.FinPlLoc.pairA_mul, one_mul, mul_assoc]
    | zero => rw [smul_zero]; exact zero_mem _
    | add z z' _ _ h h' => rw [smul_add]; exact add_mem h h'
    | neg z _ h => rw [smul_neg]; exact neg_mem h
  | zero => rw [zero_smul]; exact zero_mem _
  | add s s' _ _ h h' => rw [add_smul]; exact add_mem h h'
  | neg s _ h => rw [neg_smul]; exact neg_mem h

end GlobalTheory.ShiftRowMul

theorem GlobalTheory.AscFin.shiftRow_smul_mulVec_mem : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))), M ∈ latRow G (2 * ρ + 1) → ∀ v : GlobalTheory.FinPl.Pl D, ∀ y ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA⁻¹ * (shiftId G)⁻¹) v, s • (M *ᵥ y) ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) := by
  intro D hq T L μ0 hL sc G W Mv hMv F hF ρ h M hM v y hy s hs
  have hBig : M ∈ latBig G (2 * ρ + 1) :=
    GlobalTheory.T.depthLatticeGridRow_le_selfDualHomLatticeShift D hq T L μ0 hL sc G W Mv hMv (2 * ρ + 1) (by omega) (by omega) hM
  have hS : IsSelfDualC (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.Λ (.grid (2 * ρ + 1 + 1) 0)) :=
    (G.isV (X := .grid (2 * ρ + 1 + 1) 0) ⟨by omega, by omega⟩ (fun j h => by injection h with h1 h2; omega)).sd
  have hT := ((GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hq T L μ0 hL sc G W Mv hMv F hF).1 (2 * ρ + 1) (by omega)).2.2.2
  have hmap := ((GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ hS hT (fun _ => True) M).1 hBig).2 y
    (GlobalTheory.ShiftRowMul.latV_at_le_all hy)
  exact GlobalTheory.ShiftRowMul.smul_mem_latV hs hmap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepDepthLatticeMulVecMemCompletionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselStep_depthLattice_mulVec_mem_completion : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))), M ∈ latRow G (2 * ρ + 1) → ∀ v : GlobalTheory.FinPl.Pl D, ∀ y ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA⁻¹ * (shiftId G)⁻¹) v, s • (M *ᵥ y) ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) := by
  first | exact @GlobalTheory.AscFin.shiftRow_smul_mulVec_mem | exact GlobalTheory.AscFin.shiftRow_smul_mulVec_mem | (intros; apply GlobalTheory.AscFin.shiftRow_smul_mulVec_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InvAAMultipleDepthLatticeMapsCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InvAAMultipleDepthLatticeMapsCompletion
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.RowAAUnit

variable {D : D7}

theorem idem_smul_latA {S : HSp D} {L : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} (v : GlobalTheory.FinPl.Pl D)
    {z : Fin S.rank → AE D} (hz : z ∈ latA S L P) : GlobalTheory.FinPlLoc.idem D (· = v) • z ∈ latA S L (· = v) := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨GlobalTheory.FinPlLoc.ePl D (· = v) * α, fun w => ?_, fun w hw => ?_, a, ha, x, hx, ?_⟩
    · rw [map_mul]; exact mul_mem (GlobalTheory.FinPlLoc.ePl_int _ w) (hαi w)
    · rw [map_mul, GlobalTheory.FinPlLoc.evalV_ePl, if_neg hw, zero_mul]
    · funext i
      rw [Pi.smul_apply, smul_eq_mul]
      unfold GlobalTheory.FinPlLoc.idem
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← GlobalTheory.FinPlLoc.pairA_mul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg y _ h => rw [smul_neg]; exact neg_mem h

theorem smul_mulVec_mem_latV : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))), M ∈ latRow G (2 * ρ + 1) → ∀ v : GlobalTheory.FinPl.Pl D, ∀ y ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA⁻¹) v, s • (M *ᵥ y) ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) := by
  intro D hOff T L μ0 hL sc G W Mv hM F hF ρ h M hMr v y hy s hs
  have hV : IsSelfDualC (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) :=
    (G.isV (X := .grid (2 * ρ + 2) 0) ⟨h, Nat.zero_le _⟩ (fun j hj => by injection hj with h1 h2; omega)).sd
  have hO : M ∈ latO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 2) 0) : Set _)
      (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (fun _ => True) :=
    GlobalTheory.RowLoc.mem_latO_negSp.1 hMr.1
  have hyT : y ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (fun _ => True) := GlobalTheory.FinPl.PsiUnit.latV_mono trivial hy
  have hA : M *ᵥ y ∈ latA _ (G.Λ (.grid (2 * ρ + 1) 0)) (fun _ => True) := GlobalTheory.FinPl.LatMem.latO_maps hV hO hyT
  have hy' : GlobalTheory.FinPlLoc.idem D (· = v) • y = y := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul]
    exact (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (GlobalTheory.FinPlLoc.latV_idAt hy i)
  have hAv : M *ᵥ y ∈ latA _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) := by
    rw [← hy', Matrix.mulVec_smul]
    exact idem_smul_latA v hA
  exact (((GlobalTheory.SeeSaw.idV_props D W.ψ W.ψ_std v).2.2.2.2.2.2 _ _ _).1 hAv).2 s hs

end GlobalTheory.AscFin.RowAAUnit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InvAAMultipleDepthLatticeMapsCompletionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_AA_multiple_depth_lattice_maps_completion : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))), M ∈ latRow G (2 * ρ + 1) → ∀ v : GlobalTheory.FinPl.Pl D, ∀ y ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA⁻¹) v, s • (M *ᵥ y) ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) := by
  first | exact @GlobalTheory.AscFin.RowAAUnit.smul_mulVec_mem_latV | exact GlobalTheory.AscFin.RowAAUnit.smul_mulVec_mem_latV | (intros; apply GlobalTheory.AscFin.RowAAUnit.smul_mulVec_mem_latV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletionOfMemModulusAndConjQuotients
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletionOfMemModulusAndConjQuotients
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

open scoped Pointwise

noncomputable section

namespace GlobalTheory.ModulInter

theorem modul_isCoprime_conj {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) :
    IsCoprime (P.modul sc) (P.modulBar sc) := by
  have hF : ∀ I : Ideal (𝓞 D.host.E), (D.host.conj • I).under (𝓞 D.host.F) = I.under (𝓞 D.host.F) :=
    GlobalTheory.PlaceOverPair.under_smul_of_fix D.host.conj
      (fun x => (D.host.conjE_mem_hostF_iff _).1 x.2)
  unfold Places.modulBar Places.modul
  rw [Finset.smul_prod']
  refine IsCoprime.prod_left fun v hv => IsCoprime.prod_right fun v' hv' => ?_
  rw [smul_pow']
  refine IsCoprime.pow ?_
  rw [Ideal.isCoprime_iff_sup_eq]
  have hm : (D.host.conj • (P.w v').asIdeal).IsMaximal := by
    have := (P.w v').isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => (P.w v').ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  refine Ideal.IsMaximal.coprime_of_ne (P.w v).isMaximal hm fun heq => ?_
  have hvv : v = v' := by
    have a := congrArg HeightOneSpectrum.asIdeal (P.under_w hv)
    have b := congrArg HeightOneSpectrum.asIdeal (P.under_w hv')
    refine HeightOneSpectrum.ext ?_
    rw [← a, ← b]
    show Ideal.under _ _ = Ideal.under _ _
    rw [heq, hF]
  subst hvv
  obtain ⟨e, he⟩ := P.w_split v hv
  exact GlobalTheory.FunObj.StdDatum.conj_smul_ne_of_isIdemAt he heq.symm

theorem incA_mul_mem {D : D7} (v : GlobalTheory.FinPl.Pl D) (𝔞 : GlobalTheory.SeeSaw.FI D) (I : Ideal (𝓞 D.host.E)) (hI : I ≠ ⊥)
    {m : 𝓞 D.host.E} (hm : m ∈ I) {s : AE D}
    (hs : s ∈ GlobalTheory.SeeSaw.idV (𝔞 * ((I : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v) :
    incA D (algebraMap (𝓞 D.host.E) D.host.E m) * s ∈ GlobalTheory.SeeSaw.idV 𝔞 v := by
  have h := GlobalTheory.SeeSaw.idV_incA_mul (algebraMap (𝓞 D.host.E) D.host.E m) _ v hs
  refine GlobalTheory.SeeSaw.idV_mono ?_ v h
  have hI0 : ((I : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hI
  have hle : FractionalIdeal.spanSingleton _ (algebraMap (𝓞 D.host.E) D.host.E m) ≤
      ((I : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) := by
    rw [FractionalIdeal.spanSingleton_le_iff_mem]
    exact (FractionalIdeal.mem_coeIdeal _).2 ⟨m, hm, rfl⟩
  calc FractionalIdeal.spanSingleton _ (algebraMap (𝓞 D.host.E) D.host.E m) * (𝔞 * ((I : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹)
      ≤ ((I : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) * (𝔞 * ((I : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) :=
        by gcongr
    _ = 𝔞 := by rw [mul_left_comm, mul_inv_cancel₀ hI0, mul_one]

theorem mem_idV_of_inter : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (v : GlobalTheory.FinPl.Pl D) (𝔞 : GlobalTheory.SeeSaw.FI D) (s : AE D), s ∈ GlobalTheory.SeeSaw.idV (𝔞 * ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v → s ∈ GlobalTheory.SeeSaw.idV (𝔞 * ((P.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v → s ∈ GlobalTheory.SeeSaw.idV 𝔞 v := by
  intro D T L P sc v 𝔞 s h1 h2
  have hsup := (Ideal.isCoprime_iff_sup_eq).1 (modul_isCoprime_conj P sc)
  obtain ⟨m, hm, m', hm', hmm⟩ := Submodule.mem_sup.1 (hsup.symm ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ P.modul sc ⊔ P.modulBar sc)
  have a1 := incA_mul_mem v 𝔞 _ (P.modul_ne_bot sc) hm h1
  have a2 := incA_mul_mem v 𝔞 _ (GlobalTheory.AscFin.PrimStd.modulBar_ne_bot P sc) hm' h2
  have e : s = incA D (algebraMap (𝓞 D.host.E) D.host.E m) * s + incA D (algebraMap (𝓞 D.host.E) D.host.E m') * s := by
    rw [← add_mul, ← map_add (f := _), ← map_add (f := _), hmm, map_one, map_one, one_mul]
  rw [e]
  exact add_mem a1 a2

end GlobalTheory.ModulInter
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletionOfMemModulusAndConjQuotientsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completion_of_mem_modulus_and_conj_quotients : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (v : GlobalTheory.FinPl.Pl D) (𝔞 : GlobalTheory.SeeSaw.FI D) (s : AE D), s ∈ GlobalTheory.SeeSaw.idV (𝔞 * ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v → s ∈ GlobalTheory.SeeSaw.idV (𝔞 * ((P.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v → s ∈ GlobalTheory.SeeSaw.idV 𝔞 v := by
  first | exact @GlobalTheory.ModulInter.mem_idV_of_inter | exact GlobalTheory.ModulInter.mem_idV_of_inter | (intros; apply GlobalTheory.ModulInter.mem_idV_of_inter <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselJacobiSuperdiagonalEntriesAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselJacobiSuperdiagonalEntriesAtPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin


open GlobalTheory.SeeSaw (idV FI dI) in
theorem GlobalTheory.AscFin.coef_superdiag : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m)
    (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))) (𝔠 : GlobalTheory.SeeSaw.FI D), 𝔠 ≠ 0 →
    ∀ v : GlobalTheory.FinPl.Pl D, (∀ y ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV 𝔠 v,
      s • (M *ᵥ y) ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v)) → ∀ i j : Fin ρ, j.1 = i.1 + 1 →
    GlobalTheory.FinPlLoc.idem D (· = v) * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j ∈
      GlobalTheory.SeeSaw.idV (FractionalIdeal.spanSingleton _ D.host.xi0 * G.pl.stAbar sc * 𝔠⁻¹) v := by
  intro D hD T L μ0 hL sc G W M0 hM0 F hF ρ h M 𝔠 h𝔠 v hM i j hij
  obtain ⟨-, f2, -, -, -, -, -⟩ := GlobalTheory.T.fractionalIdealCompletion_properties_at_place D W.ψ W.ψ_std v
  have hmono : MonoAt (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v :=
    ((GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hD T L μ0 hL sc G W M0 hM0 F hF).2.1 ρ h).2.1 v |>.2
  obtain ⟨hcB, heB, -⟩ := hF.hB ρ h
  obtain ⟨hcJ, heJ, -⟩ := hF.hJ ρ h
  have hlatB := G.sp.colLat (2 * ρ + 2) (by omega) h
  have hlatJ := G.sp.colLat (2 * ρ + 1) (by omega) (by omega)
  have hx : ∀ n : ℕ, (-D.host.xi0) ^ n ≠ 0 := fun n => pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)
  let 𝔟B : Fin ρ → FI D := fun p => FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (p.1 + 1))⁻¹) *
    stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) (Fin.castLE (by omega) p)
  let 𝔟J : Fin ρ → FI D := fun p => FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (p.1 + 1))⁻¹) *
    stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) p)
  have lineB : ∀ (p : Fin ρ) (a : AE D), GlobalTheory.FinPl.colMul (F.dB ρ h).jX p a ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (· = v) ↔
      a ∈ idV (𝔟B p) v := by
    intro p a
    have e1 : GlobalTheory.FinPl.colMul (F.dB ρ h).jX p a = fun k => a * incA D ((-D.host.xi0) ^ (p.1 + 1) *
        (G.colDec (2 * ρ + 2) (by omega) h).a k (Fin.castLE (by omega) p)) := by
      funext k
      simp only [GlobalTheory.FinPl.colMul, HypDec.jX, rat, Matrix.map_apply, heB, colsOf]
    rw [e1]
    have e2 : G.Λ (.grid (2 * ρ + 2) 0) = _ := hlatB
    rw [e2]
    exact GlobalTheory.StairLine.line_mem_iff _ _ _ _ (by simp only [Fin.coe_castLE]; omega) (hx _) v a
  have lineJ : ∀ (p : Fin ρ) (a : AE D), GlobalTheory.FinPl.colMul (F.dJ ρ h).jX p a ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) ↔
      a ∈ idV (𝔟J p) v := by
    intro p a
    have e1 : GlobalTheory.FinPl.colMul (F.dJ ρ h).jX p a = fun k => a * incA D ((-D.host.xi0) ^ (p.1 + 1) *
        (G.colDec (2 * ρ + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p)) := by
      funext k
      simp only [GlobalTheory.FinPl.colMul, HypDec.jX, rat, Matrix.map_apply, heJ, colsOf]
    rw [e1]
    have e2 : G.Λ (.grid (2 * ρ + 1) 0) = _ := hlatJ
    rw [e2]
    exact GlobalTheory.StairLine.line_mem_iff _ _ _ _ (by simp only [Fin.coe_castLE]; omega) (hx _) v a
  have hN : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (G.pl.modul_ne_bot sc)
  have hN' : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (GlobalTheory.AscFin.PrimStd.modulBar_ne_bot G.pl sc)
  have hA : G.pl.stA sc ≠ 0 := mul_ne_zero (GlobalTheory.CuspCharLattice.host_AA_ne_zero _) (inv_ne_zero hN')
  have hAb : G.pl.stAbar sc ≠ 0 := mul_ne_zero (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D) (inv_ne_zero hN)
  have hsp : ∀ n : ℕ, FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (((-D.host.xi0) ^ n)⁻¹) ≠ 0 := fun n => by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact inv_ne_zero (hx _)
  have hb0B : ∀ p, 𝔟B p ≠ 0 := fun p => mul_ne_zero (hsp _) (by
    unfold stairId; exact mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hAb)))
  have hb0J : ∀ p, 𝔟J p ≠ 0 := fun p => mul_ne_zero (hsp _) (by
    unfold stairId; exact mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hAb)))
  have hrat : 𝔟J i * (𝔟B j)⁻¹ = FractionalIdeal.spanSingleton _ D.host.xi0 * G.pl.stAbar sc := by
    rw [mul_inv_eq_iff_eq_mul₀ (hb0B j)]
    have hneg : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (-D.host.xi0) = FractionalIdeal.spanSingleton _ D.host.xi0 :=
      FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨-1, by simp⟩
    have e2 : ((-D.host.xi0) ^ (i.1 + 1))⁻¹ = -D.host.xi0 * ((-D.host.xi0) ^ (j.1 + 1))⁻¹ := by
      have hξ : -D.host.xi0 ≠ 0 := neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero
      rw [hij]
      field_simp
      ring
    show FractionalIdeal.spanSingleton _ _ * stairId _ _ _ _ = _ * (FractionalIdeal.spanSingleton _ _ * stairId _ _ _ _)
    rw [e2, ← FractionalIdeal.spanSingleton_mul_spanSingleton, hneg]
    unfold stairId
    simp only [Fin.coe_castLE]
    have e3 : 2 * ρ + 1 - 1 - i.1 = 2 * ρ + 2 - 1 - j.1 := by omega
    rw [e3, hij, pow_succ (G.pl.stAbar sc) (i.1 + 1), mul_inv]
    conv_lhs => rw [show (G.pl.stAbar sc ^ (i.1 + 1))⁻¹ = G.pl.stAbar sc * ((G.pl.stAbar sc ^ (i.1 + 1))⁻¹ * (G.pl.stAbar sc)⁻¹) by
      rw [mul_comm ((G.pl.stAbar sc ^ (i.1 + 1))⁻¹), ← mul_assoc, mul_inv_cancel₀ hAb, one_mul]]
    ring
  have hxA : GlobalTheory.FinPlLoc.idem D (· = v) * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j ∈ idAt D (· = v) :=
    Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _)
  rw [← hrat]
  refine (f2 𝔠 _ h𝔠 (mul_ne_zero (hb0J i) (inv_ne_zero (hb0B j))) _ hxA).1 ?_
  intro s hs
  have hsA : s ∈ idAt D (· = v) := GlobalTheory.SeeSaw.LiftModel.idV_le_idAt _ _ s hs
  refine (f2 (𝔟B j) (𝔟J i) (hb0B j) (hb0J i) _ (Ideal.mul_mem_right _ _ hxA)).1 ?_
  intro c hc
  have hcA : c ∈ idAt D (· = v) := GlobalTheory.SeeSaw.LiftModel.idV_le_idAt _ _ c hc
  have h1 := hM _ ((lineB j c).2 hc) s hs
  have h3 := ((hmono _).1 h1).1 i
  rw [Matrix.mulVec_smul, GlobalTheory.FinPl.PsiUnit.mulVec_colMul, GlobalTheory.FinPl.PsiUnit.mulVec_colMul] at h3
  have h4 := (lineJ i _).1 h3
  have e4 : ((s • GlobalTheory.FinPl.colMul ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) j c) i) =
      GlobalTheory.FinPlLoc.idem D (· = v) * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j * s * c := by
    rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.FinPl.colMul]
    have hc' := (GlobalTheory.FinPlLoc.mem_idAt_iff _ c).1 hcA
    calc s * (c * _) = s * ((GlobalTheory.FinPlLoc.idem D (· = v) * c) * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j) := by rw [hc']
      _ = _ := by ring
  rwa [e4] at h4
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselJacobiSuperdiagonalEntriesAtPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselJacobi_superdiagonal_entries_at_place : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))) (𝔠 : GlobalTheory.SeeSaw.FI D), 𝔠 ≠ 0 → ∀ v : GlobalTheory.FinPl.Pl D, (∀ y ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV 𝔠 v, s • (M *ᵥ y) ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v)) → ∀ i j : Fin ρ, j.1 = i.1 + 1 → GlobalTheory.FinPlLoc.idem D (· = v) * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j ∈ GlobalTheory.SeeSaw.idV (FractionalIdeal.spanSingleton _ D.host.xi0 * G.pl.stAbar sc * 𝔠⁻¹) v := by
  first | exact @GlobalTheory.AscFin.coef_superdiag | exact GlobalTheory.AscFin.coef_superdiag | (intros; apply GlobalTheory.AscFin.coef_superdiag <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdditiveCharacterSuperdiagTrivial
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

theorem GlobalTheory.AscFin.psiE_superdiag_S0 : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))), M ∈ latRow G (2 * ρ + 1) → ∀ i j : Fin ρ, j.1 = i.1 + 1 → ∀ v : GlobalTheory.FinPl.Pl D, v ∈ G.pl.S0 → ∀ o ∈ intAt D (· = v), psiE W.ψ (o * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j) = 1 := by
  intro D hQ T L μ0 hL sc G W Mv hM F hF ρ h M hMr i j hij v hv o ho
  have hAA : (D.host.AA : GlobalTheory.SeeSaw.FI D) ≠ 0 := GlobalTheory.HostAAPartition.host_AA_ne_zero D
  have hm : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (G.pl.modul_ne_bot sc)
  have hmB : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (GlobalTheory.AscFin.PrimStd.modulBar_ne_bot G.pl sc)
  have hsh : shiftId G ≠ 0 := mul_ne_zero hm (inv_ne_zero hmB)
  have h1 := GlobalTheory.T.besselJacobi_superdiagonal_entries_at_place D hQ T L μ0 hL sc G W Mv hM F hF ρ h M _ (inv_ne_zero hAA) v
    (GlobalTheory.T.inv_AA_multiple_depth_lattice_maps_completion D hQ T L μ0 hL sc G W Mv hM F hF ρ h M hMr v) i j hij
  have h2 := GlobalTheory.T.besselJacobi_superdiagonal_entries_at_place D hQ T L μ0 hL sc G W Mv hM F hF ρ h M _ (mul_ne_zero (inv_ne_zero hAA) (inv_ne_zero hsh)) v
    (GlobalTheory.T.besselStep_depthLattice_mulVec_mem_completion D hQ T L μ0 hL sc G W Mv hM F hF ρ h M hMr v) i j hij
  have e1 : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * G.pl.stAbar sc * (D.host.AA : GlobalTheory.SeeSaw.FI D)⁻¹⁻¹ =
      GlobalTheory.SeeSaw.dI D * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ := by
    unfold Places.stAbar GlobalTheory.SeeSaw.dI
    rw [inv_inv]
    ring
  have e2 : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * G.pl.stAbar sc *
      ((D.host.AA : GlobalTheory.SeeSaw.FI D)⁻¹ * (shiftId G)⁻¹)⁻¹ =
      GlobalTheory.SeeSaw.dI D * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ := by
    unfold Places.stAbar GlobalTheory.SeeSaw.dI shiftId
    rw [mul_inv, inv_inv, inv_inv]
    field_simp
  rw [e1] at h1
  rw [e2] at h2
  have hx := GlobalTheory.T.mem_completion_of_mem_modulus_and_conj_quotients G.pl sc v _ _ h1 h2
  have hxA : GlobalTheory.FinPlLoc.idem D (· = v) * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j ∈ idAt D (· = v) :=
    Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _)
  have hψ := ((GlobalTheory.T.fractionalIdealCompletion_properties_at_place D W.ψ W.ψ_std v).2.2.2.2.1 _ hxA).1 hx o ho
  have ho' : GlobalTheory.FinPlLoc.idem D (· = v) * o = o := (GlobalTheory.FinPlLoc.mem_idAt_iff _ o).1 ho.1
  rw [← ho']
  rw [← hψ]
  congr 1
  ring

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdditiveCharacterSuperdiagTrivialStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_character_superdiag_trivial : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))), M ∈ latRow G (2 * ρ + 1) → ∀ i j : Fin ρ, j.1 = i.1 + 1 → ∀ v : GlobalTheory.FinPl.Pl D, v ∈ G.pl.S0 → ∀ o ∈ intAt D (· = v), psiE W.ψ (o * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j) = 1 := by
  first | exact @GlobalTheory.AscFin.psiE_superdiag_S0 | exact GlobalTheory.AscFin.psiE_superdiag_S0 | (intros; apply GlobalTheory.AscFin.psiE_superdiag_S0 <;> assumption)
end
