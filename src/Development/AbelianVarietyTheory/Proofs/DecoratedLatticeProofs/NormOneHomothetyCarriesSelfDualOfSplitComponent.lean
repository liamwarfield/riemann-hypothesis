module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLatticeStabilizerTwistAndLevelAway
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerThetaEqSchwartzBruhat
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumOfRankOneGram
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedWeilVacuumEqVacuumOfMovedLattices

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneHomothetyCarriesSelfDualOfSplitComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneHomothetyCarriesSelfDualOfSplitComponent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

open GlobalTheory.FinPl.FrameLat


set_option maxHeartbeats 1000000 in
theorem sMoves_of_wComp : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (L L' : Lat S) (c : AE D) (g : GA D S), IsSelfDualC S L → IsSelfDualC S L' → NormOneAt p.v c → (∀ x : Fin S.rank → k, (fun i => p.sec (x i)) ∈ latV S L (· = p.v) ↔ (fun i => p.sec ((p.pr c • ((Formalism.L2.Theta.mt S g).map p.pr *ᵥ x)) i)) ∈ latV S L' (· = p.v)) → SMoves S c g L L' p.v := by
  intro D k _ _ _ _ p S L L' c g hL hL' hc hw
  have hpc : p.pr c * p.pr (cA D c) = 1 := by rw [← map_mul, hc.1, map_one]
  have hGinv : ∀ x : Fin S.rank → k,
      (Formalism.L2.Theta.mt S g).map p.pr *ᵥ ((Formalism.L2.Theta.mt S g⁻¹).map p.pr *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul,
      show Formalism.L2.Theta.mt S g * Formalism.L2.Theta.mt S g⁻¹ = Formalism.L2.Theta.mt S (g * g⁻¹) from rfl, mul_inv_cancel,
      show Formalism.L2.Theta.mt S 1 = 1 from rfl, Matrix.map_one p.pr (map_zero _) (map_one _), Matrix.one_mulVec]
  have hsec : ∀ u : Fin S.rank → k, Formalism.L2.Theta.mt S g *ᵥ (fun i => p.sec (u i)) =
      fun i => p.sec (((Formalism.L2.Theta.mt S g).map p.pr *ᵥ u) i) := by
    intro u
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sec_mul, p.sec_pr, mul_comm p.e, mul_assoc, e_mul_sec]
  have hc1 : ∀ a : k, c * p.sec a = p.sec (p.pr c * a) := by
    intro a; rw [mul_comm, sec_mul_right, mul_comm]
  have hc2 : ∀ b : k, c * cA D (p.sec b) = cA D (p.sec (p.pr (cA D c) * b)) := by
    intro b
    have h : c * cA D (p.sec b) = cA D (cA D c * p.sec b) := by rw [map_mul, cA_cA]
    rw [h, mul_comm, sec_mul_right, mul_comm]
  have hB : ∀ x z : Fin S.rank → k,
      ∑ i, ∑ j, (p.pr c • ((Formalism.L2.Theta.mt S g).map p.pr *ᵥ x)) i * p.pr (cA D (incA D (S.gram i j))) *
          (p.pr (cA D c) • ((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a)) *ᵥ z)) j =
        ∑ i, ∑ j, x i * p.pr (cA D (incA D (S.gram i j))) * z j := by
    intro x z
    rw [← pairing_inv (p := p) g x z]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination (((Formalism.L2.Theta.mt S g).map p.pr *ᵥ x) i * p.pr (cA D (incA D (S.gram i j))) *
      (((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a)) *ᵥ z) j)) * hpc
  intro y hy
  have hyd : y = (fun i => p.sec (p.pr (y i))) + (fun i => cA D (p.sec (p.pr (cA D (y i))))) := by
    funext i
    simp only [Pi.add_apply, p.sec_pr]
    rw [map_mul, cA_cA, ← add_mul]
    exact ((idem_iff p _).1 (hy i)).symm
  obtain ⟨u, z, rfl⟩ : ∃ u z : Fin S.rank → k, y = (fun i => p.sec (u i)) + (fun i => cA D (p.sec (z i))) :=
    ⟨_, _, hyd⟩
  have himg : c • (Formalism.L2.Theta.mt S g *ᵥ ((fun i => p.sec (u i)) + (fun i => cA D (p.sec (z i))))) =
      (fun i => p.sec ((p.pr c • ((Formalism.L2.Theta.mt S g).map p.pr *ᵥ u)) i)) +
        (fun i => cA D (p.sec ((p.pr (cA D c) • ((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a)) *ᵥ z)) i))) := by
    funext i
    have h1 := congrFun (hsec u) i
    have h2 := congrFun (mt_csec (p := p) g z) i
    have h3 : (Formalism.L2.Theta.mt S g *ᵥ ((fun i => p.sec (u i)) + (fun i => cA D (p.sec (z i))))) i =
        p.sec (((Formalism.L2.Theta.mt S g).map p.pr *ᵥ u) i) +
          cA D (p.sec ((((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a))) *ᵥ z) i)) := by
      rw [Matrix.mulVec_add, Pi.add_apply, h1, h2]
    have h4 : c * (p.sec (((Formalism.L2.Theta.mt S g).map p.pr *ᵥ u) i) +
          cA D (p.sec ((((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a))) *ᵥ z) i))) =
        p.sec (p.pr c * ((Formalism.L2.Theta.mt S g).map p.pr *ᵥ u) i) +
          cA D (p.sec (p.pr (cA D c) * (((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a))) *ᵥ z) i)) := by
      rw [mul_add, hc1, hc2]
    show c * (Formalism.L2.Theta.mt S g *ᵥ ((fun i => p.sec (u i)) + (fun i => cA D (p.sec (z i))))) i = _
    refine (congrArg (c * ·) h3).trans (h4.trans ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [himg, decomp hL, decomp hL']
  refine and_congr (hw u) ?_
  rw [csec_mem_iff hL, csec_mem_iff hL']
  constructor
  · intro h x' hx'
    have hx : p.pr c • ((Formalism.L2.Theta.mt S g).map p.pr *ᵥ
        (p.pr (cA D c) • ((Formalism.L2.Theta.mt S g⁻¹).map p.pr *ᵥ x'))) = x' := by
      rw [Matrix.mulVec_smul, smul_smul, hpc, one_smul, hGinv]
    have hmem := (hw (p.pr (cA D c) • ((Formalism.L2.Theta.mt S g⁻¹).map p.pr *ᵥ x'))).2 (by rw [hx]; exact hx')
    rw [← hx, hB]
    exact h _ hmem
  · intro h x hx
    have h5 := h _ ((hw x).1 hx)
    rwa [hB] at h5

end GlobalTheory.Core.Mi.LatMatch

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneHomothetyCarriesSelfDualOfSplitComponentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normOneHomothety_carries_selfDual_of_splitComponent : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (L L' : Lat S) (c : AE D) (g : GA D S), IsSelfDualC S L → IsSelfDualC S L' → NormOneAt p.v c → (∀ x : Fin S.rank → k, (fun i => p.sec (x i)) ∈ latV S L (· = p.v) ↔ (fun i => p.sec ((p.pr c • ((Formalism.L2.Theta.mt S g).map p.pr *ᵥ x)) i)) ∈ latV S L' (· = p.v)) → SMoves S c g L L' p.v := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.sMoves_of_wComp | exact GlobalTheory.Core.Mi.LatMatch.sMoves_of_wComp | (intros; apply GlobalTheory.Core.Mi.LatMatch.sMoves_of_wComp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsVTOver
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.StdOff

section Gen

open GlobalTheory.FinPl GlobalTheory.FinPl.AlmostAll GlobalTheory.FinPl.AeUnit

variable {D : D7}

theorem incA_mul_mem_intAt {v : Pl D} {c : D.host.E} {N : ℕ} (hv : (N : 𝓞 D.host.F) ∉ v.asIdeal)
    (hint : IsIntegral ℤ ((N : D.host.E) * c)) : ∀ a ∈ intAt D (· = v), incA D c * a ∈ intAt D (· = v) := by
  intro a ha
  have hv' : ((N : ℤ) : 𝓞 D.host.F) ∉ v.asIdeal := by rwa [Int.cast_natCast]
  have hN : N ≠ 0 := by
    rintro rfl
    exact hv (by simp)
  have hNF : ((N : ℤ) : D.host.F) ≠ 0 := by exact_mod_cast hN
  refine ⟨Ideal.mul_mem_left _ _ ha.1, ?_⟩
  have hc : finPart D (incA D c) = (1 : Af D.host.F) ⊗ₜ[D.host.F] c := rfl
  rw [map_mul, hc, ← idem_mul_finPart D v ha.1, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  refine GlobalTheory.HostAdeleIso.intAE_mul_mem D ?_ ha.2
  refine AddSubgroup.subset_closure ⟨_, inv_smul_singleV_mem v N hv', ⟨(N : ℤ) • c, by rw [zsmul_eq_mul, Int.cast_natCast]; exact hint⟩, ?_⟩
  exact tmul_eq_inv_smul_tmul N hNF _ c

theorem latA_eq_latV_of {v : Pl D} {N M : ℕ} (hvN : (N : 𝓞 D.host.F) ∉ v.asIdeal) (hvM : (M : 𝓞 D.host.F) ∉ v.asIdeal)
    (hNI : ∀ a ∈ D.host.AA, ∃ b : 𝓞 D.host.E, algebraMap _ _ b = a * (N : D.host.E)) (hMI : (M : D.host.E) ∈ D.host.AA)
    (S : HSp D) (L : Lat S) : latA S L (· = v) = latV S L (· = v) := by
  have hN : N ≠ 0 := by
    rintro rfl
    exact hvN (by simp)
  have hM : M ≠ 0 := by
    rintro rfl
    exact hvM (by simp)
  apply le_antisymm
  · refine AddSubgroup.closure_mono ?_
    rintro y ⟨α, hα, h0, a, ha, x, hx, rfl⟩
    obtain ⟨b, hb⟩ := hNI a ha
    obtain ⟨h1, h2⟩ := smul_inv_mem hvN hα h0
    refine ⟨_, h1, h2, 1, rfl, b • x, L.smul_mem b hx, funext fun i => ?_⟩
    rw [tmul_eq hN, ← mul_assoc, mul_comm (N : D.host.E) a, ← hb, one_mul, Pi.smul_apply, Algebra.smul_def b]
  · refine AddSubgroup.closure_mono ?_
    rintro y ⟨α, hα, h0, a, ha, x, hx, rfl⟩
    obtain rfl : a = 1 := ha
    obtain ⟨h1, h2⟩ := smul_inv_mem hvM hα h0
    refine ⟨_, h1, h2, (M : D.host.E), hMI, x, hx, funext fun i => ?_⟩
    rw [tmul_eq hM, one_mul]

theorem notMem_of_coprime {R : Type} [CommRing R] {P : Ideal R} (hP : P.IsPrime) {a b : ℕ} (h : a.Coprime b) (hb : (b : R) ∈ P) :
    (a : R) ∉ P := fun ha => by
  obtain ⟨x, y, hxy⟩ : IsCoprime (a : R) (b : R) := Nat.Coprime.cast h
  exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (hxy ▸ P.add_mem (P.mul_mem_left _ ha) (P.mul_mem_left _ hb)))

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unitAA_of (p : SplitPt D k) {l : ℕ} (hl : l.Prime) (hv : (l : 𝓞 D.host.F) ∈ p.v.asIdeal)
    (hq : (D.host.QS * D.host.q).Coprime l) (hd : D.host.d.Coprime l) (hc : (Ideal.absNorm D.host.ccK).Coprime l) : p.UnitAA := by
  have hb : (Ideal.absNorm D.host.𝔟).Coprime l := by
    rw [Nat.coprime_comm, hl.coprime_iff_not_dvd, GlobalTheory.HalfCompare.prime_dvd_absNorm_halfDifferent D hl, ← hl.coprime_iff_not_dvd]
    exact hq.symm
  have hN : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hd4 : 2 ≤ D.host.d := by have := D.host.qd_big.2; omega
  have hd0 : (D.host.d : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hs2 := Formalism.BasicNotions.Host.sqrtMinusD_sq D.host
  have hs : D.host.sqrtMinusD ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hs2
    exact hd0 (neg_eq_zero.1 hs2.symm)
  have hsi : IsIntegral ℤ D.host.sqrtMinusD := IsIntegral.of_pow two_pos (by rw [hs2]; exact (isIntegral_natCast _).neg)
  refine ⟨fun a ha => ⟨incA_mul_mem_intAt (N := Ideal.absNorm D.host.ccK * D.host.d)
    (notMem_of_coprime p.v.isPrime (hc.mul_left hd) hv) ?_ a ha, incA_mul_mem_intAt (N := 1)
    (notMem_of_coprime p.v.isPrime (Nat.coprime_one_left l) hv) ?_ a ha⟩,
    latA_eq_latV_of (notMem_of_coprime p.v.isPrime hb hv) (notMem_of_coprime p.v.isPrime hc hv)
      (fun a ha => ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.int_of_mem_b D (Ideal.absNorm_mem _) ha)
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D)⟩
  · convert hsi using 1
    unfold Host.xi0
    push_cast
    field_simp
    linear_combination -hs2
  · have : ((1 : ℕ) : D.host.E) * D.host.xi0⁻¹ = -((Ideal.absNorm D.host.ccK : D.host.E) * D.host.sqrtMinusD) := by
      unfold Host.xi0
      rw [Nat.cast_one, one_mul, inv_div, div_neg, div_one]
    rw [this]
    exact ((isIntegral_natCast _).mul hsi).neg

theorem mxAt_of_half (q : SplitPt D k) {m n : ℕ} {w : Mx D m n} (h : IsHalf (q.e + cA D q.e) w) : MxAt (· = q.v) w := by
  obtain ⟨ε, h1, h2⟩ := q.above
  obtain rfl := GlobalTheory.AdelicU.Supp.isPlaceIdem_iff.1 h1
  intro i j
  rw [GlobalTheory.FinPl.Model.mem_idAt_iff, ← h2]
  exact h i j

theorem sec_mem_idAt (p : SplitPt D k) (a : k) : p.sec a ∈ idAt D (· = p.v) := by
  have h1 : p.e * p.sec a = p.sec a := by rw [← p.sec_pr, p.pr_sec]
  have h2 : (p.e + cA D p.e) * p.sec a = p.sec a := by
    rw [← h1, ← mul_assoc, add_mul, p.split.1, mul_comm (cA D p.e), p.split.2.1, add_zero]
  exact mxAt_of_half p (m := 1) (n := 1) (w := Matrix.of fun _ _ => p.sec a) (fun _ _ => h2) 0 0

theorem mem_latV_int {S : HSp D} {L : Lat S} (hL : ∀ z, z ∈ L ↔ z ∈ intVec D S.rank) (v : Pl D) (y : Fin S.rank → AE D) :
    y ∈ latV S L (· = v) ↔ ∀ i, y i ∈ intAt D (· = v) :=
  GlobalTheory.FinPl.Model.mem_latV_std S L (fun x => (hL x).trans (forall_congr' fun i =>
    ⟨fun h => ⟨⟨x i, h⟩, rfl⟩, fun ⟨b, hb⟩ => hb ▸ b.isIntegral_coe⟩)) v y

end Gen

section Loc

open GlobalTheory.LatPair IsLocalRing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Loc

section Level

open GlobalTheory.FinPl

variable {D : D7} {u : D.what₂.Word} {a : XPart D u} {ζ₀ : Fin a.Lz.rank → D.host.E}

end Level

end GlobalTheory.SeeSaw.StdOff

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactAverageProjectionThetaSchrodinger
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactAverageProjectionThetaSchrodinger
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RegSchProj

open GlobalTheory.Unf

variable {D : D7}

theorem realSize_mul_le (θ : InfFam D) {m n k : ℕ} (Y : Mx D m n) (a : Mx D n k) :
    realSize θ (Y ⬝ a) ≤ (k * realSize θ Y) * realSize θ a := by
  calc realSize θ (Y ⬝ a) = ∑ τ, ∑ i, ∑ j, ‖∑ l, compAt θ τ Y i l * compAt θ τ a l j‖ := by
        simp only [realSize, MajMeas.compAt_mul, Matrix.mul_apply]
    _ ≤ ∑ τ, ∑ i, ∑ _j : Fin k, ∑ l, ‖compAt θ τ Y i l‖ * realSize θ a := by
        gcongr with τ _ i _ j _
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (MajMeas.norm_compAt_le_realSize θ a τ l j) (norm_nonneg _)
    _ = _ := by
        generalize realSize θ a = r
        simp only [realSize, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum,
          Finset.sum_mul, mul_assoc]

theorem maj_mt_le {θ : InfFam D} (hθ : IsInfFam θ) (T : HSp D) (n : ℕ) {K : Set (GA D T)} (hK : IsCompact K)
    {K₀ : Set (Mx D T.rank n)} (hK₀ : IsCompact K₀) :
    ∃ K' : Set (Mx D T.rank n), IsCompact K' ∧ ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ k ∈ K, ∀ u : Mx D T.rank n,
      maj θ K₀ N (mt T k⁻¹ ⬝ u) ≤ C * maj θ K' N u := by
  obtain ⟨h1, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  have hmt : Continuous (mt T) := GlobalTheory.MixModel.continuous_mt T
  obtain ⟨c, hc⟩ := (hK.image ((MajMeas.continuous_realSize hθ).comp hmt)).bddAbove
  let P : GA D T × Mx D T.rank n → Mx D T.rank n := fun p => mt T p.1 ⬝ p.2
  have hP : Continuous P := (hmt.comp continuous_fst).matrix_mul continuous_snd
  refine ⟨P '' (K ×ˢ K₀), (hK.prod hK₀).image hP, fun N => ⟨(1 + n * |c|) ^ N, by positivity, fun k hk u => ?_⟩⟩
  have hyx : (mt T k : Mx D T.rank T.rank) * mt T k⁻¹ = 1 := by
    show mt T (k * k⁻¹) = 1
    rw [mul_inv_cancel]; rfl
  have hu : (mt T k ⬝ (mt T k⁻¹ ⬝ u) : Mx D T.rank n) = u := by
    rw [← Matrix.mul_assoc, hyx, Matrix.one_mul]
  by_cases hb : InBox K₀ (mt T k⁻¹ ⬝ u)
  · have hb' : InBox (P '' (K ×ˢ K₀)) u := by
      obtain ⟨k0, hk0, hkx⟩ := hb
      refine ⟨P (k, k0), ⟨(k, k0), ⟨hk, hk0⟩, rfl⟩, ?_⟩
      have e : u - P (k, k0) = (mt T k ⬝ ((mt T k⁻¹ ⬝ u : Mx D T.rank n) - k0) : Mx D T.rank n) := by
        rw [Matrix.mul_sub, hu]
      rw [e, Matrix.map_mul, hkx, Matrix.mul_zero]
    simp only [maj, if_pos hb, if_pos hb']
    have hs := realSize_mul_le θ (mt T k) (mt T k⁻¹ ⬝ u : Mx D T.rank n)
    rw [hu] at hs
    have hck : realSize θ (mt T k) ≤ |c| := (hc ⟨k, hk, rfl⟩).trans (le_abs_self c)
    have h0 := realSize_nonneg θ (mt T k⁻¹ ⬝ u : Mx D T.rank n)
    have h0' := realSize_nonneg θ u
    generalize realSize θ (mt T k⁻¹ ⬝ u : Mx D T.rank n) = r at hs h0 ⊢
    have hs' : realSize θ u ≤ (n * |c|) * r := hs.trans (by gcongr)
    have hn : (0 : ℝ) ≤ n * |c| := by positivity
    have hle : 1 + realSize θ u ≤ (1 + n * |c|) * (1 + r) := by nlinarith
    have hA : 0 < (1 + r) ^ N := by positivity
    have hB : 0 < (1 + realSize θ u) ^ N := by positivity
    rw [inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ hA hB, one_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hle N
  · have e : maj θ K₀ N (mt T k⁻¹ ⬝ u) = 0 := by simp only [maj, if_neg hb]
    rw [e]
    exact mul_nonneg (by positivity) (maj_nonneg θ _ N u)

theorem exists_summable_bound {θ : InfFam D} (hθ : IsInfFam θ) (T : HSp D) (n : ℕ) {K : Set (GA D T)} (hK : IsCompact K)
    {Φ : Mx D T.rank n → ℂ} (hΦ : Φ ∈ schwartzA θ T.rank n) (x : Mx D T.rank n) :
    ∃ b : Matrix (Fin T.rank) (Fin n) D.host.E → ℝ, Summable b ∧
      ∀ k ∈ K, ∀ ξ, ‖Φ (mt T k⁻¹ ⬝ (x + rat ξ : Mx D T.rank n))‖ ≤ b ξ := by
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_summable_bound_schwartz_majorant_rational_translates D θ hθ T.rank n
  obtain ⟨-, K₀, hK₀, hC⟩ := GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ T.rank n Φ
    (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ T.rank n Φ hΦ)
  obtain ⟨C, hC⟩ := hC N
  obtain ⟨K', hK', hM⟩ := maj_mt_le hθ T n hK hK₀
  obtain ⟨C', hC', hM⟩ := hM N
  obtain ⟨b, hb, hb'⟩ := hN K' {x} hK' isCompact_singleton
  refine ⟨fun ξ => |C| * (C' * b ξ), (hb.mul_left C').mul_left |C|, fun k hk ξ => (hC _).trans ?_⟩
  exact mul_le_mul (le_abs_self C) ((hM k hk _).trans (mul_le_mul_of_nonneg_left (hb' x rfl ξ) hC'))
    (maj_nonneg _ _ _ _) (abs_nonneg C)

theorem hasSum_sch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D)
    {ν : Measure (WO A B)} {𝓨 : Set (WO A B)} (hν : IsCovolOne (ratL B A) ν 𝓨) {f : WO (dblSp A) B → ℂ}
    (hf : IsThetaFunO ψ (dblSp A) B f) (x y : Mx D B.rank A.rank) :
    HasSum (fun ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E =>
      ψ (symplO (dblSp A) B ((GlobalTheory.Core.Rk.SWLaw.dblDec A).extX B (x + rat ξ)) ((GlobalTheory.Core.Rk.SWLaw.dblDec A).extY B y)) * sch ψ A B ν 𝓨 f (x + rat ξ))
      (ψ (symplOH (dblSp A) B ((GlobalTheory.Core.Rk.SWLaw.dblDec A).extX B x) ((GlobalTheory.Core.Rk.SWLaw.dblDec A).extY B y)) *
        f ((GlobalTheory.Core.Rk.SWLaw.dblDec A).extX B x + (GlobalTheory.Core.Rk.SWLaw.dblDec A).extY B y)) := by
  have hg := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf ((GlobalTheory.Core.Rk.SWLaw.dblDec A).extY B y)
  have hsum := (GlobalTheory.Core.Rk.SchPeriod.theta_eq_sum_sch D ψ hψ A B ν 𝓨 hν _ hg x).2
  simp only [GlobalTheory.Core.Rk.SchwInj.sch_heisO_extY hψ A B hν hf] at hsum
  exact hsum

theorem projK_theta_sch : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle) (om : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ om → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ K : Subgroup (GA D B), IsCompact (K : Set (GA D B)) → ∀ νK : Measure K, IsProbabilityMeasure νK → ∀ φ, IsThetaFunO ψ (dblSp A) B φ → IsThetaFunO ψ (dblSp A) B (projK om νK φ) ∧ sch ψ A B ν 𝓨 (projK om νK φ) = projS νK (sch ψ A B ν 𝓨 φ) := by
  intro D ψ A B χ om hW ν 𝓨 hν K hK νK hνK φ hφ
  have hψ := hW.std
  obtain ⟨θ, hθ⟩ : ∃ θ : InfFam D, IsInfFam θ := GlobalTheory.DualPairCompare.exists_infFam D
  obtain ⟨h1, h2, -⟩ := GlobalTheory.SchSchwartzAll.schSchwartz D ψ hψ θ hθ A B ν 𝓨 hν
  obtain ⟨f', hf', hs⟩ := h2 _ (GlobalTheory.T.compactAverageSchwartzProjection_mem_adelicSchwartz D θ hθ B A.rank K hK νK hνK _ (h1 φ hφ))
  suffices h : projK om νK φ = f' by rw [h]; exact ⟨hf', hs⟩
  funext w
  obtain ⟨x, y, rfl⟩ := GlobalTheory.Core.Rk.SchwInj.exists_extX_add_extY A B w
  obtain ⟨b, hb, hb'⟩ := exists_summable_bound hθ B A.rank hK (h1 φ hφ) x
  obtain ⟨-, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  haveI : BorelSpace (GA D B) := ⟨rfl⟩
  haveI : IsTopologicalGroup (GA D B) := (Formalism.IndefR.Eqv.ga_facts D B).1
  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin B.rank) (Fin A.rank) D.host.E) := inferInstanceAs (Countable (Fin _ → Fin _ → _))
  have hc := (GlobalTheory.Core.Rk.SchInt.sch_continuous_integrable D ψ hψ A B ν 𝓨 hν φ hφ).1
  have hmt : Continuous fun k : K => mt B (k : GA D B)⁻¹ :=
    (GlobalTheory.MixModel.continuous_mt B).comp continuous_subtype_val.inv
  have hn : ∀ a, ‖ψ a‖ = 1 := hψ.1.2.1
  have key := hasSum_integral_of_dominated_convergence (μ := νK)
    (F := fun (ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E) (k : K) =>
      ψ (symplO (dblSp A) B ((GlobalTheory.Core.Rk.SWLaw.dblDec A).extX B (x + rat ξ)) ((GlobalTheory.Core.Rk.SWLaw.dblDec A).extY B y)) *
        sch ψ A B ν 𝓨 φ (mt B (k : GA D B)⁻¹ ⬝ (x + rat ξ : Mx D B.rank A.rank)))
    (f := fun k : K => ψ (symplOH (dblSp A) B ((GlobalTheory.Core.Rk.SWLaw.dblDec A).extX B x) ((GlobalTheory.Core.Rk.SWLaw.dblDec A).extY B y)) *
        om (1, (k : GA D B)) φ ((GlobalTheory.Core.Rk.SWLaw.dblDec A).extX B x + (GlobalTheory.Core.Rk.SWLaw.dblDec A).extY B y))
    (fun ξ _ => b ξ)
    (fun ξ => (continuous_const.mul (hc.comp (hmt.matrix_mul continuous_const))).measurable.aestronglyMeasurable)
    (fun ξ => .of_forall fun k => by rw [norm_mul, hn, one_mul]; exact hb' k k.2 ξ)
    (.of_forall fun _ => hb) (integrable_const _)
    (.of_forall fun k => by
      have h := hasSum_sch hψ A B hν (hW.om_pres (1, (k : GA D B)) φ hφ) x y
      simp only [(GlobalTheory.Core.Rk.SchLaws.sch_laws D ψ A B χ om hW ν 𝓨 hν φ hφ).1] at h
      exact h)
  simp only [integral_const_mul] at key
  have h' := hasSum_sch hψ A B hν hf' x y
  rw [hs] at h'
  have e := key.unique h'
  exact mul_left_cancel₀ (norm_ne_zero_iff.1 (by rw [hn]; exact one_ne_zero)) e

end GlobalTheory.RegSchProj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactAverageProjectionThetaSchrodingerStatement
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactAverageProjection_theta_schrodinger : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle) (om : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ om → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ K : Subgroup (GA D B), IsCompact (K : Set (GA D B)) → ∀ νK : Measure K, IsProbabilityMeasure νK → ∀ φ, IsThetaFunO ψ (dblSp A) B φ → IsThetaFunO ψ (dblSp A) B (projK om νK φ) ∧ sch ψ A B ν 𝓨 (projK om νK φ) = projS νK (sch ψ A B ν 𝓨 φ) := by
  first | exact @GlobalTheory.RegSchProj.projK_theta_sch | exact GlobalTheory.RegSchProj.projK_theta_sch | (intros; apply GlobalTheory.RegSchProj.projK_theta_sch <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanLevelVolumeMulRelIndex
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanLevelVolumeMulRelIndex
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevVol

variable {D : D7}

theorem mul_set_eq_comap (V : HSp D) (U : Subgroup (GA D V)) (hU : U ≤ GfC V) :
    {g : GA D V | ∃ k ∈ GinfC V, ∃ κ ∈ U, g = k * κ} =
      (((U.subgroupOf (GfC V)).comap (GlobalTheory.AutMult.toFin V) : Subgroup (GA D V)) : Set (GA D V)) := by
  ext g
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨k, hk, κ, hκ, rfl⟩
    have e : GlobalTheory.AutMult.toFin V (k * κ) = ⟨κ, hU hκ⟩ := by
      rw [map_mul, GlobalTheory.AutMult.toFin_coe_inf (⟨k, hk⟩ : GinfC V), one_mul]
      exact GlobalTheory.AutMult.toFin_coe (⟨κ, hU hκ⟩ : GfC V)
    rw [e]
    exact hκ
  · intro h
    exact ⟨_, (GlobalTheory.AutMult.toInf V g).2, _, h, (GlobalTheory.AutMult.toInf_mul_toFin g).symm⟩

theorem volLev_mul_relIndex : ∀ (D : D7) (V : HSp D) (v : GlobalTheory.Unf.Vol V) (U U' : Subgroup (GA D V)), U ≤ U' → U' ≤ GfC V →
    IsCompact (U' : Set (GA D V)) → IsOpen ((U.subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) →
    volLev v U * (U.relIndex U' : ℝ) = volLev v U' := by
  intro D V v U U' hle hU' _ hopn
  obtain ⟨i1, -, -, -, i5, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V
  haveI := i1
  haveI := i5
  haveI := v.haar
  have hU : U ≤ GfC V := hle.trans hU'
  set A := (U.subgroupOf (GfC V)).comap (GlobalTheory.AutMult.toFin V) with hA
  set A' := (U'.subgroupOf (GfC V)).comap (GlobalTheory.AutMult.toFin V) with hA'
  have hAA : A ≤ A' := Subgroup.comap_mono (fun x hx => Subgroup.mem_subgroupOf.2 (hle (Subgroup.mem_subgroupOf.1 hx)))
  have hAo : IsOpen (A : Set (GA D V)) := hopn.preimage (GlobalTheory.AutMult.continuous_toFin V)
  have key := MassDataLevelSSteps.toReal_eq_relIndex_mul_of_open v.μ A A' hAA hAo
  have hsurj : Function.Surjective (GlobalTheory.AutMult.toFin V) := fun y => ⟨y, GlobalTheory.AutMult.toFin_coe y⟩
  have hidx : A.relIndex A' = U.relIndex U' := by
    rw [hA, Subgroup.relIndex_comap, hA', Subgroup.map_comap_eq_self_of_surjective hsurj,
      Subgroup.relIndex_subgroupOf hU']
  unfold GlobalTheory.SeeSaw.volLev
  rw [mul_set_eq_comap V U hU, mul_set_eq_comap V U' hU', ← hA, ← hA', key, hidx, mul_comm]

end GlobalTheory.LevVol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanLevelVolumeMulRelIndexStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanLevelVolume_mul_relIndex : ∀ (D : D7) (V : HSp D) (v : GlobalTheory.Unf.Vol V) (U U' : Subgroup (GA D V)), U ≤ U' → U' ≤ GfC V → IsCompact (U' : Set (GA D V)) → IsOpen ((U.subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) → volLev v U * (U.relIndex U' : ℝ) = volLev v U' := by
  first | exact @GlobalTheory.LevVol.volLev_mul_relIndex | exact GlobalTheory.LevVol.volLev_mul_relIndex | (intros; apply GlobalTheory.LevVol.volLev_mul_relIndex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralUnitaryScalarOfNormOneIdele
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralUnitaryScalarOfNormOneIdele
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

variable {D : D7}

section Scal

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def scalGL (c c' : A) (h : c * c' = 1) : GL n A where
  val := c • (1 : Matrix n n A)
  inv := c' • (1 : Matrix n n A)
  val_inv := by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, h, one_smul]
  inv_val := by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_comm, h, one_smul]

theorem scalGL_mem (σ : A →+* A) (J : Matrix n n A) (c : A) (h : c * σ c = 1) :
    scalGL (n := n) c (σ c) h ∈ Formalism.UG.UJ σ J := by
  show Formalism.UG.cT σ (c • (1 : Matrix n n A)) * J * (c • (1 : Matrix n n A)) = J
  have hm : Formalism.UG.cT σ (c • (1 : Matrix n n A)) = σ c • (1 : Matrix n n A) := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases h1 : j = i
    · subst h1; simp
    · rw [if_neg h1, if_neg (Ne.symm h1)]; simp
  rw [hm, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, h, one_smul]

end Scal

variable {D : D7}

def scalGA (S : HSp D) (c : AE D) (hc : c * cA D c = 1) : GA D S :=
  ⟨scalGL c (cA D c) hc, by exact scalGL_mem _ _ c hc⟩

theorem mt_scalGA (S : HSp D) (c : AE D) (hc : c * cA D c = 1) :
    Formalism.L2.Theta.mt S (scalGA S c hc) = c • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := rfl

theorem scalGA_mem_center (S : HSp D) (c : AE D) (hc : c * cA D c = 1) :
    scalGA S c hc ∈ Subgroup.center (GA D S) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply GlobalTheory.FinPlLoc.mt_inj
  rw [GlobalTheory.FinPlLoc.mt_mul, GlobalTheory.FinPlLoc.mt_mul, mt_scalGA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.one_mul]

theorem scalGA_mem_grpAt (S : HSp D) (v : GlobalTheory.FinPl.Pl D) (c : AE D) (hc : NormOneAt v c) :
    scalGA S c hc.1 ∈ grpAt S (· = v) := by
  unfold grpAt
  rw [GlobalTheory.FinPlLoc.mem_congGrp]
  intro i j
  rw [mt_scalGA, Matrix.smul_apply, smul_eq_mul, ← sub_one_mul]
  exact Ideal.mul_mem_right _ _ hc.2

theorem exists_cenAt_scalar : ∀ (D : D7) (S : HSp D) (v : GlobalTheory.FinPl.Pl D) (c : AE D), NormOneAt v c → ∃ z : GA D S, CenAt S v z ∧ Formalism.L2.Theta.mt S z = c • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
  intro D S v c hc
  exact ⟨scalGA S c hc.1, ⟨scalGA_mem_grpAt S v c hc, scalGA_mem_center S c hc.1⟩, mt_scalGA S c hc.1⟩

end GlobalTheory.Core.Mi.LatMatch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralUnitaryScalarOfNormOneIdeleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_centralUnitary_scalar_of_normOneIdele : ∀ (D : D7) (S : HSp D) (v : GlobalTheory.FinPl.Pl D) (c : AE D), NormOneAt v c → ∃ z : GA D S, CenAt S v z ∧ Formalism.L2.Theta.mt S z = c • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.exists_cenAt_scalar | exact GlobalTheory.Core.Mi.LatMatch.exists_cenAt_scalar | (intros; apply GlobalTheory.Core.Mi.LatMatch.exists_cenAt_scalar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrOfMulEqZero
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.PutIn

variable {D : D7}

def tens {S T : HSp D} (b : AE D) (Φ Ψ : WO S T → ℂ) : WO S T → ℂ := fun t => Φ (t - b • t) * Ψ (b • t)

theorem tens_apply {S T : HSp D} (b : AE D) (Φ Ψ : WO S T → ℂ) (t : WO S T) :
    tens b Φ Ψ t = Φ (t - b • t) * Ψ (b • t) := rfl

def tensL {S T : HSp D} (b : AE D) (Ψ : WO S T → ℂ) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun Φ := tens b Φ Ψ
  map_add' Φ Φ' := by funext t; simp only [tens, Pi.add_apply, add_mul]
  map_smul' c Φ := by funext t; simp only [tens, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]

def tensR {S T : HSp D} (b : AE D) (Φ : WO S T → ℂ) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun Ψ := tens b Φ Ψ
  map_add' Ψ Ψ' := by funext t; simp only [tens, Pi.add_apply, mul_add]
  map_smul' c Ψ := by funext t; simp only [tens, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem tensL_apply {S T : HSp D} (b : AE D) (Ψ Φ : WO S T → ℂ) : tensL b Ψ Φ = tens b Φ Ψ := rfl

theorem tensR_apply {S T : HSp D} (b : AE D) (Φ Ψ : WO S T → ℂ) : tensR b Φ Ψ = tens b Φ Ψ := rfl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

def eSum (p : ι → SplitPt D k) (J : List ι) : AE D := (J.map fun i => (p i).e).sum

theorem eSum_cons (p : ι → SplitPt D k) (i : ι) (J : List ι) : eSum p (i :: J) = (p i).e + eSum p J := by
  simp [eSum]


open Classical in
def datJ (p : ι → SplitPt D k) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {S T : HSp D}
    (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n) (Ψ : ι → Matrix n n' k → ℂ) (J : List ι) (t : WO S T) : ℂ :=
  if IsHalf (eSum p J) t then (J.map fun i => Ψ i (rd (α i) (β i) t)).prod else 0

theorem pr_e (p : SplitPt D k) : p.pr p.e = 1 := by
  rw [← p.sec_one, p.pr_sec]

theorem pr_of_mul_eq_zero (p : SplitPt D k) {a : AE D} (h : p.e * a = 0) : p.pr a = 0 := by
  have := congrArg p.pr h
  rwa [map_mul, pr_e, one_mul, map_zero] at this

theorem mul_eSum (p : ι → SplitPt D k) (a : AE D) (J : List ι) (h : ∀ j ∈ J, a * (p j).e = 0) : a * eSum p J = 0 := by
  induction J with
  | nil => simp [eSum]
  | cons j J ih =>
    rw [eSum_cons, mul_add, h j (List.mem_cons_self), ih fun j' hj' => h j' (List.mem_cons_of_mem _ hj'), add_zero]

theorem eSum_mul (p : ι → SplitPt D k) (a : AE D) (J : List ι) (h : ∀ j ∈ J, (p j).e * a = 0) : eSum p J * a = 0 := by
  rw [mul_comm]; exact mul_eSum p a J fun j hj => by rw [mul_comm]; exact h j hj

theorem eSum_idem (p : ι → SplitPt D k) (horth : ∀ i j, i ≠ j → (p i).e * (p j).e = 0) (J : List ι) (hJ : J.Nodup) :
    eSum p J * eSum p J = eSum p J := by
  induction J with
  | nil => simp [eSum]
  | cons i J ih =>
    rw [List.nodup_cons] at hJ
    have h1 : (p i).e * eSum p J = 0 := mul_eSum p _ J fun j hj => horth i j fun h => hJ.1 (h ▸ hj)
    have h2 : eSum p J * (p i).e = 0 := by rw [mul_comm, h1]
    rw [eSum_cons, add_mul, mul_add, mul_add, (p i).split.1, h1, h2, ih hJ.2, add_zero, zero_add]

theorem pr_eSum (p : ι → SplitPt D k) (horth : ∀ i j, i ≠ j → (p i).e * (p j).e = 0) (J : List ι) (hJ : J.Nodup)
    (i : ι) (hi : i ∈ J) : (p i).pr (eSum p J) = 1 := by
  induction J with
  | nil => simp at hi
  | cons j J ih =>
    rw [List.nodup_cons] at hJ
    rw [eSum_cons, map_add (f := _)]
    by_cases hij : i = j
    · subst hij
      rw [pr_e, pr_of_mul_eq_zero (p i) (mul_eSum p _ J fun j hj => horth i j fun h => hJ.1 (h ▸ hj)), add_zero]
    · rw [pr_of_mul_eq_zero (p i) (horth i j hij), zero_add, ih hJ.2 ((List.mem_cons.1 hi).resolve_left hij)]

end GlobalTheory.FinPl.PutIn

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntLocIffValBar
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.LineUnit

open GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped NNReal

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {k : ℕ}

theorem exists_lt_nnnorm (v : HeightOneSpectrum (𝓞 F)) (C : ℝ≥0) : ∃ t : Fv F v, C < ‖t‖₊ := by
  letI : NontriviallyNormedField (Fv F v) := Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
  obtain ⟨t, ht⟩ := NormedField.exists_lt_norm (Fv F v) (C : ℝ)
  exact ⟨t, by exact_mod_cast ht⟩

theorem valBar_smul (τ : E →ₐ[F] FvBar F v) (t : Fv F v) (y : Fv F v ⊗[F] E) :
    valBar F v (finEmb F v τ (t • y)) = ‖t‖₊ * valBar F v (finEmb F v τ y) := by
  rw [map_smul, Algebra.smul_def, map_mul]
  congr 1
  exact absBar_algebraMap F v t

theorem mem_intLoc_iff_valBar {y : Fv F v ⊗[F] E} :
    y ∈ intLoc F E v ↔ ∀ τ : E →ₐ[F] FvBar F v, valBar F v (finEmb F v τ y) ≤ 1 :=
  mem_intLoc_iff_absFin_le_one.trans (absFin_le_iff F v)

theorem exists_valBar_ne_zero {u l : Fin k → Fv F v ⊗[F] E} (h : ∑ j, l j * u j = 1) (τ : E →ₐ[F] FvBar F v) :
    ∃ j, valBar F v (finEmb F v τ (u j)) ≠ 0 := by
  by_contra hc
  push Not at hc
  have := congrArg (finEmb F v τ) h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_one, Finset.sum_eq_zero fun j _ => by
    rw [map_mul, (Valuation.zero_iff _).1 (hc j), mul_zero]] at this
  exact zero_ne_one this

theorem mem_intLoc_of_stable {u l : Fin k → Fv F v ⊗[F] E} (h : ∑ j, l j * u j = 1) {c : Fv F v ⊗[F] E}
    (hc : ∀ a, (∀ j, a * u j ∈ intLoc F E v) → ∀ j, c * a * u j ∈ intLoc F E v) : c ∈ intLoc F E v := by
  obtain ⟨t, ht⟩ := exists_lt_nnnorm v (Finset.univ.sup fun j => absFin F v (u j))
  have ht0 : ‖t‖₊ ≠ 0 := (lt_of_le_of_lt zero_le ht).ne'
  have h0 : ∀ j, (t⁻¹ • (1 : Fv F v ⊗[F] E)) * u j ∈ intLoc F E v := fun j => by
    rw [smul_mul_assoc, one_mul, mem_intLoc_iff_valBar]
    intro τ
    rw [valBar_smul, nnnorm_inv, inv_mul_le_iff₀ (pos_iff_ne_zero.2 ht0), mul_one]
    exact (le_absFin F v τ (u j)).trans
      ((Finset.le_sup (f := fun j => absFin F v (u j)) (Finset.mem_univ j)).trans ht.le)
  have hk : ∀ m : ℕ, ∀ j, c ^ m * (t⁻¹ • (1 : Fv F v ⊗[F] E)) * u j ∈ intLoc F E v := fun m => by
    induction m with
    | zero => simpa only [pow_zero, one_mul] using h0
    | succ m ih =>
      intro j
      have := hc _ ih j
      rwa [← mul_assoc, ← pow_succ'] at this
  rw [mem_intLoc_iff_valBar]
  intro τ
  obtain ⟨j, hj⟩ := exists_valBar_ne_zero h τ
  by_contra hlt
  rw [not_le] at hlt
  have hpos : 0 < ‖t‖₊⁻¹ * valBar F v (finEmb F v τ (u j)) :=
    mul_pos (inv_pos.2 (pos_iff_ne_zero.2 ht0)) (pos_iff_ne_zero.2 hj)
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (‖t‖₊⁻¹ * valBar F v (finEmb F v τ (u j)))⁻¹ hlt
  have h1 := mem_intLoc_iff_valBar.1 (hk m j) τ
  rw [mul_assoc, smul_mul_assoc, one_mul, map_mul, map_mul, map_pow, map_pow, valBar_smul, nnnorm_inv,
    ← le_mul_inv_iff₀ hpos, one_mul] at h1
  exact absurd h1 (not_le.2 hm)

theorem isUnit_of_reflect {u l : Fin k → Fv F v ⊗[F] E} (h : ∑ j, l j * u j = 1) {c : Fv F v ⊗[F] E}
    (hc : ∀ a, (∀ j, c * a * u j ∈ intLoc F E v) → ∀ j, a * u j ∈ intLoc F E v) : IsUnit c := by
  haveI : IsArtinianRing (Fv F v ⊗[F] E) := IsArtinianRing.of_finite (Fv F v) _
  refine IsArtinianRing.isUnit_of_mem_nonZeroDivisors (mem_nonZeroDivisors_iff_left.2 fun a ha => ?_)
  refine absFin_eq_zero_iff.1 (le_antisymm ((absFin_le_iff F v).2 fun τ => ?_) zero_le)
  by_contra hne
  have hpa : 0 < valBar F v (finEmb F v τ a) := not_le.1 hne
  obtain ⟨j, hj⟩ := exists_valBar_ne_zero h τ
  have hpos : 0 < valBar F v (finEmb F v τ (a * u j)) := by
    rw [map_mul, map_mul]; exact mul_pos hpa (pos_iff_ne_zero.2 hj)
  obtain ⟨t, ht⟩ := exists_lt_nnnorm v (valBar F v (finEmb F v τ (a * u j)))⁻¹
  have h1 := mem_intLoc_iff_valBar.1
    (hc (t • a) (fun j => by rw [mul_smul_comm, ha, smul_zero, zero_mul]; exact zero_mem _) j) τ
  rw [smul_mul_assoc, valBar_smul, ← le_mul_inv_iff₀ hpos, one_mul] at h1
  exact absurd h1 (not_le.2 ht)

theorem smul_mem_latLoc_iff {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L)
    {w l : Fin n → Fv F v ⊗[F] E} (h : l ⬝ᵥ w = 1) {c : Fv F v ⊗[F] E}
    (hc : ∀ a : Fv F v ⊗[F] E, (c * a) • w ∈ latLoc F L v ↔ a • w ∈ latLoc F L v) (y : Fin n → Fv F v ⊗[F] E) :
    y ∈ latLoc F L v ↔ c • y ∈ latLoc F L v := by
  obtain ⟨k, S, Φ, h1, hS, hΦ⟩ := SelfDual.exists_frame L hL
  have h2 := SelfDual.map_mul_eq_one (F := F) (Fv F v) h1
  set u := Φ.map (inclR (F := F) (Fv F v)) *ᵥ w with hu
  have hl : ∑ j, (l ᵥ* S.map (inclR (F := F) (Fv F v))) j * u j = 1 := by
    change (l ᵥ* _) ⬝ᵥ u = 1
    rw [← Matrix.dotProduct_mulVec, hu, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, h]
  have key : ∀ a : Fv F v ⊗[F] E, a • w ∈ latLoc F L v ↔ ∀ j, a * u j ∈ intLoc F E v := fun a => by
    rw [SelfDual.mem_latLoc_iff_of_frame h1 hS hΦ v, Matrix.mulVec_smul]
    rfl
  simp only [key] at hc
  have hc1 := mem_intLoc_of_stable hl fun a => (hc a).2
  obtain ⟨c, rfl⟩ := isUnit_of_reflect hl fun a => (hc a).1
  have hc2 : ((c⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ intLoc F E v :=
    mem_intLoc_of_stable hl fun a ha => (hc _).1 fun j => by rw [Units.mul_inv_cancel_left]; exact ha j
  refine ⟨fun hy => (latLoc F L v).smul_mem ⟨_, hc1⟩ hy, fun hy => ?_⟩
  have := (latLoc F L v).smul_mem ⟨_, hc2⟩ hy
  change ((c⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) • (c : Fv F v ⊗[F] E) • y ∈ _ at this
  rwa [smul_smul, Units.inv_mul, one_smul] at this

end Local


set_option maxHeartbeats 1600000 in
theorem smul_mem_latV_iff : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (Λ : GlobalTheory.FinPl.Lat V), Submodule.IsFullLattice D.host.E Λ → ∀ (v : GlobalTheory.FinPl.Pl D) (ε : Fin V.rank → D.host.E), ε ≠ 0 → ∀ (c : AE D) (s : Matrix (Fin V.rank) (Fin V.rank) (AE D)), IsUnit s → (∀ a ∈ GlobalTheory.FinPl.idAt D (· = v), (Matrix.mulVec (s) (fun i => c * (a * Formalism.L2.Theta.incA D (ε i))) ∈ GlobalTheory.FinPl.latV V Λ (· = v) ↔ Matrix.mulVec (s) (fun i => a * Formalism.L2.Theta.incA D (ε i)) ∈ GlobalTheory.FinPl.latV V Λ (· = v))) → ∀ y : Fin V.rank → AE D, (∀ i, y i ∈ GlobalTheory.FinPl.idAt D (· = v)) → (y ∈ GlobalTheory.FinPl.latV V Λ (· = v) ↔ c • y ∈ GlobalTheory.FinPl.latV V Λ (· = v)) := by
  intro D V Λ hΛ v ε hε c s hs h y hy
  have hfg : Λ.FG := by
    letI := hΛ
    exact Submodule.IsLattice.fg D.host.E Λ
  let π : AE D →+* Fv D.host.F v ⊗[D.host.F] D.host.E := (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v).comp (finPart D)
  have hπ : ∀ z : Fin V.rank → AE D, (∀ i, z i ∈ GlobalTheory.FinPl.idAt D (· = v)) →
      (z ∈ GlobalTheory.FinPl.latV V Λ (· = v) ↔ (fun i => π (z i)) ∈ latLoc D.host.F Λ v) := fun z hz =>
    GlobalTheory.StMoves.mem_latV_iff_latLoc V Λ hfg v z hz
  let w : Fin V.rank → AE D := s *ᵥ fun i => Formalism.L2.Theta.incA D (ε i)
  have hw : ∀ a : AE D, (s *ᵥ fun i => a * Formalism.L2.Theta.incA D (ε i)) = a • w := fun a =>
    Matrix.mulVec_smul s a _
  obtain ⟨l, hl⟩ : ∃ l : Fin V.rank → AE D, l ⬝ᵥ w = 1 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hε
    obtain ⟨s', rfl⟩ := hs
    refine ⟨(Pi.single i (Formalism.L2.Theta.incA D (ε i)⁻¹)) ᵥ* (s'⁻¹).1, ?_⟩
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, single_dotProduct,
      ← map_mul, inv_mul_cancel₀ hi, map_one]
  have hl' : (fun i => π (l i)) ⬝ᵥ (fun i => π (w i)) = 1 := by
    rw [← map_one π, ← hl]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sum, map_mul]
  have hsm : ∀ (a : AE D) (z : Fin V.rank → AE D), (fun i => π ((a • z) i)) = π a • fun i => π (z i) :=
    fun a z => funext fun i => map_mul π a (z i)
  rw [hπ y hy, hπ (c • y) fun i => Ideal.mul_mem_left _ _ (hy i), hsm]
  refine smul_mem_latLoc_iff Λ hΛ hl' (fun b => ?_) _
  obtain ⟨a, ha, hab⟩ := GlobalTheory.StMoves.exists_supp_vecLoc_eq (D := D) (n := 1) v fun _ => b
  have hab' : π (a 0) = b := congrFun hab 0
  have h1 := h (a 0) (ha 0)
  simp only [← mul_assoc] at h1
  rw [hw, hw, hπ ((c * a 0) • w) fun i => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (ha 0)),
    hπ (a 0 • w) fun i => Ideal.mul_mem_right _ _ (ha 0), hsm, hsm, map_mul, hab'] at h1
  exact h1

end GlobalTheory.LineUnit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthAtSumLatO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Core.Rk.SumSplit

theorem orthAt_sumLatO : ∀ (D : D7) (S A B : HSp D) (o : OrthDec S A B) (LA : Lat A) (LB : Lat B) (v : Pl D),
    OrthAt o (GlobalTheory.Core.Rk.SumBox.sumLatO o LA LB) LA LB v := by
  intro D S A B o LA LB v y
  constructor
  · intro hy
    refine ⟨GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.qA (fun x hx => ?_) _ hy,
      GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.qB (fun x hx => ?_) _ hy⟩
    · obtain ⟨x₁, hx₁, x₂, -, rfl⟩ := (GlobalTheory.Core.Rk.SumBox.mem_sumLatO o LA LB x).1 hx
      rw [GlobalTheory.Core.Rk.SumBox.qA_split]; exact hx₁
    · obtain ⟨x₁, -, x₂, hx₂, rfl⟩ := (GlobalTheory.Core.Rk.SumBox.mem_sumLatO o LA LB x).1 hx
      rw [GlobalTheory.Core.Rk.SumBox.qB_split]; exact hx₂
  · rintro ⟨hA, hB⟩
    have e : y = o.jA *ᵥ (o.pA *ᵥ y) + o.jB *ᵥ (o.pB *ᵥ y) := by
      have hs : o.jA * o.pA + o.jB * o.pB = 1 := by
        change (o.iA.map (incA D)) * (o.qA.map (incA D)) + (o.iB.map (incA D)) * (o.qB.map (incA D)) = 1
        rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add (incA D)),
          o.iA_qA_add, Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))]
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, hs, Matrix.one_mulVec]
    rw [e]
    exact add_mem
      (GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.iA
        (fun x hx => GlobalTheory.Core.Rk.SumBox.iA_mem_sumLatO o LB hx) _ hA)
      (GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.iB
        (fun x hx => GlobalTheory.Core.Rk.SumBox.iB_mem_sumLatO o LA hx) _ hB)

end GlobalTheory.Core.Rk.SumSplit
end
end
