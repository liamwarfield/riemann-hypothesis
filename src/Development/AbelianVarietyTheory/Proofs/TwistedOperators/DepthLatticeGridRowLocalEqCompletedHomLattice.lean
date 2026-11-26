module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankCol
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelFourth

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLocalEqCompletedHomLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLocalEqCompletedHomLattice
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.RowLoc

variable {D : D7}

theorem gen_negSp (S T : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * (negSp S).gram k j) : WO (negSp S) T) =
      -(Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) := by
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem mem_latO_negSp {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : GlobalTheory.FinPl.Pl D → Prop} {u : WO S T} : u ∈ latO (negSp S) T LS LT P ↔ u ∈ latO S T LS LT P := by
  constructor
  · intro hu
    induction hu using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
      rw [gen_negSp]
      exact neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩)
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
  · intro hu
    induction hu using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
      rw [← neg_neg (Matrix.of _), ← gen_negSp]
      exact neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩)
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx

theorem latRow_at : All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∀ v ∉ G.pl.S0, ∀ u : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)),
    MxAt (· = v) u → (u ∈ latRow G i ↔ u ∈ latO _ _ (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (· = v)) := by
  intro D _ T L μ0 _ sc G W M _ i _ v hv u hu
  have hoff : ∀ e : AE D, IsIdemSum e G.pl.W0 → e • u = 0 := by
    intro e he
    have he' := GlobalTheory.StepComb.idemSum_mem_idAt he
    have hev : e ∈ idOff D (· = v) := by
      rw [idOff, Ideal.mem_iInf]
      rintro ⟨w, rfl⟩
      rw [idAt, Ideal.mem_inf, Ideal.mem_iInf] at he'
      refine he'.2 ⟨w, ?_⟩
      rintro ⟨PP, hPP, hw⟩
      classical
      simp only [Places.W0, Finset.mem_image] at hPP
      obtain ⟨s, hs, rfl⟩ := hPP
      exact hv (by rw [hw, G.pl.under_w hs]; exact hs)
    refine Matrix.ext fun a b => ?_
    rw [Matrix.smul_apply, smul_eq_mul, mul_comm, Matrix.zero_apply]
    exact GlobalTheory.FinPl.FlatUnitPf.idAt_mul_idOff _ _ _ (hu a b) hev
  have k1 : u ∈ latO (negSp (G.V (.grid (i + 1) 0))) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (fun _ => True) ↔
      u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (fun _ => True) := mem_latO_negSp
  have k2 : u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (fun _ => True) ↔
      u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (· = v) :=
    GlobalTheory.AscFinWit.mem_latO_at (LS := G.Λ (.grid (i + 1) 0)) (LT := G.Λ (.grid i 0)) hu
  exact ⟨fun h => k2.1 (k1.1 h.1), fun h => ⟨k1.2 (k2.2 h), fun e he => by rw [hoff e he]; exact zero_mem _⟩⟩

end GlobalTheory.RowLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLocalEqCompletedHomLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthLatticeGridRow_local_eq_completed_homLattice : All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∀ v ∉ G.pl.S0, ∀ u : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)), MxAt (· = v) u → (u ∈ latRow G i ↔ u ∈ latO _ _ (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (· = v)) := by
  first | exact @GlobalTheory.RowLoc.latRow_at | exact GlobalTheory.RowLoc.latRow_at | (intros; apply GlobalTheory.RowLoc.latRow_at <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeIffIntegralOnUnitHalf
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeIffIntegralOnUnitHalf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


open GlobalTheory.RowLatChi in
theorem GlobalTheory.ColLatDict.mem_latO_iff_intM : ∀ {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)} {βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)}, IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsFrame βS ΛS → IsFrame βT ΛT → ∀ {e₁ : AE D} {P₁ : Finset (Pl D.host.E)}, IsIdemSum e₁ P₁ → (∀ w ∈ P₁, ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)) → ∀ z : WO S T, IsHalf e₁ z → (z ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔ ∀ w ∈ P₁, GlobalTheory.StepData.IntM ((GlobalTheory.FunObj.Comparison₂.fr βT βS (z.map (toEAf D))).map (cpt (D := D) w))) := by
  intro D S T ΛS ΛT βS βT hS hT hβS hβT e₁ P₁ hI hAA z hz
  have key : ∀ w, GlobalTheory.StepData.IntM ((GlobalTheory.FunObj.Comparison₂.fr βT βS (z.map (toEAf D))).map (cpt (D := D) w)) ↔
      ∀ a b, Valued.v (cpt (D := D) w (Comparison₂.fr βT βS (z.map (toEAf D)) a b)) ≤ 1 := fun w => by
    rw [intM_iff]; rfl
  simp only [key]
  constructor
  · intro h w hw a b
    exact int_of_mem_latO hS hβS hβT w (hAA w hw).1 h a b
  · intro h
    exact mem_latO_of_mem_hatMx hS hI (fun w hw => (hAA w hw).2) hz (mem_hatMx_of_int hβS hβT hI hz h)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeIffIntegralOnUnitHalfStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedHomLattice_iff_integral_on_unit_half : ∀ {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)} {βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)}, IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsFrame βS ΛS → IsFrame βT ΛT → ∀ {e₁ : AE D} {P₁ : Finset (Pl D.host.E)}, IsIdemSum e₁ P₁ → (∀ w ∈ P₁, ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)) → ∀ z : WO S T, IsHalf e₁ z → (z ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔ ∀ w ∈ P₁, GlobalTheory.StepData.IntM ((GlobalTheory.FunObj.Comparison₂.fr βT βS (z.map (toEAf D))).map (cpt (D := D) w))) := by
  first | exact @GlobalTheory.ColLatDict.mem_latO_iff_intM | exact GlobalTheory.ColLatDict.mem_latO_iff_intM | (intros; apply GlobalTheory.ColLatDict.mem_latO_iff_intM <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixingNegativeVacuumDefiniteBottom
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixingNegativeVacuumDefiniteBottom
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

open scoped Topology

noncomputable section

namespace GlobalTheory.VacFixNeg

open GlobalTheory.Grid (neg)


set_option maxHeartbeats 1000000 in
theorem exists_open_fix_vac_neg : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D A), IsOpen (U : Set (GA D A)) ∧ GinfC A ≤ U ∧
      ∀ k ∈ U, k ∈ GfC A → X.ω t (k, 1) X.vac = X.vac := by
  intro D T L sc G W i j A A' WW X hX t
  set om' := (X.ω t).toSgn true with hom'
  have hW : IsWeilDatumO W.ψ (neg A) WW _ _ om' := hX.is.weil t
  have hvac : IsVacO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.Λ X.rW.Λ X.vac := hX.is.isVac
  have hθ : IsInfFam W.θ := hvac.2.inf
  have hsdS : IsSelfDualC (neg A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' hX.is.rigA.1
  have hsdT : IsSelfDualC WW X.rW.Λ := hX.is.rigW.1
  have hcS : ∀ τ, IsCartanInv (gramAt D (neg A) τ) (-X.rA.s τ) := fun τ =>
    GlobalTheory.Grid.isCartanInv_sgn true A τ (hX.is.rigA.2.2 τ).1
  have hcT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hX.is.rigW.2.2 τ).1
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.VacTranslate.exists_finCong_mod (neg A) WW X.rA.Λ X.rW.Λ hsdS hsdT 1 one_pos
  set N₁ := n₀.factorial with hN₁def
  have hN₁ : 0 < N₁ := n₀.factorial_pos
  have hscal : ∀ k ∈ GfC (neg A), GlobalTheory.Member.FinCong (neg A) N₁ k →
      ∃ c : ℂ, ‖c‖ = 1 ∧ om' (k, 1) X.vac = c • X.vac := by
    intro k hk hc
    have hΛ := GlobalTheory.VacTranslate.lat_iff_of_mod hn₀
      (show k ∈ GlobalTheory.Member.PrincLevel.levelGroup (neg A) N₁ from ⟨hk, hc⟩)
    have hvac' := GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ (neg A) WW _ _ om' hW hθ
      (fun τ => -X.rA.s τ) (fun τ => -X.rA.s τ) X.rW.s X.rW.s _ _ _ _ k 1
      (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ (neg A) hk τ, Matrix.one_mul, Matrix.mul_one])
      (fun τ => GlobalTheory.SmoothVac.comm_compAt_one WW W.θ τ (X.rW.s τ)) hΛ X.vac hvac
    exact GlobalTheory.VacUnique.vacUniqueO D W.ψ W.θ hvac.1 hθ (Formalism.L2.Fam.ThC.fixSig (neg A)) (Formalism.L2.Fam.ThC.fixSig WW)
      (fun τ => -X.rA.s τ) X.rW.s (Formalism.L2.Fam.ThC.fixSig_ok _) (Formalism.L2.Fam.ThC.fixSig_ok _) hcS hcT X.rA.Λ X.rW.Λ
      hsdS hsdT X.vac _ (GlobalTheory.VacFixTarget.isVacO_fixSig hvac) (GlobalTheory.VacFixTarget.isVacO_fixSig hvac')
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hvac
  have hcont : Continuous fun k : GA D (neg A) => om' (k, 1) X.vac w₀ :=
    (hW.om_cont _ hvac.2.theta w₀).comp (continuous_id.prodMk continuous_const)
  have key : ∃ n : ℕ, ∀ k ∈ GfC (neg A), GlobalTheory.Member.FinCong (neg A) (N₁ * n.factorial) k →
      om' (k, 1) X.vac = X.vac := by
    by_contra hne
    push_neg at hne
    choose k hk hkc hkne using hne
    have hpow : ∀ n, ∃ m : ℕ, ∃ c : ℂ, om' (k n ^ m, 1) X.vac = c • X.vac ∧ ¬ ‖c - 1‖ ≤ 1 / 2 := by
      intro n
      obtain ⟨c, -, hc⟩ := hscal (k n) (hk n) (GlobalTheory.SmoothVac.finCong_of_mul_left (hkc n))
      have hc1 : c ≠ 1 := by
        rintro rfl
        exact hkne n (by rw [hc, one_smul])
      by_contra h
      push_neg at h
      exact hc1 (GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le (A := ℂ) fun m =>
        h m (c ^ m) (GlobalTheory.VacFixSource.om_pow_eq_fst _ (k n) _ c hc m))
    choose m c hmc hc using hpow
    have hmem : ∀ n, k n ^ m n ∈ GlobalTheory.Member.PrincLevel.levelGroup (neg A) (N₁ * n.factorial) :=
      fun n => pow_mem (show k n ∈ GlobalTheory.Member.PrincLevel.levelGroup (neg A) (N₁ * n.factorial) from ⟨hk n, hkc n⟩) _
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := fun n => k n ^ m n) (fun n => (hmem n).1)
      (fun n => GlobalTheory.SmoothVac.finCong_of_mul_right (hmem n).2)
    have h2 := (hcont.tendsto 1).comp ht
    have e1 : om' ((1 : GA D (neg A)), (1 : GA D WW)) X.vac w₀ = X.vac w₀ := by
      show om' 1 X.vac w₀ = _
      rw [map_one]
      rfl
    rw [Function.comp_def, e1] at h2
    have hpos : 0 < ‖X.vac w₀‖ / 2 := half_pos (norm_pos_iff.2 hw₀)
    obtain ⟨n, hn⟩ := (h2.eventually (Metric.ball_mem_nhds _ hpos)).exists
    rw [hmc n, Pi.smul_apply, smul_eq_mul, dist_eq_norm, ← sub_one_mul, norm_mul] at hn
    have := hc n
    push_neg at this
    nlinarith [norm_nonneg (X.vac w₀)]
  obtain ⟨n, hn⟩ := key
  have hNpos : 0 < N₁ * n.factorial := Nat.mul_pos hN₁ n.factorial_pos
  refine ⟨(GlobalTheory.VacFixTarget.congGroup (neg A) (N₁ * n.factorial)).comap (GlobalTheory.Grid.ofSgn true A).symm.toMonoidHom,
    (GlobalTheory.Grid.continuous_ofSgn_symm true A).isOpen_preimage _ (GlobalTheory.VacFixTarget.isOpen_congGroup (neg A) hNpos),
    fun k hk => ?_, fun k hU hk => ?_⟩
  · show GlobalTheory.Member.FinCong (neg A) (N₁ * n.factorial) ((GlobalTheory.Grid.ofSgn true A).symm k)
    have h1 : finHom (neg A) ((GlobalTheory.Grid.ofSgn true A).symm k) = 1 := hk
    intro z hz
    refine ⟨0, by first | exact zero_mem _ | exact Submodule.zero_mem _ | exact AddSubgroup.zero_mem _ | simp [Formalism.L2.Pj.latHat], ?_⟩
    rw [h1, Units.val_one, Matrix.one_mulVec, sub_self]
    exact (nsmul_zero _).symm
  · have h1 := hn ((GlobalTheory.Grid.ofSgn true A).symm k) hk hU
    have e : om' ((GlobalTheory.Grid.ofSgn true A).symm k, 1) = X.ω t (k, 1) := by
      simp [hom', GlobalTheory.Grid.WRep.toSgn]
    rw [e] at h1
    exact h1

end GlobalTheory.VacFixNeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixingNegativeVacuumDefiniteBottomStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_fixing_negative_vacuum_definite_bottom : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D A), IsOpen (U : Set (GA D A)) ∧ GinfC A ≤ U ∧
      ∀ k ∈ U, k ∈ GfC A → X.ω t (k, 1) X.vac = X.vac := by
  first | exact @GlobalTheory.VacFixNeg.exists_open_fix_vac_neg | exact GlobalTheory.VacFixNeg.exists_open_fix_vac_neg | (intros; apply GlobalTheory.VacFixNeg.exists_open_fix_vac_neg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopPairSourceCharProdLocalIdeles
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopPairSourceCharProdLocalIdeles
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)

noncomputable section

namespace GlobalTheory.TopLevelInv

theorem chrS_top_prod_locIdele : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {t μ₀ : T}, L.Is μ₀ →
    ∀ (j : ℕ), j + 1 < D.R.m → ∀ y : ∀ w : locPl G t, (Kw w.1)ˣ,
    ((G.chrS (.top t j) (∏ w : locPl G t, GlobalTheory.LFun.locIdele D.host.F w.1 (y w)) : Circle) : ℂ) =
      ∏ w : locPl G t, (((locGrid G t w).mu (j + 1) (y w) : ℂˣ) : ℂ) := by
  intro D T L sc G t μ₀ hL j hj y
  have hrank : (G.pS (.top t j)).rank = rankX D j :=
    (G.isV (X := .top j) (show j ≤ D.R.m by omega) (fun _ h => by cases h)).rank
  have hchr : G.chrS (.top t j) = L.mu t (j + 1) := by
    rw [GridData.chrS, hrank]
    simp [Formalism.IndefR.Lift.attChr, GridData.chr, Nat.not_odd_iff_even.2 (even_rankX D j)]
  have hE : ChrEq (L.mu t (j + 1)) (muBase L (j + 1) * L.xiH t) := by
    have h1 : muBase L (j + 1) = L.C.mu0 ⟨j, by omega⟩ := dif_pos (by omega)
    rw [h1]
    exact GlobalTheory.TowerCharRead.chrEq_mul (hL.mu0 ⟨j, by omega⟩) (hL.xi t)
  rw [hchr, map_prod]
  rw [show ∀ (s : Finset (locPl G t)) (f : locPl G t → Circle), ((∏ w ∈ s, f w : Circle) : ℂ) = ∏ w ∈ s, (f w : ℂ) from
    fun s f => map_prod Circle.coeHom f s]
  refine Finset.prod_congr rfl fun w _ => ?_
  exact congrArg (fun f => ((f (y w) : ℂˣ) : ℂ)) (GlobalTheory.LFun.locChar_eq_of_chrEq hE w.1)

end GlobalTheory.TopLevelInv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopPairSourceCharProdLocalIdelesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topPairSourceChar_prod_localIdeles : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {t μ₀ : T}, L.Is μ₀ →
    ∀ (j : ℕ), j + 1 < D.R.m → ∀ y : ∀ w : locPl G t, (Kw w.1)ˣ,
    ((G.chrS (.top t j) (∏ w : locPl G t, GlobalTheory.LFun.locIdele D.host.F w.1 (y w)) : Circle) : ℂ) =
      ∏ w : locPl G t, (((locGrid G t w).mu (j + 1) (y w) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.TopLevelInv.chrS_top_prod_locIdele | exact GlobalTheory.TopLevelInv.chrS_top_prod_locIdele | (intros; apply GlobalTheory.TopLevelInv.chrS_top_prod_locIdele <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralAdeleSmulDepthLatticeGridRowMemLatO
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralAdeleSmulDepthLatticeGridRowMemLatO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.RowInt

variable {D : D7}

theorem latO_negSp_le (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO (negSp S) T LS LT P ≤ latO S T LS LT P := by
  unfold latO
  rw [AddSubgroup.closure_le]
  rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  rw [← neg_neg (Matrix.of _)]
  refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem smul_mem_latO_at : All fun {D} _ _ _ {G} _ _ =>
    ∀ i, i < D.R.m → ∀ v, ∀ e ∈ intAt D (· = v), ∀ u ∈ latRow G i,
      e • u ∈ latO _ _ (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (· = v) := by
  intro D _ T L μ0 _ sc G W M _ i _ v e he u hu
  have h0 : u ∈ latO (negSp (G.V (.grid (i + 1) 0))) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _)
      (G.Λ (.grid i 0) : Set _) (fun _ => True) := hu.1
  have h1 : u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _)
      (G.Λ (.grid i 0) : Set _) (fun _ => True) := latO_negSp_le _ _ _ _ _ h0
  have h2 := GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ e he.2 u h1
  have h3 : MxAt (· = v) (e • u) := fun a b => Ideal.mul_mem_right _ _ he.1
  exact (GlobalTheory.AscFinWit.mem_latO_at h3).1 h2

end GlobalTheory.RowInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralAdeleSmulDepthLatticeGridRowMemLatOStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralAdele_smul_depthLatticeGridRow_mem_latO : All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∀ v, ∀ e ∈ intAt D (· = v), ∀ u ∈ latRow G i, e • u ∈ latO _ _ (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (· = v) := by
  first | exact @GlobalTheory.RowInt.smul_mem_latO_at | exact GlobalTheory.RowInt.smul_mem_latO_at | (intros; apply GlobalTheory.RowInt.smul_mem_latO_at <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DeterminantIdeleAtSplitPlaceMovedGridNode
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DeterminantIdeleAtSplitPlaceMovedGridNode
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar
namespace GlobalTheory.RowDetLocal
variable {D : D7}

theorem toFinAd_eq (z : TensorProduct D.host.F (Af D.host.F) D.host.E) :
    GlobalTheory.LFun.toFinAd D.host.F D.host.E z = GlobalTheory.StdFrames.toAd D (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [Algebra.TensorProduct.comm_tmul, GlobalTheory.StdFrames.toAd_spec, mul_comm]
    rfl
  | add x y hx hy => rw [map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]

theorem compAt_eq_cpt (w : Pl D.host.E) (a : AE D) :
    GlobalTheory.LFun.compAt D.host.F w (finPart D a) = GlobalTheory.StdFrames.cpt w (toEAf D a) := by
  show (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.E w) (GlobalTheory.LFun.toFinAd D.host.F D.host.E (finPart D a)) = _
  rw [toFinAd_eq]
  rfl

theorem gdet_inBasis_val (V : HSp D) {n' : ℕ} (h : n' = V.rank) (β : GL (Fin V.rank) (Lev.EAf D)) (w : Pl D.host.E) (k : GfC V) :
    ((gdet (inBasis h β w (finG V k)) : (Kw w)ˣ) : Kw w) =
      GlobalTheory.StdFrames.cpt w (toEAf D (Formalism.L2.Theta.mt V (k : GA D V)).det) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  rw [GlobalTheory.FunObj.inBasis, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, GlobalTheory.TopLevelInv.det_val_reGL, GlobalTheory.TopLevelInv.val_loc, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    GlobalTheory.TopLevelInv.det_val_conj_inv, GlobalTheory.TopLevelInv.val_finG, ← RingHom.mapMatrix_apply, ← RingHom.map_det]

theorem detIdl_eq_locIdele (V : HSp D) (g : GA D V) (w : Pl D.host.E) (hs : ∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e w)
    (z : (Kw w)ˣ) (hz : (z : Kw w) = GlobalTheory.StdFrames.cpt w (toEAf D (Formalism.L2.Theta.mt V g).det)) :
    detIdl (idemAt w) V g = GlobalTheory.LFun.locIdele D.host.F w z := by
  have he : Formalism.L2.NTheta.IsIdemAt (idemAt w) w := Classical.epsilon_spec hs
  have hee : idemAt w * idemAt w = idemAt w := he.1.1
  have hP : Formalism.IndefR.Mult.IsPrimeIdem w (idemAt w) (idemAt w + cA D (idemAt w)) := Or.inl ⟨he, rfl⟩
  have hx := detIdl_val hee V g
  obtain ⟨y, hy, hxy⟩ := GlobalTheory.WeilAtPlace.exists_eq_locIdele (GlobalTheory.WeilAtPlace.isPrimeIdem_infPart hP)
    (GlobalTheory.LFun.finPart_of_isPrimeIdem hP) (detIdl (idemAt w) V g) (by
      rw [hx]
      linear_combination ((Formalism.L2.Theta.mt V g).det - 1) * hee)
  have hyz : y = z := by
    apply Units.ext
    rw [hy, hx, GlobalTheory.WeilAtPlace.compAt_cut (GlobalTheory.LFun.finPart_of_isPrimeIdem hP), compAt_eq_cpt]
    exact hz.symm
  rw [hxy, hyz]

theorem detIdl_conj_eq_locIdele (V : HSp D) {n' : ℕ} (h : n' = V.rank) (β : GL (Fin V.rank) (Lev.EAf D)) (k u : GfC V)
    (w : Pl D.host.E) (hs : ∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e w) :
    detIdl (idemAt w) V ((u⁻¹ * k * u : GfC V) : GA D V) =
      GlobalTheory.LFun.locIdele D.host.F w (gdet (inBasis h β w (finG V k))) :=
  detIdl_eq_locIdele V _ w hs _ (by rw [gdet_inBasis_val, GlobalTheory.TopLevelInv.det_mt_conj])
end GlobalTheory.RowDetLocal

theorem GlobalTheory.RowDetLocal.detIdl_moved_eq_locIdele : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (t : T) (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)) (w : Pl D.host.E),
    (∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e w) →
    detIdl (idemAt w) (G.V (.grid (j + 1) D.R.m)) (moved S j k) =
      GlobalTheory.LFun.locIdele D.host.F w (gdet (inBasis (rank_vertex G t w (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩)
        (S.B.β (j + 1) D.R.m) w (finG (G.V (.grid (j + 1) D.R.m)) k))) := by
  intro D T L sc G W U S t j hj k w hs
  exact GlobalTheory.RowDetLocal.detIdl_conj_eq_locIdele _ _ _ k (S.N.u (.grid (j + 1) D.R.m)) w hs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DeterminantIdeleAtSplitPlaceMovedGridNodeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinantIdeleAtSplitPlace_moved_gridNode : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (t : T) (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)) (w : Pl D.host.E),
    (∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e w) →
    detIdl (idemAt w) (G.V (.grid (j + 1) D.R.m)) (moved S j k) =
      GlobalTheory.LFun.locIdele D.host.F w (gdet (inBasis (rank_vertex G t w (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩)
        (S.B.β (j + 1) D.R.m) w (finG (G.V (.grid (j + 1) D.R.m)) k))) := by
  first | exact @GlobalTheory.RowDetLocal.detIdl_moved_eq_locIdele | exact GlobalTheory.RowDetLocal.detIdl_moved_eq_locIdele | (intros; apply GlobalTheory.RowDetLocal.detIdl_moved_eq_locIdele <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryInductionOnSplitPlaceSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryInductionOnSplitPlaceSupport
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SplitInduct

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem

theorem induct_suppSplit : ∀ {D : D7} (V : HSp D) (N : ℕ) (Q : GA D V → Prop), Q 1 → (∀ x y, Q x → Q y → Q (x * y)) →
    (∀ (e : AE D) (P : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P → ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal →
      ∀ x ∈ GfC V, Formalism.L2.Theta.SuppAt e V x → Q x) →
    ∀ g ∈ GfC V, GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N ((finHom V) g : Matrix (Fin V.rank) (Fin V.rank) _) → Q g := by
  classical
  intro D V N Q h1 hmul hloc g hg hs
  obtain ⟨e₀, he1, he2, he3, he4⟩ := hs
  have heS : e₀ = GlobalTheory.LocalApprox.indA D.host.F he2.toFinset := by
    refine GlobalTheory.LocalApprox.af_ext _ fun w => ?_
    by_cases hw : w ∈ he2.toFinset
    · rw [GlobalTheory.LocalApprox.evalV_indA_of_mem _ hw]
      have hne : evalV D.host.F w e₀ ≠ 0 := he2.mem_toFinset.1 hw
      have h := congrArg (evalV D.host.F w) he1
      rw [map_mul] at h
      exact mul_left_cancel₀ hne (h.trans (mul_one _).symm)
    · rw [GlobalTheory.LocalApprox.evalV_indA_of_notMem _ hw]
      by_contra h
      exact hw (he2.mem_toFinset.2 h)
  have hsupp : ∀ i j, GlobalTheory.LocalApprox.idemE D he2.toFinset * (Formalism.L2.Theta.mt V g - 1) i j =
      (Formalism.L2.Theta.mt V g - 1) i j := by
    intro i j
    have e0 : GlobalTheory.LocalApprox.idemE D he2.toFinset = fj D e₀ := (congrArg (fj D) heS).symm
    rw [e0]
    refine GlobalTheory.UnitarySplit.parts_inj D _ _ ?_ ?_
    · have h5 : infPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
        have h6 : (Formalism.L2.Theta.mt V g).map (infPart D) = 1 := congrArg Units.val (show infHom V g = 1 from hg)
        have h7 := congrFun (congrFun h6 i) j
        rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero]
        refine h7.trans ?_
        by_cases e : i = j
        · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
        · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]
      rw [RingHom.map_mul, h5, mul_zero]
    · have h5 : finPart D ((Formalism.L2.Theta.mt V g - 1) i j) = ((finHom V g).1 - 1) i j := by
        rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub]
        congr 1
        by_cases e : i = j
        · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
        · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]
      rw [RingHom.map_mul, h5]
      exact congrFun (congrFun he4 i) j
  have hgS : GlobalTheory.LocalApprox.cutAt V g he2.toFinset = g := by
    refine GlobalTheory.IdemSupport.mt_inj V ?_
    rw [GlobalTheory.LocalApprox.mt_cutAt]
    ext i j
    have h := hsupp i j
    rw [Matrix.sub_apply] at h
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
    linear_combination h
  have hpl : ∀ v, pl D v = GlobalTheory.LocalApprox.idemE D {v} := fun v => by
    show fj D _ = fj D _
    congr 1
    refine GlobalTheory.LocalApprox.af_ext _ fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [evalV_singleV_same, GlobalTheory.LocalApprox.evalV_indA_of_mem _ (Finset.mem_singleton_self _)]
    · rw [evalV_singleV_ne _ v _ hw, GlobalTheory.LocalApprox.evalV_indA_of_notMem _ (Finset.notMem_singleton.2 hw)]
  have hv : ∀ v ∈ he2.toFinset, Q (GlobalTheory.LocalApprox.cutAt V g {v}) := by
    intro v hvS
    have hv' := he3 v (he2.mem_toFinset.1 hvS)
    obtain ⟨e, he⟩ := _root_.GlobalTheory.MovedSplit.exists_splitAt D v hv'.1
    obtain ⟨PP, hP, hco⟩ := _root_.GlobalTheory.IdemPrime.exists_isIdemAt D v e he
    refine hloc e PP hP ?_ _ (GlobalTheory.LocalApprox.cutAt_mem_GfC V g {v}) ?_
    · intro hm
      refine hv'.2 ?_
      rw [← hco, Ideal.mem_comap, map_natCast]
      exact hm
    · intro i j
      rw [he.2.2, hpl v]
      exact GlobalTheory.LocalApprox.cutAt_supp V g {v} i j
  have key : ∀ s : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)), s ⊆ he2.toFinset →
      Q (GlobalTheory.LocalApprox.cutAt V g s) := by
    intro s
    induction s using Finset.cons_induction with
    | empty => intro _; rw [GlobalTheory.LocalApprox.cutAt_empty]; exact h1
    | cons v s h ih =>
      intro hsub
      rw [GlobalTheory.LocalApprox.cutAt_cons]
      exact hmul _ _ (hv v (hsub (Finset.mem_cons_self _ _))) (ih ((Finset.subset_cons h).trans hsub))
  rw [← hgS]
  exact key _ subset_rfl

end GlobalTheory.SplitInduct

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryInductionOnSplitPlaceSupportStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_induction_on_splitPlaceSupport : ∀ {D : D7} (V : HSp D) (N : ℕ) (Q : GA D V → Prop), Q 1 → (∀ x y, Q x → Q y → Q (x * y)) →
    (∀ (e : AE D) (P : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P → ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal →
      ∀ x ∈ GfC V, Formalism.L2.Theta.SuppAt e V x → Q x) →
    ∀ g ∈ GfC V, GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N ((finHom V) g : Matrix (Fin V.rank) (Fin V.rank) _) → Q g := by
  first | exact @GlobalTheory.SplitInduct.induct_suppSplit | exact GlobalTheory.SplitInduct.induct_suppSplit | (intros; apply GlobalTheory.SplitInduct.induct_suppSplit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualHomLatticeModulusShiftLocalEqLatO
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualHomLatticeModulusShiftLocalEqLatO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.BigLoc

variable {D : D7}

theorem latO_tgt_le {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT LT' : Set (Fin T.rank → D.host.E)}
    (v : GlobalTheory.FinPl.Pl D) (c : 𝓞 D.host.F) (hc : c ∉ v.asIdeal)
    (h : ∀ t ∈ LT, (((c : D.host.F) : D.host.E)) • t ∈ LT') :
    latO S T LS LT (· = v) ≤ latO S T LS LT' (· = v) := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro w ⟨α, hα, hsupp, a, ha, s, hs, t, ht, rfl⟩
  refine AddSubgroup.subset_closure ⟨GlobalTheory.IdeleAA.gam v c * α, GlobalTheory.IdeleAA.gam_mul_int v c hc hα,
    GlobalTheory.IdeleAA.gam_mul_supp v c α, a, ha, s, hs, _, h t ht, ?_⟩
  ext i j
  simp only [Matrix.of_apply]
  rw [← GlobalTheory.IdeleAA.pair_scale v c α hsupp]
  congr 1
  have h0 := GlobalTheory.IdeleAA.coe_ne_zero v c hc
  rw [Pi.smul_apply, smul_eq_mul]
  field_simp

end GlobalTheory.BigLoc

namespace GlobalTheory.BigLoc

variable {D : D7}

theorem coe_alg (c : 𝓞 D.host.F) :
    algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c) = ((c : D.host.F) : D.host.E) := rfl

theorem exists_c {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∉ P.S0) :
    ∃ c : 𝓞 D.host.F, c ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ P.modul sc ∧
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ P.modulBar sc := by
  classical
  set J : Ideal (𝓞 D.host.F) := ∏ v' ∈ P.S0, v'.asIdeal ^ P.depth sc v' with hJdef
  have hJ : ¬ J ≤ v.asIdeal := by
    intro h
    obtain ⟨v', hv', hle⟩ := (Ideal.IsPrime.prod_le v.isPrime).1 h
    have h1 : v'.asIdeal ≤ v.asIdeal := Ideal.IsPrime.le_of_pow_le (hP := v.isPrime) hle
    have : v' = v := HeightOneSpectrum.ext (v'.isMaximal.eq_of_le v.isPrime.ne_top h1)
    exact hv (this ▸ hv')
  obtain ⟨c, hcJ, hcv⟩ := Set.not_subset.1 hJ
  have hmap : J.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ P.modul sc := by
    rw [hJdef]
    change Ideal.mapHom (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) _ ≤ _
    rw [map_prod]
    refine Finset.prod_le_prod' fun v' hv' => ?_
    rw [map_pow]
    refine pow_le_pow_left' ?_ _
    refine Ideal.map_le_iff_le_comap.2 (le_of_eq ?_)
    have := congrArg HeightOneSpectrum.asIdeal (P.under_w hv')
    exact this.symm
  have hmod : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ P.modul sc := hmap (Ideal.mem_map_of_mem _ hcJ)
  refine ⟨c, hcv, hmod, ?_⟩
  have hfix : D.host.conj • algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c := by
    apply FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
    rw [Formalism.L2.Pj.algebraMap_conj_smul, coe_alg]
    exact GlobalTheory.IdeleAA.conj_F c
  unfold Places.modulBar
  rw [← hfix]
  exact Ideal.smul_mem_pointwise_smul _ _ _ hmod

end GlobalTheory.BigLoc

namespace GlobalTheory.BigLoc

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem smul_mem_idLat (G : GridData L sc) {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {c : 𝓞 D.host.F}
    (hc : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ G.pl.modul sc) (hne : G.pl.modulBar sc ≠ ⊥)
    {y : Fin n → D.host.E} (hy : y ∈ Λ) : ((c : D.host.F) : D.host.E) • y ∈ idLat (shiftId G) Λ := by
  refine Submodule.subset_span ⟨_, ?_, y, hy, rfl⟩
  unfold shiftId
  rw [← mul_one ((c : D.host.F) : D.host.E)]
  exact FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal (𝓞 D.host.E)⁰).2 ⟨_, hc, coe_alg c⟩)
    (FractionalIdeal.one_mem_inv_coe_ideal hne)

theorem smul_idLat_mem (G : GridData L sc) {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {c : 𝓞 D.host.F}
    (hcb : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ G.pl.modulBar sc) (hne : G.pl.modulBar sc ≠ ⊥)
    {z : Fin n → D.host.E} (hz : z ∈ idLat (shiftId G) Λ) : ((c : D.host.F) : D.host.E) • z ∈ Λ := by
  refine Submodule.span_induction (p := fun z _ => ((c : D.host.F) : D.host.E) • z ∈ Λ) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨s, hs, y, hy, rfl⟩
    have hm : ((c : D.host.F) : D.host.E) * s ∈ ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
      have := FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal (𝓞 D.host.E)⁰).2 ⟨_, hcb, coe_alg c⟩) hs
      have h0 : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
        rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
      rwa [shiftId, mul_left_comm, mul_inv_cancel₀ h0, mul_one] at this
    obtain ⟨o, -, ho⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 D.host.E)⁰).1 hm
    rw [smul_smul, ← ho, algebraMap_smul]
    exact Λ.smul_mem o hy
  · simp
  · intro x y _ _ hx hy; rw [smul_add]; exact add_mem hx hy
  · intro a x _ hx; rw [smul_comm]; exact Λ.smul_mem a hx

end GlobalTheory.BigLoc

theorem GlobalTheory.BigLoc.latBig_at : All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∀ v ∉ G.pl.S0,
    ∀ u : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)), MxAt (· = v) u →
      (u ∈ latBig G i ↔ u ∈ latO _ _ (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (· = v)) := by
  intro D _ T L μ0 _ sc G W M _ i _ v hv u hu
  obtain ⟨c, hcv, hc, hcb⟩ := GlobalTheory.BigLoc.exists_c G.pl sc hv
  have hne : G.pl.modulBar sc ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hcb
    apply GlobalTheory.IdeleAA.coe_ne_zero v c hcv
    rw [← GlobalTheory.BigLoc.coe_alg, hcb, map_zero]
  unfold latBig
  rw [GlobalTheory.AscFinWit.mem_latO_at hu]
  exact ⟨fun h => GlobalTheory.BigLoc.latO_tgt_le v c hcv (fun t ht => GlobalTheory.BigLoc.smul_idLat_mem G hcb hne ht) h,
    fun h => GlobalTheory.BigLoc.latO_tgt_le v c hcv (fun t ht => GlobalTheory.BigLoc.smul_mem_idLat G hc hne ht) h⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualHomLatticeModulusShiftLocalEqLatOStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualHomLatticeModulusShift_local_eq_latO : All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∀ v ∉ G.pl.S0, ∀ u : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)), MxAt (· = v) u → (u ∈ latBig G i ↔ u ∈ latO _ _ (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (· = v)) := by
  first | exact @GlobalTheory.BigLoc.latBig_at | exact GlobalTheory.BigLoc.latBig_at | (intros; apply GlobalTheory.BigLoc.latBig_at <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridFirstColumnStepIsSchwartzBruhatHalf
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridFirstColumnStepIsSchwartzBruhatHalf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FlipTop

open GlobalTheory.FunObj.Comparison₂

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}


open Classical in
theorem stepFn_congr_red (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T) {j : ℕ} (hj : j < D.R.m) {w : Pl D.host.E}
    (hw : w ∈ topPl L t) {a b : ℕ} (ha : a = D.R.r + j * D.R.t) (hb : b = D.R.r + (j + 1) * D.R.t)
    (N N' : Matrix (Fin b) (Fin a) (OA D)) (h : N.map (resS D.host.F w) = N'.map (resS D.host.F w)) :
    stepFn L t w j ((N.map (cptO w)).submatrix (ixOf G t w hb) (ixOf G t w ha)) =
      stepFn L t w j ((N'.map (cptO w)).submatrix (ixOf G t w hb) (ixOf G t w ha)) := by
  by_cases hP : w ∈ L.Pg
  · have hr : D.R.r ≤ a := ha ▸ Nat.le_add_right _ _
    rw [stepFn_of_mem_Pg t w hP]
    by_cases H : LowZero a (N.map (resS D.host.F w)) ∧ ∃ g, TopCond D.R.t hr (N.map (resS D.host.F w)) g
    · obtain ⟨h0, g, hg⟩ := H
      have h0' : LowZero a (N'.map (resS D.host.F w)) := by rw [← h]; exact h0
      have hg' : TopCond D.R.t hr (N'.map (resS D.host.F w)) g := by rw [← h]; exact hg
      have e1 := iterPhi_eq (isTame_muBase (L := L) w) (isRed w) (isIx_ixOf G t w ha) (isIx_ixOf G t w hb) hr (χ := fun c => L.chi c w)
          (fun c hc => compat_chi w hL hP (hc.trans_lt hj)) N h0 hg
      have e2 := iterPhi_eq (isTame_muBase (L := L) w) (isRed w) (isIx_ixOf G t w ha) (isIx_ixOf G t w hb) hr (χ := fun c => L.chi c w)
          (fun c hc => compat_chi w hL hP (hc.trans_lt hj)) N' h0' hg'
      exact e1.trans e2.symm
    · have H' : ¬ (LowZero a (N'.map (resS D.host.F w)) ∧ ∃ g, TopCond D.R.t hr (N'.map (resS D.host.F w)) g) := by rw [← h]; exact H
      have e1 := not_ne_iff.1 (mt (iterPhi_ne_zero_iff (isTame_muBase (L := L) w) (isRed w) (isIx_ixOf G t w ha) (isIx_ixOf G t w hb) hr N).1 H)
      have e2 := not_ne_iff.1 (mt (iterPhi_ne_zero_iff (isTame_muBase (L := L) w) (isRed w) (isIx_ixOf G t w ha) (isIx_ixOf G t w hb) hr N').1 H')
      exact e1.trans e2.symm
  · have hQ : w ∈ L.Q t := by
      unfold topPl at hw
      exact (Finset.mem_union.1 hw).resolve_left hP
    have e1 := stepFn_eq_of_mem_Q G t w hL hQ ha hb N
    have e2 := stepFn_eq_of_mem_Q G t w hL hQ ha hb N'
    refine e1.trans (Eq.trans ?_ e2.symm)
    exact congrArg (fun y => if H : LowZero D.R.r y ∧ IsUnit (topL D.R.r y).det then (L.xiR t w H.2.unit : ℂ) else 0) h


set_option maxHeartbeats 1000000 in
theorem isSBHalf_topFn : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (B : Frames G) {μ₀ : T},
    L.Is μ₀ → ∀ (t : T) {e : AE D}, IsIdemSum e (GlobalTheory.FlipTop.topPl L t) → ∀ (j : ℕ) (hj : j < D.R.m),
    IsSBHalf e (latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _) (G.latT (.mu t 0 j) : Set _)
      fun _ => True) (GlobalTheory.FlipTop.topFn B t e j (GlobalTheory.FlipTop.rank_col G hj.le) (GlobalTheory.FlipTop.rank_col G hj)) := by
  intro D T L sc G B μ₀ hL t e he j hj
  classical
  have hFS : IsFrame (B.β 0 j) (G.Λ (.grid 0 j)) := B.isFrame_β hL (Nat.zero_le _) hj.le
  have hFT : IsFrame (B.β 0 (j + 1)) (G.Λ (.grid 0 (j + 1))) := B.isFrame_β hL (Nat.zero_le _) hj
  obtain ⟨a, ha, h1⟩ := WeilOver.exists_hom_le (S := G.V (.grid 0 j)) (T := G.V (.grid 0 (j + 1)))
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ (node_isV G hL (X := .grid 0 j) ⟨Nat.zero_le _, hj.le⟩).sd)
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ (node_isV G hL (X := .grid 0 (j + 1)) ⟨Nat.zero_le _, hj⟩).sd)
  obtain ⟨b, hb, h2⟩ := WeilOver.exists_le_hom (S := G.V (.grid 0 j)) (T := G.V (.grid 0 (j + 1)))
    (GlobalTheory.DiagLiftFix.isLattice_of_isFrame hFS) (GlobalTheory.DiagLiftFix.isLattice_of_isFrame hFT)
  obtain ⟨e0, -, -⟩ := cpt_idemSum he

  set 𝔪 : Ideal (𝓞 D.host.E) := ∏ w ∈ topPl L t, w.asIdeal ^ 1 with h𝔪
  have hN : 0 < Ideal.absNorm 𝔪 :=
    Nat.pos_of_ne_zero fun h => CosSB.prod_pow_ne_bot (topPl L t) 1 (Ideal.absNorm_eq_zero_iff.1 h)
  have hle : ∀ w ∈ topPl L t, 𝔪 ≤ w.asIdeal ^ 1 := fun w hw =>
    Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun w : Pl D.host.E => w.asIdeal ^ 1) hw)
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = a * (b * Ideal.absNorm 𝔪) := ⟨_, rfl⟩
  refine ⟨fun x hx => ?_, K, by rw [hK]; positivity, fun u hu hh x => ?_, fun x hx => ?_⟩
  · by_contra h
    exact hx (by unfold GlobalTheory.FlipTop.topFn; rw [if_neg fun H => h H.1])
  · have hk : K • u ∈ hatMx (𝔪 • homLat (G.Λ (.grid 0 j)) (G.Λ (.grid 0 (j + 1)))) := by
      have := nsmul_mem (CosSB.nsmul_mem_hatMx h2 𝔪 hu) a
      rwa [smul_smul, ← hK] at this
    have hk2 := ((mem_hatMx_iff hFS hFT 𝔪 _).1 hk).2
    have hXYZ : fr (B.β 0 (j + 1)) (B.β 0 j) ((x + K • u).map (toEAf D)) =
        fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D)) + fr (B.β 0 (j + 1)) (B.β 0 j) ((K • u).map (toEAf D)) := by
      have hm : (x + K • u).map (toEAf D) = x.map (toEAf D) + (K • u).map (toEAf D) := by
        ext i l
        exact (toEAf D).map_add _ _
      rw [hm, fr_add]
    have hZ : ∀ i l, fr (B.β 0 (j + 1)) (B.β 0 j) ((K • u).map (toEAf D)) i l ∈ OA D := fun i l => by
      obtain ⟨s, -, hs⟩ := hk2 i l
      rw [← hs]
      exact s.2
    have hint : IsIntM (fr (B.β 0 (j + 1)) (B.β 0 j) ((x + K • u).map (toEAf D))) ↔
        IsIntM (fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))) := by
      refine forall₂_congr fun i l => ?_
      rw [hXYZ, Matrix.add_apply]
      exact ⟨fun h => by simpa using sub_mem h (hZ i l), fun h => add_mem h (hZ i l)⟩
    unfold GlobalTheory.FlipTop.topFn
    split_ifs with H1 H2 H2
    · refine Finset.prod_congr rfl fun w hw => ?_
      let NX : Matrix (Fin (G.V (.grid 0 (j + 1))).rank) (Fin (G.V (.grid 0 j)).rank) (OA D) :=
        fun i l => ⟨_, H1.2 i l⟩
      let NY : Matrix (Fin (G.V (.grid 0 (j + 1))).rank) (Fin (G.V (.grid 0 j)).rank) (OA D) :=
        fun i l => ⟨_, H2.2 i l⟩
      have eX : (fr (B.β 0 (j + 1)) (B.β 0 j) ((x + K • u).map (toEAf D))).map (cpt (D := D) w) = NX.map (cptO w) :=
        Matrix.ext fun i l => (cptO_apply w (NX i l)).symm
      have eY : (fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))).map (cpt (D := D) w) = NY.map (cptO w) :=
        Matrix.ext fun i l => (cptO_apply w (NY i l)).symm
      rw [eX, eY]
      refine stepFn_congr_red G hL t hj hw _ _ NX NY (Matrix.ext fun i l => ?_)
      rw [Matrix.map_apply, Matrix.map_apply, ← sub_eq_zero, ← map_sub, (isRed w).ker, cptO_apply]
      obtain ⟨s, hs, hs'⟩ := hk2 i l
      have e3 : ((NX i l - NY i l : OA D) : EAf D) = s.1 := by
        rw [hs', AddSubgroupClass.coe_sub]
        change fr (B.β 0 (j + 1)) (B.β 0 j) ((x + K • u).map (toEAf D)) i l -
          fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D)) i l = _
        rw [hXYZ, Matrix.add_apply, add_sub_cancel_left]
      rw [e3]
      exact (vEq w).lt_one_iff_lt_one.2 ((v_lt_one_iff _).2 (v_le_of_mem_idS (hle w hw) hs))
    · exact absurd ⟨(CosSB.isHalf_add_nsmul K hh).1 H1.1, hint.1 H1.2⟩ H2
    · exact absurd ⟨(CosSB.isHalf_add_nsmul K hh).2 H2.1, hint.2 H2.2⟩ H1
    · rfl
  · obtain ⟨hth, hti⟩ : IsHalf e x ∧ IsIntM (fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))) := by
      by_contra h
      exact hx (by unfold GlobalTheory.FlipTop.topFn; rw [if_neg h])
    have hmem : x ∈ hatMx ((⊤ : Ideal (𝓞 D.host.E)) • homLat (G.Λ (.grid 0 j)) (G.Λ (.grid 0 (j + 1)))) := by
      refine (mem_hatMx_iff hFS hFT ⊤ _).2 ⟨fun i l => ?_, fun i l => ⟨⟨_, hti i l⟩, ?_, rfl⟩⟩
      · rw [← hth i l, map_mul, e0, zero_mul]
      · rw [idS, Ideal.map_top]
        exact Submodule.mem_top
    have := nsmul_mem (CosSB.nsmul_mem_latO h1 ⊤ hmem) (b * Ideal.absNorm 𝔪)
    rwa [smul_smul, mul_comm (b * Ideal.absNorm 𝔪) a, ← hK] at this

end GlobalTheory.FlipTop

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridFirstColumnStepIsSchwartzBruhatHalfStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridFirstColumnStep_isSchwartzBruhat_half : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (B : Frames G) {μ₀ : T}, L.Is μ₀ →
    ∀ (t : T) {e : AE D}, IsIdemSum e (GlobalTheory.FlipTop.topPl L t) → ∀ (j : ℕ) (hj : j < D.R.m),
    IsSBHalf e (latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _) (G.latT (.mu t 0 j) : Set _) fun _ => True) (GlobalTheory.FlipTop.topFn B t e j (GlobalTheory.FlipTop.rank_col G hj.le) (GlobalTheory.FlipTop.rank_col G hj)) := by
  first | exact @GlobalTheory.FlipTop.isSBHalf_topFn | exact GlobalTheory.FlipTop.isSBHalf_topFn | (intros; apply GlobalTheory.FlipTop.isSBHalf_topFn <;> assumption)
end
end
