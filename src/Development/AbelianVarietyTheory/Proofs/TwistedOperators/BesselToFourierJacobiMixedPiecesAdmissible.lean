module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiAnnihilatorPieceCompactOpen
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualModulusShiftHalfMemCompletedModulusHom
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterTrivialBesselStepUnitriangular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiDepthLatticeSplits

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteLatticeStandardParabolic
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteLatticeStandardParabolic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.PieceA

variable {D : D7}

theorem mxAt_mul_right {m n k : ℕ} {a : Mx D m n} (ha : MxAt (fun _ => True) a) (M : Mx D n k) :
    MxAt (fun _ => True) (a ⬝ M) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (ha i l)

theorem finLat_comap_extX {V V₀ W : HSp D} {ρ : ℕ} (d : GlobalTheory.MixModel.HypDec V V₀ ρ) {Γ : AddSubgroup (WO V W)}
    (hΓ : FinLat Γ) : FinLat (Γ.comap (d.extX W)) := by
  haveI : T2Space (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.1
  have hc : Continuous (d.extX W) := by
    show Continuous fun a : Mx D W.rank ρ => a ⬝ d.pX
    exact continuous_id.matrix_mul continuous_const
  have hinv : ∀ a : Mx D W.rank ρ, d.extX W a ⬝ d.jX = a := fun a => by
    rw [GlobalTheory.MixModel.HypDec.extX_apply, Matrix.mul_assoc, GlobalTheory.MixModel.HypDec.pX_jX, Matrix.mul_one]
  refine ⟨fun a ha => ?_, ?_, ?_⟩
  · rw [← hinv a]
    exact mxAt_mul_right (hΓ.fin _ ha) _
  · have hK : IsCompact ((fun w : WO V W => w ⬝ d.jX) '' (Γ : Set (WO V W))) :=
      hΓ.cpt.image (continuous_id.matrix_mul continuous_const)
    refine hK.of_isClosed_subset (hΓ.cpt.isClosed.preimage hc) ?_
    intro a ha
    exact ⟨_, ha, hinv a⟩
  · obtain ⟨U, hU, h0, hUA⟩ := hΓ.opn
    refine ⟨d.extX W ⁻¹' U, hU.preimage hc, by simpa using h0, fun a ha haf => ?_⟩
    exact hUA _ ha (by rw [GlobalTheory.MixModel.HypDec.extX_apply]; exact mxAt_mul_right haf _)

end GlobalTheory.AscFin.PieceA

namespace GlobalTheory.AscFin

open GlobalTheory.AscFin.PieceA

theorem finLat_pcBF_A₁ : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), FinLat (pcBF W F ρ h).A₁ := by
  have H := GlobalTheory.T.grid_lattices_compact_selfDual_splitting
  unfold OnStd at H ⊢
  delta All at H ⊢
  intro D hD T L μ0 hL sc G W M hM F hF ρ h
  exact finLat_comap_extX _ ((H D hD T L μ0 hL sc G W M hM F hF).1 (2 * ρ + 1) (by omega)).1

end GlobalTheory.AscFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteLatticeStandardParabolicStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_lattice_standard_parabolic : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), FinLat (pcBF W F ρ h).A₁ := by
  first | exact @GlobalTheory.AscFin.finLat_pcBF_A₁ | exact GlobalTheory.AscFin.finLat_pcBF_A₁ | (intros; apply GlobalTheory.AscFin.finLat_pcBF_A₁ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepPiecesBMutualAnnihilators
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepPiecesBMutualAnnihilators
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.PcBFDual

variable {D : D7}

section Proj

variable {T : HSp D} {Λ : Lat T} {P : GlobalTheory.FinPl.Pl D → Prop} (M : Mx D T.rank T.rank)

theorem mulVec_latV (hM : ∀ v, P v → ∀ y ∈ latV T Λ (· = v), M *ᵥ y ∈ latV T Λ (· = v))
    (hΛ : Submodule.IsLattice D.host.E Λ) {y : Fin T.rank → AE D} (hy : y ∈ latV T Λ P) : M *ᵥ y ∈ latV T Λ P := by
  refine (GlobalTheory.FinPlLoc.part_lat P T Λ _ hΛ).2 ⟨GlobalTheory.FinPl.ExtZeroAt.mulVec_idAt _ (GlobalTheory.FinPlLoc.latV_idAt hy), fun v hv e he => ?_⟩
  rw [← Matrix.mulVec_smul]
  exact hM v hv _ (GlobalTheory.FinPlLoc.smul_latV v he hy)

theorem smul_mem_latA_idLat (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) {a s : D.host.E} (ha : a ∈ D.host.AA) (hs : s ∈ I)
    {w : Fin T.rank → AE D} (hw : w ∈ latV T Λ P) :
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] (a * s)) • w ∈ latA T (idLat I Λ) P := by
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, s • x, Submodule.subset_span ⟨s, hs, x, hx, rfl⟩, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_assoc]
  | zero => rw [smul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [smul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [smul_neg]; exact neg_mem hz


set_option maxHeartbeats 1000000 in
theorem mulVec_latA_idLat (hM : ∀ v, P v → ∀ y ∈ latV T Λ (· = v), M *ᵥ y ∈ latV T Λ (· = v))
    (hΛ : Submodule.IsLattice D.host.E Λ) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) {z : Fin T.rank → AE D}
    (hz : z ∈ latA T (idLat I Λ) P) : M *ᵥ z ∈ latA T (idLat I Λ) P := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    have key : ∀ x ∈ Submodule.span (𝓞 D.host.E) {z | ∃ s ∈ I, ∃ y ∈ Λ, z = s • y}, ∀ c : 𝓞 D.host.E,
        M *ᵥ (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * (c • x) i)) ∈ latA T (idLat I Λ) P := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨s, hs, y, hy, rfl⟩ := hx
        intro c
        have hyv : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * y i)) ∈ latV T Λ P :=
          AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, y, hy, rfl⟩
        have e : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * (c • s • y) i)) =
            ((1 : AF D.host.F) ⊗ₜ[D.host.F] (a * (c • s))) • (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * y i)) := by
          funext i
          rw [← smul_assoc]
          simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_assoc]
        rw [e, Matrix.mulVec_smul]
        exact smul_mem_latA_idLat I ha (Submodule.smul_mem _ c hs) (mulVec_latV M hM hΛ hyv)
      | zero =>
        intro c
        have e : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * (c • (0 : Fin T.rank → D.host.E)) i)) = 0 := by
          funext i; simp only [smul_zero, Pi.zero_apply, mul_zero, TensorProduct.tmul_zero]
        rw [e, Matrix.mulVec_zero]; exact zero_mem _
      | add x x' _ _ h h' =>
        intro c
        have e : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * (c • (x + x')) i)) =
            (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * (c • x) i)) +
              (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * (c • x') i)) := by
          funext i; simp only [smul_add, Pi.add_apply, mul_add, TensorProduct.tmul_add]
        rw [e, Matrix.mulVec_add]; exact add_mem (h c) (h' c)
      | smul c' x _ h =>
        intro c
        rw [smul_smul]
        exact h (c * c')
    have := key x hx 1
    simpa only [one_smul] using this
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

end Proj

section Split

theorem projY_mem {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {v : GlobalTheory.FinPl.Pl D}
    (h : MonoAt d L L₀ v) {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = v)) : (d.jY ⬝ d.pY) *ᵥ y ∈ latV S L (· = v) := by
  have e : (d.jY ⬝ d.pY) *ᵥ y = ∑ i, GlobalTheory.FinPl.colMul d.jY i ((d.pY *ᵥ y) i) := by
    rw [← Matrix.mulVec_mulVec]
    funext k
    rw [Finset.sum_apply]
    simp only [Matrix.mulVec, dotProduct, GlobalTheory.FinPl.colMul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e]
  exact sum_mem fun i _ => ((h y).1 hy).2.1 i

theorem projX_mem {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {v : GlobalTheory.FinPl.Pl D}
    (h : MonoAt d L L₀ v) {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = v)) : (d.jX ⬝ d.pX) *ᵥ y ∈ latV S L (· = v) := by
  have e : (d.jX ⬝ d.pX) *ᵥ y = ∑ i, GlobalTheory.FinPl.colMul d.jX i ((d.pX *ᵥ y) i) := by
    rw [← Matrix.mulVec_mulVec]
    funext k
    rw [Finset.sum_apply]
    simp only [Matrix.mulVec, dotProduct, GlobalTheory.FinPl.colMul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e]
  exact sum_mem fun i _ => ((h y).1 hy).1 i

theorem extend_mem_lattice_iff {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {LV : Lat V} {LV₀ : Lat V₀} {LW : Lat W}
    (hV : IsSelfDualC V LV) (hV₀ : IsSelfDualC V₀ LV₀) (hW : IsSelfDualC W LW) {P : GlobalTheory.FinPl.Pl D → Prop}
    (hm : ∀ v, P v → MonoAt d LV LV₀ v) (w : WO V₀ W) :
    d.ext0 W w ∈ latO V W (LV : Set _) (LW : Set _) P ↔ w ∈ latO V₀ W (LV₀ : Set _) (LW : Set _) P := by
  constructor
  · intro hw
    have hx := GlobalTheory.FinPl.LatMem.latO_mxAt hw
    refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D V₀ W LV₀ LW hV₀ hW P _).2 ⟨?_, fun y hy => ?_⟩
    · have := GlobalTheory.AscFinWit.mxAt_mul' hx d.j0
      rwa [HypDec.matrixExtendByZero_apply, Matrix.mul_assoc, d.p0_j0, Matrix.mul_one] at this
    · have h2 := GlobalTheory.FinPl.LatMem.latO_maps hV hw (GlobalTheory.FinPl.ExtZeroAt.wittCoreInclusion_mem_latticeCompletionAtPlace d hV.1 hm hy)
      rwa [HypDec.matrixExtendByZero_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc, d.p0_j0, Matrix.mul_one] at h2
  · intro hw
    refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D V W LV LW hV hW P _).2
      ⟨GlobalTheory.AscFinWit.mxAt_mul' (GlobalTheory.FinPl.LatMem.latO_mxAt hw) _, fun y hy => ?_⟩
    rw [HypDec.matrixExtendByZero_apply, ← Matrix.mulVec_mulVec]
    exact GlobalTheory.FinPl.LatMem.latO_maps hV₀ hw (GlobalTheory.FinPl.ExtZeroAt.wittProjectionZero_mem_latticeCompletion_of_splits d hV₀.1 hm hy)

theorem left_mem {S W : HSp D} {LS : Lat S} {Λ : Lat W} {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {P : GlobalTheory.FinPl.Pl D → Prop}
    (hS : IsSelfDualC S LS) (hW : IsSelfDualC W (idLat I Λ)) (hΛ : Submodule.IsLattice D.host.E Λ) (M : Mx D W.rank W.rank)
    (hM : ∀ v, P v → ∀ y ∈ latV W Λ (· = v), M *ᵥ y ∈ latV W Λ (· = v)) {u : WO S W}
    (hu : u ∈ latO S W (LS : Set _) (idLat I Λ : Set _) P) : M ⬝ u ∈ latO S W (LS : Set _) (idLat I Λ : Set _) P := by
  refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D S W LS _ hS hW P _).2
    ⟨GlobalTheory.AscFinWit.mxAt_mul _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu), fun y hy => ?_⟩
  show (M * u) *ᵥ y ∈ _
  rw [← Matrix.mulVec_mulVec]
  exact mulVec_latA_idLat M hM hΛ I (GlobalTheory.FinPl.LatMem.latO_maps hS hu hy)

end Split

end GlobalTheory.PcBFDual

namespace GlobalTheory.PcBFDual

theorem dualB : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m),
    (∀ ξ, MxAt (fun _ => True) ξ → (ξ ∈ (pcBF W F ρ h).B₁ ↔ ∀ η ∈ (pcBF W F ρ h).B₂,
      W.ψ (symplO (F.V₀ ρ) _ ((F.dJ ρ h).incX _ ξ) ((F.dJ ρ h).incY _ η)) = 1)) ∧
    ∀ η, MxAt (fun _ => True) η → (η ∈ (pcBF W F ρ h).B₂ ↔ ∀ ξ ∈ (pcBF W F ρ h).B₁,
      W.ψ (symplO (F.V₀ ρ) _ ((F.dJ ρ h).incX _ ξ) ((F.dJ ρ h).incY _ η)) = 1) := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h
  have I := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hq T L μ0 hL sc G W M hM F hF
  have sd : ∀ X : Node, X.InRange D.R.m → (∀ j, X ≠ .grid 0 j) → IsSelfDualC (G.V X) (G.Λ X) :=
    fun X h1 h2 => (G.isV h1 h2).sd
  have hV : IsSelfDualC (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) :=
    sd _ ⟨h, Nat.zero_le _⟩ (fun j e => by cases e)
  have hΛ : IsSelfDualC (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) :=
    sd _ ⟨by omega, Nat.zero_le _⟩ (fun j e => by cases e)
  have hV₀ : IsSelfDualC (F.V₀ ρ) (lat0 F ρ h) := (I.2.1 ρ h).1
  have hW : IsSelfDualC (G.V (.grid (2 * ρ + 1) 0)) (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0))) :=
    (I.1 (2 * ρ + 1) (by omega)).2.2.2
  have hmV : ∀ v, MonoAt (F.dB ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (lat0 F ρ h) v := fun v => ((I.2.1 ρ h).2.1 v).1
  have hmW : ∀ v, MonoAt (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v :=
    fun v => ((I.2.1 ρ h).2.1 v).2
  have hψ : IsStdChar D W.ψ (-1) := W.ψ_std
  have hB : ∀ w, (F.dB ρ h).ext0 _ w ∈ latBig G (2 * ρ + 1) ↔
      w ∈ latO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)) (lat0 F ρ h : Set _)
        (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0)) : Set _) fun _ => True :=
    fun w => extend_mem_lattice_iff (F.dB ρ h) hV hV₀ hW (fun v _ => hmV v) w
  have tY : ∀ u ∈ latO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)) (lat0 F ρ h : Set _)
      (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0)) : Set _) (fun _ => True),
      (F.dJ ρ h).incY _ ((F.dJ ρ h).pY ⬝ u) ∈ latO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)) (lat0 F ρ h : Set _)
        (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0)) : Set _) (fun _ => True) := fun u hu => by
    rw [HypDec.incY_apply, ← Matrix.mul_assoc]
    exact left_mem hV₀ hW hΛ.1 _ (fun v _ y hy => projY_mem _ (hmW v) hy) hu
  have tX : ∀ u ∈ latO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)) (lat0 F ρ h : Set _)
      (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0)) : Set _) (fun _ => True),
      (F.dJ ρ h).incX _ ((F.dJ ρ h).pX ⬝ u) ∈ latO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)) (lat0 F ρ h : Set _)
        (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0)) : Set _) (fun _ => True) := fun u hu => by
    rw [HypDec.incX_apply, ← Matrix.mul_assoc]
    exact left_mem hV₀ hW hΛ.1 _ (fun v _ y hy => projX_mem _ (hmW v) hy) hu
  refine ⟨fun ξ hξ => ?_, fun η hη => ?_⟩
  · refine (hB ((F.dJ ρ h).incX _ ξ)).trans ?_
    refine (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ hψ _ _ _ _ hV₀ hW _ _ (GlobalTheory.AscFinWit.mxAt_mul (F.dJ ρ h).jX hξ)).trans ?_
    refine ⟨fun H η hη => H _ ((hB ((F.dJ ρ h).incY _ η)).1 hη), fun H u hu => ?_⟩
    exact (congrArg W.ψ (GlobalTheory.AscFinWit.symplO_incX (F.dJ ρ h) _ ξ u)).trans (H _ ((hB ((F.dJ ρ h).incY _ _)).2 (tY u hu)))
  · refine (hB ((F.dJ ρ h).incY _ η)).trans ?_
    refine (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ hψ _ _ _ _ hV₀ hW _ _ (GlobalTheory.AscFinWit.mxAt_mul (F.dJ ρ h).jY hη)).trans ?_
    refine ⟨fun H ξ hξ => (GlobalTheory.AscFinWit.psi_swap _ _).1 (H _ ((hB ((F.dJ ρ h).incX _ ξ)).1 hξ)), fun H u hu => ?_⟩
    exact (congrArg W.ψ (GlobalTheory.AscFinWit.symplO_incY (F.dJ ρ h) _ η u)).trans
      ((GlobalTheory.AscFinWit.psi_swap _ _).1 (H _ ((hB ((F.dJ ρ h).incX _ _)).2 (tX u hu))))

end GlobalTheory.PcBFDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepPiecesBMutualAnnihilatorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_step_pieces_B_mutual_annihilators : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), (∀ ξ, MxAt (fun _ => True) ξ → (ξ ∈ (pcBF W F ρ h).B₁ ↔ ∀ η ∈ (pcBF W F ρ h).B₂, W.ψ (symplO (F.V₀ ρ) _ ((F.dJ ρ h).incX _ ξ) ((F.dJ ρ h).incY _ η)) = 1)) ∧ ∀ η, MxAt (fun _ => True) η → (η ∈ (pcBF W F ρ h).B₂ ↔ ∀ ξ ∈ (pcBF W F ρ h).B₁, W.ψ (symplO (F.V₀ ρ) _ ((F.dJ ρ h).incX _ ξ) ((F.dJ ρ h).incY _ η)) = 1) := by
  first | exact @GlobalTheory.PcBFDual.dualB | exact GlobalTheory.PcBFDual.dualB | (intros; apply GlobalTheory.PcBFDual.dualB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BidualityDepthLatticePieceBesselStep
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowSmulMemSelfDualModulusShift
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowSmulMemSelfDualModulusShift
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
namespace GlobalTheory.DepHalf

open scoped Pointwise

theorem smul_mem_latBig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → OffQ D →
    ∀ (G : GridData L sc) (i : ℕ), i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ u ∈ latRow G i, e • u ∈ latBig G i := by
  intro D T L sc μ₀ hL hQ G i hi e he u hu
  have h1 : e • u ∈ hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) := hu.2 e he
  have hmB : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    refine FractionalIdeal.coeIdeal_ne_zero.2 ?_
    unfold Places.modulBar
    intro h
    apply G.pl.modul_ne_bot sc
    have := congrArg (fun J : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • J) h
    simpa [smul_smul] using this
  have hone : (1 : D.host.E) ∈ ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹ := by
    have hle : (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤
        ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹ := by
      have := FractionalIdeal.inv_anti_mono hmB FractionalIdeal.coeIdeal_le_one
      rwa [inv_one] at this
    exact hle (FractionalIdeal.one_mem_one _)
  have hsub : G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0)) ≤
      homLat (G.Λ (.grid (i + 1) 0)) (idLat (shiftId G) (G.Λ (.grid i 0))) := by
    refine Submodule.smul_le.2 fun r hr x hx y hy => ?_
    rw [smul_mulVec]
    refine Submodule.subset_span ⟨algebraMap (𝓞 D.host.E) D.host.E r, ?_, x *ᵥ y, hx y hy, ?_⟩
    · unfold shiftId
      rw [show algebraMap (𝓞 D.host.E) D.host.E r = algebraMap (𝓞 D.host.E) D.host.E r * 1 by rw [mul_one]]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hr) hone
    · exact (algebraMap_smul D.host.E r (x *ᵥ y)).symm
  have h2 : e • u ∈ hatMx (homLat (G.Λ (.grid (i + 1) 0)) (idLat (shiftId G) (G.Λ (.grid i 0)))) := by
    refine AddSubgroup.closure_mono ?_ h1
    rintro w ⟨α, hα, x, hx, rfl⟩
    exact ⟨α, hα, x, hsub hx, rfl⟩
  have hhalf : IsHalf e (e • u) := fun a b => by
    rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, GlobalTheory.PlaceDatum.idemSum_mul_self he]
  have h0 : ∀ j, (Node.grid (i + 1) 0 : Node) ≠ .grid 0 j := fun j h => by
    injection h with h'
    omega
  have hsd : IsSelfDualC (G.V (.grid (i + 1) 0)) (G.Λ (.grid (i + 1) 0)) := (G.isV (show (Node.grid (i + 1) 0 : Node).InRange D.R.m from ⟨hi, Nat.zero_le _⟩) h0).sd
  exact GlobalTheory.RowLatChi.mem_latO_of_mem_hatMx hsd he (GlobalTheory.AAUnit.exists_valuation_one_element_at_grid_places hQ hL G) hhalf h2

end GlobalTheory.DepHalf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowSmulMemSelfDualModulusShiftStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthLatticeGridRow_smul_mem_selfDualModulusShift : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → OffQ D → ∀ (G : GridData L sc) (i : ℕ), i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ u ∈ latRow G i, e • u ∈ latBig G i := by
  first | exact @GlobalTheory.DepHalf.smul_mem_latBig | exact GlobalTheory.DepHalf.smul_mem_latBig | (intros; apply GlobalTheory.DepHalf.smul_mem_latBig <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BidualityDepthLatticePieceBesselStep
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.BidualLattice

variable {D : D7}


set_option maxHeartbeats 1000000 in
theorem latO_negSp (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO (negSp S) T LS LT P = latO S T LS LT P := by
  unfold latO
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    rw [← neg_neg (Matrix.of _)]
    refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
    funext i j
    simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]
  · rw [AddSubgroup.closure_le]
    rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    rw [← neg_neg (Matrix.of _)]
    refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
    funext i j
    simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem extY_jY_mem {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {LS : Lat S} {L₀ : Lat S₀} {LT : Lat T}
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (hm : ∀ v, MonoAt d LS L₀ v) {u : WO S T}
    (hu : u ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True) :
    d.extY T (u * d.jY) ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True := by
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ hS hT] at hu ⊢
  refine ⟨GlobalTheory.AscFinWit.mxAt_mul' (GlobalTheory.AscFinWit.mxAt_mul' hu.1 _) _, fun y hy => ?_⟩
  have e : (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from d.extY T (u * d.jY)) *ᵥ y =
      (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from u) *ᵥ (d.jY *ᵥ (d.pY *ᵥ y)) := by
    simp only [HypDec.extY_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e]
  refine hu.2 _ ?_
  rw [GlobalTheory.FinPlLoc.part_lat _ _ _ _ hS.1] at hy ⊢
  refine ⟨fun i => ?_, fun v _ c hc => ?_⟩
  · simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _
      (Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hy.1 l))
  · have hs := ((hm v) (c • y)).1 (hy.2 v trivial c hc)
    have e1 : c • (d.jY *ᵥ (d.pY *ᵥ y)) = ∑ i, GlobalTheory.FinPl.colMul d.jY i ((d.pY *ᵥ (c • y)) i) := by
      funext k
      simp only [GlobalTheory.FinPl.colMul, Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [e1]
    exact sum_mem fun i _ => hs.2.1 i

theorem dual_extX {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {LS : Lat S} {L₀ : Lat S₀} {LT : Lat T}
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT)
    (hm : ∀ v, MonoAt d LS L₀ v) {a : Mx D T.rank ρ} (ha : MxAt (fun _ => True) a) :
    d.extX T a ∈ latO S T (LS : Set _) (LT : Set _) (fun _ => True) ↔
      ∀ a', d.extY T a' ∈ latO S T (LS : Set _) (LT : Set _) (fun _ => True) →
        ψ (symplO S T (d.extX T a) (d.extY T a')) = 1 := by
  refine (GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ S T LS LT hS hT _ _ (GlobalTheory.AscFinWit.mxAt_mul' ha d.pX)).trans ?_
  exact ⟨fun h _ ha' => h _ ha', fun h u hu =>
    (congrArg ψ (GlobalTheory.AscFinWit.symplO_extX d T a u)).trans (h _ (extY_jY_mem d hS hT hm hu))⟩

theorem mxAt_of_extY {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {a' : Mx D T.rank ρ}
    (h : MxAt (fun _ => True) (d.extY T a')) : MxAt (fun _ => True) a' := by
  simpa only [HypDec.extY_apply, Matrix.mul_assoc, d.pY_jY, Matrix.mul_one] using GlobalTheory.AscFinWit.mxAt_mul' h d.jY

end GlobalTheory.AscFin.BidualLattice

namespace GlobalTheory.AscFin.BidualLattice

theorem bidual_main (hin : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → OffQ D → ∀ (G : GridData L sc) (i : ℕ), i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ u ∈ latRow G i, e • u ∈ latBig G i) (hout : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → OffQ D → ∀ (G : GridData L sc) (i : ℕ), i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ u ∈ latBig G i, e • u ∈ hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0)))) : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ a, MxAt (fun _ => True) a → (∀ a' ∈ (pcBF W F ρ h).A₂, W.ψ (symplO _ _ ((F.dB ρ h).extX _ a) ((F.dB ρ h).extY _ a')) = 1) → a ∈ (pcBF W F ρ h).A₁ := by
  have hI := GlobalTheory.T.grid_lattices_compact_selfDual_splitting
  unfold OnStd at hI ⊢
  delta All at hI ⊢
  intro D hD T L μ0 hL sc G W M hM F hF ρ h a ha H
  have hJ := hI D hD T L μ0 hL sc G W M hM F hF
  have hi : 2 * ρ + 1 < D.R.m := by omega
  have hψ : IsStdChar D W.ψ (-1) := W.ψ_std
  have hSV : IsSelfDualC (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) :=
    (G.isV (X := .grid (2 * ρ + 2) 0) ⟨h, Nat.zero_le _⟩ (fun j hj => by cases hj)).sd
  have hSW : IsSelfDualC (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) :=
    (GlobalTheory.CosetRow.selfDual_chi hL G (2 * ρ + 1) hi).2
  have hbig : IsSelfDualC (G.V (.grid (2 * ρ + 1) 0)) (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0))) :=
    (hJ.1 (2 * ρ + 1) hi).2.2.2
  have hmono : ∀ v, MonoAt (F.dB ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (lat0 F ρ h) v := fun v => ((hJ.2.1 ρ h).2.1 v).1
  have hrowO : ∀ u ∈ latRow G (2 * ρ + 1), u ∈ latO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))
      (G.Λ (.grid (2 * ρ + 2) 0) : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (fun _ => True) := fun u hu => by
    have h0 := hu.1
    rwa [BidualLattice.latO_negSp] at h0
  have hA2 : ∀ a', MxAt (fun _ => True) a' → (∀ b, (F.dB ρ h).extX _ b ∈ latRow G (2 * ρ + 1) →
      W.ψ (symplO _ _ ((F.dB ρ h).extX _ b) ((F.dB ρ h).extY _ a')) = 1) →
      W.ψ (symplO _ _ ((F.dB ρ h).extX _ a) ((F.dB ρ h).extY _ a')) = 1 :=
    fun a' h1 h2 => H a' (AddSubgroup.subset_closure ⟨h1, h2⟩)
  have hO : (F.dB ρ h).extX _ a ∈ latO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))
      (G.Λ (.grid (2 * ρ + 2) 0) : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (fun _ => True) := by
    refine (BidualLattice.dual_extX (F.dB ρ h) hψ hSV hSW hmono ha).2 fun a' ha' => ?_
    refine hA2 a' (BidualLattice.mxAt_of_extY _ (GlobalTheory.FinPl.LatMem.latO_mxAt ha')) fun b hb => ?_
    have hb' := hrowO _ hb
    exact (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ hψ _ _ _ _ hSV hSW _ _ (GlobalTheory.FinPl.LatMem.latO_mxAt hb')).1 hb' _ ha'
  refine ⟨?_, fun e he => ?_⟩
  · exact (BidualLattice.latO_negSp (G.V (.grid (2 * ρ + 2) 0)) _ _ _ _).ge hO
  · have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
    have hsx : ∀ x : Mx D (G.V (.grid (2 * ρ + 1) 0)).rank ρ, (F.dB ρ h).extX _ (e • x) = e • (F.dB ρ h).extX _ x :=
      fun x => by simp only [HypDec.extX_apply, Matrix.smul_mul]
    have hsy : ∀ x : Mx D (G.V (.grid (2 * ρ + 1) 0)).rank ρ, (F.dB ρ h).extY _ (cA D e • x) =
        cA D e • (F.dB ρ h).extY _ x := fun x => by simp only [HypDec.extY_apply, Matrix.smul_mul]
    have hea : MxAt (fun _ => True) (e • a) := fun i j => Ideal.mul_mem_left _ _ (ha i j)
    have hB : (F.dB ρ h).extX _ (e • a) ∈ latBig G (2 * ρ + 1) := by
      refine (BidualLattice.dual_extX (F.dB ρ h) hψ hSV hbig hmono hea).2 fun a' ha' => ?_
      rw [hsx, GlobalTheory.SplitScalar.symplO_smul, ← hsy]
      have ha'f := BidualLattice.mxAt_of_extY _ (GlobalTheory.FinPl.LatMem.latO_mxAt ha')
      refine hA2 _ (fun i j => Ideal.mul_mem_left _ _ (ha'f i j)) fun b hb => ?_
      rw [hsy, ← GlobalTheory.SplitScalar.symplO_smul]
      have hb' := hin hL hD G (2 * ρ + 1) hi e he _ hb
      exact (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ hψ _ _ _ _ hSV hbig _ _ (GlobalTheory.FinPl.LatMem.latO_mxAt hb')).1 hb' _ ha'
    have h2 := hout hL hD G (2 * ρ + 1) hi e he _ hB
    rwa [hsx, smul_smul, hee] at h2

theorem bidual_pcBF : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ a, MxAt (fun _ => True) a → (∀ a' ∈ (pcBF W F ρ h).A₂, W.ψ (symplO _ _ ((F.dB ρ h).extX _ a) ((F.dB ρ h).extY _ a')) = 1) → a ∈ (pcBF W F ρ h).A₁ :=
  bidual_main GlobalTheory.T.depthLatticeGridRow_smul_mem_selfDualModulusShift GlobalTheory.T.selfDualModulusShift_half_mem_completedModulusHom

end GlobalTheory.AscFin.BidualLattice

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BidualityDepthLatticePieceBesselStepStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.biduality_depth_lattice_piece_bessel_step : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ a, MxAt (fun _ => True) a → (∀ a' ∈ (pcBF W F ρ h).A₂, W.ψ (symplO _ _ ((F.dB ρ h).extX _ a) ((F.dB ρ h).extY _ a')) = 1) → a ∈ (pcBF W F ρ h).A₁ := by
  first | exact @GlobalTheory.AscFin.BidualLattice.bidual_pcBF | exact GlobalTheory.AscFin.BidualLattice.bidual_pcBF | (intros; apply GlobalTheory.AscFin.BidualLattice.bidual_pcBF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepCorePieceFiniteNonzeroVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepCorePieceFiniteNonzeroVacuum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.CorePiece

variable {D : D7}

theorem proj_mem_adelic_lattice_of_mono {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {P : GlobalTheory.FinPl.Pl D → Prop}
    (hL₀ : Submodule.IsLattice D.host.E L₀) (hm : ∀ v, P v → MonoAt d L L₀ v) {z : Fin S.rank → AE D}
    (hz : z ∈ latA S L P) : d.p0 *ᵥ z ∈ latA S₀ L₀ P := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    set u : Fin S.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hu
    have hu' : u ∈ latV S L P := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have heq : d.p0 *ᵥ (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) =
        fun k => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (d.p0 *ᵥ u) k := by
      funext k
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, hu]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i) =
          ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
      rw [h1]; ring
    rw [heq]
    exact GlobalTheory.FinPl.VacFlat.smul_mem_latA ha (GlobalTheory.FinPl.ExtZeroAt.wittProjectionZero_mem_latticeCompletion_of_splits d hL₀ hm hu')
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem mem_lattice_of_extend_inclusion {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    {LV : Lat V} {LV₀ : Lat V₀} {LW : Lat W} {LW₀ : Lat W₀}
    (hV : IsSelfDualC V LV) (hV₀ : IsSelfDualC V₀ LV₀) (hW₀ : IsSelfDualC W₀ LW₀)
    (hmV : ∀ v, MonoAt dV LV LV₀ v) (hmW : ∀ v, MonoAt dW LW LW₀ v) {u : WO V₀ W₀}
    (hu : dV.ext0 W (dW.inc0 V₀ u) ∈ latO V W (LV : Set _) (LW : Set _) fun _ => True) :
    u ∈ latO V₀ W₀ (LV₀ : Set _) (LW₀ : Set _) fun _ => True := by
  have hE : dV.ext0 W (dW.inc0 V₀ u) = dW.j0 * u * dV.p0 := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply]
  rw [hE] at hu
  have hx := GlobalTheory.FinPl.LatMem.latO_mxAt hu
  have hu0 : dW.p0 * (dW.j0 * u * dV.p0) * dV.j0 = u := by
    simp only [← Matrix.mul_assoc, HypDec.p0_j0, Matrix.one_mul]
    simp only [Matrix.mul_assoc, HypDec.p0_j0, Matrix.mul_one]
  refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D V₀ W₀ LV₀ LW₀ hV₀ hW₀ _ u).2 ⟨?_, fun y hy => ?_⟩
  · rw [← hu0]
    intro i j
    rw [Matrix.mul_apply]
    refine sum_mem fun l _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine sum_mem fun k _ => ?_
    rw [mul_assoc]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (hx k l))
  · have key : (show Matrix (Fin W₀.rank) (Fin V₀.rank) (AE D) from u) *ᵥ y =
        dW.p0 *ᵥ ((dW.j0 * u * dV.p0) *ᵥ (dV.j0 *ᵥ y)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hu0]
    rw [key]
    exact proj_mem_adelic_lattice_of_mono dW hW₀.1 (fun v _ => hmW v)
      (GlobalTheory.FinPl.LatMem.latO_maps hV hu (GlobalTheory.FinPl.ExtZeroAt.wittCoreInclusion_mem_latticeCompletionAtPlace dV hV.1 (fun v _ => hmV v) hy))

theorem core_fin_vac : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m),
    (∀ u ∈ (pcBF W F ρ h).Γ₀, MxAt (fun _ => True) (show Mx D (G.V (.core (2 * ρ + 1))).rank (F.V₀ ρ).rank from u)) ∧
      ∃ f, VacG W.ψ (F.V₀ ρ) (G.V (.core (2 * ρ + 1))) (pcBF W F ρ h).Γ₀ f ∧ f ≠ 0 := by
  intro D hOff T L μ0 hL sc G W M hM F hF ρ h
  obtain ⟨-, hB, -⟩ := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hOff T L μ0 hL sc G W M hM F hF
  obtain ⟨hsd0, hmono, -, -⟩ := hB ρ h
  have hV : IsSelfDualC (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) :=
    (G.isV (X := .grid (2 * ρ + 2) 0) ⟨h, Nat.zero_le _⟩ (fun j hj => by injection hj with h1 h2; omega)).sd
  have hW₀ : IsSelfDualC (G.V (.core (2 * ρ + 1))) (G.Λ (.core (2 * ρ + 1))) :=
    (G.isV (X := .core (2 * ρ + 1)) (show 2 * ρ + 1 ≤ D.R.m by omega) (fun j hj => Node.noConfusion hj)).sd
  have hle : (pcBF W F ρ h).Γ₀ ≤ latO (F.V₀ ρ) (G.V (.core (2 * ρ + 1))) (lat0 F ρ h : Set _)
      (G.Λ (.core (2 * ρ + 1)) : Set _) fun _ => True := by
    intro u hu
    refine mem_lattice_of_extend_inclusion (F.dB ρ h) (F.dJ ρ h) hV hsd0 hW₀ (fun v => (hmono v).1) (fun v => (hmono v).2) ?_
    exact GlobalTheory.RowLoc.mem_latO_negSp.1 (AddSubgroup.mem_comap.1 hu).1
  exact ⟨fun u hu => GlobalTheory.FinPl.LatMem.latO_mxAt (hle hu), GlobalTheory.T.exists_ne_zero_latticeVacuum_selfDual D W.ψ W.ψ_std _ _ _ _ hsd0 hW₀ _ hle⟩

end GlobalTheory.AscFin.CorePiece

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepCorePieceFiniteNonzeroVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_step_core_piece_finite_nonzero_vacuum : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), (∀ u ∈ (pcBF W F ρ h).Γ₀, MxAt (fun _ => True) (show Mx D (G.V (.core (2 * ρ + 1))).rank (F.V₀ ρ).rank from u)) ∧ ∃ f, VacG W.ψ (F.V₀ ρ) (G.V (.core (2 * ρ + 1))) (pcBF W F ρ h).Γ₀ f ∧ f ≠ 0 := by
  first | exact @GlobalTheory.AscFin.CorePiece.core_fin_vac | exact GlobalTheory.AscFin.CorePiece.core_fin_vac | (intros; apply GlobalTheory.AscFin.CorePiece.core_fin_vac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepPiecesBFiniteAdelicLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepPiecesBFiniteAdelicLattices
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.BesselPieceB

variable {D : D7}

theorem mxAt_mul_left {P : GlobalTheory.FinPl.Pl D → Prop} {k m n : ℕ} (M : Mx D k m) {x : Mx D m n} (hx : MxAt P x) :
    MxAt P (M ⬝ x) := fun i j => by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hx l j)

theorem mxAt_mul_right {P : GlobalTheory.FinPl.Pl D → Prop} {k m n : ℕ} {x : Mx D k m} (hx : MxAt P x) (M : Mx D m n) :
    MxAt P (x ⬝ M) := fun i j => by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx i l)

theorem finLat_comap_mul {k n k' m' : ℕ} {A : AddSubgroup (Mx D k' m')} (hA : FinLat A) (f : Mx D k n →+ Mx D k' m')
    (M : Mx D k' k) (N : Mx D n m') (M' : Mx D k k') (N' : Mx D m' n) (hf : ∀ x : Mx D k n, f x = M ⬝ x ⬝ N)
    (hM : M' ⬝ M = 1) (hN : N ⬝ N' = 1) : FinLat (A.comap f) := by
  haveI : T2Space (Mx D k' m') := (lattice_Mx D k' m').2.2.2.1
  have hfc : Continuous f := by
    have : (f : Mx D k n → Mx D k' m') = fun x : Mx D k n => M ⬝ x ⬝ N := funext hf
    rw [this]; exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hgc : Continuous fun y : Mx D k' m' => M' ⬝ y ⬝ N' :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hgf : ∀ x, M' ⬝ f x ⬝ N' = x := fun x => by
    have e : M' ⬝ f x ⬝ N' = (M' ⬝ M) ⬝ x ⬝ (N ⬝ N') := by rw [hf]; simp only [Matrix.mul_assoc]
    rw [e, hM, hN, Matrix.one_mul, Matrix.mul_one]
  refine ⟨fun a ha => ?_, ?_, ?_⟩
  · rw [← hgf a]; exact mxAt_mul_right (mxAt_mul_left _ (hA.fin _ ha)) _
  · refine (hA.cpt.image hgc).of_isClosed_subset (hA.cpt.isClosed.preimage hfc) fun a ha => ⟨f a, ha, hgf a⟩
  · obtain ⟨U, hU, h0, hUA⟩ := hA.opn
    refine ⟨f ⁻¹' U, hU.preimage hfc, by simpa using h0, fun a ha hfin => hUA _ ha ?_⟩
    rw [hf]; exact mxAt_mul_right (mxAt_mul_left _ hfin) _

end GlobalTheory.BesselPieceB


open GlobalTheory.BesselPieceB in
theorem GlobalTheory.BesselPieceB.finLat_pcBF_B : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m),
    FinLat (pcBF W F ρ h).B₁ ∧ FinLat (pcBF W F ρ h).B₂ := by
  intro D hD T L μ0 hL sc G W M hM F hF ρ h
  have hB : FinLat (latBig G (2 * ρ + 1)) :=
    ((GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hD T L μ0 hL sc G W M hM F hF).1 (2 * ρ + 1) (by omega)).2.2.1
  exact ⟨finLat_comap_mul hB _ (F.dJ ρ h).jX (F.dB ρ h).p0 (F.dJ ρ h).pX (F.dB ρ h).j0 (fun _ => rfl)
      (F.dJ ρ h).pX_jX (F.dB ρ h).p0_j0,
    finLat_comap_mul hB _ (F.dJ ρ h).jY (F.dB ρ h).p0 (F.dJ ρ h).pY (F.dB ρ h).j0 (fun _ => rfl)
      (F.dJ ρ h).pY_jY (F.dB ρ h).p0_j0⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepPiecesBFiniteAdelicLatticesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_step_pieces_B_finite_adelic_lattices : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), FinLat (pcBF W F ρ h).B₁ ∧ FinLat (pcBF W F ρ h).B₂ := by
  first | exact @GlobalTheory.BesselPieceB.finLat_pcBF_B | exact GlobalTheory.BesselPieceB.finLat_pcBF_B | (intros; apply GlobalTheory.BesselPieceB.finLat_pcBF_B <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiMixedPiecesAdmissible
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.PcBF

variable {D : D7}

theorem symplO_add_right' (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  simp only [symplO, hO, Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem symplO_zero_right' (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  simp [symplO, hO]

theorem symplO_neg_right' (S T : HSp D) (x y : WO S T) : symplO S T x (-y) = - symplO S T x y := by
  have := symplO_add_right' S T x y (-y)
  rw [add_neg_cancel, symplO_zero_right'] at this
  exact eq_neg_of_add_eq_zero_right this.symm

theorem ann_of_mem {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    (ψ : AddChar (AF D.host.F) ℂ) (Γ Γ' : AddSubgroup (WO V W)) {a' : Mx D W.rank ρ}
    (ha' : a' ∈ (piecesOf (W₀ := W₀) dV dW ψ Γ Γ').A₂) :
    ∀ a ∈ (piecesOf (W₀ := W₀) dV dW ψ Γ Γ').A₁, ψ (symplO V W (dV.extX W a) (dV.extY W a')) = 1 := by
  intro a ha
  induction ha' using AddSubgroup.closure_induction with
  | mem b hb => exact hb.2 a ha
  | zero => rw [map_zero, symplO_zero_right', AddChar.map_zero_eq_one]
  | add b c _ _ hb hc => rw [map_add (f := _), symplO_add_right', AddChar.map_add_eq_mul, hb, hc, one_mul]
  | neg b _ hb => rw [map_neg, symplO_neg_right', AddChar.map_neg_eq_inv, hb, inv_one]

end GlobalTheory.PcBF

namespace GlobalTheory.PcBF

theorem pieces_bf : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), (pcBF W F ρ h).Is (F.dB ρ h) (F.dJ ρ h) (xZero (F.dJ ρ h)) W.ψ ∧ Splits (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (xZero (F.dJ ρ h)) (yBF F ρ h) W.ψ (latRow G (2 * ρ + 1)) := by
  set_option maxHeartbeats 0 in
    intro D hD T L μ0 hL sc G W M hM F hF ρ h
    refine ⟨⟨GlobalTheory.T.finite_lattice_standard_parabolic D hD T L μ0 hL sc G W M hM F hF ρ h, ⟨?_, (GlobalTheory.T.besselToFourierJacobi_annihilatorPiece_compactOpen D hD T L μ0 hL sc G W M hM F hF ρ h).1, (GlobalTheory.T.besselToFourierJacobi_annihilatorPiece_compactOpen D hD T L μ0 hL sc G W M hM F hF ρ h).2⟩,
      (GlobalTheory.T.bessel_step_pieces_B_finite_adelic_lattices D hD T L μ0 hL sc G W M hM F hF ρ h).1, (GlobalTheory.T.bessel_step_pieces_B_finite_adelic_lattices D hD T L μ0 hL sc G W M hM F hF ρ h).2, ?_, ?_,
      (GlobalTheory.T.bessel_step_pieces_B_mutual_annihilators D hD T L μ0 hL sc G W M hM F hF ρ h).1, (GlobalTheory.T.bessel_step_pieces_B_mutual_annihilators D hD T L μ0 hL sc G W M hM F hF ρ h).2,
      GlobalTheory.T.genericCharacter_trivial_besselStep_unitriangular D hD T L μ0 hL sc G W M hM F hF ρ h, (GlobalTheory.T.bessel_step_core_piece_finite_nonzero_vacuum D hD T L μ0 hL sc G W M hM F hF ρ h).1, (GlobalTheory.T.bessel_step_core_piece_finite_nonzero_vacuum D hD T L μ0 hL sc G W M hM F hF ρ h).2⟩,
      GlobalTheory.T.besselToFourierJacobi_depthLattice_splits D hD T L μ0 hL sc G W M hM F hF ρ h⟩
    · intro a' ha'
      induction ha' using AddSubgroup.closure_induction with
      | mem b hb => exact hb.1
      | zero => intro i j; simp only [Matrix.zero_apply]; exact zero_mem _
      | add b c _ _ hb hc => intro i j; simp only [Matrix.add_apply]; exact add_mem (hb i j) (hc i j)
      | neg b _ hb => intro i j; simp only [Matrix.neg_apply]; exact neg_mem (hb i j)
    · intro a ha
      exact ⟨fun h1 a' h2 => ann_of_mem _ _ _ _ _ h2 a h1, GlobalTheory.T.biduality_depth_lattice_piece_bessel_step D hD T L μ0 hL sc G W M hM F hF ρ h a ha⟩
    · intro a' ha'
      exact ⟨fun h2 a h1 => ann_of_mem _ _ _ _ _ h2 a h1, fun H => AddSubgroup.subset_closure ⟨ha', fun a h1 => H a h1⟩⟩

end GlobalTheory.PcBF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiMixedPiecesAdmissibleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselToFourierJacobi_mixedPieces_admissible : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), (pcBF W F ρ h).Is (F.dB ρ h) (F.dJ ρ h) (xZero (F.dJ ρ h)) W.ψ ∧ Splits (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (xZero (F.dJ ρ h)) (yBF F ρ h) W.ψ (latRow G (2 * ρ + 1)) := by
  first | exact @GlobalTheory.PcBF.pieces_bf | exact GlobalTheory.PcBF.pieces_bf | (intros; apply GlobalTheory.PcBF.pieces_bf <;> assumption)
end
