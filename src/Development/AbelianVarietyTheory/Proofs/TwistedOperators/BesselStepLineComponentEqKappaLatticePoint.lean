module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAlgebraicIdealExpansion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StarSmulMemSpanModulusDivConjugateLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StarSmulMemSpanModulusDivConjugateLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AdjSrcZero

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem AAbar_ne_zero (D : D7) : D.host.AAbar ≠ 0 := by
  obtain ⟨⟨hAA, hbar⟩, -⟩ := GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D
  intro h0
  apply hAA
  rw [FractionalIdeal.eq_zero_iff] at h0 ⊢
  intro x hx
  have h1 : star x ∈ D.host.AAbar := (hbar _).2 (by rwa [star_star])
  have h2 := h0 _ h1
  simpa using congrArg star h2

theorem AAbar_mul_st (G : GridData L sc) :
    D.host.AAbar * (G.pl.stA sc ^ (0 + 1) * (G.pl.stAbar sc ^ (0 + 1))⁻¹) = D.host.AA * shiftId G := by
  have hA := AAbar_ne_zero D
  simp only [zero_add, pow_one, Places.stA, Places.stAbar, shiftId, mul_inv, inv_inv]
  calc _ = (D.host.AAbar * D.host.AAbar⁻¹) * (D.host.AA *
        (((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) *
        ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hA, one_mul]

theorem star_smul_mem_span : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {n : ℕ}
    (Λ₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), ∀ a ∈ D.host.AA,
    ∀ s ∈ idLat (G.pl.stA sc ^ (0 + 1) * (G.pl.stAbar sc ^ (0 + 1))⁻¹) Λ₀,
    star a • s ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat (shiftId G) Λ₀, y = a' • s'} := by
  intro D T L sc G n Λ₀ a ha s hs
  obtain ⟨⟨-, hbar⟩, -⟩ := GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D
  have key : ∀ b ∈ D.host.AA * shiftId G, ∀ y ∈ Λ₀, b • y ∈
      Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat (shiftId G) Λ₀, y = a' • s'} := by
    intro b hb y hy
    refine FractionalIdeal.mul_induction_on (C := fun b => b • y ∈
      Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat (shiftId G) Λ₀, y = a' • s'}) hb ?_ ?_
    · intro i hi j hj
      refine Submodule.subset_span ⟨i, hi, j • y, Submodule.subset_span ⟨j, hj, y, hy, rfl⟩, ?_⟩
      rw [smul_smul]
    · intro x z hx hz
      rw [add_smul]
      exact add_mem hx hz
  have hsa : star a ∈ D.host.AAbar := (hbar _).2 (by rwa [star_star])
  unfold idLat at hs
  refine Submodule.span_induction (p := fun z _ => star a • z ∈
      Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat (shiftId G) Λ₀, y = a' • s'}) ?_ ?_ ?_ ?_ hs
  · rintro _ ⟨i, hi, y, hy, rfl⟩
    rw [smul_smul]
    exact key _ (AAbar_mul_st G ▸ FractionalIdeal.mul_mem_mul hsa hi) y hy
  · simp
  · intro x z _ _ hx hz
    rw [smul_add]
    exact add_mem hx hz
  · intro c x _ hx
    rw [smul_comm]
    exact Submodule.smul_mem _ c hx

end GlobalTheory.AdjSrcZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StarSmulMemSpanModulusDivConjugateLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_smul_mem_span_modulusDivConjugate_lattice : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {n : ℕ} (Λ₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), ∀ a ∈ D.host.AA, ∀ s ∈ idLat (G.pl.stA sc ^ (0 + 1) * (G.pl.stAbar sc ^ (0 + 1))⁻¹) Λ₀, star a • s ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat (shiftId G) Λ₀, y = a' • s'} := by
  first | exact @GlobalTheory.AdjSrcZero.star_smul_mem_span | exact GlobalTheory.AdjSrcZero.star_smul_mem_span | (intros; apply GlobalTheory.AdjSrcZero.star_smul_mem_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepZeroLineComponentAdjointMemLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselFirstStepAdjointLineComponentMemLatO
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselFirstStepAdjointLineComponentMemLatO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LineAdjZero

open GlobalTheory.AdjLatO GlobalTheory.LineCompLat

variable {D : D7}

theorem genT_smul_left (T : HSp D) {n : ℕ} (x : AF D.host.F) (c : D.host.E) (t : Fin T.rank → D.host.E)
    (u : Fin n → D.host.E) : genT T x (c • t) u = genT T x t (star c • u) := by
  ext p q
  simp only [genT, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem genT_add_left (T : HSp D) {n : ℕ} (x : AF D.host.F) (t t' : Fin T.rank → D.host.E)
    (u : Fin n → D.host.E) : genT T x (t + t') u = genT T x t u + genT T x t' u := by
  ext p q
  simp only [genT, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib, mul_add,
    TensorProduct.tmul_add]

theorem genT_zero_left (T : HSp D) {n : ℕ} (x : AF D.host.F) (u : Fin n → D.host.E) :
    genT T x 0 u = 0 := by
  ext p q
  simp [genT]

theorem latO_idLat_le (S T : HSp D) (LS : Lat S) (LT : Lat T) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (hI : ∀ σ ∈ I, ∀ τ ∈ I, ∃ c : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E c = star σ * τ) (P : GlobalTheory.FinPl.Pl D → Prop) :
    latO S T (idLat I LS : Set _) (idLat I LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) P := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  have hσ : ∀ σ ∈ I, ∀ t ∈ idLat I LT, star σ • t ∈ LT := by
    intro σ hσ t ht
    unfold idLat at ht
    induction ht using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨τ, hτ, y, hy, rfl⟩ := hz
      obtain ⟨c, hc⟩ := hI σ hσ τ hτ
      rw [smul_smul, ← hc, algebraMap_smul]
      exact LT.smul_mem c hy
    | zero => rw [smul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
    | smul r y _ hy => rw [smul_comm]; exact LT.smul_mem r hy
  have key : ∀ t ∈ idLat I LT, genT S (pairA D.host.F 0 α) s (a • t) ∈ latO S T (LS : Set _) (LT : Set _) P := by
    have hs' : s ∈ Submodule.span (𝓞 D.host.E) {z | ∃ s ∈ I, ∃ y ∈ LS, z = s • y} := hs
    clear hs
    induction hs' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨σ, hσI, y, hy, rfl⟩ := hz
      intro t ht
      rw [genT_smul_left, smul_comm]
      exact genT_mem_of_mem_span T S LT LS P α hα hP y hy _
        (Submodule.subset_span ⟨a, ha, _, hσ σ hσI t ht, rfl⟩)
    | zero => intro t _; rw [genT_zero_left]; exact zero_mem _
    | add y z _ _ hy hz => intro t ht; rw [genT_add_left]; exact add_mem (hy t ht) (hz t ht)
    | smul r y _ hy =>
      intro t ht
      obtain ⟨r', hr'⟩ := GlobalTheory.FinPl.LatMem.star_int r
      have e1 : r • y = (r : D.host.E) • y := (algebraMap_smul D.host.E r y).symm
      have e2 : (r' : D.host.E) • t = r' • t := algebraMap_smul D.host.E r' t
      rw [e1, genT_smul_left, smul_comm, ← hr', e2]
      exact hy _ (Submodule.smul_mem _ r' ht)
  exact key t ht

theorem star_mul_shiftId {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) :
    ∀ σ ∈ shiftId G, ∀ τ ∈ shiftId G, ∃ c : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E c = star σ * τ := by
  intro σ hσ τ hτ
  have h1 : star σ ∈ (shiftId G)⁻¹ := by
    rw [← GlobalTheory.RowBig.conjFI_shiftId, GlobalTheory.SeeSaw.mem_conjFI, ← Formalism.BasicNotions.bridge_star_holds D.R D.host, star_star]
    exact hσ
  have h2 := FractionalIdeal.mul_mem_mul h1 hτ
  rw [inv_mul_cancel₀ (GlobalTheory.RowBig.shiftId_ne_zero G)] at h2
  exact (FractionalIdeal.mem_one_iff _).1 h2

theorem mulVec_idLat {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (hM : ∀ x ∈ Λ, M *ᵥ x ∈ Λ')
    (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : ∀ x ∈ idLat I Λ, M *ᵥ x ∈ idLat I Λ' := by
  intro x hx
  unfold idLat at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨τ, hτ, y, hy, rfl⟩ := hz
    rw [Matrix.mulVec_smul]
    exact Submodule.subset_span ⟨τ, hτ, _, hM y hy, rfl⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [Matrix.mulVec_add]; exact add_mem hy hz
  | smul r y _ hy => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ r hy

theorem lineComp_mem_shift : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F ρ h).Γ₀, ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).2 ∈ latO (negSp F.Lz) (G.V (.core (2 * ρ + 1))) (idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0}) : Set _) (idLat (shiftId G) (G.Λ (.core (2 * ρ + 1))) : Set _) fun _ => True := by
  intro D hD T L μ0 hL sc G W Mv hM F hF ρ h u hu
  obtain ⟨hsd0, hloc, hsdM, horth⟩ := (GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hD T L μ0 hL sc G W Mv hM F hF).2.1 ρ h
  have sdV : IsSelfDualC (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.Λ (.grid (2 * ρ + 1 + 1) 0)) :=
    (G.sp.V_is (2 * ρ + 1 + 1) 0 (by omega) h (by omega)).sd
  have sdC : IsSelfDualC (G.V (.core (2 * ρ + 1))) (G.Λ (.core (2 * ρ + 1))) :=
    (G.sp.P_is (2 * ρ + 1) (by omega)).sd
  have sdC' := GlobalTheory.RowBig.isSelfDualC_idLat_shiftId G _ sdC
  have hU1 : (F.dJ ρ h).j0 * u * (F.dB ρ h).p0 ∈ latRow G (2 * ρ + 1) := hu
  have hU : (F.dJ ρ h).j0 * u * (F.dB ρ h).p0 ∈ latO (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.V (.grid (2 * ρ + 1) 0))
      (G.Λ (.grid (2 * ρ + 1 + 1) 0) : Set _) (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0)) : Set _) fun _ => True :=
    GlobalTheory.T.depthLatticeGridRow_le_selfDualHomLatticeShift D hD T L μ0 hL sc G W Mv hM (2 * ρ + 1) (by omega) (by omega) hU1
  clear hU1 hu
  have hq : ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0), (F.dJ ρ h).q0 *ᵥ t ∈ G.Λ (.core (2 * ρ + 1)) :=
    GlobalTheory.FinPl.CoreProj.wittCoreProjection_mem_lattice_of_splits (F.dJ ρ h) (GlobalTheory.FinPl.LocGlob.mem_of_mem_latV_all sdC) fun v => (hloc v).2
  have hu' : u = (F.dJ ρ h).p0 * ((F.dJ ρ h).j0 * u * (F.dB ρ h).p0) * (F.dB ρ h).j0 := by
    simp only [← Matrix.mul_assoc, HypDec.p0_j0, Matrix.one_mul]
    rw [Matrix.mul_assoc u, HypDec.p0_j0, Matrix.mul_one]
  rw [OrthDec.resS_apply]
  refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ hsdM sdC' _ _).2 ⟨?_, fun z hz => ?_⟩
  · rw [hu']
    exact mxAt_mul_right (mxAt_mul_right (mxAt_mul_left _ (GlobalTheory.FinPl.LatMem.latO_mxAt hU)) _) _
  have h1 : (F.oB ρ h).jB *ᵥ z ∈ latV (F.V₀ ρ) (lat0 F ρ h) fun _ => True := by
    refine GlobalTheory.FinPl.FlatVacuum.mulVec_latV_of_local hsdM.1 hsd0.1 (F.oB ρ h).jB (fun v _ y hy => ?_) hz
    refine ((horth v) _).2 ⟨?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, OrthDec.pA_jB, Matrix.zero_mulVec]; exact zero_mem _
    · rw [Matrix.mulVec_mulVec, OrthDec.pB_jB, Matrix.one_mulVec]; exact hy
  have h2 : (F.dB ρ h).j0 *ᵥ ((F.oB ρ h).jB *ᵥ z) ∈
      latV (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.Λ (.grid (2 * ρ + 1 + 1) 0)) fun _ => True :=
    rat_mulVec_latV (F.dB ρ h).i₀ (fun x hx => hx) h1
  have h3 := GlobalTheory.FinPl.LatMem.latO_maps sdV hU h2
  have h4 : (F.dJ ρ h).p0 *ᵥ (((F.dJ ρ h).j0 * u * (F.dB ρ h).p0) *ᵥ ((F.dB ρ h).j0 *ᵥ ((F.oB ρ h).jB *ᵥ z))) ∈
      latA _ (idLat (shiftId G) (G.Λ (.core (2 * ρ + 1)))) fun _ => True := by
    refine GlobalTheory.FinPl.FlatVacuum.mulVec_latA (F.dJ ρ h).p0 (fun y hy => ?_) h3
    exact rat_mulVec_latV (F.dJ ρ h).q0 (mulVec_idLat _ hq _) hy
  have e : (F.dJ ρ h).p0 *ᵥ (((F.dJ ρ h).j0 * u * (F.dB ρ h).p0) *ᵥ ((F.dB ρ h).j0 *ᵥ ((F.oB ρ h).jB *ᵥ z))) =
      (u * (F.oB ρ h).jB) *ᵥ z := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, HypDec.p0_j0, Matrix.one_mul]
    rw [Matrix.mul_assoc u, HypDec.p0_j0, Matrix.mul_one]
  rw [← e]
  exact h4

theorem adj_lineComp_mem_latO : OnStd fun {D} _ _ {sc} {G} W F => ∀ (h : 2 * 0 + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F 0 h).Γ₀, incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj _ _ (((F.oB 0 h).resS (G.V (.core (2 * 0 + 1))) u).2) ∈ latO (G.V (.core (2 * 0 + 1))) (negSp F.Lz) (G.Λ (.core (2 * 0 + 1)) : Set _) (Submodule.span (𝓞 D.host.E) {F.ζ 0} : Set _) fun _ => True := by
  intro D hD T L μ0 hL sc G W Mv hM F hF h u hu
  have hx := lineComp_mem_shift D hD T L μ0 hL sc G W Mv hM F hF 0 h u hu
  exact latO_idLat_le _ _ _ _ (shiftId G) (star_mul_shiftId G) _
    (incA_inv_xi0_smul_starAdj_mem_latO D (negSp F.Lz) (G.V (.core (2 * 0 + 1))) _ _ _ _
      (GlobalTheory.AdjSrcZero.star_smul_mem_span G _) _ hx)

end GlobalTheory.LineAdjZero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselFirstStepAdjointLineComponentMemLatOStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselFirstStep_adjointLineComponent_mem_latO : OnStd fun {D} _ _ {sc} {G} W F => ∀ (h : 2 * 0 + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F 0 h).Γ₀, incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj _ _ (((F.oB 0 h).resS (G.V (.core (2 * 0 + 1))) u).2) ∈ latO (G.V (.core (2 * 0 + 1))) (negSp F.Lz) (G.Λ (.core (2 * 0 + 1)) : Set _) (Submodule.span (𝓞 D.host.E) {F.ζ 0} : Set _) fun _ => True := by
  first | exact @GlobalTheory.LineAdjZero.adj_lineComp_mem_latO | exact GlobalTheory.LineAdjZero.adj_lineComp_mem_latO | (intros; apply GlobalTheory.LineAdjZero.adj_lineComp_mem_latO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StarAdjointMemHatLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationAAModulusDivConjLeCosetExponent
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationAAModulusDivConjLeCosetExponent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.ShiftVal

open scoped Pointwise

theorem valuation_le_of_mem {K : Type} [Field K] [NumberField K] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {I : FractionalIdeal (𝓞 K)⁰ K} {b : K} (hb : b ∈ I) :
    w.valuation K b ≤ WithZero.exp (-FractionalIdeal.count K w I) := by
  by_cases hb0 : b = 0
  · rw [hb0, map_zero]; exact zero_le'
  have h1 : FractionalIdeal.count K w I ≤ FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ b) :=
    FractionalIdeal.count_mono K w (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hb0)
      ((FractionalIdeal.spanSingleton_le_iff_mem).mpr hb)
  rw [ReciprocityTheory.Neutral.Bridge.HCFR.count_spanSingleton K w hb0] at h1
  have hv : w.valuation K b ≠ 0 := (map_ne_zero _).mpr hb0
  rw [← WithZero.exp_log hv, WithZero.exp_le_exp]
  omega

theorem val_le_cosExp : ∀ {D : D7}, OffQ D → ∀ {T : Type} {L : LevCh D T} (μ0 : T), L.Is μ0 → ∀ {sc : Consts}
    (G : GridData L sc), ∀ w ∈ G.pl.W0, ∀ b ∈ D.host.AA * shiftId G,
      Valued.v (algebraMap D.host.E (Kw w) b) ≤ WithZero.exp (-(cosExp G w : ℤ)) := by
  intro D hq T L μ0 hL sc G w hw b hb
  classical
  have hM : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact G.pl.modul_ne_bot sc
  have hMb : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    unfold Places.modulBar
    intro h
    apply G.pl.modul_ne_bot sc
    have := congrArg (fun J : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • J) h
    simpa [smul_smul] using this
  have hwl : w ∈ locPl G μ0 := by unfold locPl; exact Finset.mem_union_left _ hw
  have hc : FractionalIdeal.count D.host.E w (shiftId G) = cosExp G w := by
    show FractionalIdeal.count D.host.E w
      (((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) *
        ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹) = _
    rw [FractionalIdeal.count_mul _ _ hM (inv_ne_zero hMb), FractionalIdeal.count_inv,
      count_modul, count_modulBar G hwl, neg_zero, add_zero]
  rw [Good.valued_alg]
  refine FractionalIdeal.mul_induction_on hb ?_ ?_
  · intro a ha s hs
    rw [map_mul]
    have h1 := GlobalTheory.DepthFix.aa_int hL hq G hw a ha
    rw [Good.valued_alg] at h1
    have h2 := valuation_le_of_mem w hs
    rw [hc] at h2
    calc _ ≤ 1 * WithZero.exp (-(cosExp G w : ℤ)) := mul_le_mul' h1 h2
      _ = _ := one_mul _
  · intro x y hx hy
    exact Valuation.map_add_le _ hx hy

end GlobalTheory.AscFin.ShiftVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationAAModulusDivConjLeCosetExponentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_AA_modulusDivConj_le_cosetExponent : ∀ {D : D7}, OffQ D → ∀ {T : Type} {L : LevCh D T} (μ0 : T), L.Is μ0 → ∀ {sc : Consts} (G : GridData L sc), ∀ w ∈ G.pl.W0, ∀ b ∈ D.host.AA * shiftId G, Valued.v (algebraMap D.host.E (Kw w) b) ≤ WithZero.exp (-(cosExp G w : ℤ)) := by
  first | exact @GlobalTheory.AscFin.ShiftVal.val_le_cosExp | exact GlobalTheory.AscFin.ShiftVal.val_le_cosExp | (intros; apply GlobalTheory.AscFin.ShiftVal.val_le_cosExp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumScalarSmulMemCompletedModulus
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumScalarSmulMemCompletedModulus
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.HalfScalarHat

open GlobalTheory.FunObj.HatFrame

theorem smul_map_mem_genGrp {D : D7} {m n : ℕ} (M : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E))
    (𝔪 : Ideal (𝓞 D.host.E)) {g : Matrix (Fin m) (Fin n) D.host.E} (hg : g ∈ M)
    {t : Formalism.L2.Herm.intAf D.host.F D.host.E} (ht : t ∈ Formalism.L2.DIV.idS D.host.F 𝔪) :
    (t : EAf D) • g.map (eToEAf D) ∈ genGrp D.host.F (𝔪 • M) := by
  have hgen : ∀ a ∈ 𝔪, ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) •
      g.map (eToEAf D) ∈ genGrp D.host.F (𝔪 • M) := by
    intro a ha
    refine AddSubgroup.subset_closure ⟨1, one_mem _, a • g, Submodule.smul_mem_smul ha hg, ?_⟩
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, Formalism.L2.DIV.oToS_coe, smul_eq_mul, eToEAf,
      Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.smul_def]
  have hspan : t ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((Formalism.L2.DIV.oToS D.host.F D.host.E) '' (𝔪 : Set (𝓞 D.host.E))) := ht
  clear ht
  induction hspan using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, ha, rfl⟩ := hu
    exact hgen a ha
  | zero =>
    simp only [ZeroMemClass.coe_zero, zero_smul]
    exact zero_mem _
  | add u v _ _ hu hv =>
    simp only [AddMemClass.coe_add, add_smul]
    exact add_mem hu hv
  | smul r u _ hu =>
    simp only [smul_eq_mul, MulMemClass.coe_mul, mul_smul]
    exact smul_mem_genGrp _ _ r.2 _ hu

theorem tmul_split {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (x : A ⊗[R] B) (b g : A) (α : B) :
    x * ((b * g) ⊗ₜ[R] α) = x * ((b ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] α)) * (g ⊗ₜ[R] (1 : B)) := by
  simp only [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem v_triple_le {D : D7} {w : HeightOneSpectrum (𝓞 D.host.E)} {s x y z : EAf D} {c : WithZero (Multiplicative ℤ)} (h : s = x * (y * z))
    (hx : GlobalTheory.StdFrames.cpt (D := D) w x = 1) (hy : Valued.v (GlobalTheory.StdFrames.cpt (D := D) w y) ≤ c)
    (hz : Valued.v (GlobalTheory.StdFrames.cpt (D := D) w z) ≤ 1) : Valued.v (GlobalTheory.StdFrames.cpt (D := D) w s) ≤ c := by
  subst h
  rw [map_mul, hx, one_mul, map_mul, map_mul]
  calc Valued.v (GlobalTheory.StdFrames.cpt (D := D) w y) * Valued.v (GlobalTheory.StdFrames.cpt (D := D) w z) ≤ c * 1 :=
        mul_le_mul' hy hz
    _ = c := mul_one c

theorem scalar_mem_idS {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {s x y z : EAf D}
    (h : s = x * (y * z)) (e1 : ∀ w ∈ G.pl.W0, GlobalTheory.StdFrames.cpt (D := D) w x = 1)
    (e2 : ∀ w ∉ G.pl.W0, GlobalTheory.StdFrames.cpt (D := D) w x = 0)
    (hy : ∀ w ∈ G.pl.W0, Valued.v (GlobalTheory.StdFrames.cpt (D := D) w y) ≤ WithZero.exp (-(cosExp G w : ℤ)))
    (hz : z ∈ GlobalTheory.StdFrames.OA D) :
    ∃ t ∈ Formalism.L2.DIV.idS D.host.F G.modul, t.1 = s := by
  have hz' : ∀ w, Valued.v (GlobalTheory.StdFrames.cpt (D := D) w z) ≤ 1 := fun w =>
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((GlobalTheory.StdFrames.mem_OA_iff z).1 hz w)
  have hs : s ∈ GlobalTheory.StdFrames.OA D := by
    rw [GlobalTheory.StdFrames.mem_OA_iff]
    intro w
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    by_cases hw : w ∈ G.pl.W0
    · refine v_triple_le h (e1 w hw) ((hy w hw).trans ?_) (hz' w)
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    · rw [h, map_mul, e2 w hw, zero_mul, map_zero]
      exact zero_le'
  refine ⟨⟨s, hs⟩, ?_, rfl⟩
  rw [GlobalTheory.FunObj.Comparison₂.mem_idS_modul]
  intro w hw
  exact v_triple_le h (e1 w hw) (hy w hw) (hz' w)

theorem toEAf_pair {D : D7} (α : Formalism.L2.Herm.Af D.host.F) (x : D.host.E) :
    toEAf D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x) = x ⊗ₜ[D.host.F] α := rfl

theorem map_toEAf_smul {D : D7} {m n : ℕ} (e : AE D) (X : Mx D m n) :
    (e • X).map (toEAf D) = toEAf D e • X.map (toEAf D) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem infPart_smul {D : D7} {m n : ℕ} {e : AE D} (he : infPart D e = 0) (X : Mx D m n) (i : Fin m) (j : Fin n) :
    infPart D ((e • X) i j) = 0 := by
  rw [Matrix.smul_apply, smul_eq_mul, map_mul, he, zero_mul]

theorem smul_pair {D : D7} {m n : ℕ} (x : EAf D) (α : Formalism.L2.Herm.Af D.host.F) (b : D.host.E)
    (g : Matrix (Fin m) (Fin n) D.host.E) :
    x • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (b * g i j) : Mx D m n).map (toEAf D) =
      (x * ((b ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) : EAf D) * ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D))) •
        g.map (eToEAf D) := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul, toEAf_pair, eToEAf,
    Algebra.TensorProduct.includeLeftRingHom_apply]
  exact tmul_split _ b (g i j) α

end GlobalTheory.HalfScalarHat

open GlobalTheory.FunObj.HatFrame GlobalTheory.HalfScalarHat in
theorem GlobalTheory.HalfScalarHat.idemSum_smul_mem_hatMx : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {m n : ℕ} (M : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E)) (e : AE D), IsIdemSum e G.pl.W0 → ∀ α ∈ intAf D.host.F, ∀ b : D.host.E, (∀ w ∈ G.pl.W0, Valued.v (algebraMap D.host.E (Kw w) b) ≤ WithZero.exp (-(cosExp G w : ℤ))) → ∀ g ∈ M, e • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (b * g i j) : Mx D m n) ∈ hatMx (G.modul • M) := by
  intro D T L sc G m n M e he α hα b hb g hg
  obtain ⟨hinf, h1, h0⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he
  rw [GlobalTheory.FunObj.HatFrame.mem_hatMx_iff]
  refine ⟨fun i j => infPart_smul hinf _ i j, ?_⟩
  rw [map_toEAf_smul, smul_pair]
  have hα' : ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) ∈ GlobalTheory.StdFrames.OA D :=
    Subring.subset_closure (Or.inr ⟨⟨α, fun v => hα v⟩, rfl⟩)
  obtain ⟨t, ht, hts⟩ := scalar_mem_idS G rfl h1 h0
    (fun w hw => by rw [GlobalTheory.FunObj.Comparison₂.cpt_tmul]; exact hb w hw) hα'
  rw [← hts]
  exact smul_map_mem_genGrp M G.modul hg ht
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumScalarSmulMemCompletedModulusStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentSum_scalar_smul_mem_completedModulus : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {m n : ℕ} (M : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E)) (e : AE D), IsIdemSum e G.pl.W0 → ∀ α ∈ intAf D.host.F, ∀ b : D.host.E, (∀ w ∈ G.pl.W0, Valued.v (algebraMap D.host.E (Kw w) b) ≤ WithZero.exp (-(cosExp G w : ℤ))) → ∀ g ∈ M, e • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (b * g i j) : Mx D m n) ∈ hatMx (G.modul • M) := by
  first | exact @GlobalTheory.HalfScalarHat.idemSum_smul_mem_hatMx | exact GlobalTheory.HalfScalarHat.idemSum_smul_mem_hatMx | (intros; apply GlobalTheory.HalfScalarHat.idemSum_smul_mem_hatMx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StarAdjointMemHatLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.LineDepthZero

set_option maxHeartbeats 1000000

theorem smul_mem_hatMx_of_mem_latO {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {S B : HSp D}
    (LS : Lat S) (Λ₀ : Lat B) (hS : IsSelfDualC S LS)
    (hv : ∀ w ∈ G.pl.W0, ∀ b ∈ D.host.AA * shiftId G,
      Valued.v (algebraMap D.host.E (Kw w) b) ≤ WithZero.exp (-(cosExp G w : ℤ)))
    (e : AE D) (he : IsIdemSum e G.pl.W0) :
    ∀ z ∈ latO S B (LS : Set _) (idLat (shiftId G) Λ₀ : Set _) (fun _ => True),
      e • z ∈ hatMx (G.modul • homLat LS Λ₀) := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    have key : ∀ t ∈ idLat (shiftId G) Λ₀, ∀ a ∈ D.host.AA,
        e • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S B) ∈
          hatMx (G.modul • homLat LS Λ₀) := by
      intro t ht
      induction ht using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨j, hj, y, hy, rfl⟩ := hx
        intro a ha
        have h1 := GlobalTheory.T.idempotentSum_scalar_smul_mem_completedModulus G (homLat LS Λ₀) e he α hα (a * j)
          (fun w hw => hv w hw _ (FractionalIdeal.mul_mem_mul ha hj)) _
          (GlobalTheory.RowLatChi.genMap_one_mem_homLat hS hs hy)
        convert h1 using 3
        ext i k
        simp only [Matrix.of_apply, GlobalTheory.LatVac.genMap, Pi.smul_apply, smul_eq_mul]
        ring_nf
      | zero =>
        intro a ha
        have e0 : (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
            (a * (0 : Fin B.rank → D.host.E) i * ∑ k, star (s k) * S.gram k j) : WO S B) = 0 := by
          ext i j; simp
        rw [e0, smul_zero]; exact zero_mem _
      | add x y _ _ hx hy =>
        intro a ha
        have e0 : (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
            (a * (x + y) i * ∑ k, star (s k) * S.gram k j) : WO S B) =
            (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * x i * ∑ k, star (s k) * S.gram k j)) +
            (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * y i * ∑ k, star (s k) * S.gram k j)) := by
          ext i j
          simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply, mul_add, add_mul, TensorProduct.tmul_add]
        rw [e0, smul_add]; exact add_mem (hx a ha) (hy a ha)
      | smul o x _ hx =>
        intro a ha
        have ha' : a * algebraMap (𝓞 D.host.E) D.host.E o ∈ D.host.AA := by
          rw [mul_comm, ← Algebra.smul_def]; exact Submodule.smul_mem _ o ha
        convert hx _ ha' using 4
        ext i j
        simp only [Matrix.of_apply, Pi.smul_apply, Algebra.smul_def]
        ring_nf
    exact key t ht a ha
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

end GlobalTheory.LineDepthZero


open GlobalTheory.LineDepthZero in
theorem GlobalTheory.AscFin.BoxBF.lineAdj_zero_dep : OnStd fun {D} _ _ {sc} {G} W F => ∀ (h : 2 * 0 + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F 0 h).Γ₀, ∀ e : AE D, IsIdemSum e G.pl.W0 → e • (incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj _ _ (((F.oB 0 h).resS (G.V (.core (2 * 0 + 1))) u).2)) ∈ hatMx (G.modul • homLat (G.Λ (.core (2 * 0 + 1))) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) := by
  intro D hD T L μ0 hL sc G W Mv hM F hF h u hu e he
  have hx := GlobalTheory.T.bessel_step_line_component_mem_hom_lattice D hD T L μ0 hL sc G W Mv hM F hF 0 h u hu
  have hy := GlobalTheory.AdjLatO.incA_inv_xi0_smul_starAdj_mem_latO D (negSp F.Lz) (G.V (.core (2 * 0 + 1))) _
    (idLat (shiftId G) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) (G.Λ (.core (2 * 0 + 1))) (fun _ => True)
    (GlobalTheory.T.star_smul_mem_span_modulusDivConjugate_lattice G _) _ hx
  have sdC : IsSelfDualC (G.V (.core (2 * 0 + 1))) (G.Λ (.core (2 * 0 + 1))) := (G.sp.P_is (2 * 0 + 1) (by omega)).sd
  exact smul_mem_hatMx_of_mem_latO G _ _ sdC (GlobalTheory.T.valuation_AA_modulusDivConj_le_cosetExponent hD μ0 hL G) e he _ hy
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StarAdjointMemHatLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_adjoint_mem_hat_lattice : OnStd fun {D} _ _ {sc} {G} W F => ∀ (h : 2 * 0 + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F 0 h).Γ₀, ∀ e : AE D, IsIdemSum e G.pl.W0 → e • (incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj _ _ (((F.oB 0 h).resS (G.V (.core (2 * 0 + 1))) u).2)) ∈ hatMx (G.modul • homLat (G.Λ (.core (2 * 0 + 1))) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) := by
  first | exact @GlobalTheory.AscFin.BoxBF.lineAdj_zero_dep | exact GlobalTheory.AscFin.BoxBF.lineAdj_zero_dep | (intros; apply GlobalTheory.AscFin.BoxBF.lineAdj_zero_dep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepZeroLineComponentAdjointMemLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000

namespace GlobalTheory.LineZero

variable {D : D7}

noncomputable def mulL {k m n : ℕ} (A : Mx D k m) : Mx D m n →+ Mx D k n where
  toFun y := A * y
  map_zero' := Matrix.mul_zero _
  map_add' y y' := Matrix.mul_add _ _ _

theorem rat_mul_mem_latO {S B T : HSp D} (M : Matrix (Fin T.rank) (Fin B.rank) D.host.E)
    {LS : Set (Fin S.rank → D.host.E)} {LB : Set (Fin B.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : GlobalTheory.FinPl.Pl D → Prop} (hM : ∀ t ∈ LB, M *ᵥ t ∈ LT) {y : WO S B} (hy : y ∈ latO S B LS LB P) :
    (rat M : Mx D T.rank B.rank) * y ∈ latO S T LS LT P := by
  suffices h : latO S B LS LB P ≤ (latO S T LS LT P).comap (mulL (rat M : Mx D T.rank B.rank)) from h hy
  refine (AddSubgroup.closure_le _).2 ?_
  rintro w ⟨α, hα, hαP, a, ha, s, hs, t, ht, rfl⟩
  refine AddSubgroup.subset_closure ⟨α, hα, hαP, a, ha, s, hs, M *ᵥ t, hM t ht, ?_⟩
  ext i j
  simp only [mulL, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, incA, inclR,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, Matrix.mulVec, dotProduct, Finset.sum_mul]
  rw [← TensorProduct.tmul_sum]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  first
    | exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
    | (rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring)

end GlobalTheory.LineZero

namespace GlobalTheory.LineZero

variable {D : D7}

theorem latO_le_negSp {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : GlobalTheory.FinPl.Pl D → Prop} : latO S T LS LT P ≤ latO (negSp S) T LS LT P := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro w ⟨α, hα, hαP, a, ha, s, hs, t, ht, rfl⟩
  have e : (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) =
      -(Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * (negSp S).gram k j)) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.neg_apply, negSp_gram, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib,
      TensorProduct.tmul_neg, neg_neg]
  rw [e]
  exact neg_mem (AddSubgroup.subset_closure ⟨α, hα, hαP, a, ha, s, hs, t, ht, rfl⟩)

theorem rat_mul_mem_hatMx {k m n : ℕ} (A : Matrix (Fin k) (Fin m) D.host.E)
    {N : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E)} {N' : Submodule (𝓞 D.host.E) (Matrix (Fin k) (Fin n) D.host.E)}
    (hA : ∀ x ∈ N, A * x ∈ N') {y : Mx D m n} (hy : y ∈ hatMx N) : (rat A : Mx D k m) * y ∈ hatMx N' := by
  suffices h : hatMx N ≤ (hatMx N').comap (mulL (rat A : Mx D k m)) from h hy
  refine (AddSubgroup.closure_le _).2 ?_
  rintro w ⟨α, hα, x, hx, rfl⟩
  refine AddSubgroup.subset_closure ⟨α, hα, A * x, hA x hx, ?_⟩
  ext i j
  simp only [mulL, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, incA, inclR,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul]
  rw [← TensorProduct.tmul_sum]

theorem mul_mem_smul_homLat {k m n : ℕ} (A : Matrix (Fin k) (Fin m) D.host.E) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {Λ'' : Submodule (𝓞 D.host.E) (Fin k → D.host.E)}
    (hA : ∀ t ∈ Λ', A *ᵥ t ∈ Λ'') (I : Ideal (𝓞 D.host.E)) {x : Matrix (Fin m) (Fin n) D.host.E}
    (hx : x ∈ I • homLat Λ Λ') : A * x ∈ I • homLat Λ Λ'' := by
  refine Submodule.smul_induction_on hx (fun r hr y hy => ?_) (fun _ _ hy hy' => ?_)
  · rw [Matrix.mul_smul]
    refine Submodule.smul_mem_smul hr fun z hz => ?_
    rw [← Matrix.mulVec_mulVec]
    exact hA _ (hy z hz)
  · rw [Matrix.mul_add]
    exact add_mem hy hy'

end GlobalTheory.LineZero


open GlobalTheory.LineZero in
theorem GlobalTheory.LineZero.adj_mem_lineLat : OnStd fun {D} _ _ {sc} {G} W F => ∀ (h : 2 * 0 + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F 0 h).Γ₀, incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj _ _ (((F.oB 0 h).resS (G.V (.core (2 * 0 + 1))) u).2) ∈ lineLat F 0 := by
  intro D hq T L μ0 hL sc G W M hM F hF h u hu
  have h1 := GlobalTheory.T.besselFirstStep_adjointLineComponent_mem_latO D hq T L μ0 hL sc G W M hM F hF h u hu
  have h2 := GlobalTheory.T.star_adjoint_mem_hat_lattice D hq T L μ0 hL sc G W M hM F hF h u hu
  have hz : ∀ t ∈ Submodule.span (𝓞 D.host.E) {F.ζ 0}, F.oz.iB *ᵥ t ∈ G.Λ (.core 0) := by
    intro t ht
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ht
    rw [Matrix.mulVec_smul, hF.zB]
    refine Submodule.smul_mem _ c ?_
    show _ ∈ (G.sp.P 0).lat
    rw [G.sp.lat0]
    refine ⟨0, zero_mem _, fun _ => 1, fun _ => FractionalIdeal.one_mem_one _, ?_⟩
    funext i
    simp [Matrix.mulVec, dotProduct]
  show _ ∈ (latCore G 0).comap _
  rw [AddSubgroup.mem_comap]
  simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe, Function.comp_apply,
    AddMonoidHom.inr_apply]
  rw [GlobalTheory.MixModel.OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add (F.oz.jB * _)]
  refine ⟨?_, fun e he => ?_⟩
  · exact latO_le_negSp (rat_mul_mem_latO F.oz.iB hz h1)
  · rw [← Matrix.mul_smul]
    exact rat_mul_mem_hatMx F.oz.iB (fun x hx => mul_mem_smul_homLat F.oz.iB hz _ hx) (h2 e he)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepZeroLineComponentAdjointMemLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselStepZero_lineComponent_adjoint_mem_lattice : OnStd fun {D} _ _ {sc} {G} W F => ∀ (h : 2 * 0 + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F 0 h).Γ₀, incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj _ _ (((F.oB 0 h).resS (G.V (.core (2 * 0 + 1))) u).2) ∈ lineLat F 0 := by
  first | exact @GlobalTheory.LineZero.adj_mem_lineLat | exact GlobalTheory.LineZero.adj_mem_lineLat | (intros; apply GlobalTheory.LineZero.adj_mem_lineLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardFrameLinkMapInvertsHermitianSkewAdjoint
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardFrameLinkMapInvertsHermitianSkewAdjoint
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.KapAdjLine

theorem kap_starAdj : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (x : WO (negSp F.Lz) (G.V (.core (2 * ρ + 1)))), (F.lnk ρ).κ _ (incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj _ _ x) = x := by
  unfold OnStd
  intro D _ _ _ _ _ _ G _ _ _ F hF ρ x
  have hτ : (F.lnk ρ).τ = D.host.xi0 • (1 : Matrix (Fin (negSp F.Lz).rank) (Fin (negSp F.Lz).rank) D.host.E) := by
    have hl := F.line ρ
    have hu : Unique (Fin (negSp F.Lz).rank) := by rw [hl.1]; infer_instance
    have hz : F.ζ (ρ + 1) = (-D.host.xi0) • F.ζ ρ := by rw [hF.ζ, hF.ζ (ρ), pow_succ', mul_smul]
    have e : (F.lnk ρ).τ *ᵥ F.ζ ρ = -((-D.host.xi0) • F.ζ ρ) := by rw [← hz]; exact (F.lnk ρ).map
    have h2 := hl.2
    simp only [dotProduct, Matrix.mulVec, Fintype.sum_unique] at h2
    have b : F.ζ ρ default ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul h2)
    have e1 := congrFun e default
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_unique, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, neg_mul, neg_neg] at e1
    funext i j
    rw [Subsingleton.elim i default, Subsingleton.elim j default]
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    exact mul_right_cancel₀ b e1
  rw [Lnk.κ, hτ, rat_smul, rat_one, Matrix.smul_mul, Matrix.one_mul, smul_smul, ← map_mul,
    mul_inv_cancel₀ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero, map_one, one_smul, GlobalTheory.Unf.LinkGram.ofAdj_starAdj]

end GlobalTheory.KapAdjLine
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardFrameLinkMapInvertsHermitianSkewAdjointStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardFrameLink_map_inverts_hermitianSkewAdjoint : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (x : WO (negSp F.Lz) (G.V (.core (2 * ρ + 1)))), (F.lnk ρ).κ _ (incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj _ _ x) = x := by
  first | exact @GlobalTheory.KapAdjLine.kap_starAdj | exact GlobalTheory.KapAdjLine.kap_starAdj | (intros; apply GlobalTheory.KapAdjLine.kap_starAdj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepLineComponentEqKappaLatticePoint
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.LineComp

theorem star_smul_mem_span : ∀ (D : D7) (n : ℕ) (I J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), D.host.AAbar * I ≤ D.host.AA * J → ∀ a ∈ D.host.AA, ∀ s ∈ idLat I Λ, star a • s ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat J Λ, y = a' • s'} := by
  intro D n I J Λ hIJ a ha s hs
  have hsa : star a ∈ D.host.AAbar := by
    have e : star a = D.host.conj a := by
      first
      | exact GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.bridge_star_holds D.R D.host a
      | exact Formalism.BasicNotions.Examples₂.star_eq_conj D.host a
      | (apply D.host.φ₀.injective
         have h1 : D.host.φ₀ (D.host.conj a) = starRingEnd ℂ (D.host.φ₀ a) := Formalism.HC.HostAx.conjE_apply _ _ _
         rw [h1]
         haveI := D.host.isCMField_hostE
         exact IsCMField.complexEmbedding_complexConj _ _ _)
    rw [e]; exact Formalism.L2.Pj.conj_mem_AAbar D ha
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, y, hy, rfl⟩ := hx
    have hm : star a * c ∈ (D.host.AA * J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :=
      hIJ (FractionalIdeal.mul_mem_mul hsa hc)
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul] at hm
    rw [smul_smul]
    have key : ∀ z ∈ ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E) * (J : Submodule (𝓞 D.host.E) D.host.E)),
        z • y ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat J Λ, y = a' • s'} := by
      intro z hz
      induction hz using Submodule.mul_induction_on' with
      | mem_mul_mem a' ha' j hj =>
        exact Submodule.subset_span ⟨a', ha', j • y, Submodule.subset_span ⟨j, hj, y, hy, rfl⟩, by rw [smul_smul]⟩
      | add x x' _ _ ihx ihy => rw [add_smul]; exact Submodule.add_mem _ ihx ihy
    exact key _ hm
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ r hx

theorem stairRatio_le : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (σ : ℕ), D.host.AAbar * (G.pl.stA sc ^ (σ + 2) * (G.pl.stAbar sc ^ (σ + 2))⁻¹) ≤ D.host.AA * (G.pl.stA sc ^ (σ + 1) * (G.pl.stAbar sc ^ (σ + 1))⁻¹ * shiftId G) := by
  intro D T L sc G σ
  have hA : (D.host.AAbar : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    intro h
    have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rw [h] at h1
    simp at h1
  refine le_of_eq ?_
  simp only [shiftId, Places.stA, Places.stAbar, GridData.modul]
  generalize D.host.AA = a at *
  generalize D.host.AAbar = b at *
  generalize ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = n
  generalize ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = m
  rw [pow_succ (a * n⁻¹) (σ + 1), pow_succ (b * m⁻¹) (σ + 1), mul_inv (_ ^ (σ + 1)), mul_inv b, inv_inv]
  calc b * ((a * n⁻¹) ^ (σ + 1) * (a * n⁻¹) * (((b * m⁻¹) ^ (σ + 1))⁻¹ * (b⁻¹ * m)))
      = (b * b⁻¹) * (a * ((a * n⁻¹) ^ (σ + 1) * ((b * m⁻¹) ^ (σ + 1))⁻¹ * (m * n⁻¹))) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hA, one_mul]

theorem main : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F ρ h).Γ₀,
    ∃ w ∈ lineLat F ρ, ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).2 = (F.lnk ρ).κ _ w := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h u hu
  refine ⟨_, ?_, (GlobalTheory.T.standardFrameLink_map_inverts_hermitianSkewAdjoint D hq T L μ0 hL sc G W M hM F hF ρ _).symm⟩
  cases ρ with
  | zero => exact GlobalTheory.T.besselStepZero_lineComponent_adjoint_mem_lattice D hq T L μ0 hL sc G W M hM F hF h u hu
  | succ σ =>
    exact GlobalTheory.T.hermitianSkewAdjoint_mem_adjoint_homLattice D _ _ _ _ _ _ (star_smul_mem_span D _ _ _ _ (stairRatio_le G σ)) _
      (GlobalTheory.T.bessel_step_line_component_mem_hom_lattice D hq T L μ0 hL sc G W M hM F hF (σ + 1) h u hu)

end GlobalTheory.LineComp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepLineComponentEqKappaLatticePointStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselStep_lineComponent_eq_kappa_lattice_point : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F ρ h).Γ₀, ∃ w ∈ lineLat F ρ, ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).2 = (F.lnk ρ).κ _ w := by
  exact @GlobalTheory.LineComp.main
end
