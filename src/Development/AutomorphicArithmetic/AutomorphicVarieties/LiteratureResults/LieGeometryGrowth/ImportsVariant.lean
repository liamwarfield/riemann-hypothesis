module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.G2Assumption

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsDecP
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsPbSz
open UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.pbSz :
    PbSz := by
  intro V F _ _ _ _ _ _ q k c
  obtain ⟨hAcd, C2, hC2⟩ := altSz V F q k (1 + c)
  obtain ⟨C1, hC1, hcomp1⟩ := compSz V V (V [⋀^Fin q]→L[ℝ] F) k (1 + c)
  obtain ⟨C3, hC3, hcomp3⟩ := compSz V (V →L[ℝ] V)
    ((V [⋀^Fin q]→L[ℝ] F) →L[ℝ] (V [⋀^Fin q]→L[ℝ] F)) k (1 + c)
  refine ⟨2 ^ k * (C3 * max C2 0) * C1, by positivity, ?_⟩
  intro W t w p b ht hW hWs hw hws
  obtain ⟨hF1, hF2, hF3, hF4⟩ := flowSz V k c W t p ht hW hWs
  have hg := hcomp1 w (UpperTheory.V.Lit.Geo.flow W t) p b hF1 hw
    (fun i h1 h2 => hF4 i h1 (by omega)) hws
  have hL : ‖fderiv ℝ (UpperTheory.V.Lit.Geo.flow W t) p‖ ≤ 1 + c := by
    simpa using hF3 0 (Nat.zero_le _)
  have hA : Sz k _ (fderiv ℝ (UpperTheory.V.Lit.Geo.flow W t) p) (max C2 0) :=
    fun i hi => (hC2 _ hL i hi).trans (le_max_left _ _)
  have hf := hcomp3 _ (fderiv ℝ (UpperTheory.V.Lit.Geo.flow W t)) p (max C2 0) hF2
    hAcd.contDiffAt (fun i h1 h2 => hF3 i h2) hA
  have hprod := (appSz V (V [⋀^Fin q]→L[ℝ] F) (V [⋀^Fin q]→L[ℝ] F) k p).1 _ _ _ _
    (hAcd.contDiffAt.comp p hF2) (hw.comp p hF1) hf hg
  have e : 2 ^ k * (C3 * max C2 0) * C1 * b = 2 ^ k * (C3 * max C2 0) * (C1 * b) := by ring
  rw [e]
  exact hprod
end

open UpperTheory.V.Lit.Geo

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor in
open scoped ContDiff Topology in
theorem UpperTheory.V.Lit.Geo.Cs.decP :
    UpperTheory.V.Lit.Geo.Cs.DecP := by
  intro E _ _ _ a ho U Ξ f Y C c f₀ hS W hW lam hl q k B hB
  obtain ⟨hfl, hflow⟩ := fieldFlow E a ho U Ξ Y C hS.fld W hW
  obtain ⟨c₁, hc₁⟩ := Cs.zwSz E a U Y C hS.fld W hW (k + 1)
  obtain ⟨C₁, hC₁, hpb⟩ := Cs.pbSz (HV E a) (Fin Ξ.d → ℂ) q k c₁
  obtain ⟨D₁, hD₁, hmv⟩ := Cs.move E a ho U Ξ q k C
  obtain ⟨B₁, hB₁⟩ := hl.bdd C
  refine ⟨C₁ * D₁ * Real.exp (B * B₁), by positivity, fun A M hA hM w hw g x hg => ?_⟩
  obtain ⟨hF, hfe, hops⟩ := Cs.twOps E a ho U Ξ W hfl g x
  obtain ⟨hsm, hpe⟩ := (hops q).1 w
  obtain ⟨h, hh, hb⟩ := hS.root (Cs.pt g x) 1 (by simp)
  have hone : hOne E a ∈ cone E a := hOne_mem_cone
  have hpt : flow (Cs.Zw U W g x) 1 (hOne E a) = sand h (hOne E a) := by
    rw [hfe, hflow g h x 1 hh, ← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel_left]
  have hup : f (Cs.pt g x) + c ≤ f (Cs.pt (g * h) x) := by
    rw [Cs.pt_mul]
    exact hS.up _ h hg (by rw [hh, one_smul])
  have hlam : |lam (Cs.pt (g * h) x)| ≤ |lam (Cs.pt g x)| + B₁ := by
    rw [Cs.pt_mul, hl.add]
    exact (abs_add_le _ _).trans (add_le_add le_rfl (hB₁ h hb))
  have h1 := hmv w g x h _ hb (hw (g * h) x (by linarith [hS.c_pos]))
  rw [← hpt] at h1
  have hmem : flow (Cs.Zw U W g x) 1 (hOne E a) ∈ cone E a := hF.2 _ hone 1 ⟨zero_le_one, le_rfl⟩
  have h2 := hpb (Cs.Zw U W g x) 1 (Cs.Tw U Ξ w.1 g x) (hOne E a) _ (by simp)
    (hF.1.contDiffAt (ho.mem_nhds hone)) (hc₁ g x) (hsm.contDiffAt (ho.mem_nhds hmem)) h1
  refine (h2.congr (Filter.eventuallyEq_of_mem (ho.mem_nhds hone) fun p hp => (hpe p hp).symm)).mono ?_
  have he : Real.exp (B * |lam (Cs.pt (g * h) x)| - A * f (Cs.pt (g * h) x)) ≤
      Real.exp (B * B₁) * Real.exp (-(A * c)) * Real.exp (B * |lam (Cs.pt g x)| - A * f (Cs.pt g x)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith [mul_le_mul_of_nonneg_left hlam hB, mul_le_mul_of_nonneg_left hup hA]
  calc _ = C₁ * D₁ * M * Real.exp (B * |lam (Cs.pt (g * h) x)| - A * f (Cs.pt (g * h) x)) := by ring
    _ ≤ C₁ * D₁ * M * (Real.exp (B * B₁) * Real.exp (-(A * c)) *
        Real.exp (B * |lam (Cs.pt g x)| - A * f (Cs.pt g x))) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Imports
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsLocBd
open UpperTheory.V.Lit.Geo.Cs
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr Filter Topology

theorem UpperTheory.V.Lit.Geo.Cs.locBd :
    LocBd := by
  intro E _ _ a p₀ hp
  obtain ⟨τ, h1, h2⟩ := locSec E a p₀ hp
  have c1 : ContinuousAt (fun p => toL (τ p).val) p₀ := h1.continuousAt
  have c1' : ContinuousAt (fun p => ((τ p).val : Matrix (Fin a) (Fin a) (Cinf E))) p₀ := c1
  have hi : ContinuousAt (Inv.inv : Matrix (Fin a) (Fin a) (Cinf E) → _) (τ p₀).val := by
    apply continuousAt_matrix_inv
    have := NormedRing.inverse_continuousAt (GeneralLinearGroup.det (τ p₀))
    simpa using this
  have c2' : ContinuousAt (fun p => (((τ p)⁻¹).val : Matrix (Fin a) (Fin a) (Cinf E))) p₀ := by
    have := ContinuousAt.comp (f := fun p => ((τ p).val : Matrix (Fin a) (Fin a) (Cinf E))) hi c1'
    simpa only [Matrix.coe_units_inv, Function.comp_def] using this
  have c2 : ContinuousAt (fun p => toL ((τ p)⁻¹).val) p₀ := c2'
  refine ⟨max (‖toL (τ p₀).val‖ + 1) (‖toL ((τ p₀)⁻¹).val‖ + 1), ?_⟩
  filter_upwards [h2, c1.norm.eventually_lt_const (lt_add_one _), c2.norm.eventually_lt_const (lt_add_one _)]
    with p e b1 b2
  exact ⟨τ p, ⟨b1.le.trans (le_max_left _ _), b2.le.trans (le_max_right _ _)⟩, e⟩
end

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Geo.Cs
open scoped Topology

theorem UpperTheory.V.Lit.Geo.Cs.loc :
    UpperTheory.V.Lit.Geo.Cs.Loc := by
  intro E _ _ _ a ho U Ξ f lam hf hl Φ hD hΦ q k A B R hA hB s p hp hR
  obtain ⟨c, hc⟩ := UpperTheory.V.Lit.Geo.Cs.locBd E a p hp
  obtain ⟨D, hD0, hmv⟩ := UpperTheory.V.Lit.Geo.Cs.move E a ho U Ξ q k c
  obtain ⟨B₀, hB₀⟩ := hl.bdd c
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective s
  have hcont : ContinuousAt (Φ (y : GL (Fin a) (Af E) ⧸ U)) p :=
    ((hΦ.1 _).continuousOn.continuousAt (ho.mem_nhds hp))
  have hev : ∀ᶠ x in 𝓝 p, R < Φ (y : GL (Fin a) (Af E) ⧸ U) x := hcont.eventually (lt_mem_nhds hR)
  refine ⟨_, hc.and hev, D * Real.exp (B * (B₀ + |lam (finGL E a y)|)), fun M hM w hw x hx => ?_⟩
  obtain ⟨⟨h, hh, rfl⟩, hx⟩ := hx
  rw [hD h y] at hx
  have h1 := hw h y hx.le
  have h2 := hmv w 1 y h _ hh (by rw [one_mul]; exact h1)
  rw [Tw_one] at h2
  refine h2.mono ?_
  rw [mul_assoc, mul_comm _ M]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM) hD0
  have h3 : |lam (pt h y)| ≤ B₀ + |lam (finGL E a y)| := by
    rw [pt, hl.add]
    exact (abs_add_le _ _).trans (add_le_add (hB₀ h hh) le_rfl)
  have h4 := mul_nonneg hA (hf (pt h y))
  have h5 := mul_le_mul_of_nonneg_left h3 hB
  linarith
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsCorrSz
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsCorrForm
open UpperTheory.V.Lit.Geo.Cs
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct ContDiff Topology

private theorem ev_eq_cmp {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a d : ℕ}
    (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) (g : GA E a) : ev m g j = (UpperTheory.V.Lit.Bor.cmp j m).1 g := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul φ v => simp [mul_comm]

private theorem alt_expand {V W M : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup M] [Module ℝ M] {q n : ℕ} (α : V [⋀^Fin q]→ₗ[ℝ] M) (e : V ≃ₗ[ℝ] W) (b : Module.Basis (Fin n) ℝ W)
    (u : Fin q → W) :
    α (fun i => e.symm (u i)) = ∑ I : Fin q → Fin n, (∏ i, b.repr (u i) (I i)) • α fun i => e.symm (b (I i)) := by
  have h : (fun i => e.symm (u i)) = fun i => ∑ k, b.repr (u i) k • e.symm (b k) := by
    funext i
    conv_lhs => rw [← b.sum_repr (u i)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  rw [h]
  refine (α.toMultilinearMap.map_sum (fun i k => b.repr (u i) k • e.symm (b k))).trans ?_
  exact Finset.sum_congr rfl fun I _ => α.map_smul_univ _ _

theorem UpperTheory.V.Lit.Geo.Cs.corrForm :
    CorrForm := by
  intro E _ _ _ a Ξ q v
  classical
  obtain ⟨τ, h1, hτ, -, -, hi, hs⟩ := secOne E a
  let b := Module.finBasis ℝ (HV E a)
  let u : HV E a → Fin q → HV E a := fun p i => (2 : ℝ)⁻¹ • sand (τ p)⁻¹ (v i)
  refine ⟨(Fin q → Fin (Module.finrank ℝ (HV E a))) × Fin Ξ.d, inferInstance,
    fun I i => hv.symm (b (I.1 i)), fun I => I.2,
    fun I p k => ((∏ i, b.repr (u p i) (I.1 i) : ℝ) : ℂ) * Ξ.mat (τ p) k I.2,
    fun p => toL (τ p).val, by simp only [h1]; rfl, hτ, fun I => ?_, fun U α w hc g x => ?_⟩
  · refine contDiffAt_pi.2 fun k => ContDiffAt.mul ?_ ?_
    · refine Complex.ofRealCLM.contDiff.contDiffAt.comp (hOne E a)
        (f := fun p => ∏ i, b.repr (u p i) (I.1 i)) ?_
      refine contDiffAt_prod fun i _ => ?_
      have hu : ContDiffAt ℝ ∞ (fun p => u p i) (hOne E a) := (hi.clm_apply contDiffAt_const).const_smul _
      exact (LinearMap.toContinuousLinearMap (b.coord (I.1 i))).contDiff.contDiffAt.comp (hOne E a) hu
    · have := (((matSmooth E a Ξ k I.2).1).contDiffAt
          (isOpen_invSet.mem_nhds (val_mem_invSet (τ (hOne E a))))).comp (hOne E a) hτ
      simpa only [Function.comp_def, extGL_val] using this
  · refine hs.mono fun p hp => ?_
    have e1 : sand (g * τ p) (hOne E a) = sand g p := by
      rw [map_mul, ContinuousLinearMap.mul_apply, hp]
    have e2 : ∀ i, (2 : ℝ) • sand (g * τ p) (u p i) = sand g (v i) := fun i => by
      simp only [u, map_smul, smul_smul]
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel_right]
      simp
    have h := hc (g * τ p) x fun i => hv.symm (u p i)
    simp only [LinearEquiv.apply_symm_apply, e1, e2] at h
    have e3 : infGL E a (g * τ p) * finGL E a x = pt g x * infGL E a (τ p) := pt_mul g (τ p) x
    simp only [Tw, tp_apply, mulVecL_apply, h, e3, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel_left, chart_val]
    rw [alt_expand α hv b (u p)]
    funext k
    have e4 : ∀ (I : Fin q → Fin (Module.finrank ℝ (HV E a))) (r : ℝ) (y : GA E a),
        ev (r • α fun i => hv.symm (b (I i))) y = (r : ℂ) • ev (α fun i => hv.symm (b (I i))) y := fun I r y => by
      rw [← algebraMap_smul ℂ r, map_smul]; rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [Finset.sum_apply, e4, Matrix.mulVec, dotProduct, Pi.smul_apply, ← ev_eq_cmp,
      Fintype.sum_prod_type, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun j _ => ?_
    ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsAltEv
open UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.altEv :
    AltEv := by
  classical
  intro V F _ _ _ _ _ _ q k
  let bs := Module.finBasis ℝ V
  let L : (V [⋀^Fin q]→L[ℝ] F) →ₗ[ℝ] ((Fin q → Fin (Module.finrank ℝ V)) → F) :=
    { toFun := fun g σ => g (fun i => bs (σ i))
      map_add' := fun g h => by ext σ; simp
      map_smul' := fun c g => by ext σ; simp }
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro g hg
    have e : g.toAlternatingMap = (0 : V [⋀^Fin q]→L[ℝ] F).toAlternatingMap :=
      Module.Basis.ext_alternating bs (fun v _ => by simpa [L] using congrFun hg v)
    ext m
    simpa using DFunLike.congr_fun e m
  obtain ⟨M, hM⟩ := L.exists_leftInverse_of_injective hker
  let A : (Fin q → Fin (Module.finrank ℝ V)) → F →L[ℝ] (V [⋀^Fin q]→L[ℝ] F) := fun σ =>
    LinearMap.toContinuousLinearMap (M.comp (LinearMap.single ℝ (fun _ => F) σ))
  refine ⟨Finset.univ.image (fun σ : Fin q → Fin (Module.finrank ℝ V) => fun i => bs (σ i)),
    ∑ σ, ‖A σ‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩
  intro f x b hb hcd hsz
  have mem : ∀ σ : Fin q → Fin (Module.finrank ℝ V),
      (fun i => bs (σ i)) ∈ Finset.univ.image (fun σ : Fin q → Fin (Module.finrank ℝ V) =>
        fun i => bs (σ i)) :=
    fun σ => Finset.mem_image_of_mem _ (Finset.mem_univ σ)
  have hrep : f = fun y => ∑ σ, A σ (f y (fun i => bs (σ i))) := by
    funext y
    calc f y = M (L (f y)) := (LinearMap.congr_fun hM (f y)).symm
      _ = M (∑ σ, Pi.single σ (L (f y) σ)) := by rw [Finset.univ_sum_single]
      _ = ∑ σ, A σ (f y (fun i => bs (σ i))) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        rfl
  intro i hi
  have hcdi : ∀ σ : Fin q → Fin (Module.finrank ℝ V),
      ContDiffAt ℝ i (fun y => f y (fun i => bs (σ i))) x :=
    fun σ => (hcd _ (mem σ)).of_le (by exact_mod_cast le_top)
  have hsum := iteratedFDeriv_fun_sum_apply (𝕜 := ℝ) (n := i) (x := x) (u := Finset.univ)
    (f := fun σ y => A σ (f y (fun i => bs (σ i))))
    (fun σ _ => (A σ).contDiff.contDiffAt.comp x (hcdi σ))
  rw [hrep, hsum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
  refine ((A σ).norm_iteratedFDeriv_comp_left (hcdi σ) le_rfl).trans ?_
  exact mul_le_mul_of_nonneg_left (hsz _ (mem σ) i hi) (norm_nonneg _)
end

open UpperTheory.V.Lit.Geo

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct ContDiff Topology

namespace UpperTheory.V.Lit.Geo.Cs

private theorem term_sz {V W F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (k : ℕ) (τ : V → W) (Θ : V → F) (p : V)
    (hτ : ContDiffAt ℝ ∞ τ p) (hΘ : ContDiffAt ℝ ∞ Θ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : W → ℂ) (b : ℝ), ContDiffAt ℝ ∞ u (τ p) → Sz k u (τ p) b →
      Sz k (fun y => u (τ y) • Θ y) p (C * b) := by
  obtain ⟨c, hc⟩ := exists_sz k τ p
  obtain ⟨t, ht⟩ := exists_sz k Θ p
  obtain ⟨C, hC, H⟩ := compSz V W ℂ k c
  let L : ℂ →L[ℝ] F →L[ℝ] F := ContinuousLinearMap.lsmul ℝ ℂ
  refine ⟨2 ^ k * (‖L‖ * C) * t, by have := ht.nonneg; positivity, fun u b hu hb => ?_⟩
  have h1 := H u τ p b hτ hu (fun i _ hi => hc i hi) hb
  have s1 : ContDiffAt ℝ ∞ (fun y => u (τ y)) p := hu.comp p hτ
  have h2 := (appSz V ℂ (F →L[ℝ] F) k p).2.1 L _ _ s1 h1
  have s2 : ContDiffAt ℝ ∞ (fun y => L (u (τ y))) p := L.contDiff.contDiffAt.comp p s1
  have h3 := (appSz V F F k p).1 _ Θ _ _ s2 hΘ h2 ht
  exact h3.mono (le_of_eq (by ring))

private theorem val_sz (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (q : ℕ) (α : Co Ξ q) (w : Fm U Ξ q) (hw : Corr U Ξ α w) (ρ : GA E a → ℝ) (hρ : ∀ g, 0 ≤ ρ g)
    (hb : ∀ (X : Fin q → Herm E a) (j : Fin Ξ.d) (l : List (Lie E a)), ∃ M : ℝ, ∀ g,
      ‖((l.map (lie E a)).prod (Bor.cmp j (α X))).1 g‖ ≤ M * ρ g) (k : ℕ) (v : Fin q → HV E a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ g x, ContDiffAt ℝ ∞ (fun p => Tw U Ξ w g x p v) (hOne E a) ∧
      Sz k (fun p => Tw U Ξ w g x p v) (hOne E a) (M * ρ (pt g x)) := by
  obtain ⟨ι, _, X, j, Θ, τ, h1, hτ, hΘ, H⟩ := corrForm E a Ξ q v
  choose C hC HC using fun i => term_sz k τ (Θ i) (hOne E a) hτ (hΘ i)
  choose D hD HD using fun i => chartSz E a k ρ hρ (Bor.cmp (j i) (α (X i))) (hb (X i) (j i))
  refine ⟨∑ i, C i * D i, Finset.sum_nonneg fun i _ => mul_nonneg (hC i) (hD i), fun g x => ?_⟩
  have e := H U α w hw g x
  have su : ∀ i, ContDiffAt ℝ ∞ (chart (Bor.cmp (j i) (α (X i))).1 (pt g x)) (τ (hOne E a)) := fun i => by
    rw [h1]; exact contDiffAt_chart (Bor.cmp (j i) (α (X i))).2 _ isUnit_one
  have st : ∀ i, ContDiffAt ℝ ∞ (fun p => chart (Bor.cmp (j i) (α (X i))).1 (pt g x) (τ p) • Θ i p) (hOne E a) :=
    fun i => ((su i).comp _ hτ).smul (hΘ i)
  refine ⟨(ContDiffAt.sum fun i _ => st i).congr_of_eventuallyEq e, ?_⟩
  have := (appSz (HV E a) ℝ (Fin Ξ.d → ℂ) k (hOne E a)).2.2 ι Finset.univ _ _ (fun i _ => st i)
    (fun i _ => HC i _ (D i * ρ (pt g x)) (su i) (by rw [h1]; exact HD i _))
  refine (this.congr e.symm).mono (le_of_eq ?_)
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

end UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.corrSz :
    UpperTheory.V.Lit.Geo.Cs.CorrSz := by
  intro E _ _ _ a U Ξ q α w hw ρ hρ hb k
  obtain ⟨T, C, hC, H⟩ := Cs.altEv (HV E a) (Fin Ξ.d → ℂ) q k
  choose M hM HM using Cs.val_sz E a U Ξ q α w hw ρ hρ hb k
  have h0 : 0 ≤ ∑ v ∈ T, M v := Finset.sum_nonneg fun v _ => hM v
  refine ⟨C * ∑ v ∈ T, M v, mul_nonneg hC h0, fun g x => ?_⟩
  rw [mul_assoc]
  exact H _ _ _ (mul_nonneg h0 (hρ _)) (fun v _ => (HM v g x).1) fun v hv => (HM v g x).2.mono
    (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun v _ => hM v) hv) (hρ _))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsGeoSum
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsSumSm
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff Topology

private theorem sz_fderiv {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {k : ℕ} {f : V → F} {x : V} {b : ℝ} (h : Sz (k + 1) f x b) : Sz k (fderiv ℝ f) x b :=
  fun i hi => by
    rw [norm_iteratedFDeriv_fderiv]
    exact h (i + 1) (Nat.succ_le_succ hi)

private theorem sum_deriv {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {Y : Set V} (hY : IsOpen Y) {y : ℕ → V → F}
    (hy : ∀ j, ContDiffOn ℝ ∞ (y j) Y)
    (hb : ∀ k, ∀ p ∈ Y, ∃ N ∈ 𝓝 p, ∃ b : ℕ → ℝ, Summable b ∧ ∀ j, ∀ x ∈ N, Sz k (y j) x (b j))
    {p : V} (hp : p ∈ Y) :
    Summable (fun j => fderiv ℝ (y j) p) ∧
      HasFDerivAt (fun x => ∑' j, y j x) (∑' j, fderiv ℝ (y j) p) p := by
  obtain ⟨N, hN, b, hs, hle⟩ := hb 1 p hp
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hN (hY.mem_nhds hp))
  have hpN : p ∈ N := mem_of_mem_nhds hN
  have h1 : ∀ j, ∀ x ∈ N, ‖fderiv ℝ (y j) x‖ ≤ b j := fun j x hx => (sz_fderiv (k := 0) (hle j x hx)).norm_le
  refine ⟨Summable.of_norm_bounded hs fun j => h1 j p hpN, ?_⟩
  refine hasFDerivAt_tsum_of_isPreconnected (u := b) (s := Metric.ball p r) (f := y)
    (f' := fun j x => fderiv ℝ (y j) x) (x₀ := p) hs Metric.isOpen_ball (convex_ball p r).isPreconnected
    (fun j x hx => ?_) (fun j x hx => h1 j x (hball hx).1) (Metric.mem_ball_self hr) ?_ (Metric.mem_ball_self hr)
  · exact (((hy j).contDiffAt (hY.mem_nhds (hball hx).2)).differentiableAt (by simp)).hasFDerivAt
  · exact Summable.of_norm_bounded hs fun j => (hle j p hpN).norm_le

private theorem sum_smooth {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Y : Set V} (hY : IsOpen Y) (n : ℕ) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (y : ℕ → V → F),
    (∀ j, ContDiffOn ℝ ∞ (y j) Y) →
    (∀ k, ∀ p ∈ Y, ∃ N ∈ 𝓝 p, ∃ b : ℕ → ℝ, Summable b ∧ ∀ j, ∀ x ∈ N, Sz k (y j) x (b j)) →
    ContDiffOn ℝ n (fun x => ∑' j, y j x) Y := by
  induction n with
  | zero =>
    intro F _ _ _ y hy hb
    simp only [CharP.cast_eq_zero, Nat.cast_zero, contDiffOn_zero]
    exact fun p hp => (sum_deriv hY hy hb hp).2.continuousAt.continuousWithinAt
  | succ n ih =>
    intro F _ _ _ y hy hb
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hY]
    refine ⟨fun p hp => (sum_deriv hY hy hb hp).2.differentiableAt.differentiableWithinAt, by simp, ?_⟩
    have h := ih (V →L[ℝ] F) (fun j => fderiv ℝ (y j))
      (fun j => (hy j).fderiv_of_isOpen hY (by simp)) (fun k p hp => by
        obtain ⟨N, hN, b, hs, hle⟩ := hb (k + 1) p hp
        exact ⟨N, hN, b, hs, fun j x hx => sz_fderiv (hle j x hx)⟩)
    exact h.congr fun p hp => (sum_deriv hY hy hb hp).2.fderiv

theorem UpperTheory.V.Lit.Geo.Cs.sumSm :
    SumSm := by
  intro V F _ _ _ _ _ Y hY y hy hb
  refine ⟨contDiffOn_infty.2 fun n => sum_smooth hY n F y hy hb, fun p hp => ?_⟩
  rw [(sum_deriv hY hy hb hp).2.fderiv]
  exact (sum_deriv hY hy hb hp).1.hasSum
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsGeoCut
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff Topology

theorem UpperTheory.V.Lit.Geo.Cs.geoCut :
    GeoCut := by
  intro Γ V S _ _ _ _ d G Φ hΦ R q η hη hinv
  classical
  set χ : ℝ → ℝ := fun t => Real.smoothTransition (2 * (t - R) - 1) with hχ
  have hχc : ContDiff ℝ ∞ χ :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul (contDiff_id.sub contDiff_const)).sub contDiff_const)
  have hχ0 : ∀ t, t ≤ R + 1 / 2 → χ t = 0 := fun t ht =>
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hχ1 : ∀ t, R + 1 ≤ t → χ t = 1 := fun t ht =>
    Real.smoothTransition.one_of_one_le (by linarith)
  let f : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ) :=
    fun s p => if p ∈ G.Y ∧ R < Φ s p then χ (Φ s p) • η s p else 0
  have hf : f ∈ G.Om q := by
    show ∀ s, ContDiffOn ℝ ∞ (f s) G.Y ∧ ∀ p ∉ G.Y, f s p = 0
    refine fun s => ⟨?_, fun p hp => by simp [f, hp]⟩
    apply contDiffOn_of_locally_contDiffOn
    intro p hp
    by_cases hR : R < Φ s p
    · refine ⟨G.Y ∩ Φ s ⁻¹' Set.Ioi R, (hΦ.1 s).continuousOn.isOpen_inter_preimage G.isOpen isOpen_Ioi,
        ⟨hp, hR⟩, ?_⟩
      have hsm : ContDiffOn ℝ ∞ (fun x => χ (Φ s x) • η s x) (G.Y ∩ (G.Y ∩ Φ s ⁻¹' Set.Ioi R)) :=
        ((hχc.comp_contDiffOn (hΦ.1 s)).mono (fun x (hx : x ∈ G.Y ∩ (G.Y ∩ Φ s ⁻¹' Set.Ioi R)) => hx.1)).smul
          ((hη s).mono (fun x (hx : x ∈ G.Y ∩ (G.Y ∩ Φ s ⁻¹' Set.Ioi R)) => ⟨hx.2.1, hx.2.2⟩))
      refine hsm.congr (fun x hx => ?_)
      have hx' : x ∈ G.Y ∧ R < Φ s x := ⟨hx.2.1, hx.2.2⟩
      simp only [f, if_pos hx']
    · push_neg at hR
      refine ⟨G.Y ∩ Φ s ⁻¹' Set.Iio (R + 1 / 2),
        (hΦ.1 s).continuousOn.isOpen_inter_preimage G.isOpen isOpen_Iio,
        ⟨hp, show Φ s p < R + 1 / 2 by linarith⟩, ?_⟩
      refine (contDiffOn_const (c := (0 : V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)))).congr (fun x hx => ?_)
      have hx2 : Φ s x < R + 1 / 2 := hx.2.2
      simp only [f]
      split_ifs with h
      · rw [hχ0 _ hx2.le, zero_smul]
      · rfl
  refine ⟨⟨f, hf⟩, ?_, ?_⟩
  · intro γ
    apply Subtype.ext
    funext s p
    show G.tr q γ (f (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p)) = f s p
    have hρ : ∀ x, G.ρ γ (G.ρ γ⁻¹ x) = x := by
      intro x
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    by_cases hp : p ∈ G.Y
    · have hp' : G.ρ γ⁻¹ p ∈ G.Y := G.maps _ _ hp
      have hΦ' : Φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) = Φ s p := hΦ.2.1 γ⁻¹ s p hp
      by_cases hR : R < Φ s p
      · have h1 : G.ρ γ⁻¹ p ∈ G.Y ∧ R < Φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) := ⟨hp', by rw [hΦ']; exact hR⟩
        have h2 : p ∈ G.Y ∧ R < Φ s p := ⟨hp, hR⟩
        simp only [f, if_pos h1, if_pos h2]
        rw [hΦ', map_smul, hinv γ s p hp hR]
      · have h1 : ¬ (G.ρ γ⁻¹ p ∈ G.Y ∧ R < Φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p)) := by
          rw [hΦ']
          exact fun h => hR h.2
        have h2 : ¬ (p ∈ G.Y ∧ R < Φ s p) := fun h => hR h.2
        simp only [f, if_neg h1, if_neg h2, map_zero]
    · have hp' : G.ρ γ⁻¹ p ∉ G.Y := fun h => hp (by simpa [hρ] using G.maps γ _ h)
      have h1 : ¬ (G.ρ γ⁻¹ p ∈ G.Y ∧ R < Φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p)) := fun h => hp' h.1
      have h2 : ¬ (p ∈ G.Y ∧ R < Φ s p) := fun h => hp h.1
      simp only [f, if_neg h1, if_neg h2, map_zero]
  · intro s p hp h1
    have h2 : p ∈ G.Y ∧ R < Φ s p := ⟨hp, by linarith⟩
    show f s p = η s p
    simp only [f, if_pos h2, hχ1 _ h1, one_smul]
end

open UpperTheory.V.Lit.Geo.Cs
open scoped Topology ContDiff

theorem UpperTheory.V.Lit.Geo.Cs.geoSum :
    GeoSum := by
  intro Γ V S _ _ _ _ d G Φ hΦ R q y w hy hdy hsz hw
  have hopen : ∀ s, IsOpen {p | p ∈ G.Y ∧ R < Φ s p} := fun s =>
    (hΦ.1 s).continuousOn.isOpen_inter_preimage G.isOpen isOpen_Ioi
  have hmem : ∀ j s, ContDiffOn ℝ ∞ ((y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) G.Y :=
    fun j s => ((y j).2 s).1
  have hsm : ∀ s,
      ContDiffOn ℝ ∞ (fun x => ∑' j, (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x)
        {p | p ∈ G.Y ∧ R < Φ s p} ∧
      ∀ p ∈ {p | p ∈ G.Y ∧ R < Φ s p},
        HasSum (fun j => fderiv ℝ ((y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) p)
          (fderiv ℝ (fun x => ∑' j, (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x) p) :=
    fun s => sumSm V _ _ (hopen s) (fun j x => (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x)
      (fun j => (hmem j s).mono (fun p hp => hp.1)) (fun k p hp => hsz k s p hp.1 hp.2)
  have hsumv : ∀ s, ∀ p ∈ G.Y, R < Φ s p →
      Summable (fun j => (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p) := by
    intro s p hp hR
    obtain ⟨N, hN, b, hb, hbd⟩ := hsz 0 s p hp hR
    refine Summable.of_norm_bounded hb (fun j => ?_)
    have h0 := hbd j p (mem_of_mem_nhds hN) 0 le_rfl
    simpa using h0
  obtain ⟨z, hzinv, hz⟩ := geoCut Γ V S d G Φ hΦ R q
    (fun s p => -∑' j, (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p)
    (fun s => (hsm s).1.neg) (by
      intro γ s p hp hR
      have hp2 : (G.ρ γ⁻¹) p ∈ G.Y := G.maps _ p hp
      have hR2 : R < Φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) := by rw [hΦ.2.1 γ⁻¹ s p hp]; exact hR
      simp only [map_neg]
      congr 1
      rw [ContinuousLinearMap.map_tsum _ (hsumv _ _ hp2 hR2)]
      congr 1
      funext j
      exact congrFun (congrFun (congrArg Subtype.val (hy j γ)) s) p)
  refine ⟨z, hzinv, fun s p hp hR => ?_⟩
  have hev : (z : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s =ᶠ[𝓝 p]
      (fun x => -∑' j, (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x) := by
    have hc : ContinuousAt (Φ s) p := (hΦ.1 s).continuousOn.continuousAt (G.isOpen.mem_nhds hp)
    filter_upwards [G.isOpen.mem_nhds hp, Filter.Tendsto.eventually hc (lt_mem_nhds hR)]
      with x hx hx'
    exact hz s x hx hx'.le
  have hp' : p ∈ {p | p ∈ G.Y ∧ R < Φ s p} := ⟨hp, by linarith⟩
  have hD := ((hsm s).2 p hp').mapL (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V (Fin d → ℂ))
  have hterm : ∀ j, ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V (Fin d → ℂ)
      (fderiv ℝ ((y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) p) =
      (w (j + 1) : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p -
        (w j : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p := by
    intro j
    have h1 := congrFun (congrFun (congrArg Subtype.val (hdy j)) s) p
    rw [ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
    change _ = ((w (j + 1) - w j : G.Om (q + 1)) : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p
    rw [← h1]
    show _ = G.Y.indicator (extDeriv ((y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s)) p
    rw [Set.indicator_of_mem hp]
    rfl
  have hL : ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V (Fin d → ℂ)
      (fderiv ℝ (fun x => ∑' j, (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x) p) =
      -(w 0 : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p := by
    have ht := hD.tendsto_sum_nat
    simp_rw [hterm, Finset.sum_range_sub
      (fun j => (w j : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p)] at ht
    have ht2 := (hw s p hp (by linarith)).sub_const
      ((w 0 : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p)
    rw [zero_sub] at ht2
    exact tendsto_nhds_unique ht ht2
  show G.Y.indicator (extDeriv ((z : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s)) p = _
  rw [Set.indicator_of_mem hp, hev.extDeriv_eq]
  show ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ
    (-(fun x => ∑' j, (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x)) p) = _
  rw [fderiv_neg, ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply, map_neg, hL, neg_neg]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsRapidAll
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsRapidEig
open UpperTheory.V.Lit.Geo.Cs
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct

section
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem one_comm (X : Lie E a) (φ : Sm E a) :
    lie E a (oneL E a) (lie E a X φ) = lie E a X (lie E a (oneL E a) φ) := by
  have h := lie_comm (oneL E a) X
  have e : Matrix.of (oneL E a) * Matrix.of X = Matrix.of X * Matrix.of (oneL E a) :=
    (one_mul (Matrix.of X)).trans (mul_one (Matrix.of X)).symm
  rw [e, sub_self, sub_eq_zero] at h
  exact LinearMap.congr_fun h φ

private theorem eig_prod (c : ℂ) (φ : Sm E a) (h : lie E a (oneL E a) φ = c • φ) (l : List (Lie E a)) :
    lie E a (oneL E a) ((l.map (lie E a)).prod φ) = c • (l.map (lie E a)).prod φ := by
  induction l with
  | nil => simpa using h
  | cons X l ih => rw [List.map_cons, List.prod_cons, Module.End.mul_apply, one_comm, ih, map_smul]

private theorem cmp_rTensor {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (j : Fin d) (T : Module.End ℂ W)
    (m : W ⊗[ℂ] (Fin d → ℂ)) : Bor.cmp j (T.rTensor _ m) = T (Bor.cmp j m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul φ v => rw [LinearMap.rTensor_tmul, cmp_tmul, cmp_tmul, map_smul]

private theorem cmp_prod (Ξ : AlgRep E a) (j : Fin Ξ.d) (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) (l : List (Lie E a)) :
    Bor.cmp j ((l.map (smA Ξ)).prod m) = (l.map (lie E a)).prod (Bor.cmp j m) := by
  induction l with
  | nil => simp
  | cons X l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, smA_apply, cmp_rTensor, ih, List.map_cons, List.prod_cons,
      Module.End.mul_apply]

private theorem ev_eq {d : ℕ} (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) (g : GA E a) : ev m g j = (Bor.cmp j m).1 g := by
  induction m using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero]
    rfl
  | tmul φ v => simp [mul_comm]
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), Pi.add_apply, Pi.add_apply, Submodule.coe_add, Pi.add_apply, hx, hy]

end

theorem UpperTheory.V.Lit.Geo.Cs.rapidEig :
    RapidEig := by
  intro E _ _ _ a U Ξ r hr q α hα X j l
  refine ⟨eig_prod _ _ ?_ l, fun g => by rw [ev_eq, cmp_prod]⟩
  have h : Bor.cmp j (α X) ∈ LinearMap.eqLocus (lie E a (oneL E a)) (-(r : ℂ) • LinearMap.id) :=
    mem_tens.1 (span_le_tens (fun φ hφ => hφ.2.2 _ hr) (hα.val X)) j
  exact h
end

open UpperTheory.V.Lit.Geo.Cs

private theorem le_div_one_add_pow_succ_of_mul_le {x K Q A C F : ℝ} {N : ℕ} (hQ : 1 ≤ Q) (hA : 0 ≤ A) (hN : A * C ≤ N)
    (hF : F ≤ C * (1 + Real.log Q)) (hx : 0 ≤ x) (h : x * Q ^ N ≤ K) :
    x ≤ K * Real.exp (A * C) * Real.exp (-(A * F)) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le one_pos hQ
  have hl : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hp : Q ^ N = Real.exp (N * Real.log Q) := by
    rw [Real.exp_nat_mul, Real.exp_log hQ0]
  have h1 : A * F - A * C ≤ N * Real.log Q := by
    have := mul_le_mul_of_nonneg_left hF hA
    have := mul_le_mul_of_nonneg_right hN hl
    nlinarith
  have h2 : x * Real.exp (A * F - A * C) ≤ K := by
    refine le_trans ?_ h
    rw [hp]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h1) hx
  have h3 : x = x * Real.exp (A * F - A * C) * (Real.exp (A * C) * Real.exp (-(A * F))) := by
    rw [mul_assoc, ← Real.exp_add, ← Real.exp_add, show A * F - A * C + (A * C + -(A * F)) = 0 by ring,
      Real.exp_zero, mul_one]
  rw [h3, mul_assoc K]
  exact mul_le_mul_of_nonneg_right h2 (by positivity)

open GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
  GroundTheory.Automorphic.CuspidalSpectrum in
theorem UpperTheory.V.Lit.Geo.Cs.rapidAll :
    RapidAll := by
  intro E _ _ _ a U Ξ f lam C hlam hf q α hα hR
  obtain ⟨r, hr⟩ := UpperTheory.V.Lit.Bor.oneReal E a Ξ
  obtain ⟨hq1, hq2, -⟩ := UpperTheory.V.Lit.Geo.qhtFacts E a
  refine ⟨|r|, abs_nonneg r, fun A hA X j l => ?_⟩
  obtain ⟨he, hv⟩ := UpperTheory.V.Lit.Geo.Cs.rapidEig E a U Ξ r hr q α hα X j l
  obtain ⟨K, hK⟩ := hR l X ⌈A * C⌉₊
  refine ⟨K * Real.exp (A * C), fun g => ?_⟩
  obtain ⟨g₁, hs⟩ : ∃ g₁ : KernelIndexFullLattice.G1 E a, splitCentre E a (lam g) * g₁.1 = g := ⟨_, hlam.split g⟩
  have hK' := hK g₁
  have hq : qht g = qht (E := E) (a := a) g₁.1 := by
    have := hq2 1 (lam g) g₁.1
    rw [map_one, one_mul, hs] at this
    exact this
  have ha := UpperTheory.V.Lit.Bor.aInv E a _ _ he (lam g) g₁.1
  rw [hs] at ha
  rw [← hq] at hK'
  have hb := le_div_one_add_pow_succ_of_mul_le (hq1 g) hA (Nat.le_ceil (A * C)) (hf g) (norm_nonneg _)
    (le_trans (mul_le_mul_of_nonneg_right (norm_le_pi_norm _ j) (pow_nonneg (zero_le_one.trans (hq1 g)) _)) hK')
  have hb' : ‖((l.map (lie E a)).prod (Bor.cmp j (α X))).1 g₁.1‖ ≤
      K * Real.exp (A * C) * Real.exp (-(A * f g)) := by
    rw [← hv]
    exact hb
  have hc : ‖Complex.exp (-(r : ℂ) * (lam g : ℂ))‖ ≤ Real.exp (|r| * |lam g|) := by
    rw [Complex.norm_exp, Real.exp_le_exp, ← abs_mul]
    simpa using neg_le_abs (r * lam g)
  rw [ha, norm_mul, sub_eq_add_neg, Real.exp_add, mul_left_comm]
  exact mul_le_mul hc hb' (norm_nonneg _) (Real.exp_pos _).le
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsLamEx
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V.Lit.Geo.Cs

namespace UpperTheory.V.Lit.Geo.Cs

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private noncomputable def lam0 (g : GA E a) : ℝ :=
  Real.log (Reduction.detModule E a g).1 / (a * Module.finrank ℚ E)

private theorem deg_pos (ha : 1 ≤ a) : (0 : ℝ) < a * Module.finrank ℚ E :=
  mul_pos (Nat.cast_pos.2 ha) (Nat.cast_pos.2 Module.finrank_pos)

private theorem central_log_mul (g h : GA E a) : lam0 (g * h) = lam0 g + lam0 h := by
  unfold lam0
  rw [map_mul, ← add_div, ← Real.log_mul (Reduction.detModule E a g).2.ne' (Reduction.detModule E a h).2.ne']
  rfl

private theorem central_split_mul_retract (ha : 1 ≤ a) (g : GA E a) :
    splitCentre E a (lam0 g) * (retractOne g : KernelIndexFullLattice.G1 E a).1 = g := by
  have e : splitCentre E a (lam0 g) = Reduction.centralSection E a (Reduction.detModule E a g) := by
    rw [KernelIndexFullLattice.splitEq_holds E a]
    refine congrArg (Reduction.centralSection E a) (Subtype.ext ?_)
    change Real.exp _ = _
    rw [lam0, mul_div_cancel₀ _ (deg_pos ha).ne', Real.exp_log (Reduction.detModule E a g).2]
  rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm, e, coe_retractOne, inv_mul_cancel_right]

private theorem central_log_eq_zero_on_norm_one (x : KernelIndexFullLattice.G1 E a) : lam0 (x.1 : GA E a) = 0 := by
  rw [lam0, (Reduction.mem_normOneGL_iff_detModule).1 x.2]
  simp

private theorem central_log_split (ha : 1 ≤ a) (t : ℝ) : lam0 (splitCentre E a t) = t := by
  rw [lam0, KernelIndexFullLattice.splitEq_holds E a, Reduction.detModule_centralSection (by omega)]
  change Real.log (Real.exp _) / _ = _
  rw [Real.log_exp, mul_div_cancel_left₀ _ (deg_pos ha).ne']

end UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.lamEx :
    LamEx := by
  intro E _ _ _ a ha
  refine ⟨lam0, central_log_mul, central_split_mul_retract ha, fun c => ?_⟩
  obtain ⟨T, hT⟩ := (UpperTheory.V.Lit.Geo.retrFacts E a).2.2 c
  refine ⟨T, fun h hh => ?_⟩
  obtain ⟨t, ht, e⟩ := hT 1 h hh.1 hh.2
  have e' := congrArg lam0 e
  rw [central_log_mul, central_log_mul, central_log_eq_zero_on_norm_one, central_log_eq_zero_on_norm_one, central_log_split ha, zero_add, add_zero] at e'
  rwa [e']
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsSupp
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.Cs.supp :
    UpperTheory.V.Lit.Geo.Cs.Supp := by
  intro E _ _ _ a U Ξ f Y C c f₀ hs Φ hΦ q α w R hc hw
  refine ⟨Real.exp (|C| * (1 + |R|)), fun X g hg => ?_⟩
  have hf : R < f g := by
    by_contra hle
    have hle' : f g ≤ R := not_lt.1 hle
    have h1 : |C| * (1 + |R|) < Real.log (qht g) :=
      (Real.lt_log_iff_exp_lt ((Real.exp_pos _).trans hg)).2 hg
    have h0 := hs.f_nonneg g
    have h2 : C * (1 + f g) ≤ |C| * (1 + |R|) :=
      mul_le_mul (le_abs_self C) (by linarith [le_abs_self R]) (by linarith) (abs_nonneg C)
    linarith [hs.le_f g]
  obtain ⟨y, x, rfl⟩ : ∃ y x, infGL E a y * finGL E a x = g := ⟨_, _, infGL_mul_finGL g⟩
  have hz := hw (x : GL (Fin a) (Af E) ⧸ U) _ (sand_mem_cone y hOne_mem_cone) (by rw [hΦ y x]; exact hf)
  have h := hc y x X
  rw [hz] at h
  have h2 := congrArg (fun z => Ξ.mat y⁻¹ *ᵥ z) h
  simpa only [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec,
    ContinuousAlternatingMap.coe_zero, Pi.zero_apply, Matrix.mulVec_zero] using h2.symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsGeoRet
open UpperTheory.V.Lit.Geo.Cs UpperTheory.V.Lit.Dr

theorem UpperTheory.V.Lit.Geo.Cs.geoRet :
    GeoRet := by
  intro Γ V S _ _ _ _ d G hc l hl Φ hΦ R q w z hw hb hz h
  have hB := fun s => pullB V (Fin d → ℂ) G.Y G.isOpen hc (l s) (hl.1 s) q (z.1 s) (z.2 s).1
  have hA := fun s => pullA V (Fin d → ℂ) G.Y G.isOpen hc (l s) (hl.1 s)
  have hs : ∀ s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pull (l s) (z.1 s)) G.Y := fun s => (hB s).1
  have hv := fun s p (hp : p ∈ G.Y) => UpperTheory.V.Lit.Geo.toOm_apply G hs s hp
  have hd : ∀ s, ∀ p ∈ G.Y, (G.dOm q (UpperTheory.V.Lit.Geo.toOm G fun s => pull (l s) (z.1 s))).1 s p =
      pull (l s) (extDeriv (z.1 s)) p := fun s p hp => by
    rw [G.dOm_apply _ s hp, ← (hB s).2 p hp]
    refine Filter.EventuallyEq.extDeriv_eq ?_
    filter_upwards [G.isOpen.mem_nhds hp] with y hy using hv s y hy
  refine ⟨UpperTheory.V.Lit.Geo.toOm G fun s => pull (l s) (z.1 s), ⟨fun γ => ?_, fun s p hp v i hi => ?_,
    fun s p hp v i hi => ?_⟩, fun s p hp hR => ?_⟩
  · refine Subtype.ext (funext fun s => funext fun p => ?_)
    by_cases hp : p ∈ G.Y
    · rw [hv s p hp, ← pullEquiv Γ V S d G hc l hl q z hz γ s p hp, ← hv _ _ (G.maps _ _ hp)]
      rfl
    · rw [((G.act q γ _).2 s).2 p hp, (Subtype.prop (p := fun x => x ∈ G.Om q) _ s).2 p hp]
  · rw [hv s p hp]
    exact (hA s q _).1 p hp v i hi
  · rw [hd s p hp]
    exact (hA s (q + 1) _).1 p hp v i hi
  · have hcl : ∀ x ∈ G.Y, extDeriv (w.1 s) x = 0 := fun x hx => by
      rw [← G.dOm_apply w s hx, hw]
      rfl
    have hH := homog V (Fin d → ℂ) G.Y G.isOpen hc (q + 1) _ (w.2 s).1 (hb s) hcl
    have hpos := (hl.1 s).2.1 p hp
    have hm := hc _ hpos p hp
    rw [hd s p hp, ← (hA s (q + 1) _).2 (hb s) hH p hp]
    unfold pull
    rw [← G.dOm_apply z s hm, h s _ hm (by rw [hΦ.2.2 s _ hpos p hp]; exact hR)]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsDescEx
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr
open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Geo.Cs

section

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem exists_unitary {g h : GL (Fin a) (Cinf E)} (e : sand g (hOne E a) = sand h (hOne E a)) :
    ∃ k : Kinf E a, h = g * Unitary.toUnits k := by
  have comp : ∀ (g h : GL (Fin a) (Cinf E)) (v : HV E a), sand g (sand h v) = sand (g * h) v := fun g h v => by
    rw [map_mul]; rfl
  have h1 : sand (g⁻¹ * h) (hOne E a) = hOne E a := by
    rw [← comp, ← e, comp, inv_mul_cancel, map_one]; rfl
  have h2 : (g⁻¹ * h).val * star (g⁻¹ * h).val = 1 := by
    have h3 := sand_val (g⁻¹ * h) (hOne E a)
    rw [h1, hOne_val, mul_one] at h3
    exact h3.symm
  refine ⟨⟨(g⁻¹ * h).val, Matrix.mem_unitaryGroup_iff.2 h2⟩, ?_⟩
  rw [← inv_mul_eq_iff_eq_mul]
  exact Units.ext rfl

end

theorem UpperTheory.V.Lit.Geo.Cs.descEx :
    DescEx := by
  classical
  intro E _ _ _ a U f Y C c f₀ hf
  refine ⟨fun s p => if h : p ∈ cone E a then f (pt h.choose s.out) else 0, fun g x => ?_⟩
  have hp : sand g (hOne E a) ∈ cone E a := ⟨g, rfl⟩
  obtain ⟨k, hk⟩ := exists_unitary hp.choose_spec.symm
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U x
  beta_reduce
  rw [dite_eq_left hp, hk, pt_mul, hf.f_cpt, hu, pt, pt, map_mul (finGL E a), ← mul_assoc, hf.f_lev _ u.2]
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsDescFun
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr
open scoped ContDiff

namespace UpperTheory.V.Lit.Geo.Cs

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem rat_pt (γ : GL (Fin a) E) (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) :
    pt (GeneralLinearGroup.map (pInf E) (ratGL E a γ) * g) (GeneralLinearGroup.map (algebraMap E (Af E)) γ * x) =
      ratGL E a γ * pt g x := by
  unfold pt
  refine ga_ext ?_ ?_
  · simp only [map_mul, pInf_infGL, pInf_finGL, mul_one]
  · simp only [map_mul, pFin_infGL, pFin_finGL, one_mul]
    rfl

private theorem centre_zero : splitCentre E a 0 = 1 := by
  have h : (expU fun _ : InfinitePlace E => ((0 : ℝ) : ℂ)) = 1 := by
    ext w
    simp [expU]
  rw [splitCentre, h, map_one, map_one]

private theorem scal_ex (r : ℝ) (hr : 0 < r) : ∃ (t : ℝ) (c : GL (Fin a) (Cinf E)),
    infGL E a c = splitCentre E a t ∧ ∀ p : HV E a, sand c p = r • p := by
  refine ⟨Real.log r / 2, _, rfl, fun p => Subtype.ext ?_⟩
  have h : (Units.map (Matrix.scalar (Fin a)).toMonoidHom
      (expU fun _ : InfinitePlace E => ((Real.log r / 2 : ℝ) : ℂ)) : GL (Fin a) (Cinf E)).val =
      Real.exp (Real.log r / 2) • (1 : Matrix (Fin a) (Fin a) (Cinf E)) := by
    ext i j w
    by_cases hij : i = j <;> simp [expU, hij, Matrix.one_apply]
  have e : Real.exp (Real.log r / 2) * Real.exp (Real.log r / 2) = r := by
    rw [← Real.exp_add, add_halves, Real.exp_log hr]
  change Matrix.of (sand _ p).1 = r • Matrix.of p.1
  rw [sand_val, h, star_smul, star_one, star_trivial, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, e]

end UpperTheory.V.Lit.Geo.Cs

open UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.descFun :
    DescFun := by
  intro E _ _ _ a ho U Ξ f Y C c f₀ hS Φ hΦ
  refine ⟨fun s p₀ hp₀ => ?_, ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    obtain ⟨τ, hτ, hs⟩ := locSec E a p₀ hp₀
    refine ContDiffAt.contDiffWithinAt ?_
    obtain ⟨φ, hφ, -⟩ := hS.f_sm
    have h0 := (contDiffAt_chart φ.2 (finGL E a x) (val_mem_invSet (τ p₀))).comp p₀ hτ
    simp only [Function.comp_def, chart_val, hφ] at h0
    have h1 := Complex.reCLM.contDiff.contDiffAt.comp p₀ h0
    refine h1.congr_of_eventuallyEq (hs.mono fun p hp => ?_)
    have := hΦ (τ p) x
    rw [hp] at this
    rw [this, pt, infGL_comm]
    simp
  · rintro γ s p ⟨g, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    have hs : ∀ p : HV E a, (geo ho U Ξ).ρ γ (sand g p) =
        sand (GeneralLinearGroup.map (pInf E) (ratGL E a γ.1) * g) p := fun p => by
      rw [geo_ρ, map_mul]; rfl
    have hσ : (geo ho U Ξ).σ γ (x : GL (Fin a) (Af E) ⧸ U) =
        ((GeneralLinearGroup.map (algebraMap E (Af E)) γ.1 * x : GL (Fin a) (Af E)) : GL (Fin a) (Af E) ⧸ U) := rfl
    have hl := hS.f_left γ.1 0 (pt g x)
    rw [centre_zero, mul_one] at hl
    rw [hσ, hs, hΦ, hΦ, rat_pt, hl]
  · rintro s r hr p ⟨g, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    obtain ⟨t, c, hc, hp⟩ := scal_ex (E := E) (a := a) r hr
    have hl := hS.f_left 1 t (pt g x)
    rw [map_one, one_mul, ← hc, pt, ← mul_assoc, ← map_mul] at hl
    have hs : ∀ p : HV E a, r • sand g p = sand (c * g) p := fun p => by
      rw [map_mul, ContinuousLinearMap.mul_apply, hp]
    rw [hs, hΦ, hΦ]
    exact hl
end
end

open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.g2 :
    G2 :=
  Cs.galois_twist_preserves_siegel_bound Cs.lamEx Cs.descEx Cs.descFun Cs.rapidAll Cs.corrSz Cs.decP Cs.decK Cs.loc Cs.geoSum Cs.geoRet Cs.supp
