module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullOmGood

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullLevD
open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Dr Matrix

theorem UpperTheory.V.Lit.Geo.levD :
    LevD := by
  intro E _ _ _ a U Ξ q α hα
  have ho : IsOpen (cone E a) := isOpen_iff_mem_nhds.2 fun p hp => by
    obtain ⟨τ, -, h⟩ := locSec E a p hp
    exact h.mono fun x hx => ⟨τ x, hx⟩
  obtain ⟨w, hc, hg⟩ := (levGood E a ho U Ξ q).1 α hα
  have hom := omGood _ _ _ _ (geo ho U Ξ) 0 (isFlow_zero _) q
  refine ⟨?_, fun β hβ => ?_⟩
  · obtain ⟨α', hc', hl⟩ := (levGood E a ho U Ξ (q + 1)).2 _ (hom.1 w hg).2
    rw [(corrUniq E a ho U Ξ (q + 1)).1 _ _ _ (corrD E a ho U Ξ q α w hc) hc']
    exact hl
  · obtain ⟨w', hc', hg'⟩ := (levGood E a ho U Ξ q).1 β hβ
    obtain ⟨γ, hc'', hl⟩ := (levGood E a ho U Ξ q).2 _ (hom.2.1 w w' hg hg')
    have hs : Corr U Ξ (α - β) (w - w').1 := fun g x X => by
      rw [AlternatingMap.sub_apply, map_sub, Pi.sub_apply, Matrix.mulVec_sub, ← hc g x X, ← hc' g x X]
      rfl
    rw [(corrUniq E a ho U Ξ q).1 _ _ _ hs hc'']
    exact hl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsDecK
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsHomSz
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsHkSz
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff

theorem UpperTheory.V.Lit.Geo.Cs.hkSz :
    HkSz := by
  intro V F _ _ _ _ _ _ q k c
  obtain ⟨hA, C₁, hC₁⟩ := altSz V F q k (1 + c)
  obtain ⟨C₂, h₂, hC₂⟩ := compSz V (V →L[ℝ] V) ((V [⋀^Fin q]→L[ℝ] F) →L[ℝ] (V [⋀^Fin q]→L[ℝ] F)) k (1 + c)
  obtain ⟨C₃, h₃, hC₃⟩ := compSz V V (V [⋀^Fin (q + 1)]→L[ℝ] F) k (1 + c)
  let L : (V [⋀^Fin (q + 1)]→L[ℝ] F) →L[ℝ] (V →L[ℝ] V [⋀^Fin q]→L[ℝ] F) :=
    (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := V) (F := F) (n := q)).toContinuousLinearMap
  refine ⟨2 ^ k * (C₂ * |C₁|) * (2 ^ k * (‖L‖ * C₃) * |c|), by positivity, ?_⟩
  intro W t w p b ht hW hWs hw hws
  obtain ⟨f1, f2, f3, f4⟩ := flowSz V k c W t p ht hW hWs
  have a1 : Sz k (fun y => w (UpperTheory.V.Lit.Geo.flow W t y)) p (C₃ * b) :=
    hC₃ w _ p b f1 hw (fun i h1 h2 => f4 i h1 (h2.trans (Nat.le_succ k))) hws
  have s1 : ContDiffAt ℝ ∞ (fun y => w (UpperTheory.V.Lit.Geo.flow W t y)) p := hw.comp p f1
  have a2 := (appSz V _ _ k p).2.1 L _ _ s1 a1
  have s2 : ContDiffAt ℝ ∞ (fun y => L (w (UpperTheory.V.Lit.Geo.flow W t y))) p := L.contDiff.contDiffAt.comp p s1
  have a3 := (appSz V _ _ k p).1 _ W _ _ s2 hW a2 ((hWs.of_le (Nat.le_succ k)).mono (le_abs_self c))
  have s3 : ContDiffAt ℝ ∞ (fun y => L (w (UpperTheory.V.Lit.Geo.flow W t y)) (W y)) p := s2.clm_apply hW
  have a4 := hC₂ _ _ p _ f2 hA.contDiffAt (fun i _ h2 => f3 i h2) ((hC₁ _ f3.norm_le).mono (le_abs_self C₁))
  have s4 := hA.contDiffAt.comp p f2
  have a5 := (appSz V _ _ k p).1 _ _ _ _ s4 s3 a4 a3
  have e : 2 ^ k * (C₂ * |C₁|) * (2 ^ k * (‖L‖ * C₃) * |c|) * b =
      2 ^ k * (C₂ * |C₁|) * (2 ^ k * (‖L‖ * (C₃ * b)) * |c|) := by ring
  rw [e]
  exact a5
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsIntSz
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff Topology

private theorem parametric_integral_deriv_bound (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (p : V)
    (O : Set (V × ℝ)) (hO : IsOpen O) (hp : ∀ t ∈ Set.Icc (0 : ℝ) 1, (p, t) ∈ O) (b : ℝ) (i : ℕ) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (Φ : V × ℝ → F), ContDiffOn ℝ ∞ Φ O →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ i (fun x => Φ (x, t)) p‖ ≤ b) →
      ‖iteratedFDeriv ℝ i (fun x => ∫ t in (0 : ℝ)..1, Φ (x, t)) p‖ ≤ b := by
  induction i with
  | zero =>
    intro F _ _ _ Φ _ h
    simp only [norm_iteratedFDeriv_zero] at h ⊢
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := b) (f := fun t => Φ (p, t))
      (fun t ht => h t (by
        rw [Set.uIoc_of_le zero_le_one] at ht
        exact Set.Ioc_subset_Icc_self ht))
    simpa using this
  | succ i ih =>
    intro F _ _ _ Φ hΦ h
    let Ψ : V × ℝ → V →L[ℝ] F := fun z => (fderiv ℝ Φ z).comp (ContinuousLinearMap.inl ℝ V ℝ)
    have hΨ : ContDiffOn ℝ ∞ Ψ O :=
      (hΦ.fderiv_of_isOpen hO (by simp)).clm_comp contDiffOn_const
    have hd : ∀ x t, (x, t) ∈ O → fderiv ℝ (fun y => Φ (y, t)) x = Ψ (x, t) := fun x t hx => by
      have h1 : DifferentiableAt ℝ Φ (x, t) := (hΦ.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
      exact (h1.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x t)).fderiv
    have htube : ∀ᶠ x in 𝓝 p, ∀ t ∈ Set.Icc (0 : ℝ) 1, (x, t) ∈ O :=
      isCompact_Icc.eventually_forall_of_forall_eventually fun t ht => hO.mem_nhds (hp t ht)
    have e : fderiv ℝ (fun x => ∫ t in (0 : ℝ)..1, Φ (x, t)) =ᶠ[𝓝 p] fun x => ∫ t in (0 : ℝ)..1, Ψ (x, t) := by
      filter_upwards [htube] with x hx
      rw [(UpperTheory.V.Lit.Dr.paramDeriv V F x O Φ hO hx hΦ).2.fderiv]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le zero_le_one] at ht
      exact hd x t (hx t ht)
    rw [← norm_iteratedFDeriv_fderiv, (e.iteratedFDeriv ℝ i).eq_of_nhds]
    refine ih _ Ψ hΨ fun t ht => ?_
    have e' : fderiv ℝ (fun y => Φ (y, t)) =ᶠ[𝓝 p] fun x => Ψ (x, t) := by
      filter_upwards [htube] with x hx using hd x t (hx t ht)
    rw [← (e'.iteratedFDeriv ℝ i).eq_of_nhds, norm_iteratedFDeriv_fderiv]
    exact h t ht

theorem UpperTheory.V.Lit.Geo.Cs.intSz :
    IntSz := by
  intro V F _ _ _ _ _ _ k p O Φ b hO hp hΦ h i hi
  exact parametric_integral_deriv_bound V p O hO hp b i F Φ hΦ fun t ht => h t ht i hi
end

open UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.homSz :
    HomSz := by
  intro V F _ _ _ _ _ _ q k c
  obtain ⟨C, hC, h⟩ := hkSz V F q k c
  refine ⟨C, hC, fun Y W w b hY hW hw p hp hc hb => ?_⟩
  obtain ⟨ho, hs, -, -⟩ := UpperTheory.V.Lit.Geo.hkSmooth V F Y hY W hW q w hw
  haveI : CompleteSpace F := FiniteDimensional.complete ℝ F
  refine intSz V (V [⋀^Fin q]→L[ℝ] F) k p _ (fun z : V × ℝ => UpperTheory.V.Lit.Geo.hk W z.2 w z.1) (C * b) ho
    (fun t ht => ⟨hp, hW.2 p hp t ht⟩) hs fun t ht => ?_
  exact h W t w p b (abs_le.2 ⟨by linarith [ht.1], ht.2⟩) (hW.1.contDiffAt (hY.mem_nhds hp)) hc
    (hw.contDiffAt (hY.mem_nhds (hW.2 p hp t ht))) (hb t ht)
end

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped Topology
open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.Cs.decK :
    UpperTheory.V.Lit.Geo.Cs.DecK := by
  intro E _ _ _ a ho U Ξ f Y C c f₀ hS W hW lam hl q k A B hA hB
  obtain ⟨hfl, hflow⟩ := fieldFlow E a ho U Ξ Y C hS.fld W hW
  obtain ⟨z, hz⟩ := zwSz E a U Y C hS.fld W hW (k + 1)
  obtain ⟨C₁, hC₁, hhom⟩ := homSz (HV E a) (Fin Ξ.d → ℂ) q k z
  obtain ⟨D₁, hD₁, hmv⟩ := move E a ho U Ξ (q + 1) k C
  obtain ⟨L, hL⟩ := hl.bdd C
  refine ⟨C₁ * D₁ * Real.exp (B * L + A * C), by positivity, fun M hM w hw g x hg => ?_⟩
  obtain ⟨hfield, hfz, hq⟩ := twOps E a ho U Ξ W hfl g x
  have hsm := ((hq (q + 1)).1 w).1
  have heq := (hq q).2 w
  have key : ∀ t ∈ Set.Icc (0 : ℝ) 1, Sz k (Tw U Ξ w.1 g x) (flow (Zw U W g x) t (hOne E a))
      (D₁ * (M * (Real.exp (B * L + A * C) * Real.exp (B * |lam (pt g x)| - A * f (pt g x))))) := by
    intro t ht
    have ht' : |t| ≤ 1 := abs_le.2 ⟨by linarith [ht.1], ht.2⟩
    obtain ⟨h, hh, h1, h2⟩ := hS.root (pt g x) t ht'
    have hn := abs_le.1 (hS.near (pt g x) t h ht' hh)
    have e : flow (Zw U W g x) t (hOne E a) = sand h (hOne E a) := by
      rw [hfz, hflow g h x t hh, ← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel_left]
    rw [e]
    refine hmv w g x h _ ⟨h1, h2⟩ ((hw (g * h) x (by rw [pt_mul]; linarith [hn.1])).mono ?_)
    refine mul_le_mul_of_nonneg_left ?_ hM
    rw [← Real.exp_add, pt_mul, hl.add]
    refine Real.exp_le_exp.2 ?_
    have b1 : |lam (pt g x) + lam (infGL E a h)| ≤ L + |lam (pt g x)| := by
      linarith [abs_add_le (lam (pt g x)) (lam (infGL E a h)), hL h ⟨h1, h2⟩]
    have b2 := mul_le_mul_of_nonneg_left b1 hB
    have b3 := mul_le_mul_of_nonneg_left hn.1 hA
    linarith
  have main := hhom (cone E a) (Zw U W g x) (Tw U Ξ w.1 g x) _ ho hfield hsm (hOne E a) hOne_mem_cone (hz g x) key
  refine (main.congr ?_).mono (le_of_eq (by ring))
  filter_upwards [ho.mem_nhds hOne_mem_cone] with p hp
  exact (heq p hp).symm
end
