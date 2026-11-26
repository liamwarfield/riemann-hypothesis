module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicRealNonzero

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ScaledFockFormCoefficientsIntegral
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

private theorem exists_of_mem_coefLatFn {D : D7} {n : ℕ} (lam : D.what₂.Tau → DomWeight n)
    (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (φ : GLR D n → ℂ)
    (hφ : φ ∈ coefLatFn D.what₂.embLL (labLL D) (intLL D) lam M) :
    ∃ F : VV D.what₂.LL lam, F ∈ nabAtr (labLL D) lam M ∧ φ = coefFn D.what₂.embLL lam (F : Pol D.what₂.LL D.what₂.Tau n) := by
  induction hφ using Submodule.span_induction with
  | mem φ hφ => exact hφ
  | zero => exact ⟨0, zero_mem _, funext fun y => by simp [coefFn]⟩
  | add φ ψ _ _ h1 h2 =>
    obtain ⟨F1, m1, rfl⟩ := h1
    obtain ⟨F2, m2, rfl⟩ := h2
    exact ⟨F1 + F2, add_mem m1 m2, funext fun y => by simp [coefFn, mul_add]⟩
  | smul a φ _ h1 =>
    obtain ⟨F1, m1, rfl⟩ := h1
    obtain ⟨t, ht⟩ := a.2
    refine ⟨t • F1, Submodule.smul_mem _ _ m1, funext fun y => ?_⟩
    have e1 : ((t • F1 : VV D.what₂.LL lam) : Pol D.what₂.LL D.what₂.Tau n) =
        MvPolynomial.C (t : D.what₂.LL) * (F1 : Pol D.what₂.LL D.what₂.Tau n) := by
      rw [← MvPolynomial.smul_eq_C_mul]
      rfl
    have e2 : D.what₂.embLL (t : D.what₂.LL) = (a : ℂ) := by
      rw [← ht]
      rfl
    show (a : ℂ) * coefFn _ _ (F1 : Pol D.what₂.LL D.what₂.Tau n) y = _
    rw [e1, coefFn, coefFn, map_mul, MvPolynomial.eval₂Hom_C, e2]
    ring

theorem _root_.UpperTheory.KN.scaled_fock_form_coefficients_integral :
    ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
      ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
      ∀ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ), IsLow X j u →
      ∀ gramR c0R c0L, Bridge.FamTie X.R.B X.R.pl (X.R.Sb : Set (Pl D.host.E)) X.R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L →
      ∀ κ : ℂ, κ ≠ 0 → (∀ F : VV D.what₂.LL (lamV D j), harmFn (Wc D j).rank (baseOf Z c w j).w (baseOf Z c w j).F.BS (X.R.ioP j (PiTensorProduct.tprod ℂ u) (c0L j F)) = κ • coefFn D.what₂.embLL (lamV D j) (F : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank)) →
      ∀ (h : Bridge.Gf (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank), P ∈ (baseOf Z c w j).coefLat D.what₂.embLL (labLL D) (intLL D) h ↔
        ∃ F : VV D.what₂.LL (lamV D j), F ∈ nabAtr (labLL D) (lamV D j) (Bridge.hLat (Vc D j) h) ∧ P = κ⁻¹ • X.R.ioP j (PiTensorProduct.tprod ℂ u) (c0L j F) := by
  intro D X X0 Y S YS Z c w j H ι hι u hu gramR c0R c0L _ κ hκ hF h P
  have hB := Z.good.base (c.twI w) j (c.sd w)
  have hBo := GlobalTheory.BigOn.Exp.TwConj.baseOf_of_realPin X.char.lev Z.good Z.pin (c.twI w) j (c.sd w)
  have hval : ∀ v, X.R.ioP j (PiTensorProduct.tprod ℂ u) v ∈
      harm (Wc D j).rank (baseOf Z c w j).w (baseOf Z c w j).F.BS := fun v => by
    have h1 := LinearMap.mem_range_self (X.R.ioP j (PiTensorProduct.tprod ℂ u)) v
    rw [(UpperTheory.KN.ioP_tprod_injective_and_range_eq_valSpace D X X0 Y S YS Z c w j H ι hι u hu).2] at h1
    exact h1
  have hM : (baseOf Z c w j).latAt h = Bridge.hLat (Vc D j) h :=
    GlobalTheory.LatAtHLat.latAt_eq_hLat _ _ _ _ (GlobalTheory.LatFull.baseFrame_one_eq _ _ _ (Z.good.latS _ j _)) _
  have hlam : (baseOf Z c w j).w.lam = lamV D j := hBo.lam
  unfold Base.coefLat
  rw [mem_harmLat, hlam, hM]
  constructor
  · rintro ⟨hPh, hPF⟩
    obtain ⟨F, hF0, hFe⟩ := exists_of_mem_coefLatFn _ _ _ hPF
    refine ⟨F, hF0, ?_⟩
    have hm : ∀ τ, (baseOf Z c w j).w.p τ + (baseOf Z c w j).w.q τ ≤ (Wc D j).rank := fun τ => by
      have h1 := hB.sig τ
      have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (Formalism.BasicNotions.TH.tauE D τ)
      rw [← h1] at h2
      exact h2.le
    have hinj := GlobalTheory.T.harmonic_polynomial_eq_zero_of_function _ _ _ _ (baseOf Z c w j).F.BS hB.wt hm
    exact (eq_inv_smul_iff₀ hκ).2
      (IsScaleAt.ioP_eq (Rl := X.R) (B := baseOf Z c w j) (c0 := c0L j) hF hinj hPh (hval _) hFe).symm
  · rintro ⟨F, hF0, rfl⟩
    refine ⟨Submodule.smul_mem _ _ (hval _), ?_⟩
    rw [map_smul, hF F, inv_smul_smul₀ hκ]
    exact Submodule.subset_span ⟨F, hF0, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsRationalStructureLowestFormSpace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

theorem _root_.UpperTheory.KN.exists_rational_structure_lowest_form_space :
    ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (μ : D.what₂.Tup) (hμ : Used0 D μ) (j : Fin D.R.m),
      ∃ e : (Fin (lDim D X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j (Y.tupT μ)) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL μ (j.1 + 1),
        (∀ x, (X.R.HV j (Y.tupT μ)).e (formOf Y hμ j (D.what₂.jMt μ (j.1 + 1) (e x))) = (X.R.B.jL j (Y.tupT μ) (GlobalTheory.Mem.R3.liftForm X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j (Y.tupT μ) x))) ∧
        OLatTie D.what₂.embLL (D.what₂.MtLat μ (j.1 + 1)) ((D.what₂.jMt μ (j.1 + 1)).comp e.toLinearMap) (lNab D X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j (Y.tupT μ)) ∧
        Submodule.span ℂ (Set.range (D.what₂.jMt μ (j.1 + 1))) = ⊤ := by
  intro D X X0 Y μ hμ j
  have key : ∀ (t : _) (μ : D.what₂.Tup) (h : Y.tup t = μ) (hμ : Used0 D μ),
      ∃ e : (Fin (lDim D X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL μ (j.1 + 1),
        (∀ x, HEq (Y.IL.jMt μ hμ j (D.what₂.jMt μ (j.1 + 1) (e x))).1
          (X.R.toRealDat.extV j t (X.R.jV j t (GlobalTheory.Mem.R3.liftForm X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j t x)))) ∧
        OLatTie D.what₂.embLL (D.what₂.MtLat μ (j.1 + 1)) ((D.what₂.jMt μ (j.1 + 1)).comp e.toLinearMap) (lNab D X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j t) ∧
        Submodule.span ℂ (Set.range (D.what₂.jMt μ (j.1 + 1))) = ⊤ := by
    intro t μ h hμ
    subst h
    refine ⟨Y.eMt j t, fun x => heq_of_eq (Y.mtRead j t hμ x), Y.latL j t, ?_⟩
    rw [eq_top_iff, ← (Y.formsL j t).span]
    refine Submodule.span_mono ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  obtain ⟨e, h1, h2, h3⟩ := key (Y.tupT μ) μ (Y.tupTie μ hμ) hμ
  refine ⟨e, fun x => ?_, h2, h3⟩
  have h4 : formOf Y hμ j (D.what₂.jMt μ (j.1 + 1) (e x)) =
      X.R.jV j (Y.tupT μ) (GlobalTheory.Mem.R3.liftForm X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j (Y.tupT μ) x) :=
    Y.hinj j _ ((extV_formOf Y hμ j _).trans (eq_of_heq (h1 x)))
  rw [h4]
  exact X.char.models.jV _ _ _
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ScaledFockFormMemMtLatIff
section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.MemMtLatOfCoefficientsMemCoefLat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

theorem _root_.UpperTheory.KN.mem_mtLat_of_coefficients_mem_coefLat :
    ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
      ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
      ∀ F ∈ (baseOf Z c w j).formsC (twVia Z.ρ ι), (∀ a, F ((X.R.B.L j (Y.tupT (D.what₂.muTw w))).pres.y a) ∈ (baseOf Z c w j).coefLat D.what₂.embLL (labLL D) (intLL D) ((X.R.B.L j (Y.tupT (D.what₂.muTw w))).pres.y a)) →
      F ∈ (baseOf Z c w j).mtLat D.what₂.embLL (labLL D) (intLL D) (twVia Z.ρ ι) := by
  intro D X X0 Y S YS Z c w j H ι hι F hF hy
  have hB := Z.good.base (c.twI w) j (c.sd w)
  have hc : IsCoefRing D.what₂.embLL (labLL D) (intLL D) :=
    ⟨fun τ => FWT.embV_spec (RingHom.id _) D.what₂.embLL (RingHom.comp_id _) τ, fun a => ⟨a, rfl⟩⟩
  refine (Base.mem_mtLat _ _ _ _).2 ⟨hF, fun h => ?_⟩
  obtain ⟨a, γ, k, e⟩ := ((X.R.B.L j (Y.tupT (D.what₂.muTw w))).pres.reps h).exists
  obtain ⟨hk, -⟩ := UpperTheory.KN.levEnv_level_subgroup_le_levJ_and_character_eq D X X0 Y S YS Z c w j H ι hι k
  have h1 := ((Base.mem_formsC _).1 hF).2 γ ((X.R.B.L j (Y.tupT (D.what₂.muTw w))).pres.y a) ⟨k, hk⟩
  have h2 := Base.act_mem_coefLat hB.frame hc γ _ k (Base.mem_St_of_mem_levJ hk) (hy a)
  have h3 := GlobalTheory.T.level_twist_character_mem_coefficientIntegers D X X0 Y S YS Z c w j H ι hι ⟨k, hk⟩
  have h4 := Submodule.smul_mem _ (⟨_, h3⟩ : intLL D) h2
  subst e
  exact h1 ▸ h4
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.MemLNabIffCoefficientsInNablaLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

theorem _root_.UpperTheory.KN.mem_lNab_iff_coefficients_in_nabla_lattice :
    ∀ (D : D7) (X : RealSide D) (j : Fin D.R.m) (t : X.T),
      ∀ gramR c0R c0L, Bridge.FamTie X.R.B X.R.pl (X.R.Sb : Set (Pl D.host.E)) X.R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L →
      ∀ x, x ∈ lNab D X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j t ↔
        ∀ a, ∃ F : VV D.what₂.LL (lamV D j), F ∈ nabAtr (labLL D) (lamV D j) (Bridge.hLat (Vc D j) ((X.R.B.L j t).pres.y a)) ∧ (X.R.B.jL j t (GlobalTheory.Mem.R3.liftForm X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j t x)) ((X.R.B.L j t).pres.y a) = c0L j F := by
  intro D X j t gramR c0R c0L hT x
  obtain ⟨e, -, he, -, hN, -⟩ := hT.coefL j t
  have h1 : x ∈ lNab D X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j t ↔ ∀ a, (show (X.A3.A.MtCSD j t).Forms from GlobalTheory.Mem.R3.liftForm X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j t x).1 a ∈ (X.A3.A.MtCSD j t).Nab a :=
    GlobalTheory.Mem.LiftForms.mem_lvlNab _ _ _ _ x
  refine h1.trans (forall_congr' fun a => ?_)
  generalize GlobalTheory.Mem.R3.liftForm X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j t x = f
  have h2 : (X.R.B.jL j t f) ((X.R.B.L j t).pres.y a) = (X.R.B.L j t).pres.coef ((show (X.A3.A.MtCSD j t).Forms from f).1 a) :=
    GlobalTheory.PresBasic.ext_y (X.R.B.L j t).pres f a
  have h3 := hN a
  constructor
  · intro h
    refine ⟨e _, ?_, h2.trans (he _)⟩
    exact h3.le ⟨_, h, rfl⟩
  · rintro ⟨F, hF, hv⟩
    obtain ⟨v, hv1, hv2⟩ := h3.ge hF
    have h4 : (X.R.B.L j t).pres.coef ((show (X.A3.A.MtCSD j t).Forms from f).1 a) = (X.R.B.L j t).pres.coef v := by
      refine h2.symm.trans (hv.trans ?_)
      refine Eq.trans ?_ (he v).symm
      exact congrArg (c0L j) hv2.symm
    have h5 : (show (X.A3.A.MtCSD j t).Forms from f).1 a - v = 0 :=
      Bridge.ClassPres.coef_inj (X.R.B.L j t).pres (by rw [map_sub, h4, sub_self])
    rw [sub_eq_zero.1 h5]
    exact hv1
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

theorem _root_.UpperTheory.KN.scaled_fock_form_mem_mtLat_iff :
    ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
      ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
      ∀ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ), IsLow X j u →
      ∀ κ : ℂ, κ ≠ 0 → IsScale X.R X.geo.v₀ (baseOf Z c w j) κ →
      ∀ m : D.what₂.MtL (D.what₂.muTw w) (j.1 + 1), κ⁻¹ • fockOf Y (used_of_tw H.tw) j u (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) m) ∈ (baseOf Z c w j).mtLat D.what₂.embLL (labLL D) (intLL D) (twVia Z.ρ ι) ↔
        ∃ a : D.what₂.Mt (D.what₂.muTw w) (j.1 + 1) → 𝓞 D.what₂.LL, D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) m = ∑ v ∈ (D.what₂.MtLat (D.what₂.muTw w) (j.1 + 1)).gen, D.what₂.embLL (a v : D.what₂.LL) • v := by
  intro D X X0 Y S YS Z c w j H ι hι u hu κ hκ hs m
  obtain ⟨gramR, c0R, c0L, hft, u', hu', hF⟩ := hs
  obtain rfl : u' = u := funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)
  obtain ⟨e, he, hO, -⟩ := UpperTheory.KN.exists_rational_structure_lowest_form_space D X X0 Y (D.what₂.muTw w) (used_of_tw H.tw) j
  obtain ⟨x, rfl⟩ := e.surjective m
  have hN := UpperTheory.KN.mem_lNab_iff_coefficients_in_nabla_lattice D X j (Y.tupT (D.what₂.muTw w)) gramR c0R c0L hft x
  have hC := UpperTheory.KN.scaled_fock_form_coefficients_integral D X X0 Y S YS Z c w j H ι hι u' hu gramR c0R c0L hft κ hκ hF
  have hI := (UpperTheory.KN.ioP_tprod_injective_and_range_eq_valSpace D X X0 Y S YS Z c w j H ι hι u' hu).1
  have hv : ∀ h, (κ⁻¹ • fockOf Y (used_of_tw H.tw) j u' (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) (e x))) h =
      κ⁻¹ • X.R.ioP j (PiTensorProduct.tprod ℂ u') ((X.R.B.jL j (Y.tupT (D.what₂.muTw w))
        (GlobalTheory.Mem.R3.liftForm X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j (Y.tupT (D.what₂.muTw w)) x)) h) := fun h => by
    rw [Pi.smul_apply, fockOf_apply, he x]
  refine Iff.trans ?_ (hN.symm.trans (hO.2 x))
  constructor
  · intro hm a
    obtain ⟨F, hF1, hF2⟩ := (hC _ _).1 (((Base.mem_mtLat _ _ _ _).1 hm).2 ((X.R.B.L j (Y.tupT (D.what₂.muTw w))).pres.y a))
    rw [hv] at hF2
    exact ⟨F, hF1, hI (smul_right_injective _ (inv_ne_zero hκ) hF2)⟩
  · intro hm
    refine UpperTheory.KN.mem_mtLat_of_coefficients_mem_coefLat D X X0 Y S YS Z c w j H ι hι _ (Submodule.smul_mem _ _ ?_) fun a => ?_
    · rw [← (GlobalTheory.T.definiteComplexForms_eq_twistComplexForms_fockModel D X X0 Y S YS Z c w j H ι hι u' hu).2]
      exact LinearMap.mem_range_self _ _
    · obtain ⟨F, hF1, hF2⟩ := hm a
      exact (hC _ _).2 ⟨F, hF1, by rw [hv, hF2]⟩
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsFockFormEqOfMemMtLat
section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.MemRangeSemilinearOfValuesMemRange
theorem _root_.UpperTheory.KN.mem_range_semilinear_of_values_mem_range :
    ∀ (K M N V U I J : Type) [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module ℂ N] [AddCommGroup V] [Module K V] [AddCommGroup U] [Module ℂ U]
      (σ : K →+* ℂ) (jm : M →ₛₗ[σ] N) (ev : N →ₗ[ℂ] (I → U)) (c0 : V →ₛₗ[σ] U) (b : Module.Basis J K V),
      Submodule.span ℂ (Set.range jm) = ⊤ → Function.Injective ev → LinearIndependent ℂ (fun i => c0 (b i)) →
      (∀ m h, ev (jm m) h ∈ Set.range c0) → ∀ f : N, (∀ h, ev f h ∈ Set.range c0) → f ∈ Set.range jm := by
  intro K M N V U I J _ _ _ _ _ _ _ _ _ σ jm ev c0 b hspan hev hli hjm f hf
  classical
  letI : Algebra K ℂ := σ.toAlgebra
  have hσ : ∀ k : K, algebraMap K ℂ k = σ k := fun k => rfl
  obtain ⟨lam, hlam⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K ℂ)
    (LinearMap.ker_eq_bot.mpr (algebraMap K ℂ).injective)
  have lam_mul : ∀ k z, lam (σ k * z) = k * lam z := by
    intro k z
    rw [← hσ, ← Algebra.smul_def, map_smul, smul_eq_mul]
  have lam_one : lam 1 = 1 := by
    have := LinearMap.congr_fun hlam 1
    simpa using this
  let B := Module.Basis.span hli
  obtain ⟨Ψ, hΨ⟩ := LinearMap.exists_extend (B.repr.toLinearMap)
  have hΨb : ∀ j, Ψ (c0 (b j)) = Finsupp.single j 1 := by
    intro j
    have h1 := LinearMap.congr_fun hΨ (B j)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
      B.repr_self] at h1
    rwa [Module.Basis.span_apply] at h1
  have hΨv : ∀ v j, Ψ (c0 v) j = σ (b.repr v j) := by
    intro v j
    conv_lhs => rw [← b.linearCombination_repr v, Finsupp.linearCombination_apply]
    simp [map_finsuppSum, hΨb, Finsupp.single_apply, Finsupp.sum_apply]
    intro h0
    rw [h0, map_zero]
  let R : U →+ V := b.repr.symm.toLinearMap.toAddMonoidHom.comp
    ((Finsupp.mapRange.addMonoidHom lam.toAddMonoidHom).comp Ψ.toAddMonoidHom)
  have hRrepr : ∀ u j, b.repr (R u) j = lam (Ψ u j) := by
    intro u j
    simp [R]
  have KR : ∀ (z : ℂ) (v : V), R (z • c0 v) = lam z • v := by
    intro z v
    apply b.repr.injective
    ext j
    rw [hRrepr, map_smul, Finsupp.smul_apply, hΨv, smul_eq_mul, mul_comm, lam_mul,
      map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  have Rc0 : ∀ v, R (c0 v) = v := by
    intro v
    have := KR 1 v
    rwa [one_smul, lam_one, one_smul] at this
  have hf' : f ∈ Submodule.span ℂ (Set.range jm) := hspan ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hf'
  refine ⟨c.sum fun m a => lam a • m, ?_⟩
  apply hev
  funext h
  obtain ⟨w, hw⟩ := hf h
  have hu : ∀ m, c0 (R (ev (jm m) h)) = ev (jm m) h := by
    intro m
    obtain ⟨v, hv⟩ := hjm m h
    rw [← hv, Rc0]
  have e1 : ev (jm (c.sum fun m a => lam a • m)) h = c.sum fun m a => σ (lam a) • ev (jm m) h := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Finsupp.sum, map_sum, map_smulₛₗ, Finset.sum_apply]
  have e2 : ev (c.sum fun m a => a • jm m) h = c.sum fun m a => a • ev (jm m) h := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Finsupp.sum, map_sum, Finset.sum_apply]
  have e3 : c0 (R (c.sum fun m a => a • ev (jm m) h)) = c.sum fun m a => σ (lam a) • ev (jm m) h := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    conv_lhs => rw [← hu m]
    rw [KR, map_smulₛₗ, hu m]
  rw [e1, ← e3, ← e2, ← hw, Rc0]
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

theorem _root_.UpperTheory.KN.exists_fock_form_eq_of_mem_mtLat :
    ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
      ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
      ∀ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ), IsLow X j u →
      ∀ κ : ℂ, κ ≠ 0 → IsScale X.R X.geo.v₀ (baseOf Z c w j) κ →
      ∀ F ∈ (baseOf Z c w j).mtLat D.what₂.embLL (labLL D) (intLL D) (twVia Z.ρ ι), ∃ m : D.what₂.MtL (D.what₂.muTw w) (j.1 + 1), F = κ⁻¹ • fockOf Y (used_of_tw H.tw) j u (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) m) := by
  classical
  intro D X X0 Y S YS Z c w j H ι hι u hu κ hκ hsc F hF
  have hkey := UpperTheory.KN.scaled_fock_form_mem_mtLat_iff D X X0 Y S YS Z c w j H ι hι u hu κ hκ hsc
  obtain ⟨gramR, c0R, c0L, hft, u', hu', hscale⟩ := hsc
  obtain rfl : u' = u := funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)
  have hcoef := UpperTheory.KN.scaled_fock_form_coefficients_integral D X X0 Y S YS Z c w j H ι hι u' hu gramR c0R c0L hft κ hκ hscale
  obtain ⟨hinj, hrange⟩ := GlobalTheory.T.definiteComplexForms_eq_twistComplexForms_fockModel D X X0 Y S YS Z c w j H ι hι u' hu
  obtain ⟨hio, -⟩ := UpperTheory.KN.ioP_tprod_injective_and_range_eq_valSpace D X X0 Y S YS Z c w j H ι hι u' hu
  obtain ⟨-, -, -, hspan⟩ := UpperTheory.KN.exists_rational_structure_lowest_form_space D X X0 Y (D.what₂.muTw w) (used_of_tw H.tw) j
  have hli : LinearIndependent ℂ fun i => (c0L j (bVV D.what₂.LL (FWT.lamV D j) i) : (X.R.cV j).W) := (hft.mapL j).2.1
  let ev := (X.R.HV j (Y.tupT (D.what₂.muTw w))).e ∘ₗ formOf Y (used_of_tw H.tw) j
  have hev : ∀ x h, fockOf Y (used_of_tw H.tw) j u' x h = X.R.ioP j (PiTensorProduct.tprod ℂ u') (ev x h) := fun _ _ => rfl
  have hevinj : Function.Injective ev := fun x y hxy => hinj (funext fun h => by rw [hev, hev, hxy])
  have hval : ∀ g, κ⁻¹ • fockOf Y (used_of_tw H.tw) j u' g ∈ (baseOf Z c w j).mtLat D.what₂.embLL (labLL D) (intLL D) (twVia Z.ρ ι) →
      ∀ h, ev g h ∈ Set.range (c0L j) := by
    intro g hg h
    obtain ⟨G, -, hG⟩ := (hcoef h _).1 (((Base.mem_mtLat _ _ _ _).1 hg).2 h)
    rw [Pi.smul_apply, hev] at hG
    exact ⟨G, (hio (smul_right_injective _ (inv_ne_zero hκ) hG)).symm⟩
  have hsp : Submodule.span D.what₂.LL {x | D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x ∈ ((D.what₂.MtLat (D.what₂.muTw w) (j.1 + 1)).gen : Set _)} = ⊤ :=
    GlobalTheory.T.rationalLatticeTwistedTuple_span_top D w (j.1 + 1)
  have hall : ∀ m h, ev (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) m) h ∈ Set.range (c0L j) := by
    intro m h
    have hm : m ∈ Submodule.span D.what₂.LL {x | D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x ∈ ((D.what₂.MtLat (D.what₂.muTw w) (j.1 + 1)).gen : Set _)} := by
      rw [hsp]; trivial
    induction hm using Submodule.span_induction with
    | mem x hx =>
      refine hval _ ((hkey x).2 ⟨fun v => if v = D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x then 1 else 0, ?_⟩) h
      rw [Finset.sum_eq_single_of_mem _ (Finset.mem_coe.1 hx)]
      · simp
      · intro v _ hv
        simp [hv]
    | zero => exact ⟨0, by rw [map_zero, map_zero, map_zero]; rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), map_add (f := _), Pi.add_apply, ← ha, ← hb]; rfl⟩
    | smul s x _ hx =>
      obtain ⟨a, ha⟩ := hx
      exact ⟨s • a, by rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, map_smul, Pi.smul_apply, ← ha]; rfl⟩
  have hF1 : κ • F ∈ LinearMap.range (fockOf Y (used_of_tw H.tw) j u') := by
    rw [hrange]
    exact Submodule.smul_mem _ _ ((Base.mem_mtLat _ _ _ _).1 hF).1
  obtain ⟨f, hf⟩ := hF1
  have hFf : F = κ⁻¹ • fockOf Y (used_of_tw H.tw) j u' f := by rw [hf, smul_smul, inv_mul_cancel₀ hκ, one_smul]
  obtain ⟨m, hm⟩ := UpperTheory.KN.mem_range_semilinear_of_values_mem_range _ _ _ _ _ _ _ D.what₂.embLL (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1)) ev (c0L j)
    (bVV D.what₂.LL (FWT.lamV D j)) hspan hevinj hli hall f (hval f (hFf ▸ hF))
  exact ⟨m, by rw [hm]; exact hFf⟩
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

theorem _root_.GlobalTheory.T.rational_lattice_fock_polys_span_integral_forms : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  ∀ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ), IsLow X j u → ∀ κ : ℂ, κ ≠ 0 → IsScale X.R X.geo.v₀ (baseOf Z c w j) κ →
  (baseOf Z c w j).mtLat D.what₂.embLL (labLL D) (intLL D) (twVia Z.ρ ι) =
    Submodule.span (intLL D) ((fun x => κ⁻¹ • fockOf Y (used_of_tw H.tw) j u (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) '' latS w (j.1 + 1)) := by
  intro D X X0 Y S YS Z c w j H ι hι u hu κ hκ hs
  classical
  have key := UpperTheory.KN.scaled_fock_form_mem_mtLat_iff D X X0 Y S YS Z c w j H ι hι u hu κ hκ hs
  have hrat := UpperTheory.KN.exists_fock_form_eq_of_mem_mtLat D X X0 Y S YS Z c w j H ι hι u hu κ hκ hs
  obtain ⟨e, -, htie, -⟩ := UpperTheory.KN.exists_rational_structure_lowest_form_space D X X0 Y (D.what₂.muTw w) (used_of_tw H.tw) j
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · intro F hF
    obtain ⟨m, rfl⟩ := hrat F hF
    obtain ⟨a, ha⟩ := (key m).1 hF
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ha, map_sum, Finset.smul_sum]
    refine Submodule.sum_mem _ fun v hv => ?_
    rw [map_smul, smul_comm]
    refine Submodule.smul_mem _ (⟨D.what₂.embLL (a v : D.what₂.LL), a v, rfl⟩ : intLL D) (Submodule.subset_span ?_)
    obtain ⟨x, hx⟩ := htie.1 v hv
    have hx' : D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) (e x) = v := hx
    exact ⟨e x, by show D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) (e x) ∈ (D.what₂.MtLat (D.what₂.muTw w) (j.1 + 1)).gen; rw [hx']; exact hv, by simp only [hx']⟩
  · rintro _ ⟨m, hm, rfl⟩
    refine (key m).2 ⟨fun v => if v = D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) m then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) m)]
    · simp
    · intro v _ hv
      simp [hv]
    · exact fun h => absurd hm h
