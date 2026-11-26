module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LeadingMinors
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBLGapPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotMeas
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal
open Matrix

set_option linter.dupNamespace false

namespace Formalism.L2.SG.Pf.Carrier.JointQuot

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section PiProd


set_option backward.isDefEq.respectTransparency false in
theorem lintegral_fin_nat_prod {n : ℕ} {E : Fin n → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc ∫⁻ x : (i : Fin (n + 1)) → E i, ∏ i, f i (x i) ∂(Measure.pi μ)
        = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)), f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi fun i => μ (Fin.succ i))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero]
          simp
      _ = (∫⁻ x, f 0 x ∂(μ 0)) * ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂(μ (Fin.succ i)) := by
          rw [← ih (fun i => f (Fin.succ i)) (fun i => hf _)]
          exact lintegral_prod_mul (hf 0).aemeasurable
            (Finset.measurable_prod _ fun i _ => (hf _).comp (measurable_pi_apply i)).aemeasurable
      _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

theorem lintegral_fintype_prod {ι : Type*} [Fintype ι] {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft μ e).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_nat_prod (fun i => f (e i)) (fun i => hf _)

theorem pi_withDensity {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
    (μ : (i : ι) → Measure (E i)) [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (hfin : ∀ i x, f i x ≠ ⊤) :
    Measure.pi (fun i => (μ i).withDensity (f i)) = (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  haveI : ∀ i, SigmaFinite ((μ i).withDensity (f i)) := fun i =>
    SigmaFinite.withDensity_of_ne_top (Filter.Eventually.of_forall (hfin i))
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi,
    lintegral_fintype_prod _ hf]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i)]

end PiProd

section WeilGen

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

theorem weil_of_bruhat (μG μS : Measure G) [SigmaFinite μG] [SFinite μS] [μG.IsMulLeftInvariant]
    (B : G → ℝ≥0∞) (hBm : Measurable B) (hinv : μS.map (fun s => s⁻¹) = μS)
    (hb1 : ∀ x, ∫⁻ s, B (s * x) ∂μS = 1) (f : G → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (s * x) ∂μS) ∂(μG.withDensity B) := by
  have hF : Measurable fun p : G × G => f (p.1 * p.2) := hf.comp measurable_mul
  have hg : Measurable fun x => ∫⁻ s, f (s * x) ∂μS := hF.lintegral_prod_left'
  have hBinv : ∀ x, ∫⁻ s, B (s⁻¹ * x) ∂μS = 1 := by
    intro x
    have h1 : ∫⁻ s, B (s * x) ∂(μS.map fun s => s⁻¹) = ∫⁻ s, B (s⁻¹ * x) ∂μS :=
      lintegral_map (hBm.comp (measurable_mul_const x)) measurable_inv
    rw [← h1, hinv, hb1]
  rw [lintegral_withDensity_eq_lintegral_mul _ hBm hg]
  symm
  calc _ = ∫⁻ x, ∫⁻ s, B x * f (s * x) ∂μS ∂μG := by
        refine lintegral_congr fun x => ?_
        rw [Pi.mul_apply]
        exact (lintegral_const_mul _ (hf.comp (measurable_mul_const x))).symm
    _ = ∫⁻ s, ∫⁻ x, B x * f (s * x) ∂μG ∂μS :=
        lintegral_lintegral_swap
          ((hBm.comp measurable_fst).mul (hf.comp (measurable_snd.mul measurable_fst))).aemeasurable
    _ = ∫⁻ s, ∫⁻ x, B (s⁻¹ * x) * f x ∂μG ∂μS := by
        refine lintegral_congr fun s => ?_
        simpa only [inv_mul_cancel_left] using
          lintegral_mul_left_eq_self (μ := μG) (fun x => B (s⁻¹ * x) * f x) s
    _ = ∫⁻ x, ∫⁻ s, B (s⁻¹ * x) * f x ∂μS ∂μG :=
        lintegral_lintegral_swap
          ((hBm.comp (measurable_fst.inv.mul measurable_snd)).mul (hf.comp measurable_snd)).aemeasurable
    _ = ∫⁻ x, f x ∂μG := by
        refine lintegral_congr fun x => ?_
        rw [show ∫⁻ s, B (s⁻¹ * x) * f x ∂μS = (∫⁻ s, B (s⁻¹ * x) ∂μS) * f x from
          lintegral_mul_const _ (hBm.comp (measurable_inv.mul_const x)), hBinv, one_mul]

end WeilGen

variable {D : D7}

def NV (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    Set (Formalism.REAL.UJ (X.B.I.ε v)) :=
  {g | Formalism.L2.SG.HidaSetting.InN (X.B.I.ε v) (fun a => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a))
    (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)) (uMat g)}

def StV (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) :
    Set (Formalism.REAL.UJ (X.B.I.ε v)) :=
  StSet (NV X u v) (NV X u' v) (γ v)

def stCoordV (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf)
    (v : InfinitePlace X.B.I.F) (y : Formalism.REAL.UJ (X.B.I.ε v)) : FreeE w → ℂ :=
  fun p => ((D.host.rdE : ℂ) ^ (D.R.rS - p.1.1.1)) *
    Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v)
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR ⟨p.1.1.1, by have := p.2.1; omega⟩))
      (uMat ((γ v)⁻¹ * y * γ v) *ᵥ frm X u' D.host.rdE v p.1.2)

def muStabV (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : Point D.host.E (D.R.rS + 1)) : Measure (FreeE w → ℂ) :=
  Measure.pi fun _ => ENNReal.ofReal (D.host.ka / (X.B.g : ℝ) / Real.pi) • (volume : Measure ℂ)

def LocPinAt (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (ν : ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) : Prop :=
  ∀ v, ∃ μRv : Measure (Formalism.REAL.UJ (X.B.I.ε v)), IsHaarLoc (StV X u u' (gamW X u u' w) v) μRv ∧
    IsQuotLoc μRv (ν v) ∧ μRv.map (stCoordV X u' w (gamW X u u' w) v) = muStabV X w

def LocPin (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) : Prop :=
  LocPinAt X u u' w (νl w)

def LocUni (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ w, OkPt X u u' w → ∀ μR : Measure X.B.I.Ginf,
    Formalism.L2.SG.HidaSetting.IsHaarOnSet X.B.I (StInf X u u' (gamW X u u' w)) μR →
    μR.map (stCoord X u' w (gamW X u u' w)) = muStab X w → ∀ v, ∃ μRv : Measure (Formalism.REAL.UJ (X.B.I.ε v)),
    IsHaarLoc (StV X u u' (gamW X u u' w) v) μRv ∧ μRv.map (fun s => s⁻¹) = μRv ∧
    μRv.map (stCoordV X u' w (gamW X u u' w) v) = muStabV X w ∧
    ∃ b : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, Measurable b ∧ (∀ x, b x ≠ ⊤) ∧ ∀ x, ∫⁻ s, b (s * x) ∂μRv = 1

def GlobProd (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ w, OkPt X u u' w → ∀ μR : Measure X.B.I.Ginf,
    Formalism.L2.SG.HidaSetting.IsHaarOnSet X.B.I (StInf X u u' (gamW X u u' w)) μR →
    μR.map (stCoord X u' w (gamW X u u' w)) = muStab X w →
    ∀ μRv : ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)),
      (∀ v, IsHaarLoc (StV X u u' (gamW X u u' w) v) (μRv v) ∧
        (μRv v).map (stCoordV X u' w (gamW X u u' w) v) = muStabV X w) →
      μR = Measure.pi μRv

theorem ooQuot_pin (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (hN : NuQPin X u u' νq) (hR : StRel X u u')
    (hLU : LocUni X u u') (hGP : GlobProd X u u') :
    ∃ νl, (∀ w, OkPt X u u' w → LocPin X u u' w νl) ∧ Formalism.L2.SG.Pf.Carrier.JointPf.OOQuot X u u' νq νl := by
  have hI := stInv_of_rel X u u' hR
  have key : ∀ w : Point D.host.E (D.R.rS + 1),
      ∃ ν : ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)), OkPt X u u' w →
        LocPinAt X u u' w ν ∧ ∀ y : ∀ v, X.Vloc u' v,
          (haveI := FiniteDimensional.complete ℂ (X.Vpi u);
            Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w))
              (X.tensU u' y) =
          X.tensU u (fun v => (haveI := FiniteDimensional.complete ℂ (X.Vloc u v);
            Jv (ν v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v)) (y v)) := by
    intro w
    by_cases hw : OkPt X u u' w
    · obtain ⟨μR, hH, hQ, hM⟩ := hN.2 w hw.1
      haveI : SigmaFinite μR := hH.1
      choose μRv hHv hIv hMv b hbm hbt hb1 using hLU w hw μR hH hM
      have hprod : μR = Measure.pi μRv := hGP w hw μR hH hM μRv fun v => ⟨hHv v, hMv v⟩
      haveI : ∀ v, SigmaFinite (μRv v) := fun v => (hHv v).1
      have hσ : ∀ v, SigmaFinite ((Formalism.REAL.muG (X.B.I.ε v)).withDensity (b v)) :=
        fun v => SigmaFinite.withDensity_of_ne_top' (hbt v)
      have hBm : Measurable fun x : X.B.I.Ginf => ∏ v, b v (x v) :=
        Finset.measurable_prod _ fun v _ => (hbm v).comp (measurable_pi_apply v)
      have hb1G : ∀ x : X.B.I.Ginf, ∫⁻ s, (∏ v, b v ((s * x) v)) ∂μR = 1 := by
        intro x
        rw [hprod]
        have := lintegral_fintype_prod (μ := μRv) (fun v t => b v (t * x v))
          (fun v => (hbm v).comp (measurable_mul_const _))
        refine this.trans ?_
        exact Finset.prod_eq_one fun v _ => hb1 v (x v)
      have hinvG : μR.map (fun s => s⁻¹) = μR := by
        haveI : ∀ v, SigmaFinite ((μRv v).map (fun s => s⁻¹)) := fun v => by rw [hIv v]; infer_instance
        rw [hprod]
        have := Measure.pi_map_pi (μ := μRv) (f := fun _ s => s⁻¹) (fun v => measurable_inv.aemeasurable)
        refine this.trans ?_
        congr 1
        funext v
        exact hIv v
      have hp : Formalism.L2.SG.HidaSetting.IsQuotMeasS X.B.I μR
          (Measure.pi fun v => (Formalism.REAL.muG (X.B.I.ε v)).withDensity (b v)) := by
        intro f hf
        rw [pi_withDensity _ b hbm hbt]
        exact weil_of_bruhat (Formalism.L2.SG.ProjRows.muInf X.B.I) μR _ hBm hinvG hb1G f hf
      refine ⟨fun v => (Formalism.REAL.muG (X.B.I.ε v)).withDensity (b v), fun _ => ⟨fun v => ?_, fun y => ?_⟩⟩
      · refine ⟨μRv v, hHv v, fun f hf => ?_, hMv v⟩
        exact weil_of_bruhat (Formalism.REAL.muG (X.B.I.ε v)) (μRv v) (b v) (hbm v) (hIv v) (hb1 v) f hf
      · exact oo_eq_tens X u u' _ μR _ _ hH.2.2.1 _ hBm hb1G _ hσ hQ hp (hI w hw) y
    · exact ⟨fun v => Formalism.REAL.muG (X.B.I.ε v), fun h => absurd h hw⟩
  choose νl hνl using key
  exact ⟨νl, fun w hw => (hνl w hw).1, fun w hw hG y => (hνl w ⟨hw, hG⟩).2 y⟩

end Formalism.L2.SG.Pf.Carrier.JointQuot
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SubMemOfIndQ
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.Pf.FibreCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Flag

variable {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem fix_e {c : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hfix : ∀ a, c (F0.fvec a) = F0.fvec a) (i : Fin D.R.rS) :
    c (F0.e i) = F0.e i := by
  have h := hfix (Fin.castSucc i)
  simpa [FlagG.fvec] using h

theorem fix_X {c : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hfix : ∀ a, c (F0.fvec a) = F0.fvec a) :
    ∀ x ∈ F0.X, c x = x := by
  intro x hx
  have h := LinearMap.eqOn_span' (f := (c : (VS D).V →ₗ[D.host.E] (VS D).V)) (g := LinearMap.id)
    (s := Set.range F0.e) (fun y ⟨i, hi⟩ => by rw [← hi]; exact fix_e F0 hfix i) hx
  simpa using h

theorem inv_fix {c : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hfix : ∀ a, c (F0.fvec a) = F0.fvec a) :
    ∀ a, c⁻¹ (F0.fvec a) = F0.fvec a := by
  intro a
  show c.symm (F0.fvec a) = F0.fvec a
  rw [LinearEquiv.symm_apply_eq, hfix]

theorem Xa_le_X (j : ℕ) : F0.Xa j ≤ F0.X := Submodule.span_mono (Set.image_subset_range _ _)

theorem perp_maps {c : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hc : c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hfix : ∀ a, c (F0.fvec a) = F0.fvec a) : ∀ y ∈ perpS (VS D) F0.X, c y ∈ perpS (VS D) F0.X := by
  intro y hy x hx
  have h1 : c x = x := fix_X F0 hfix x hx
  have h2 := hc x y
  rw [h1] at h2
  rw [h2]
  exact hy x hx

def indQ (c : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hc : c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hfix : ∀ a, c (F0.fvec a) = F0.fvec a) : WbQ D F0 → WbQ D F0 :=
  Submodule.mapQ _ _ ((c : (VS D).V →ₗ[D.host.E] (VS D).V).restrict (perp_maps F0 hc hfix)) (by
    intro y hy
    simp only [Submodule.mem_comap, Submodule.coe_subtype] at hy ⊢
    rw [LinearMap.restrict_coe_apply]
    show c (y : (VS D).V) ∈ F0.X
    rw [fix_X F0 hfix _ hy]
    exact hy)

theorem indQ_mk (c : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hc : c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hfix : ∀ a, c (F0.fvec a) = F0.fvec a) (x : perpS (VS D) F0.X) :
    indQ F0 c hc hfix (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨c x, perp_maps F0 hc hfix _ x.2⟩ := by
  rfl

theorem indQ_mem {Λ : Submodule (𝓞 D.host.E) (VS D).V} (c : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hc : c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hfix : ∀ a, c (F0.fvec a) = F0.fvec a) (hg : Formalism.HermitianLatticesTheory.gmap c Λ = Λ) :
    indQ F0 c hc hfix ∈ autLz D F0 Λ := by
  refine ⟨c, ⟨hc, fun j => ?_, ?_⟩, hg, fun x hx => indQ_mk F0 c hc hfix x⟩
  · have hfixX : ∀ y ∈ F0.Xa j, c y = y := fun y hy => fix_X F0 hfix y (Xa_le_X F0 j hy)
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      show c z ∈ F0.Xa j
      rw [hfixX z hz]; exact hz
    · intro hy
      exact ⟨y, hy, hfixX y hy⟩
  · have h := hfix (Fin.last D.R.rS)
    simpa [FlagG.fvec] using h

theorem sub_mem_of_indQ {c c' : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hc : c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hfix : ∀ a, c (F0.fvec a) = F0.fvec a) (hc' : c' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hfix' : ∀ a, c' (F0.fvec a) = F0.fvec a) (h : indQ F0 c hc hfix = indQ F0 c' hc' hfix') :
    ∀ y ∈ perpS (VS D) F0.X, c y - c' y ∈ F0.X := by
  intro y hy
  have h1 := congrArg (fun f => f (Submodule.Quotient.mk (⟨y, hy⟩ : perpS (VS D) F0.X))) h
  simp only [indQ_mk] at h1
  rw [Submodule.Quotient.eq] at h1
  simpa using h1

theorem nlam_of_sub {Λ : Submodule (𝓞 D.host.E) (VS D).V} {c c' : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hA : IsAutLam (VS D) Λ c) (hA' : IsAutLam (VS D) Λ c') (hfix : ∀ a, c (F0.fvec a) = F0.fvec a)
    (hfix' : ∀ a, c' (F0.fvec a) = F0.fvec a) (hq : ∀ y ∈ perpS (VS D) F0.X, c y - c' y ∈ F0.X) :
    c⁻¹ * c' ∈ NLam Λ (lf D F0) := by
  obtain ⟨hci, hcg⟩ := hA
  obtain ⟨hci', hcg'⟩ := hA'
  have hX : ∀ x ∈ F0.X, c x = x := fix_X F0 hfix
  have hX' : ∀ x ∈ F0.X, c' x = x := fix_X F0 hfix'
  have hXinv : ∀ x ∈ F0.X, c⁻¹ x = x := fun x hx => by
    show c.symm x = x
    rw [LinearEquiv.symm_apply_eq, hX x hx]
  have hn : ∀ x ∈ F0.X, (c⁻¹ * c') x = x := fun x hx => by
    show c⁻¹ (c' x) = x
    rw [hX' x hx, hXinv x hx]
  refine ⟨⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hci) hci', ?_⟩, fun j x hx => ?_, fun x hx => ?_⟩
  · have hinv : Formalism.HermitianLatticesTheory.gmap c⁻¹ Λ = Λ := by
      conv_lhs => rw [← hcg]
      rw [← gmap_mul_sat, inv_mul_cancel]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [gmap_mul_sat, hcg', hinv]
  · have hxX : x ∈ F0.X := Xa_le_X F0 (j + 1) hx
    rw [hn x hxX, sub_self]
    exact Submodule.zero_mem _
  · have hxp : x ∈ perpS (VS D) F0.X := by
      intro z hz
      have := (Submodule.mem_iInf _).1 hx z
      exact (Submodule.mem_iInf _).1 this hz
    have hd := hq x hxp
    have e1 : (c⁻¹ * c') x - x = c⁻¹ (c' x - c x) := by
      show c⁻¹ (c' x) - x = c⁻¹ (c' x - c x)
      rw [map_sub]
      congr 1
      show x = c.symm (c x)
      rw [LinearEquiv.symm_apply_apply]
    rw [e1]
    have hmem : c' x - c x ∈ F0.X := by
      have := F0.X.neg_mem hd
      simpa using this
    rw [hXinv _ hmem]
    exact hmem

end Flag

section Fib

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem nlam_congr {Λ₁ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V} (h : Λ₁ = Λ₂) {T : D.host.E}
    {F : LFlag (D.sp.Y 0) D.R.rS T} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NLam Λ₁ F) : n ∈ NLam Λ₂ F := h ▸ hn

theorem gmap_congr {Λ₁ Λ₂ Λ₃ : Submodule (𝓞 D.host.E) (VS D).V} {c : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (h : Formalism.HermitianLatticesTheory.gmap c Λ₁ = Λ₃) (e : Λ₁ = Λ₂) : Formalism.HermitianLatticesTheory.gmap c Λ₂ = Λ₃ := e ▸ h

theorem fib_c {s₀ s : TT Y u u'} (h : s₀.toTerm = s.toTerm) :
    ∃ c : (VS D).V ≃ₗ[D.host.E] (VS D).V, c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ Formalism.HermitianLatticesTheory.gmap c s₀.lam' = s₀.lam' ∧
      (∀ a, c ((X.Fu u').fvec a) = (X.Fu u').fvec a) ∧
      ∃ n ∈ NLam s₀.lam (lf D (X.Fu u)), ∃ ν ∈ NLam s₀.lam' (lf D (X.Fu u')), s.lin = n * s₀.lin * ν * c := by
  obtain ⟨-, n, hn, ν, hν, c, hc, hg, hfix, he⟩ := fib_dec h
  exact ⟨c, hc, gmap_congr hg (lam'_eq h).symm, hfix, n, hn, ν, hν, he⟩

theorem eq_of_dec {s₀ s s' : TT Y u u'} (h : s₀.toTerm = s.toTerm) (h' : s₀.toTerm = s'.toTerm)
    {n n' ν ν' c c' : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NLam s₀.lam (lf D (X.Fu u))) (hn' : n' ∈ NLam s₀.lam (lf D (X.Fu u)))
    (hν : ν ∈ NLam s₀.lam' (lf D (X.Fu u'))) (hν' : ν' ∈ NLam s₀.lam' (lf D (X.Fu u')))
    (hc : c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hc' : c' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hg : Formalism.HermitianLatticesTheory.gmap c s₀.lam' = s₀.lam') (hg' : Formalism.HermitianLatticesTheory.gmap c' s₀.lam' = s₀.lam')
    (hfix : ∀ a, c ((X.Fu u').fvec a) = (X.Fu u').fvec a) (hfix' : ∀ a, c' ((X.Fu u').fvec a) = (X.Fu u').fvec a)
    (he : s.lin = n * s₀.lin * ν * c) (he' : s'.lin = n' * s₀.lin * ν' * c')
    (hq : ∀ y ∈ perpS (VS D) (X.Fu u').X, c y - c' y ∈ (X.Fu u').X) : s = s' := by
  have hl : s₀.lam = s.lam := (fib_dec h).1
  have hl2 : s₀.lam = s'.lam := (fib_dec h').1
  have hm : s₀.lam' = s.lam' := lam'_eq h
  have hm2 : s₀.lam' = s'.lam' := lam'_eq h'
  have hA : IsAutLam (VS D) s₀.lam' c := ⟨hc, hg⟩
  have hA' : IsAutLam (VS D) s₀.lam' c' := ⟨hc', hg'⟩
  have hb := nlam_of_sub (X.Fu u') hA hA' hfix hfix' hq
  have hνν : c⁻¹ * (ν⁻¹ * ν') * c⁻¹⁻¹ ∈ NLam s₀.lam' (lf D (X.Fu u')) :=
    Formalism.L2.SG.Pf.nlam_conj (Formalism.L2.SG.Pf.isAutLam_inv hA) (fun a => (inv_fix (X.Fu u') hfix a).symm)
      (Formalism.L2.SG.Pf.nlamPf_mul (Formalism.L2.SG.Pf.nlamPf_inv hν) hν')
  rw [inv_inv] at hνν
  refine gterm_eq (hl.symm.trans hl2) (hm.symm.trans hm2) ⟨n' * n⁻¹,
    nlam_congr hl (Formalism.L2.SG.Pf.nlamPf_mul hn' (Formalism.L2.SG.Pf.nlamPf_inv hn)),
    (c⁻¹ * (ν⁻¹ * ν') * c) * (c⁻¹ * c'), nlam_congr hm (Formalism.L2.SG.Pf.nlamPf_mul hνν hb), ?_⟩
  rw [he, he']
  group

theorem card_le {t : RT Y u u'} (S0 : Finset (TT Y u u')) (hS0 : ∀ s ∈ S0, s.toTerm = t) {s₀ : TT Y u u'}
    (h₀ : s₀.toTerm = t) [Finite (autLz D (X.Fu u') s₀.lam')] :
    S0.card ≤ Nat.card (autLz D (X.Fu u') s₀.lam') := by
  have hex : ∀ s : S0, ∃ c : (VS D).V ≃ₗ[D.host.E] (VS D).V, c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧
      Formalism.HermitianLatticesTheory.gmap c s₀.lam' = s₀.lam' ∧ (∀ a, c ((X.Fu u').fvec a) = (X.Fu u').fvec a) ∧
      ∃ n ∈ NLam s₀.lam (lf D (X.Fu u)), ∃ ν ∈ NLam s₀.lam' (lf D (X.Fu u')),
        (s : TT Y u u').lin = n * s₀.lin * ν * c :=
    fun s => fib_c (h₀.trans (hS0 s s.2).symm)
  let cf : S0 → (VS D).V ≃ₗ[D.host.E] (VS D).V := fun s => (hex s).choose
  have hcf : ∀ s, _ := fun s => (hex s).choose_spec
  let f : S0 → autLz D (X.Fu u') s₀.lam' := fun s =>
    ⟨indQ (X.Fu u') (cf s) (hcf s).1 (hcf s).2.2.1, indQ_mem (X.Fu u') _ _ _ (hcf s).2.1⟩
  have hf : Function.Injective f := by
    intro s s' hss
    have hq := sub_mem_of_indQ (X.Fu u') (hcf s).1 (hcf s).2.2.1 (hcf s').1 (hcf s').2.2.1
      (congrArg Subtype.val hss)
    obtain ⟨n, hn, ν, hν, he⟩ := (hcf s).2.2.2
    obtain ⟨n', hn', ν', hν', he'⟩ := (hcf s').2.2.2
    exact Subtype.ext (eq_of_dec (h₀.trans (hS0 s s.2).symm) (h₀.trans (hS0 s' s'.2).symm) hn hn' hν hν'
      (hcf s).1 (hcf s').1 (hcf s).2.1 (hcf s').2.1 (hcf s).2.2.1 (hcf s').2.2.1 he he' hq)
  have := Nat.card_le_card_of_injective f hf
  simpa [Nat.card_eq_fintype_card] using this

end Fib

section Count

variable {D : D7} {X : HidaSetting D}


variable (Y) in
def RowFree (Y : Full X) : Prop :=
  ∀ (u u' : D.what₂.Word) (s s' : TT Y u u'), s.toTerm = s'.toTerm →
    Formalism.L2.SG.LoopTieOf.rowL (Y := Y) s = Formalism.L2.SG.LoopTieOf.rowL (Y := Y) s' → s = s'

theorem fibreCount_of {Y : Full X} (hR : RowFree Y) : Formalism.L2.SG.LoopTieOf.FibreCount Y := by
  intro u u' t₁ t₂ S hS
  rcases S.eq_empty_or_nonempty with h0 | ⟨x₀, hx₀⟩
  · simp [h0]
  have hlam : ∀ x ∈ S, x.1.lam' = x₀.1.lam' := fun x hx => (lam'_eq ((hS x hx).1.trans (hS x₀ hx₀).1.symm))
  rw [Finset.sum_congr rfl (fun x hx => by rw [hlam x hx]), Finset.sum_const, nsmul_eq_mul]
  unfold wRow
  by_cases hfin : Finite (autLz D (X.Fu u') x₀.1.lam')
  · have hinj : Set.InjOn Prod.fst (S : Set (TT Y u u' × TT Y u u')) := by
      intro x hx y hy hxy
      have h2 : x.2 = y.2 := hR u u' x.2 y.2 ((hS x hx).2.1.trans (hS y hy).2.1.symm)
        (((hS x hx).2.2.symm.trans (congrArg _ hxy)).trans (hS y hy).2.2)
      exact Prod.ext hxy h2
    have hcard : S.card = (S.image Prod.fst).card := (Finset.card_image_of_injOn hinj).symm
    have hle := card_le (S.image Prod.fst) (fun s hs => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hs
        exact (hS x hx).1) (hS x₀ hx₀).1
    rw [← hcard] at hle
    rcases Nat.eq_zero_or_pos (Nat.card (autLz D (X.Fu u') x₀.1.lam')) with hz | hp
    · simp [hz]
    · rw [mul_inv_le_iff₀ (by exact_mod_cast hp), one_mul]
      exact_mod_cast hle
  · have : Infinite (autLz D (X.Fu u') x₀.1.lam') := not_finite_iff_infinite.1 hfin
    rw [Nat.card_eq_zero_of_infinite]
    simp

end Count

end Formalism.L2.SG.Pf.FibreCounting
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyPfLoc
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.SG.Pf.Carrier.EnergyPfLoc

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.EnergyPf
open Formalism.L2.SG.HidaSetting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gram

variable {α V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem inner_lc (f g : α → V) (h : ∀ a b, ⟪f a, f b⟫_ℂ = ⟪g a, g b⟫_ℂ) (c d : α →₀ ℂ) :
    ⟪Finsupp.linearCombination ℂ f c, Finsupp.linearCombination ℂ f d⟫_ℂ =
      ⟪Finsupp.linearCombination ℂ g c, Finsupp.linearCombination ℂ g d⟫_ℂ := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, h]

theorem norm_lc (f g : α → V) (h : ∀ a b, ⟪f a, f b⟫_ℂ = ⟪g a, g b⟫_ℂ) (c : α →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ f c‖ = ‖Finsupp.linearCombination ℂ g c‖ := by
  have hsq : ‖Finsupp.linearCombination ℂ f c‖ ^ 2 = ‖Finsupp.linearCombination ℂ g c‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, inner_lc f g h c c]
  have := congrArg Real.sqrt hsq
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

theorem exists_linearIsometryEquiv_of_inner_eq (f g : α → V) (h : ∀ a b, ⟪f a, f b⟫_ℂ = ⟪g a, g b⟫_ℂ) :
    ∃ U : V ≃ₗᵢ[ℂ] V, ∀ a, U (f a) = g a := by
  classical
  set F := Finsupp.linearCombination ℂ f with hF
  set G := Finsupp.linearCombination ℂ g with hG
  have hker : LinearMap.ker F ≤ LinearMap.ker G := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    have := norm_lc f g h c
    rw [← hF, ← hG, hc, norm_zero] at this
    exact norm_eq_zero.1 this.symm
  let φ : LinearMap.range F →ₗ[ℂ] V :=
    ((LinearMap.ker F).liftQ G hker).comp F.quotKerEquivRange.symm.toLinearMap
  have hφ : ∀ c, φ ⟨F c, LinearMap.mem_range_self F c⟩ = G c := by
    intro c
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hφn : ∀ x, ‖φ x‖ = ‖x‖ := by
    rintro ⟨_, c, rfl⟩
    rw [hφ c]
    show ‖G c‖ = ‖F c‖
    exact (norm_lc f g h c).symm
  let L : LinearMap.range F →ₗᵢ[ℂ] V := { φ with norm_map' := hφn }
  refine ⟨L.extend.toLinearIsometryEquiv rfl, fun a => ?_⟩
  have hfa : f a ∈ LinearMap.range F := ⟨Finsupp.single a 1, by simp [hF]⟩
  have e1 : (L.extend.toLinearIsometryEquiv rfl) (f a) = L.extend (f a) := rfl
  rw [e1, show f a = ((⟨f a, hfa⟩ : LinearMap.range F) : V) from rfl, LinearIsometry.extend_apply]
  have e2 : (⟨f a, hfa⟩ : LinearMap.range F) =
      ⟨F (Finsupp.single a 1), LinearMap.mem_range_self F _⟩ := by
    ext; simp [hF]
  rw [e2]
  show φ _ = g a
  rw [hφ]
  simp [hG]

end Gram

section Loc

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem wu_ne (u : D.what₂.Word) : ∃ x0, X.Wu u x0 ≠ 0 := by
  by_contra hc
  push Not at hc
  have h1 := (X.Wu_spec u).2.2.2.2
  simp [hc] at h1

open Classical in
theorem inner_upd (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) (x0 : X.B.I.Ginf)
    (y y' : Formalism.REAL.UJ (X.B.I.ε v)) :
    ⟪X.Wu u (Function.update x0 v y), X.Wu u (Function.update x0 v y')⟫_ℂ =
      ⟪X.Wloc u v y, X.Wloc u v y'⟫_ℂ * ∏ w ∈ Finset.univ.erase v, ⟪X.Wloc u w (x0 w), X.Wloc u w (x0 w)⟫_ℂ := by
  rw [X.Wu_tens, X.Wu_tens, X.tensU_inner, ← Finset.mul_prod_erase _ _ (Finset.mem_univ v)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hw), Function.update_of_ne (Finset.ne_of_mem_erase hw)]


open Classical in
theorem wloc_gram (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) (s : Formalism.REAL.UJ (X.B.I.ε v))
    (hs : InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (uMat s)) (a b : Formalism.REAL.UJ (X.B.I.ε v)) :
    ⟪X.Wloc u v (s * a), X.Wloc u v (s * b)⟫_ℂ = ⟪X.Wloc u v a, X.Wloc u v b⟫_ℂ := by
  obtain ⟨x0, hx0⟩ := wu_ne X u
  set S : X.B.I.Ginf := Function.update 1 v s with hSdef
  have hS : S ∈ X.SinfU u := by
    intro w
    by_cases hw : w = v
    · subst hw
      simpa [S] using hs
    · simp only [S, Function.update_of_ne hw, Pi.one_apply]
      refine ⟨fun a => ?_, ?_⟩ <;> simp [uMat]
  have hmul : ∀ y, S * Function.update x0 v y = Function.update x0 v (s * y) := by
    intro y
    funext w
    by_cases hw : w = v
    · subst hw
      simp [S]
    · simp [S, Function.update_of_ne hw]
  have hW : ∀ x, X.Wu u (S * x) = X.psiInfU u S • X.piU u S (X.Wu u x) := fun x => (X.Wu_spec u).1 S hS x
  have hU : ∀ x y, ⟪X.piU u S x, X.piU u S y⟫_ℂ = ⟪x, y⟫_ℂ := (X.piU_rep u).2.2.1 S hS
  have hψ : conj (X.psiInfU u S) * X.psiInfU u S = 1 := by
    rw [Complex.conj_mul', Formalism.L2.SG.RealObj.InfCut.norm_psiInfU X u S]
    simp
  have key : ∀ y y', ⟪X.Wu u (S * Function.update x0 v y), X.Wu u (S * Function.update x0 v y')⟫_ℂ =
      ⟪X.Wu u (Function.update x0 v y), X.Wu u (Function.update x0 v y')⟫_ℂ := by
    intro y y'
    rw [hW, hW, inner_smul_left, inner_smul_right, hU, ← mul_assoc, hψ, one_mul]
  have hK : (∏ w ∈ Finset.univ.erase v, ⟪X.Wloc u w (x0 w), X.Wloc u w (x0 w)⟫_ℂ) ≠ 0 := by
    have h0 := inner_upd X u v x0 (x0 v) (x0 v)
    rw [Function.update_eq_self] at h0
    have hne : ⟪X.Wu u x0, X.Wu u x0⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hx0
    rw [h0] at hne
    exact right_ne_zero_of_mul hne
  have h2 := key a b
  rw [hmul, hmul, inner_upd, inner_upd] at h2
  exact mul_right_cancel₀ hK h2

theorem wloc_unit (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) (s : Formalism.REAL.UJ (X.B.I.ε v))
    (hs : InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (uMat s)) :
    ∃ A : X.Vloc u v ≃ₗᵢ[ℂ] X.Vloc u v, ∀ x, X.Wloc u v (s * x) = (1 : ℂ) • A (X.Wloc u v x) := by
  obtain ⟨A, hA⟩ := exists_linearIsometryEquiv_of_inner_eq (fun x => X.Wloc u v x) (fun x => X.Wloc u v (s * x))
    (fun a b => (wloc_gram X u v s hs a b).symm)
  exact ⟨A, fun x => by rw [one_smul, hA x]⟩

theorem hilbertSchmidt_sq_nonneg {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V'] (A : V' →L[ℂ] V) : 0 ≤ hs2 A := by
  unfold Formalism.L2.SG.RealObj.hs2
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

theorem hilbertSchmidt_double_coset_invariant (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) (g s s' : Formalism.REAL.UJ (X.B.I.ε v))
    (hs : InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (uMat s))
    (hs' : InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) (uMat s')) :
    hs2 (JvX X u u' v (s * g * s'⁻¹)) = hs2 (JvX X u u' v g) := by
  haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
  haveI := FiniteDimensional.complete ℂ (X.Vloc u' v)
  obtain ⟨A, hA⟩ := wloc_unit X u v s hs
  obtain ⟨B, hB⟩ := wloc_unit X u' v s' hs'
  unfold JvX Formalism.L2.SG.RealObj.Jv
  rw [Formalism.L2.SG.RealObj.InfCut.OO_equiv (Formalism.REAL.muG (X.B.I.ε v)) (X.Wloc u v) (X.Wloc u' v) g s s' 1 1 A B hA hB,
    Formalism.L2.SG.RealObj.InfCut.hilbert_schmidt_smul, Formalism.L2.SG.RealObj.InfCut.hilbert_schmidt_comp_left _ _ (fun x => A.norm_map x),
    Formalism.L2.SG.RealObj.InfCut.hilbert_schmidt_comp_right]
  simp

theorem jvX_meas (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    Measurable (fun g => hs2 (JvX X u u' v g)) := by
  haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
  have hF : Continuous (fun p : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) =>
      Formalism.L2.SG.TermOp.rk1 (X.Wloc u v p.2) (X.Wloc u' v (p.1⁻¹ * p.2))) :=
    Formalism.L2.SG.RealObj.RankOneTensors.continuous_rankOneOperator ((X.Wloc_cont u v).comp continuous_snd)
      ((X.Wloc_cont u' v).comp ((continuous_fst.inv).mul continuous_snd))
  have hJ : StronglyMeasurable (fun g => JvX X u u' v g) := by
    have := hF.stronglyMeasurable.integral_prod_right' (ν := Formalism.REAL.muG (X.B.I.ε v))
    unfold JvX Formalism.L2.SG.RealObj.Jv Formalism.L2.SG.TermOp.OO
    simpa [Measure.restrict_univ] using this
  have hc : Continuous (fun A : X.Vloc u' v →L[ℂ] X.Vloc u v => hs2 A) := by
    unfold hs2
    exact continuous_finsetSum _ fun i _ =>
      ((ContinuousLinearMap.apply ℂ (X.Vloc u v) (stdOrthonormalBasis ℂ (X.Vloc u' v) i)).continuous.norm.pow 2)
  exact hc.measurable.comp hJ.measurable

end Loc

def StepSecX : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F),
    ∃ h : (Fin (D.R.rS + 1) → ℂ) → Formalism.REAL.UJ (X.B.I.ε v), Measurable h ∧
      ∀ cv ∈ GoodV (D := D) u u', Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat (h cv)) = Matrix.diagonal cv

theorem locRep_of_sec (hS : StepSecX) {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) :
    ∃ L, LocRep X u u' L := by
  classical
  choose h hm hsec using hS D X u u'
  refine ⟨fun v cv => hs2 (JvX X u u' v (h v cv)),
    ⟨fun v => ⟨(jvX_meas X u u' v).comp (hm v), fun cv => hilbertSchmidt_sq_nonneg _⟩, ?_⟩⟩
  intro c hc v
  have hex : ∃ γ, HasDiag X u u' 1 c γ := ⟨fun w => h w (c w), fun w => hsec w (c w) (hc w)⟩
  have hh : HasDiag X u u' 1 c (hOf X u u' 1 c) := by
    unfold hOf; rw [dite_eq_left hex]; exact hex.choose_spec
  have hee : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0 := fun a b => by
    rw [show X.eR a = X.crd (X.eX a) from rfl, show X.eR b = X.crd (X.eX b) from rfl,
      Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, X.ee, map_zero]
  have hez : ∀ (w : D.what₂.Word) a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR w)) = 0 :=
    fun w a => by
      rw [show X.eR a = X.crd (X.eX a) from rfl, show X.zR w = X.crd (X.zu w) from rfl,
        Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, (X.zu_orth w a).1, map_zero]
  obtain ⟨s, s', hs, hs', heq⟩ := Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.diagDC_pair (X.B.I.ε v) 1 _ _ _ (Tw u) (Tw u')
    hee (hez u) (hez u') (Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hermitian_z_z_eq_neg X v u) (Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hermitian_z_z_eq_neg X v u')
    (c v) (hc v).1 (hc v).2 (h v (c v)) ((hOf X u u' 1 c) v) (hsec v (c v) (hc v)) (hh v)
  show hs2 (JvX X u u' v ((hOf X u u' 1 c) v)) = hs2 (JvX X u u' v (h v (c v)))
  rw [heq]
  exact hilbertSchmidt_double_coset_invariant X u u' v _ s s' hs hs'

end Formalism.L2.SG.Pf.Carrier.EnergyPfLoc
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyConst
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.EnergyConst

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.EnergyPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

def e1 (D : D7) : ℕ := (D.R.rS + 1) * (8 * D.R.rS ^ 2 + 10 * D.R.rS + 3) / 3

def rdExp (D : D7) : ℕ := 2 * D.R.rS * (D.R.rS + 1) * (D.R.k - 1) + e1 D

def Anum (D : D7) : ℝ := D.host.rdE ^ rdExp D * ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (3 * (D.R.rS + 1))

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def Kexp (P : Parts X u u') : ℝ := Anum D / P.Gam0


variable (X u u') in
def LemmaMS (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : Prop :=
  (Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeArchimedean * ∏ p, (Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeAtPlace p =
    D.host.rdE ^ (D.R.f * e1 D) * ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (D.R.f * ((D.R.rS + 1) * (2 * D.R.rS + 3))) *
      (Formalism.L2.SG.LocVol.locOf X u u' ψ).volZZ

theorem anum_pow : Anum D ^ D.R.f =
    Formalism.L2.SG.MassDataConc.kapN D * (D.host.rdE ^ (D.R.f * e1 D) *
      ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (D.R.f * ((D.R.rS + 1) * (2 * D.R.rS + 3)))) := by
  have hb : ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ≠ 0 := by
    unfold Formalism.MainNotions.S.Lat.gS
    exact Nat.cast_ne_zero.mpr (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  have key : ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (D.R.f * ((D.R.rS + 1) * (2 * D.R.rS + 3))) =
      ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (2 * D.R.f * D.R.rS * (D.R.rS + 1)) *
        ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (3 * (D.R.rS + 1) * D.R.f) := by
    rw [← pow_add]
    congr 1
    ring
  rw [key]
  simp only [Anum, rdExp, Formalism.L2.SG.MassDataConc.kapN]
  rw [mul_pow, ← pow_mul, ← pow_mul]
  field_simp
  ring

theorem rdE_pos' : 0 < D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  apply Real.rpow_pos_of_pos
  have h := NumberField.discr_ne_zero (K := D.host.E)
  exact abs_pos.mpr (by exact_mod_cast h)

theorem energy_constant_nonneg (P : Parts X u u') : 0 ≤ P.Gam0 := by
  unfold Formalism.L2.SG.Pf.Carrier.Parts.Gam0 Formalism.FourierDecayAlt.D.GamLev
  apply Finset.prod_nonneg
  intro l _
  apply div_nonneg
  · apply zpow_nonneg
    unfold Formalism.FourierDecayAlt.D.kapG Formalism.FourierDecayAlt.S6.rd
    positivity
  · unfold Formalism.FourierDecayAlt.D.deG Formalism.FourierDecayAlt.S6.rd
    positivity

theorem constPin_of (P : Parts X u u') (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    (hC : Formalism.L2.SG.LocVol.ProdConv X u u' ψ) (hMS : LemmaMS X u u' ψ)
    (hf : Fintype.card (InfinitePlace X.B.I.F) = D.R.f) :
    ConstPin P ψ (fun _ => Kexp P) := by
  obtain ⟨-, -, -, -, -, -, hZZ, hPP, -⟩ := hC
  have hb : ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ≠ 0 := by
    unfold Formalism.MainNotions.S.Lat.gS
    exact Nat.cast_ne_zero.mpr (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  have hrd : 0 < D.host.rdE := rdE_pos'
  have hA : 0 ≤ Anum D := by
    unfold Anum
    exact mul_nonneg (pow_nonneg hrd.le _) (pow_nonneg (Nat.cast_nonneg _) _)
  have hK0 : 0 ≤ Kexp P := div_nonneg hA (energy_constant_nonneg P)
  refine ⟨fun _ => hK0, ?_⟩
  have hfS : P.S.f = D.R.f := by
    rw [← hf, ← Fintype.card_fin P.S.f]
    exact Fintype.card_congr P.τ
  have hprod : ∏ _v : InfinitePlace X.B.I.F, Kexp P = Anum D ^ D.R.f / P.Gam0 ^ D.R.f := by
    rw [Finset.prod_const, Finset.card_univ, hf, Kexp, div_pow]
  have hvZZ : 0 < (Formalism.L2.SG.LocVol.locOf X u u' ψ).volZZ := hZZ
  have hvPP : 0 < (Formalism.L2.SG.LocVol.locOf X u u' ψ).volPP := by
    show 0 < ∏ l : Fin (D.R.rS + 1), ∏' v : Formalism.L2.SG.LocVol.PlX X, Formalism.L2.SG.LocVol.PPX X u u' ψ l v
    exact Finset.prod_pos (fun l _ => (hPP l).2)
  have hkap : Formalism.L2.SG.MassDataConc.kapN D ≠ 0 := by
    unfold Formalism.L2.SG.MassDataConc.kapN
    exact mul_ne_zero (pow_ne_zero _ hrd.ne') (inv_ne_zero (pow_ne_zero _ hb))
  have hM : D.host.rdE ^ (D.R.f * e1 D) *
      ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (D.R.f * ((D.R.rS + 1) * (2 * D.R.rS + 3))) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hrd.ne') (pow_ne_zero _ hb)
  rw [hprod, anum_pow, hMS, hfS]
  field_simp

end Formalism.L2.SG.Pf.Carrier.EnergyConst
end
end
