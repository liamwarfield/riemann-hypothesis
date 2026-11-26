module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormula
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaFunctionMemSpanLocalSchrodingerModelsSplit
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCanonicalModuleSuccessor

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFramesReadSplitPlaceUnitaryGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFramesReadSplitPlaceUnitaryGroup
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitFrameRead

theorem tensCast_one_tmul {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2) (x : E) :
    GlobalTheory.NJoin.tensCast h ((1 : FiniteAdeleRing (𝓞 F1) F1) ⊗ₜ[F1] x) = x ⊗ₜ[F2] (1 : FiniteAdeleRing (𝓞 F2) F2) := by
  subst h; rfl

theorem gen_supp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (fin : A →+* B) (Ψ : B →+* C) {m k : ℕ}
    (M : Matrix (Fin m) (Fin m) A) (β : Matrix (Fin m) (Fin k) B) (K : Matrix (Fin k) (Fin k) B) (β' : Matrix (Fin k) (Fin m) B)
    (h1 : β * β' = 1) (hM : M.map fin = β * K * β') (hK : K.map Ψ = 1) : ((M - 1).map fin).map Ψ = 0 := by
  rw [Matrix.map_sub _ (map_sub _), hM, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_sub _ (map_sub _),
    Matrix.map_mul, Matrix.map_mul, hK, Matrix.mul_one, ← Matrix.map_mul, h1, sub_self]


set_option maxHeartbeats 1000000 in
theorem side_loc (D : D7) (s : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E)
    (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E))
    (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E)
    (hπ : ∀ a : Formalism.L2.Theta.AE D, p.π a = c (s.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a))))
    (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n) (hV : GlobalTheory.NJoin.StdFrame hF PV) :
    ∃ FS : GlobalTheory.LocMod.Frame (s.w.adicCompletion D.host.E) V.rank (Fin n), ∀ h, TrivOutside {s.v} h →
      p.IsLoc FS (PV.ψ h) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h)) := by
  obtain ⟨⟨β, β', h1, h2, hm⟩, -⟩ := hV
  let Φ := c.toRingHom.comp (s.proj.comp (GlobalTheory.NJoin.tensCast hF).toRingHom)
  refine ⟨⟨β.map Φ, β'.map Φ, ?_, ?_⟩, fun h hh => ⟨?_, ?_⟩⟩
  · rw [← Matrix.map_mul, h1]; exact Matrix.map_one _ (map_zero Φ) (map_one Φ)
  · rw [← Matrix.map_mul, h2]; exact Matrix.map_one _ (map_zero Φ) (map_one Φ)
  · intro i j
    apply GlobalTheory.T.splitPlaceIdempotent_mul_eq_self_of_supported D s hF p c hπ
    · have hk := MonoidHom.mem_ker.1 (PV.into h)
      have e2 : ((Formalism.L2.Theta.mt V (PV.ψ h)) - 1).map (Formalism.L2.Theta.infPart D) = 0 := by
        rw [Matrix.map_sub _ (map_sub (Formalism.L2.Theta.infPart D)),
          Matrix.map_one _ (map_zero (Formalism.L2.Theta.infPart D)) (map_one (Formalism.L2.Theta.infPart D))]
        have e3 : (Formalism.L2.Theta.mt V (PV.ψ h)).map (Formalism.L2.Theta.infPart D) = (Formalism.L2.Theta.infHom V (PV.ψ h)).val := rfl
        rw [e3, hk, Units.val_one, sub_self]
      exact congrFun (congrFun e2 i) j
    · intro v' hv'
      have hh' := hh v' (by simpa using hv')
      have e4 := gen_supp (Formalism.L2.Theta.finPart D) ((ReciprocityTheory.Aut.compAt D.host.E v').comp (GlobalTheory.NJoin.tensCast hF).toRingHom)
        (Formalism.L2.Theta.mt V (PV.ψ h)) β _ β' h1 (hm h) (by
          rw [← hh']
          ext a b
          exact congrArg (ReciprocityTheory.Aut.compAt D.host.E v') (RingEquiv.apply_symm_apply _ _))
      exact congrFun (congrFun e4 i) j
  · have e7 : (Formalism.L2.Theta.mt V (PV.ψ h)).map p.π = ((Formalism.L2.Theta.mt V (PV.ψ h)).map (Formalism.L2.Theta.finPart D)).map Φ :=
      Matrix.ext fun a b => hπ _
    have e5 : (Formalism.L2.Theta.mt V (PV.ψ h)).map (Formalism.L2.Theta.finPart D) = _ := hm h
    have hK : ((h.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.NJoin.tensCast hF).symm).map Φ =
        (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h)).val := by
      refine Matrix.ext fun a b => ?_
      exact congrArg (fun y => c (s.proj y)) (RingEquiv.apply_symm_apply _ _)
    rw [e7, e5, ← hK]
    exact (Matrix.map_mul).trans (congrArg (· * β'.map Φ) Matrix.map_mul)

theorem main : ∀ (D : D7) (V W : Formalism.BasicNotions.TH.HSp D) (n r : ℕ) (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n) (PW : Formalism.IndefR.principalLevelFrame.RowPsi W r) (hF : D.host.F = maximalRealSubfield D.host.E), GlobalTheory.NJoin.StdFrame hF PV → GlobalTheory.NJoin.StdFrame hF PW → ∀ (s : SplitPlace D.host.E), ∃ (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E)), Formalism.L2.JoinChr.IsPlIdem D p.e s.w ∧ (∀ x : D.host.E, p.pr x = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) ∧ ∃ (FS : GlobalTheory.LocMod.Frame (s.w.adicCompletion D.host.E) V.rank (Fin n)) (FT : GlobalTheory.LocMod.Frame (s.w.adicCompletion D.host.E) W.rank (Fin r)) (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E), Continuous c ∧ (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) ∧ (∀ h, TrivOutside {s.v} h → p.IsLoc FS (PV.ψ h) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h))) ∧ ∀ g, TrivOutside {s.v} g → p.IsLoc FT (PW.ψ g) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc r g)) := by
  intro D V W n r PV PW hF hV hW s
  obtain ⟨p, c, hId, hc, hci, hπ⟩ := GlobalTheory.T.exists_splitLocalPlaceData_at_splitPlace D s hF
  have hpr : ∀ x : D.host.E, p.pr x = algebraMap D.host.E (s.w.adicCompletion D.host.E) x := by
    intro x
    unfold GlobalTheory.LocMod.Place.pr
    rw [hπ]
    have e1 : Formalism.L2.Theta.finPart D (Formalism.L2.Theta.incA D x) =
        (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] x := by
      simp [Formalism.L2.Theta.finPart, Formalism.L2.Theta.incA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.map_tmul]
    rw [e1, tensCast_one_tmul, ← hci x]
    congr 1
    simp [ReciprocityTheory.Aut.SplitPlace.proj]
  obtain ⟨FS, hFS⟩ := side_loc D s hF p c hπ V n PV hV
  obtain ⟨FT, hFT⟩ := side_loc D s hF p c hπ W r PW hW
  exact ⟨p, hId, hpr, FS, FT, c, hc, hci, hFS, hFT⟩

end GlobalTheory.SplitFrameRead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFramesReadSplitPlaceUnitaryGroupStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardFrames_read_splitPlace_unitaryGroup : ∀ (D : D7) (V W : Formalism.BasicNotions.TH.HSp D) (n r : ℕ) (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n) (PW : Formalism.IndefR.principalLevelFrame.RowPsi W r) (hF : D.host.F = maximalRealSubfield D.host.E), GlobalTheory.NJoin.StdFrame hF PV → GlobalTheory.NJoin.StdFrame hF PW → ∀ (s : SplitPlace D.host.E), ∃ (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E)), Formalism.L2.JoinChr.IsPlIdem D p.e s.w ∧ (∀ x : D.host.E, p.pr x = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) ∧ ∃ (FS : GlobalTheory.LocMod.Frame (s.w.adicCompletion D.host.E) V.rank (Fin n)) (FT : GlobalTheory.LocMod.Frame (s.w.adicCompletion D.host.E) W.rank (Fin r)) (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E), Continuous c ∧ (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) ∧ (∀ h, TrivOutside {s.v} h → p.IsLoc FS (PV.ψ h) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h))) ∧ ∀ g, TrivOutside {s.v} g → p.IsLoc FT (PW.ψ g) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc r g)) := by
  first | exact @GlobalTheory.SplitFrameRead.main | exact GlobalTheory.SplitFrameRead.main | (intros; apply GlobalTheory.SplitFrameRead.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalComponentOfIdelicCharacterAgreement
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalComponentOfIdelicCharacterAgreement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.LocMod

theorem Place.isComp_of_chrEq : ∀ (D : D7) (s : SplitPlace D.host.E) (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E)), Formalism.L2.JoinChr.IsPlIdem D p.e s.w → (∀ x : D.host.E, p.pr x = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ (c : (Formalism.L2.Theta.AE D)ˣ →* Circle) (χ : HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ → ∀ μw, GlobalTheory.NPin.IsComp χ s.w μw → p.IsComp c μw := by
  intro D s p hpl hpr c χ hc μw hμ
  have he : p.e * p.e = p.e := hpl.1
  have e_ι : ∀ x, p.e * p.ι x = p.ι x := fun x => by rw [← p.ι_π, p.π_ι]
  have hm : ∀ x y, p.ι (x * y) = p.ι x * p.ι y := fun x y => by
    conv_lhs => rw [← p.π_ι x, ← p.π_ι y, ← RingHom.map_mul, p.ι_π, ← mul_assoc, e_ι]
  have ho : p.ι 1 = p.e := by rw [← p.π.map_one, p.ι_π, mul_one]
  let j0 : s.w.adicCompletion D.host.E →* Formalism.L2.Theta.AE D :=
    { toFun := fun x => p.ι x + (1 - p.e)
      map_one' := by rw [ho, add_sub_cancel]
      map_mul' := fun x y => by
        rw [hm]
        linear_combination e_ι x + e_ι y - he }
  have hj0 : Continuous j0 := p.cont_ι.add continuous_const
  let j : (s.w.adicCompletion D.host.E)ˣ →* (Formalism.L2.Theta.AE D)ˣ := Units.map j0
  have hj : Continuous j := by
    refine Units.continuous_iff.2 ⟨hj0.comp Units.continuous_val, ?_⟩
    have : (fun u => ((j u)⁻¹ : (Formalism.L2.Theta.AE D)ˣ).val) =
        fun u : (s.w.adicCompletion D.host.E)ˣ => j0 ((u⁻¹ : (s.w.adicCompletion D.host.E)ˣ) : s.w.adicCompletion D.host.E) := by
      funext u; rw [← map_inv]; rfl
    rw [this]
    exact hj0.comp Units.continuous_coe_inv
  have hcc : Continuous c := hc.1.1
  have hF2 : Continuous fun u => ((c (j u) : Circle) : ℂ) := (continuous_subtype_val.comp hcc).comp hj
  have hμc : Continuous μw := by
    refine continuous_of_continuousAt_one μw ?_
    have hker : (μw.ker : Set (s.w.adicCompletion D.host.E)ˣ) ∈ nhds 1 := hμ.1.mem_nhds (by simp)
    have : (fun _ => (1 : ℂˣ)) =ᶠ[nhds 1] μw := Filter.mem_of_superset hker fun x hx => (MonoidHom.mem_ker.1 hx).symm
    have h2 := (continuousAt_const.congr this).tendsto
    rw [map_one] at h2
    rw [ContinuousAt, map_one]
    exact h2
  have hF1 : Continuous fun u => ((μw u : ℂˣ) : ℂ) := Units.continuous_val.comp hμc
  have hd : Dense (Set.range (Units.map (algebraMap D.host.E (s.w.adicCompletion D.host.E) : D.host.E →* s.w.adicCompletion D.host.E))) := by
    rw [dense_iff_inter_open]
    rintro U hU ⟨u, hu⟩
    have hoe : Topology.IsOpenEmbedding (Units.val : (s.w.adicCompletion D.host.E)ˣ → s.w.adicCompletion D.host.E) :=
      { toIsEmbedding := Units.isEmbedding_val₀
        isOpen_range := by
          have : Set.range (Units.val : (s.w.adicCompletion D.host.E)ˣ → s.w.adicCompletion D.host.E) = {0}ᶜ := by
            ext y
            exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun h => ⟨Units.mk0 y h, rfl⟩⟩
          rw [this]; exact isOpen_compl_singleton }
    obtain ⟨y, hy⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := D.host.E) s.w).exists_mem_open
      (hoe.isOpenMap U hU) ⟨u, u, hu, rfl⟩
    obtain ⟨v, hv, hvy⟩ := hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact v.ne_zero (by simpa using hvy)
    refine ⟨v, hv, Units.mk0 y hy0, Units.ext ?_⟩
    simpa using hvy.symm
  have key : ∀ x : D.host.Eˣ, ((μw (Units.map (algebraMap D.host.E (s.w.adicCompletion D.host.E) : D.host.E →* s.w.adicCompletion D.host.E) x) : ℂˣ) : ℂ)
      = ((c (j (Units.map (algebraMap D.host.E (s.w.adicCompletion D.host.E) : D.host.E →* s.w.adicCompletion D.host.E) x)) : Circle) : ℂ) := by
    intro x
    refine (congrArg Units.val (hμ.2 x)).trans (hc.2 s.w p.e hpl x _ ?_).symm
    change p.ι (algebraMap D.host.E (s.w.adicCompletion D.host.E) x) + (1 - p.e) = _
    rw [← hpr, GlobalTheory.LocMod.Place.pr, p.ι_π, Formalism.L2.JoinChr.locE]
    ring
  have heq := Continuous.ext_on hd hF1 hF2 (by rintro _ ⟨x, rfl⟩; exact key x)
  intro x a ha
  have hja : j x = a := Units.ext ha.symm
  rw [← hja]
  exact congrFun heq x

end GlobalTheory.LocMod
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalComponentOfIdelicCharacterAgreementStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localComponent_of_idelicCharacterAgreement : ∀ (D : D7) (s : SplitPlace D.host.E) (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E)), Formalism.L2.JoinChr.IsPlIdem D p.e s.w → (∀ x : D.host.E, p.pr x = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ (c : (Formalism.L2.Theta.AE D)ˣ →* Circle) (χ : HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ → ∀ μw, IsComp χ s.w μw → p.IsComp c μw := by
  first | exact @GlobalTheory.LocMod.Place.isComp_of_chrEq | exact GlobalTheory.LocMod.Place.isComp_of_chrEq | (intros; apply GlobalTheory.LocMod.Place.isComp_of_chrEq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearModelFourierTransformExchange
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearModelFourierTransformExchange
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.LinearModelFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def flat (n r : ℕ) : Matrix (Fin n) (Fin r) k ≃ₜ (Fin n × Fin r → k) where
  toFun z p := z p.1 p.2
  invFun y := Matrix.of (Function.curry y)
  left_inv z := rfl
  right_inv y := rfl
  continuous_toFun := continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)
  continuous_invFun := continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)

def flatT (n r : ℕ) : Matrix (Fin r) (Fin n) k ≃ₜ (Fin n × Fin r → k) where
  toFun x p := x p.2 p.1
  invFun y := Matrix.of fun j i => y (i, j)
  left_inv x := rfl
  right_inv y := rfl
  continuous_toFun := continuous_pi fun p => (continuous_apply p.1).comp (continuous_apply p.2)
  continuous_invFun := continuous_pi fun j => continuous_pi fun i => continuous_apply (i, j)

theorem trace_mul_eq_dotProduct {n r : ℕ} (x : Matrix (Fin r) (Fin n) k) (y : Matrix (Fin n) (Fin r) k) :
    trace (x * y) = flat n r y ⬝ᵥ flatT n r x := by
  simp only [trace, diag, Matrix.mul_apply, dotProduct, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show x j i * y i j = y i j * x j i
  ring

theorem comp_mem_SB {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : Y ≃ₜ X) {f : X → ℂ}
    (hf : f ∈ GlobalTheory.SplitWeil.SB X) : (f ∘ e) ∈ GlobalTheory.SplitWeil.SB Y :=
  ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩

variable [MeasurableSpace k]

def fou (ψ : AddChar k Circle) (ν : Measure k) (n r : ℕ) (Φ : Matrix (Fin n) (Fin r) k → ℂ)
    (x : Matrix (Fin r) (Fin n) k) : ℂ :=
  ∫ y, Φ y * (ψ (trace (x * y)) : ℂ) ∂(volM ν (Fin n) (Fin r))

variable [BorelSpace k] {ψ : AddChar k Circle} (ν : Measure k) [ν.IsAddHaarMeasure] {n r : ℕ}

theorem fou_eq_pi (Φ : Matrix (Fin n) (Fin r) k → ℂ) (x : Matrix (Fin r) (Fin n) k) :
    fou ψ ν n r Φ x = ∫ z, (Φ ∘ (flat n r).symm) z * (ψ (z ⬝ᵥ flatT n r x) : ℂ) ∂(Measure.pi fun _ => ν) := by
  rw [fou, integral_volM_eq_pi]
  congr 1
  funext z
  rw [trace_mul_eq_dotProduct]
  rfl

theorem integrable_fou (hψ : Continuous ψ) {f : Matrix (Fin n) (Fin r) k → ℂ}
    (hf : f ∈ SB (Matrix (Fin n) (Fin r) k)) (x : Matrix (Fin r) (Fin n) k) :
    Integrable (fun y => f y * (ψ (trace (x * y)) : ℂ)) (volM ν (Fin n) (Fin r)) := by
  haveI := secondCountable k
  letI : MeasurableSpace (Matrix (Fin n) (Fin r) k) := GlobalTheory.SplitWeil.matrixMeasurableSpace
  haveI : BorelSpace (Matrix (Fin n) (Fin r) k) := inferInstanceAs (BorelSpace (Fin n → Fin r → k))
  haveI : (volM ν (Fin n) (Fin r)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : IsFiniteMeasureOnCompacts (volM ν (Fin n) (Fin r)) := inferInstance
  have hc : Continuous fun y : Matrix (Fin n) (Fin r) k => f y * (ψ (trace (x * y)) : ℂ) :=
    hf.1.continuous.mul (continuous_subtype_val.comp
      (hψ.comp ((continuous_const.matrix_mul continuous_id).matrix_trace)))
  exact hc.integrable_of_hasCompactSupport (μ := volM ν (Fin n) (Fin r)) hf.2.mul_right

theorem fou_mem (hψ : Continuous ψ) (h1 : ψ ≠ 1) {f : Matrix (Fin n) (Fin r) k → ℂ}
    (hf : f ∈ SB (Matrix (Fin n) (Fin r) k)) : fou ψ ν n r f ∈ SB (Matrix (Fin r) (Fin n) k) := by
  haveI := secondCountable k
  obtain ⟨c, hc⟩ := (conductor_exists k).1 ψ hψ h1
  have h2 := FourierPi.fourier_mem_SB (Measure.pi fun _ : Fin n × Fin r => ν) hc
    (comp_mem_SB (flat n r).symm hf)
  have h3 : fou ψ ν n r f = (fun y => ∫ z, (f ∘ (flat n r).symm) z * (ψ (z ⬝ᵥ y) : ℂ)
      ∂(Measure.pi fun _ => ν)) ∘ flatT n r := funext fun x => fou_eq_pi ν f x
  rw [h3]
  exact comp_mem_SB _ h2

theorem nabs_det_inv {m : ℕ} (g : GL (Fin m) k) :
    nabs k (Matrix.GeneralLinearGroup.det g⁻¹) = (nabs k (Matrix.GeneralLinearGroup.det g))⁻¹ := by
  simp [nabs, map_inv]

theorem fou_om (μ : kˣ →* ℂˣ) (gk : GL (Fin n) k) (hk : GL (Fin r) k) (Φ : Matrix (Fin n) (Fin r) k → ℂ) :
    fou ψ ν n r (om μ hk gk Φ) = om μ⁻¹ gk hk (fou ψ ν n r Φ) := by
  funext x
  set F : Matrix (Fin n) (Fin r) k → ℂ :=
    fun z => Φ z * (ψ (trace (((hk⁻¹ : GL (Fin r) k).val * x * gk.val) * z)) : ℂ) with hF
  have key := integral_comp_mul_mul_volM ν hk gk⁻¹ F
  have htr : ∀ y : Matrix (Fin n) (Fin r) k,
      trace ((hk⁻¹ : GL (Fin r) k).val * x * gk.val * ((gk⁻¹ : GL (Fin n) k).val * y * hk.val)) =
        trace (x * y) := by
    intro y
    have e : (hk⁻¹ : GL (Fin r) k).val * x * gk.val * ((gk⁻¹ : GL (Fin n) k).val * y * hk.val) =
        (hk⁻¹ : GL (Fin r) k).val * (x * y * hk.val) := by
      calc _ = (hk⁻¹ : GL (Fin r) k).val * (x * (gk.val * (gk⁻¹ : GL (Fin n) k).val) * y * hk.val) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [Units.mul_inv, Matrix.mul_one]
    rw [e, trace_mul_comm]
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  set A : ℂ := (μ (Matrix.GeneralLinearGroup.det hk) : ℂ) * ((μ (Matrix.GeneralLinearGroup.det gk))⁻¹ : ℂˣ) *
    ((nabs k (Matrix.GeneralLinearGroup.det hk) ^ ((Fintype.card (Fin n) : ℝ) / 2) : ℝ) : ℂ) *
    ((nabs k (Matrix.GeneralLinearGroup.det gk) ^ (-(Fintype.card (Fin r) : ℝ) / 2) : ℝ) : ℂ) with hA
  have lhs : fou ψ ν n r (om μ hk gk Φ) x =
      A * ∫ y, F ((gk⁻¹ : GL (Fin n) k).val * y * hk.val) ∂(volM ν (Fin n) (Fin r)) := by
    rw [fou, ← integral_const_mul]
    congr 1
    funext y
    simp only [om, hA, hF, htr]
    ring
  have hFint : ∫ z, F z ∂(volM ν (Fin n) (Fin r)) =
      fou ψ ν n r Φ ((hk⁻¹ : GL (Fin r) k).val * x * gk.val) := rfl
  rw [lhs, key, hFint, nabs_det_inv]
  simp only [om, hA, MonoidHom.inv_apply, inv_inv, Complex.real_smul, Fintype.card_fin]
  set a := nabs k (Matrix.GeneralLinearGroup.det gk) with ha
  set b := nabs k (Matrix.GeneralLinearGroup.det hk) with hb
  have ha0 : 0 < a := nabs_pos' _
  have hb0 : 0 < b := nabs_pos' _
  have h1 : ((b ^ ((n : ℝ) / 2) : ℝ) : ℂ) * ((b ^ (-(n : ℝ)) : ℝ) : ℂ) = ((b ^ (-(n : ℝ) / 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add hb0]
    ring_nf
  have h2 : ((a ^ (-(r : ℝ) / 2) : ℝ) : ℂ) * ((a⁻¹ ^ (-(r : ℝ)) : ℝ) : ℂ) = ((a ^ ((r : ℝ) / 2) : ℝ) : ℂ) := by
    rw [Real.inv_rpow ha0.le, ← Real.rpow_neg ha0.le, neg_neg, ← Complex.ofReal_mul, ← Real.rpow_add ha0]
    ring_nf
  rw [Complex.ofReal_mul]
  linear_combination
    ((μ (Matrix.GeneralLinearGroup.det hk) : ℂ) * ((μ (Matrix.GeneralLinearGroup.det gk))⁻¹ : ℂˣ) *
      fou ψ ν n r Φ ((hk⁻¹ : GL (Fin r) k).val * x * gk.val)) *
    (((a ^ (-(r : ℝ) / 2) : ℝ) : ℂ) * ((a⁻¹ ^ (-(r : ℝ)) : ℝ) : ℂ) * h1 + ((b ^ (-(n : ℝ) / 2) : ℝ) : ℂ) * h2)

def fouL (hψ : Continuous ψ) (h1 : ψ ≠ 1) :
    SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] SB (Matrix (Fin r) (Fin n) k) where
  toFun Φ := ⟨fou ψ ν n r Φ.1, fou_mem ν hψ h1 Φ.2⟩
  map_add' Φ Ψ := by
    apply Subtype.ext
    funext x
    show fou ψ ν n r (Φ.1 + Ψ.1) x = fou ψ ν n r Φ.1 x + fou ψ ν n r Ψ.1 x
    simp only [fou, Pi.add_apply, add_mul]
    exact integral_add (integrable_fou ν hψ Φ.2 x) (integrable_fou ν hψ Ψ.2 x)
  map_smul' c Φ := by
    apply Subtype.ext
    funext x
    show fou ψ ν n r (c • Φ.1) x = c * fou ψ ν n r Φ.1 x
    simp only [fou, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul _ _

theorem fouL_surjective (hψ : Continuous ψ) (h1 : ψ ≠ 1) (hν : IsSelfDual ψ ν) :
    Function.Surjective (fouL (n := n) (r := r) ν hψ h1) := by
  intro G
  obtain ⟨Φ₀, hΦ₀⟩ := (FourierSurj.hat_surjective k (Fin n × Fin r) ψ hψ h1 ν hν).2
    ⟨_, comp_mem_SB (flatT n r).symm G.2⟩
  refine ⟨⟨Φ₀.1 ∘ flat n r, comp_mem_SB _ Φ₀.2⟩, Subtype.ext (funext fun x => ?_)⟩
  show fou ψ ν n r (Φ₀.1 ∘ flat n r) x = G.1 x
  have h2 := congrFun hΦ₀ (flatT n r x)
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat, Function.comp_apply, Homeomorph.symm_apply_apply] at h2
  rw [fou_eq_pi, ← h2]
  congr 1
  funext z
  simp only [Function.comp_apply, Homeomorph.apply_symm_apply, dotProduct_comm]

end GlobalTheory.LinearModelFourier

theorem GlobalTheory.linearModel_fourier : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n r : ℕ), ∃ τ : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] GlobalTheory.SplitWeil.SB (Matrix (Fin r) (Fin n) k), Function.Surjective τ ∧ ∀ (μ : kˣ →* ℂˣ) (gk : GL (Fin n) k) (hk : GL (Fin r) k) (Φ Φ' : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) k)), Φ'.1 = GlobalTheory.SplitWeil.om μ hk gk Φ.1 → (τ Φ').1 = GlobalTheory.SplitWeil.om μ⁻¹ gk hk (τ Φ).1 := by
  intro k _ _ _ _ n r
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  obtain ⟨ψ, hψ, h1, -⟩ := (conductor_exists k).2.1
  obtain ⟨ν, hν⟩ := (selfDual_measure k ψ hψ h1).1
  haveI := hν.1
  refine ⟨GlobalTheory.LinearModelFourier.fouL ν hψ h1, GlobalTheory.LinearModelFourier.fouL_surjective ν hψ h1 hν,
    fun μ gk hk Φ Φ' hΦ => ?_⟩
  show GlobalTheory.LinearModelFourier.fou ψ ν n r Φ'.1 = om μ⁻¹ gk hk (GlobalTheory.LinearModelFourier.fou ψ ν n r Φ.1)
  rw [hΦ]
  exact GlobalTheory.LinearModelFourier.fou_om ν μ gk hk Φ.1
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearModelFourierTransformExchangeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearModel_fourier_transform_exchange : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n r : ℕ), ∃ τ : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] GlobalTheory.SplitWeil.SB (Matrix (Fin r) (Fin n) k), Function.Surjective τ ∧ ∀ (μ : kˣ →* ℂˣ) (gk : GL (Fin n) k) (hk : GL (Fin r) k) (Φ Φ' : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) k)), Φ'.1 = GlobalTheory.SplitWeil.om μ hk gk Φ.1 → (τ Φ').1 = GlobalTheory.SplitWeil.om μ⁻¹ gk hk (τ Φ).1 := by
  first | exact @GlobalTheory.linearModel_fourier | exact GlobalTheory.linearModel_fourier | (intros; apply GlobalTheory.linearModel_fourier <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaFunctionsSpannedHeckeTwistedStandardFrame
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LinModSpan

theorem isComp_mul_inv {E : Type} [Field E] [NumberField E] {μ η : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    {μw ηw : (w.adicCompletion E)ˣ →* ℂˣ} (hμ : IsComp μ w μw) (hη : IsComp η w ηw) :
    IsComp (μ * η⁻¹) w (μw * ηw⁻¹) := by
  refine ⟨?_, fun x => ?_⟩
  · have h1 := hμ.1
    have h2 := hη.1
    unfold GlobalTheory.SmGL.IsSmoothChar at h1 h2 ⊢
    have h3 : IsOpen (((μw.ker ⊓ ηw.ker : Subgroup _)) : Set (w.adicCompletion E)ˣ) := h1.inter h2
    exact Subgroup.isOpen_mono (H₁ := μw.ker ⊓ ηw.ker) (fun y hy => by
      simp only [Subgroup.mem_inf, MonoidHom.mem_ker] at hy ⊢
      simp [hy.1, hy.2]) h3
  · simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, hμ.2 x, hη.2 x]
    rfl

theorem main : ∀ (D : D7) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) (V W : Formalism.BasicNotions.TH.HSp D) (n r : ℕ) (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n) (PW : Formalism.IndefR.principalLevelFrame.RowPsi W r) (hF : D.host.F = maximalRealSubfield D.host.E), GlobalTheory.NJoin.StdFrame hF PV → GlobalTheory.NJoin.StdFrame hF PW → ∀ χV χW om, Formalism.IndefR.Datum.IsWeilDatumO ψ V W χV χW om → ∀ μ η : HChar D.host.E, Formalism.IndefR.Links.ChrEq χV μ → Formalism.IndefR.Links.ChrEq χW (μ * η⁻¹) → ∀ (s : SplitPlace D.host.E) μw ηw, IsComp μ s.w μw → IsComp η s.w ηw → ∀ f, Formalism.IndefR.Datum.IsThetaFunO ψ V W f → f ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] (Formalism.IndefR.Datum.WO V W → ℂ)) (_ : IsLinAt (om.comp (PV.ψ.prodMap PW.ψ)) s μw ηw ι ∧ ∀ Φ, Formalism.IndefR.Datum.IsThetaFunO ψ V W (ι Φ)), LinearMap.range ι := by
  intro D ψ V W n r PV PW hF hV hW χV χW om hom μ η hμ hη s μw ηw hμw hηw f hf
  obtain ⟨p, hpe, hpr, FS, FT, c, hc, hci, hlocV, hlocW⟩ := GlobalTheory.T.standardFrames_read_splitPlace_unitaryGroup D V W n r PV PW hF hV hW s
  have cV := GlobalTheory.T.localComponent_of_idelicCharacterAgreement D s p hpe hpr χV μ hμ μw hμw
  have cW := GlobalTheory.T.localComponent_of_idelicCharacterAgreement D s p hpe hpr χW (μ * η⁻¹) hη (μw * ηw⁻¹) (isComp_mul_inv hμw hηw)
  obtain ⟨τ, hτ, hτom⟩ := GlobalTheory.T.linearModel_fourier_transform_exchange (s.w.adicCompletion D.host.E) n r
  have hOm := GlobalTheory.T.weilDatum_localModel_formula D
  have h2 := GlobalTheory.T.thetaFunction_mem_span_localSchrodingerModels_split D _ p (Fin r) (Fin n) V W FS FT ψ hom.std f hf
  refine (iSup₂_le fun Tm hTm => ?_ : (⨆ (Tm : GlobalTheory.SplitWeil.SB (Matrix (Fin r) (Fin n) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] (Formalism.IndefR.Datum.WO V W → ℂ)) (_ : p.IsModel ψ FS FT Tm), LinearMap.range Tm) ≤ _) h2
  have hr : LinearMap.range Tm = LinearMap.range (Tm ∘ₗ τ) := by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.2 hτ, Submodule.map_top]
  rw [hr]
  refine le_iSup₂_of_le (f := fun (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] (Formalism.IndefR.Datum.WO V W → ℂ)) (_ : IsLinAt (om.comp (PV.ψ.prodMap PW.ψ)) s μw ηw ι ∧ ∀ Φ, Formalism.IndefR.Datum.IsThetaFunO ψ V W (ι Φ)) => LinearMap.range ι) (Tm ∘ₗ τ) ⟨?_, fun Φ => hTm.theta _⟩ le_rfl
  refine ⟨c, hc, hci, fun h g hh hg Φ Φ' hΦ => ?_⟩
  have hΦ'' : Φ'.1 = GlobalTheory.SplitWeil.om μw (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc r g)) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h)) Φ.1 := hΦ
  have key := hOm (s.w.adicCompletion D.host.E) p ψ V W χV χW om hom μw (μw * ηw⁻¹) cV cW (Fin r) (Fin n) FS FT Tm hTm
    (PV.ψ h) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h)) (PW.ψ g) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc r g))
    (hlocV h hh) (hlocW g hg) (τ Φ)
    (((ηw (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h))) : ℂˣ) : ℂ) • τ Φ') (by
      rw [Submodule.coe_smul, hτom μw _ _ Φ Φ' hΦ'']
      congr 2
      simp [mul_inv_rev, mul_comm])
  simp only [LinearMap.comp_apply, MonoidHom.comp_apply]
  show om (PV.ψ h, PW.ψ g) (Tm (τ Φ)) = _
  rw [key, map_smul]

end GlobalTheory.LinModSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaFunctionsSpannedHeckeTwistedStandardFrameStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunctions_spanned_heckeTwisted_standardFrame : ∀ (D : D7) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) (V W : Formalism.BasicNotions.TH.HSp D) (n r : ℕ) (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n) (PW : Formalism.IndefR.principalLevelFrame.RowPsi W r) (hF : D.host.F = maximalRealSubfield D.host.E), GlobalTheory.NJoin.StdFrame hF PV → GlobalTheory.NJoin.StdFrame hF PW → ∀ χV χW om, Formalism.IndefR.Datum.IsWeilDatumO ψ V W χV χW om → ∀ μ η : HChar D.host.E, Formalism.IndefR.Links.ChrEq χV μ → Formalism.IndefR.Links.ChrEq χW (μ * η⁻¹) → ∀ (s : SplitPlace D.host.E) μw ηw, IsComp μ s.w μw → IsComp η s.w ηw → ∀ f, Formalism.IndefR.Datum.IsThetaFunO ψ V W f → f ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] (Formalism.IndefR.Datum.WO V W → ℂ)) (_ : IsLinAt (om.comp (PV.ψ.prodMap PW.ψ)) s μw ηw ι ∧ ∀ Φ, Formalism.IndefR.Datum.IsThetaFunO ψ V W (ι Φ)), LinearMap.range ι := by
  first | exact @GlobalTheory.LinModSpan.main | exact GlobalTheory.LinModSpan.main | (intros; apply GlobalTheory.LinModSpan.main <;> assumption)
end
