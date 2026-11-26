module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameSupportCompatible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JetsTorsionTranslatesCmThetaProduct
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruenceElementDecompose
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamOfLadicRepSumRepAwayFromLHost
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPeriodProductEqOfInvertibleCharacter
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharInCuspidalSupportOfJacquetSubquotientFactor
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSubquotientParabolicProductTwoFiniteL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalPairIrreducibleProduct
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicProductEquivProductOfPartition

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowUnitProof

theorem exists_splitPlace_eq (D : D7) (w : PlE D.host) (hw : IsSplitPl D.host w) :
    ∃ s : SplitPlace D.host.E, s.w = w := by
  have hstar : ∀ x : D.host.E, D.host.conj x = IsCMField.complexConj D.host.E x := fun _ =>
    D.host.φ₀.injective (by
      rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])
  obtain ⟨x, hx, hy⟩ := hw
  have hc : IsSplitPl D.host (GlobalTheory.SplitConjPlace.conjPlE w) := by
    refine ⟨IsCMField.ringOfIntegersComplexConj D.host.E x, ?_, fun y hy' => ?_⟩
    · rw [GlobalTheory.SplitConjPlace.mem_conjPlE, GlobalTheory.SplitConjPlace.cO_cO]; exact hx
    · rw [GlobalTheory.SplitConjPlace.mem_conjPlE]
      apply hy
      rw [hstar, IsCMField.coe_ringOfIntegersComplexConj, hy', hstar, IsCMField.coe_ringOfIntegersComplexConj,
        IsCMField.complexConj_apply_apply]
  obtain ⟨s, -, hs, -⟩ := GlobalTheory.SplitConjPlace.splitEx_all D _ hc
  refine ⟨s, HeightOneSpectrum.ext (Ideal.ext fun y => ?_)⟩
  have h1 := hs (IsCMField.ringOfIntegersComplexConj D.host.E y) y (by
    rw [hstar, IsCMField.coe_ringOfIntegersComplexConj, IsCMField.complexConj_apply_apply])
  rw [GlobalTheory.SplitConjPlace.mem_conjPlE, GlobalTheory.SplitConjPlace.cO_cO] at h1
  exact h1.symm

end GlobalTheory.RowUnitProof

namespace GlobalTheory.RowUnitProof

end GlobalTheory.RowUnitProof

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteOfTrivOutside
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertSph

def Gv (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : Subgroup (GAf L n) where
  carrier := {x | TrivOutside {v} x}
  mul_mem' := fun hx hy => GlobalTheory.SatInd.CosetFin.trivOutside_mul hx hy
  one_mem' := by
    intro u _
    exact Matrix.map_one _ (map_zero _) (map_one _)
  inv_mem' := fun hx => GlobalTheory.SatInd.CosetFin.trivOutside_inv hx

def Kv (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : Subgroup (GAf L n) :=
  Umax L n ⊓ Gv L n v

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem trivOutside_one (T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) :
    TrivOutside T (1 : GAf L n) := by
  intro u _
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem commute_of_trivOutside (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x y : GAf L n)
    (hx : TrivOutside {v} x) (hy : TrivOutside {v}ᶜ y) : Commute x y := by
  show x * y = y * x
  apply Subtype.ext; apply Units.ext
  change (((x * y : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
    (((y * x : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))
  apply GlobalTheory.SplitAdelic.mat_ext
  intro u
  rw [GlobalTheory.SplitAdelic.mul_coe, GlobalTheory.SplitAdelic.mul_coe, Matrix.map_mul, Matrix.map_mul]
  obtain rfl | hu := eq_or_ne u v
  · rw [hy _ (by simp), mul_one, one_mul]
  · rw [hx u hu, mul_one, one_mul]

theorem heckeFunI_rt {W : Type} [AddCommGroup W] [Module ℂ W] (U : Subgroup (GAf L n))
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}
    (Dv : InertDatum L n v w) (h : Formalism.UG.GU Dv.σw n → ℂ) (φ : GAf L n → W) (b : GAf L n)
    (hb : TrivOutside {v}ᶜ b) :
    heckeFunI L n U Dv h (NG.rt L n b φ) = NG.rt L n b (heckeFunI L n U Dv h φ) := by
  funext g
  show heckeFunI L n U Dv h (NG.rt L n b φ) g = heckeFunI L n U Dv h φ (g * b)
  unfold heckeFunI
  refine finsum_congr fun c => ?_
  split_ifs with hc
  · show _ • φ (g * hc.choose * b) = _ • φ (g * b * hc.choose)
    rw [mul_assoc, mul_assoc, (commute_of_trivOutside v _ _ hc.choose_spec.2 hb).eq]
  · rfl

end GlobalTheory.InertSph
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicPartSpannedBySplitPlaceLocalComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicPartSpannedBySplitPlaceLocalComponent
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SpanLoc

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → NG.isoTyp a.ρ S ≤ ⨆ (T : σ.V →ₗ[ℂ] (GAf L n → a.W)) (_ : (∀ v, T v ∈ NG.AFall L n a.ρ) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)), LinearMap.range T := by
  intro L _ _ _ n a S hS s σ hloc c hc hcL
  obtain ⟨i, T0, hi, hiL, hT0inj, hT0S, hT0eq⟩ := hloc

  have hci : c = i := by
    have hd := IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (K := maximalRealSubfield L) s.v
    have hfun : (c : s.v.adicCompletion (maximalRealSubfield L) → s.w.adicCompletion L) = i := by
      refine hd.equalizer hc hi (funext fun y => ?_)
      simp only [Function.comp_apply]
      rw [← s.i.commutes y, hcL, hiL]
    exact RingEquiv.ext (congrFun hfun)
  subst hci
  obtain ⟨hdec, hcomm, -⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  have hrt : ∀ (h h' : GAf L n) (f : GAf L n → a.W), NG.rt L n h (NG.rt L n h' f) = NG.rt L n (h * h') f := by
    intro h h' f; funext g; simp [NG.rt, mul_assoc]
  have hnt : Nontrivial σ.V := by
    haveI := σ.irr
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    apply (bot_ne_top : (⊥ : Subrepresentation σ.ρ) ≠ ⊤)
    have : ∀ W : Subrepresentation σ.ρ, W = ⊥ := by
      intro W
      ext x
      simp [Subsingleton.elim x 0]
    rw [this ⊤]
  unfold NG.isoTyp
  refine sSup_le ?_
  rintro S' ⟨hS'irr, Φ, hΦ⟩
  let Good : (σ.V →ₗ[ℂ] (GAf L n → a.W)) → Prop := fun T =>
    (∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)) ∧
      ∀ u, T u ∈ S'
  let Wd : Submodule ℂ (GAf L n → a.W) := ⨆ T : {T // Good T}, LinearMap.range T.1
  have hWdS' : Wd ≤ S' := by
    refine iSup_le fun T => ?_
    rintro _ ⟨u, rfl⟩
    exact T.2.2 u
  have hWdle : Wd ≤ ⨆ (T : σ.V →ₗ[ℂ] (GAf L n → a.W)) (_ : (∀ v, T v ∈ NG.AFall L n a.ρ) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)), LinearMap.range T := by
    refine iSup_le fun T => ?_
    exact le_iSup₂_of_le (f := fun (T : σ.V →ₗ[ℂ] (GAf L n → a.W)) (_ : (∀ v, T v ∈ NG.AFall L n a.ρ) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)) => LinearMap.range T)
      T.1 ⟨fun u => hS'irr.1.le (T.2.2 u), T.2.1⟩ le_rfl

  have htr : ∀ (T : σ.V →ₗ[ℂ] (GAf L n → a.W)) (y : GAf L n), Good T → TrivOutside {s.v}ᶜ y → Good ((NG.rt L n y).comp T) := by
    intro T y hT hy
    refine ⟨fun x hx u => ?_, fun u => hS'irr.1.stable y _ (hT.2 u)⟩
    simp only [LinearMap.comp_apply]
    rw [hT.1 x hx u, hrt, hrt, (hcomm x y hx hy).eq]
  have hstab : ∀ h, ∀ f ∈ Wd, NG.rt L n h f ∈ Wd := by
    intro h f hf
    refine Submodule.iSup_induction _ (motive := fun f => NG.rt L n h f ∈ Wd) hf ?_ ?_ ?_
    · rintro T _ ⟨u, rfl⟩
      obtain ⟨x, y, hx, hy, he⟩ := hdec h
      have e : NG.rt L n h (T.1 u) = ((NG.rt L n y).comp T.1) (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) u) := by
        rw [LinearMap.comp_apply, T.2.1 x hx u, hrt, he, (hcomm x y hx hy).eq]
      rw [e]
      exact Submodule.mem_iSup_of_mem (⟨_, htr T.1 y T.2 hy⟩ : {T // Good T}) ⟨_, rfl⟩
    · simp
    · intro f₁ f₂ h₁ h₂; rw [map_add (f := _)]; exact Submodule.add_mem _ h₁ h₂

  let T1 : σ.V →ₗ[ℂ] (GAf L n → a.W) := S'.subtype ∘ₗ Φ.toLinearMap ∘ₗ LinearMap.codRestrict S T0 hT0S
  have hT1 : Good T1 := by
    refine ⟨fun x hx u => ?_, fun u => (Φ _).2⟩
    exact hΦ x ⟨T0 u, hT0S u⟩ ⟨T0 _, hT0S _⟩ (hT0eq x hx u)
  have hrc := hS'irr.2.2 Wd ⟨hWdS'.trans hS'irr.1.le, hstab⟩ hWdS'
  rcases hrc with h0 | h0
  · exfalso
    obtain ⟨u, hu⟩ := exists_ne (0 : σ.V)
    have hmem : T1 u ∈ Wd := Submodule.mem_iSup_of_mem (⟨T1, hT1⟩ : {T // Good T}) ⟨u, rfl⟩
    rw [h0, Submodule.mem_bot] at hmem
    apply hu
    apply hT0inj
    have h2 : Φ (LinearMap.codRestrict S T0 hT0S u) = 0 := Subtype.ext hmem
    rw [map_zero]
    have h3 := Φ.injective (h2.trans Φ.map_zero.symm)
    exact congrArg Subtype.val h3
  · rw [← h0]; exact hWdle

end GlobalTheory.SpanLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicPartSpannedBySplitPlaceLocalComponentStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotypicPart_spanned_by_splitPlace_localComponent : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → NG.isoTyp a.ρ S ≤ ⨆ (T : σ.V →ₗ[ℂ] (GAf L n → a.W)) (_ : (∀ v, T v ∈ NG.AFall L n a.ρ) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)), LinearMap.range T := by
  first | exact @GlobalTheory.SpanLoc.main | exact GlobalTheory.SpanLoc.main | (intros; apply GlobalTheory.SpanLoc.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteTypeSpannedBySplitPlaceLocalComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteTypeSpannedBySplitPlaceLocalComponent
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] GlobalTheory.NPin.ThetaMod.acg GlobalTheory.NPin.ThetaMod.mod

namespace GlobalTheory.FinTypSpanLoc

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.FinTyp L n) (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS π.S s τ → ∀ (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → π.S ≤ ⨆ (T : τ.V →ₗ[ℂ] (GAf L n → ℂ)) (_ : (∀ v, T v ∈ π.S) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)), LinearMap.range T := by
  intro L _ _ _ n π s τ hloc c hc hcL
  obtain ⟨i, T0, hi, hiL, hT0inj, hT0S, hT0eq⟩ := hloc

  have hci : c = i := by
    have hd := IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (K := maximalRealSubfield L) s.v
    have hfun : (c : s.v.adicCompletion (maximalRealSubfield L) → s.w.adicCompletion L) = i := by
      refine hd.equalizer hc hi (funext fun y => ?_)
      simp only [Function.comp_apply]
      rw [← s.i.commutes y, hcL, hiL]
    exact RingEquiv.ext (congrFun hfun)
  subst hci
  obtain ⟨hdec, hcomm, -⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  have hrt : ∀ (h h' : GAf L n) (f : GAf L n → ℂ), NG.rt L n h (NG.rt L n h' f) = NG.rt L n (h * h') f := by
    intro h h' f; funext g; simp [NG.rt, mul_assoc]
  have hnt : Nontrivial τ.V := by
    haveI := τ.irr
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    apply (bot_ne_top : (⊥ : Subrepresentation τ.ρ) ≠ ⊤)
    have : ∀ W : Subrepresentation τ.ρ, W = ⊥ := by
      intro W
      ext x
      simp [Subsingleton.elim x 0]
    rw [this ⊤]
  let Good : (τ.V →ₗ[ℂ] (GAf L n → ℂ)) → Prop := fun T =>
    (∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)) ∧
      ∀ u, T u ∈ π.S
  let Wd : Submodule ℂ (GAf L n → ℂ) := ⨆ T : {T // Good T}, LinearMap.range T.1
  have hWdS : Wd ≤ π.S := by
    refine iSup_le fun T => ?_
    rintro _ ⟨u, rfl⟩
    exact T.2.2 u
  have hWdle : Wd ≤ ⨆ (T : τ.V →ₗ[ℂ] (GAf L n → ℂ)) (_ : (∀ v, T v ∈ π.S) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)), LinearMap.range T := by
    refine iSup_le fun T => ?_
    exact le_iSup₂_of_le (f := fun (T : τ.V →ₗ[ℂ] (GAf L n → ℂ)) (_ : (∀ v, T v ∈ π.S) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)) => LinearMap.range T)
      T.1 ⟨T.2.2, T.2.1⟩ le_rfl

  have htr : ∀ (T : τ.V →ₗ[ℂ] (GAf L n → ℂ)) (y : GAf L n), Good T → TrivOutside {s.v}ᶜ y → Good ((NG.rt L n y).comp T) := by
    intro T y hT hy
    refine ⟨fun x hx u => ?_, fun u => π.stable y _ (hT.2 u)⟩
    simp only [LinearMap.comp_apply]
    rw [hT.1 x hx u, hrt, hrt, (hcomm x y hx hy).eq]
  have hstab : ∀ h, ∀ f ∈ Wd, NG.rt L n h f ∈ Wd := by
    intro h f hf
    refine Submodule.iSup_induction _ (motive := fun f => NG.rt L n h f ∈ Wd) hf ?_ ?_ ?_
    · rintro T _ ⟨u, rfl⟩
      obtain ⟨x, y, hx, hy, he⟩ := hdec h
      have e : NG.rt L n h (T.1 u) = ((NG.rt L n y).comp T.1) (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) u) := by
        rw [LinearMap.comp_apply, T.2.1 x hx u, hrt, he, (hcomm x y hx hy).eq]
      rw [e]
      exact Submodule.mem_iSup_of_mem (⟨_, htr T.1 y T.2 hy⟩ : {T // Good T}) ⟨_, rfl⟩
    · simp
    · intro f₁ f₂ h₁ h₂; rw [map_add (f := _)]; exact Submodule.add_mem _ h₁ h₂
  have hT0 : Good T0 := ⟨hT0eq, hT0S⟩
  rcases π.irr Wd hWdS hstab with h0 | h0
  · exfalso
    obtain ⟨u, hu⟩ := exists_ne (0 : τ.V)
    have hmem : T0 u ∈ Wd := Submodule.mem_iSup_of_mem (⟨T0, hT0⟩ : {T // Good T}) ⟨u, rfl⟩
    rw [h0, Submodule.mem_bot] at hmem
    exact hu (hT0inj (hmem.trans (map_zero T0).symm))
  · intro f hf
    rw [← h0] at hf
    exact hWdle hf

end GlobalTheory.FinTypSpanLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteTypeSpannedBySplitPlaceLocalComponentStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] GlobalTheory.NPin.ThetaMod.acg GlobalTheory.NPin.ThetaMod.mod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteType_spanned_by_splitPlace_localComponent : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.FinTyp L n) (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS π.S s τ → ∀ (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → π.S ≤ ⨆ (T : τ.V →ₗ[ℂ] (GAf L n → ℂ)) (_ : (∀ v, T v ∈ π.S) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)), LinearMap.range T := by
  first | exact @GlobalTheory.FinTypSpanLoc.main | exact GlobalTheory.FinTypSpanLoc.main | (intros; apply GlobalTheory.FinTypSpanLoc.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffInLetters
noncomputable section

namespace GlobalTheory.LiftTypePrime.ProdComb

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.NormSum.KernelAt GlobalTheory.ProductJets GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions

variable {D : D7} {N N' : ℕ}

theorem mem_stdL {x : Fin N → D.host.E} : x ∈ stdL D N ↔ ∀ k, IsIntegral ℤ (x k) := by
  simp only [stdL, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  exact forall_congr' fun k => ⟨fun ⟨a, ha⟩ => ha ▸ a.isIntegral_coe, fun h => ⟨⟨x k, h⟩, rfl⟩⟩

theorem eqAt_std {p : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (h : StdAt D p L) : EqAt D p L (stdL D N) := by
  obtain ⟨L₀, h0, h⟩ := h
  rwa [show stdL D N = L₀ from Submodule.ext fun x => mem_stdL.trans (h0 x).symm]

end GlobalTheory.LiftTypePrime.ProdComb

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalTwistOfBlockTypeVector
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalTwistOfBlockTypeVector
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.BlockSph

theorem sph_of_isBlockVec : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (π₁ : Irr k r) (π₂ : Irr k t) (v : π.V), IsSmoothChar χ → IsTame χ → (∀ α : ℂˣ, ¬ InSupport π₁.π (χ * unrChar k α)) → Nonempty (π.π.Equiv (prod₂ π₁.π π₂.π)) → v ≠ 0 → IsBlockVec χ π.π v → IsSpherical (GlobalTheory.SmGL.twist π₂.π (detChar (Fin t) χ⁻¹)) := by
  intro hBZ hG hDZ k _ _ _ _ r t χ π π₁ π₂ v hχ hχt hsupp ⟨φ⟩ hv hblk
  obtain ⟨E⟩ := Exponents.prod₂_equiv_multiProd k r t _ _ π₁.π π₂.π
  let Ψ := φ.trans E
  have hsm : IsSmooth (multiProd (two (stdSum (rfl : r + t = r + t))) (Exponents.twoRep π₁.π π₂.π)) :=
    isSmooth_parInd _ _
  have hirr : (multiProd (two (stdSum (rfl : r + t = r + t))) (Exponents.twoRep π₁.π π₂.π)).IsIrreducible :=
    (MultiIrr.isIrreducible_iff_of_equiv Ψ).1 π.irr
  have hv' : Ψ v ≠ 0 := fun h => hv (Ψ.injective (h.trans (map_zero Ψ).symm))
  have hblk' : IsBlockVec χ (multiProd (two (stdSum (rfl : r + t = r + t))) (Exponents.twoRep π₁.π π₂.π)) (Ψ v) :=
    fun h hh h1 h2 u hu => by
      have := Ψ.toIntertwiningMap.isIntertwining _ _ h v
      rw [hblk h hh h1 h2 u hu, map_smul] at this
      exact this.symm
  obtain ⟨hx0, hx⟩ := GlobalTheory.T.jacquetModule_image_ne_zero_of_blockTypeVector hDZ k r t χ _ _ (Ψ v) hsm hirr hχt hv' hblk'
  obtain ⟨Y, _, _, τ, hτ, hsub, y, hy0, hy⟩ := GlobalTheory.T.exists_irreducible_subquotient_common_eigenvector _ _ (GlobalTheory.SmGL.jac (two (stdSum (rfl : r + t = r + t)))
    (multiProd (two (stdSum (rfl : r + t = r + t))) (Exponents.twoRep π₁.π π₂.π)))
    {h | ∃ g ∈ KO k (Fin t), h = Pi.mulSingle true g}
    (fun h => (χ (Matrix.GeneralLinearGroup.det (h true)) : ℂ)) _ hx0
    (by rintro _ ⟨g, hg, rfl⟩; simpa using hx g hg)
  have hρs : ∀ i, IsSmooth (Exponents.twoRep π₁.π π₂.π i) := fun i => by
    cases i
    · exact π₁.smooth
    · exact π₂.smooth
  have hρl : ∀ i, HasFiniteLength (Exponents.twoRep π₁.π π₂.π i) := fun i => by
    cases i
    · exact hasFiniteLength_of_isIrreducible π₁.irr
    · exact hasFiniteLength_of_isIrreducible π₂.irr
  obtain ⟨b, f, g, s, hrow, hcol⟩ := exists_cell_of_isSubquotient (hG k).1 (hG k).2
    (two (stdSum (rfl : r + t = r + t))) (two (stdSum (rfl : r + t = r + t))) hρs hρl hτ hsub
  obtain ⟨z, hz0, hz⟩ := GlobalTheory.T.levi_rep_parabolic_char k Bool (Two (Fin r) (Fin t)) _ (fun j => multiProd (g j) fun i => (s i j).ρ)
    Y τ true χ y (fun j => isSmooth_parInd _ _) hχ hcol hy0
    (fun h hh => by simpa using hy (Pi.mulSingle true h) ⟨h, hh, rfl⟩)
  obtain ⟨w, hw0, hw⟩ := GlobalTheory.T.exists_levi_block_eigenvector_at_identity k Bool (fun i => Fin (b.1 i true)) (Fin t) (g true) _ (fun i => (s i true).ρ) χ z hz0 hz
  by_cases hm : b.1 false true = 0
  · obtain ⟨z', hz'0, hz'⟩ := GlobalTheory.T.levi_rep_parabolic_char k Bool (fun i => Fin (b.1 i true)) _ (fun i => (s i true).ρ) _
      (piTensor fun i => (s i true).ρ) true χ w (fun i => (s i true).smooth) hχ (IsSubquotient.refl _) hw0 (hw true)
    have hc : b.1 true false = 0 := by
      have h1 := b.2.1 true
      have h2 := b.2.2 true
      simp [Fintype.sum_bool] at h1 h2
      omega
    exact GlobalTheory.T.isSpherical_twist_of_jacquet_constituent_empty_block k t _ π₂.π (b.1 true) (f true) (s true) χ z' π₂.smooth π₂.irr hc (hrow true) hz'0 hz'
  · obtain ⟨z', hz'0, hz'⟩ := GlobalTheory.T.levi_rep_parabolic_char k Bool (fun i => Fin (b.1 i true)) _ (fun i => (s i true).ρ) _
      (piTensor fun i => (s i true).ρ) false χ w (fun i => (s i true).smooth) hχ (IsSubquotient.refl _) hw0 (hw false)
    obtain ⟨α, hα⟩ := GlobalTheory.T.inSupport_mul_unramifiedChar_of_integralEigenvector hBZ hG hDZ k _ _ (s false true).ρ χ z' (s false true).smooth (s false true).irr hχ
      (Nat.pos_of_ne_zero hm) hz'0 hz'
    exact absurd (GlobalTheory.T.charInCuspidalSupport_of_jacquet_subquotient_factor hBZ hG k r _ π₁.π Bool (b.1 false) (f false) (s false) true _ π₁.smooth (hrow false) hα) (hsupp α)

end GlobalTheory.BlockSph
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalTwistOfBlockTypeVectorStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_twist_of_blockTypeVector : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (π₁ : Irr k r) (π₂ : Irr k t) (v : π.V), IsSmoothChar χ → IsTame χ → (∀ α : ℂˣ, ¬ InSupport π₁.π (χ * unrChar k α)) → Nonempty (π.π.Equiv (prod₂ π₁.π π₂.π)) → v ≠ 0 → IsBlockVec χ π.π v → IsSpherical (twist π₂.π (detChar (Fin t) χ⁻¹)) := by
  first | exact @GlobalTheory.BlockSph.sph_of_isBlockVec | exact GlobalTheory.BlockSph.sph_of_isBlockVec | (intros; apply GlobalTheory.BlockSph.sph_of_isBlockVec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSplitExactTwistCountProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSubquotientProdReorderedCuspSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSubquotientProdReorderedCuspSupport
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory

theorem isSubquotient_prod₂_of_cuspSupport_reorder : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t s : ℕ) (π : Irr k (r + t)) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)) (S : Finset (Fin s)), IsCuspSupport π.π d (fun a => (σ a).π) → (∀ b ∈ S, d b = 1) → (∀ a b, a ∉ S → b ∈ S → ∀ (h : d a = d b) (α : ℂˣ), ¬ Nonempty ((h ▸ σ a : Irr k (d b)).π.Equiv (GlobalTheory.SmGL.twist (σ b).π (detChar (Fin (d b)) (unrChar k α))))) → ∑ a ∈ Sᶜ, d a = r → ∑ a ∈ S, d a = t → ∃ (s₁ s₂ : ℕ) (ι₁ : Fin s₁ → Fin s) (ι₂ : Fin s₂ → Fin s) (e₁ : (Σ a, Fin (d (ι₁ a))) ≃ Fin r) (e₂ : (Σ b, Fin (d (ι₂ b))) ≃ Fin t) (V₁ V₂ : Type) (_ : AddCommGroup V₁) (_ : Module ℂ V₁) (_ : AddCommGroup V₂) (_ : Module ℂ V₂) (ρ₁ : Representation ℂ (GL (Fin r) k) V₁) (ρ₂ : Representation ℂ (GL (Fin t) k) V₂), (∀ a, ι₁ a ∉ S) ∧ (∀ b, ι₂ b ∈ S) ∧ IsSmooth ρ₁ ∧ IsSmooth ρ₂ ∧ Nonempty (ρ₁.Equiv (multiProd e₁ fun a => (σ (ι₁ a)).π)) ∧ Nonempty (ρ₂.Equiv (multiProd e₂ fun b => (σ (ι₂ b)).π)) ∧ IsSubquotient π.π (prod₂ ρ₁ ρ₂) := by
  intro hBZ hGL hUPI k _ _ _ _ r t s π d σ S hsupp hS hunl hr ht
  obtain ⟨-, hσ, e, hsub⟩ := hsupp
  have sumc : ∀ (T : Finset (Fin s)), ∑ a : Fin T.card, d (T.orderEmbOfFin rfl a) = ∑ a ∈ T, d a := by
    intro T
    rw [← Finset.sum_coe_sort T]
    exact Fintype.sum_equiv (T.orderIsoOfFin rfl).toEquiv _ _ (fun a => by simp)
  have c₁ : Fintype.card (Σ a : Fin Sᶜ.card, Fin (d (Sᶜ.orderEmbOfFin rfl a))) = Fintype.card (Fin r) := by
    simp [Fintype.card_sigma, sumc, hr]
  have c₂ : Fintype.card (Σ b : Fin S.card, Fin (d (S.orderEmbOfFin rfl b))) = Fintype.card (Fin t) := by
    simp [Fintype.card_sigma, sumc, ht]
  let e₁ := Fintype.equivOfCardEq c₁
  let e₂ := Fintype.equivOfCardEq c₂
  obtain ⟨φ⟩ := GlobalTheory.T.parabolicProduct_equiv_product_of_partition k s d σ S r t e e₁ e₂ (fun a b ha hb n _ _ f f' =>
    GlobalTheory.T.cuspidal_pair_irreducible_product hBZ hGL hUPI k n (fun i => d (![a, b] i)) (fun i => σ (![a, b] i))
      (fun i => ⟨(hσ _).1, (hσ _).2.2⟩) (hS b hb) (hunl a b ha hb) f f')
  refine ⟨Sᶜ.card, S.card, fun a => Sᶜ.orderEmbOfFin rfl a, fun b => S.orderEmbOfFin rfl b, e₁, e₂, _, _,
    inferInstance, inferInstance, inferInstance, inferInstance,
    multiProd e₁ fun a => (σ (Sᶜ.orderEmbOfFin rfl a)).π, multiProd e₂ fun b => (σ (S.orderEmbOfFin rfl b)).π,
    fun a => Finset.mem_compl.1 (Finset.orderEmbOfFin_mem Sᶜ rfl a),
    fun b => Finset.orderEmbOfFin_mem S rfl b, isSmooth_parInd _ _, isSmooth_parInd _ _,
    ⟨Representation.Equiv.refl _⟩, ⟨Representation.Equiv.refl _⟩, ?_⟩
  exact hsub.trans (IsSubquotient.of_surjective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.surjective)

end GlobalTheory

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSubquotientProdReorderedCuspSupportStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSubquotient_prod_reordered_cuspSupport : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t s : ℕ) (π : Irr k (r + t)) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)) (S : Finset (Fin s)), IsCuspSupport π.π d (fun a => (σ a).π) → (∀ b ∈ S, d b = 1) → (∀ a b, a ∉ S → b ∈ S → ∀ (h : d a = d b) (α : ℂˣ), ¬ Nonempty ((h ▸ σ a : Irr k (d b)).π.Equiv (twist (σ b).π (detChar (Fin (d b)) (unrChar k α))))) → ∑ a ∈ Sᶜ, d a = r → ∑ a ∈ S, d a = t → ∃ (s₁ s₂ : ℕ) (ι₁ : Fin s₁ → Fin s) (ι₂ : Fin s₂ → Fin s) (e₁ : (Σ a, Fin (d (ι₁ a))) ≃ Fin r) (e₂ : (Σ b, Fin (d (ι₂ b))) ≃ Fin t) (V₁ V₂ : Type) (_ : AddCommGroup V₁) (_ : Module ℂ V₁) (_ : AddCommGroup V₂) (_ : Module ℂ V₂) (ρ₁ : Representation ℂ (GL (Fin r) k) V₁) (ρ₂ : Representation ℂ (GL (Fin t) k) V₂), (∀ a, ι₁ a ∉ S) ∧ (∀ b, ι₂ b ∈ S) ∧ IsSmooth ρ₁ ∧ IsSmooth ρ₂ ∧ Nonempty (ρ₁.Equiv (multiProd e₁ fun a => (σ (ι₁ a)).π)) ∧ Nonempty (ρ₂.Equiv (multiProd e₂ fun b => (σ (ι₂ b)).π)) ∧ IsSubquotient π.π (prod₂ ρ₁ ρ₂) := by
  first | exact @GlobalTheory.isSubquotient_prod₂_of_cuspSupport_reorder | exact GlobalTheory.isSubquotient_prod₂_of_cuspSupport_reorder | (intros; apply GlobalTheory.isSubquotient_prod₂_of_cuspSupport_reorder <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSplitExactTwistCountProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.BlockSplitProd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unrChar_mul (α β : ℂˣ) : unrChar k (α * β) = unrChar k α * unrChar k β := by
  refine MonoidHom.ext fun x => ?_
  simp [unrChar_apply, mul_zpow]

theorem twist_detRep (n : Type) [Fintype n] [DecidableEq n] (ψ φ : kˣ →* ℂˣ) :
    GlobalTheory.SmGL.twist (detRep n ψ) (detChar n φ) = detRep n (ψ * φ) := by
  refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
  simp [detRep, ofChar_apply, twist_apply, mul_comm, mul_left_comm, mul_assoc]

theorem nonempty_equiv_of_cast {n m : ℕ} (h : n = m) (x : Irr k n) (ψ : kˣ →* ℂˣ)
    (e : Nonempty ((h ▸ x : Irr k m).π.Equiv (detRep (Fin m) ψ))) :
    Nonempty (x.π.Equiv (detRep (Fin n) ψ)) := by
  subst h; exact e

theorem eq_one_of_inSupport {m : ℕ} (τ : Irr k m) (hc : IsCuspidal τ.π) {ψ : kˣ →* ℂˣ}
    (h : InSupport τ.π ψ) : m = 1 ∧ Nonempty (τ.π.Equiv (detRep (Fin m) ψ)) := by
  rcases m with _ | _ | m
  · exact absurd h (Model.not_inSupport_zero _ _)
  · obtain ⟨ω, hω, ⟨φ⟩⟩ := RankLeOne.exists_equiv_detRep k (Fin 1) _ τ.π τ.smooth τ.irr
    have h1 : InSupport (detRep (Fin 1) ω) ψ :=
      JacquetExact.inSupport_of_isSubquotient k _ _ _ τ.π _ ψ ((isSmooth_ofChar_iff _).2 hω.detChar)
        (IsSubquotient.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective) h
    obtain rfl := (Model.inSupport_one_iff ω ψ).1 h1
    exact ⟨rfl, ⟨φ⟩⟩
  · exact absurd h (Model.not_inSupport_of_isCuspidal hc ψ)

theorem exists_eq_of_inSupport (hG : GlobalTheory.Published.GeometricLemma) {n s : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a))
    (ψ : kˣ →* ℂˣ) (hc : IsCuspSupport π d (fun a => (σ a).π)) (h : InSupport π ψ) :
    ∃ a, d a = 1 ∧ Nonempty ((σ a).π.Equiv (detRep (Fin (d a)) ψ)) := by
  obtain ⟨-, hσ, e, hsub⟩ := hc
  have h1 := JacquetExact.inSupport_of_isSubquotient k _ _ _ π _ ψ (isSmooth_parInd _ _) hsub h
  obtain ⟨a, ha⟩ := ProdSupport.exists_inSupport_of_multiProd hG k (Fin s) (fun a => Fin (d a)) (Fin n) e _
    (fun a => (σ a).π) ψ (fun a => (σ a).smooth) (fun a => (σ a).irr) h1
  exact ⟨a, eq_one_of_inSupport (σ a) (hσ a).2.2 ha⟩

theorem reorder : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma →
    GlobalTheory.Published.UnlinkedProductIrreducible →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (r t s : ℕ) (π : Irr k (r + t)) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)) (S : Finset (Fin s)),
      IsCuspSupport π.π d (fun a => (σ a).π) → (∀ b ∈ S, d b = 1) →
      (∀ a b, a ∉ S → b ∈ S → ∀ (h : d a = d b) (α : ℂˣ),
        ¬ Nonempty ((h ▸ σ a : Irr k (d b)).π.Equiv (GlobalTheory.SmGL.twist (σ b).π (detChar (Fin (d b)) (unrChar k α))))) →
      ∑ a ∈ Sᶜ, d a = r → ∑ a ∈ S, d a = t →
      ∃ (π₁ : Irr k r) (π₂ : Irr k t) (s₁ s₂ : ℕ) (ι₁ : Fin s₁ → Fin s) (ι₂ : Fin s₂ → Fin s),
        (∀ a, ι₁ a ∉ S) ∧ (∀ b, ι₂ b ∈ S) ∧
        IsCuspSupport π₁.π (fun a => d (ι₁ a)) (fun a => (σ (ι₁ a)).π) ∧
        IsCuspSupport π₂.π (fun b => d (ι₂ b)) (fun b => (σ (ι₂ b)).π) ∧
        IsSubquotient π.π (prod₂ π₁.π π₂.π) := by
  intro hB hG hU k _ _ _ _ r t s π d σ S hc hS1 hlink hr ht
  have hσ := hc.2.1
  obtain ⟨s₁, s₂, ι₁, ι₂, e₁, e₂, V₁, V₂, _, _, _, _, ρ₁, ρ₂, m1, m2, sm1, sm2, ⟨φ₁⟩, ⟨φ₂⟩, hsub⟩ :=
    GlobalTheory.T.isSubquotient_prod_reordered_cuspSupport hB hG hU k r t s π d σ S hc hS1 hlink hr ht
  obtain ⟨π₁, π₂, h1, h2, h3⟩ := GlobalTheory.T.irreducibleSubquotient_parabolicProductTwo_finiteLength hB k r t V₁ V₂ ρ₁ ρ₂ π sm1 sm2
    ((GlobalTheory.T.parabolicInductionTensorProduct_hasFiniteLength hB k s₁ r (fun a => d (ι₁ a)) (fun a => σ (ι₁ a)) e₁).of_equiv φ₁.symm)
    ((GlobalTheory.T.parabolicInductionTensorProduct_hasFiniteLength hB k s₂ t (fun b => d (ι₂ b)) (fun b => σ (ι₂ b)) e₂).of_equiv φ₂.symm) hsub
  exact ⟨π₁, π₂, s₁, s₂, ι₁, ι₂, m1, m2,
    ⟨π₁.irr, fun a => hσ (ι₁ a), e₁, h1.trans (IsSubquotient.of_injective φ₁.toIntertwiningMap φ₁.toLinearEquiv.injective)⟩,
    ⟨π₂.irr, fun b => hσ (ι₂ b), e₂, h2.trans (IsSubquotient.of_injective φ₂.toIntertwiningMap φ₂.toLinearEquiv.injective)⟩, h3⟩

end GlobalTheory.BlockSplitProd

open GlobalTheory.BlockSplitProd in
theorem GlobalTheory.BlockSplitProd.main : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsSmoothChar χ → IsCuspSupport π.π d (fun a => (σ a).π) → Set.ncard {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (detRep (Fin (d a)) (χ * unrChar k α)))} = t → ∃ (π₁ : Irr k r) (π₂ : Irr k t), Nonempty (π.π.Equiv (prod₂ π₁.π π₂.π)) ∧ ∀ α : ℂˣ, ¬ InSupport π₁.π (χ * unrChar k α) := by
  intro hB hG hU k _ _ _ _ r t χ π s d σ _ hc hcard
  classical
  let S : Finset (Fin s) := Finset.univ.filter fun a =>
    d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (detRep (Fin (d a)) (χ * unrChar k α)))
  have hS : S.card = t := by
    rw [← hcard, ← Set.ncard_coe_finset]
    congr 1
    ext a
    simp [S]
  have hS1 : ∀ b ∈ S, d b = 1 := fun b hb => (Finset.mem_filter.1 hb).2.1
  have htot : ∑ a, d a = r + t := by
    obtain ⟨e, -⟩ := hc.2.2
    simpa using Fintype.card_congr e
  have ht : ∑ a ∈ S, d a = t := by
    rw [Finset.sum_congr rfl hS1]
    simp [hS]
  have hr : ∑ a ∈ Sᶜ, d a = r := by
    have := Finset.sum_add_sum_compl S d
    omega
  have hlink : ∀ a b, a ∉ S → b ∈ S → ∀ (h : d a = d b) (α : ℂˣ),
      ¬ Nonempty ((h ▸ σ a : Irr k (d b)).π.Equiv (GlobalTheory.SmGL.twist (σ b).π (detChar (Fin (d b)) (unrChar k α)))) := by
    intro a b ha hb h α ⟨φ⟩
    obtain ⟨hb1, β, ⟨ψ⟩⟩ := (Finset.mem_filter.1 hb).2
    have e1 : GlobalTheory.SmGL.twist (detRep (Fin (d b)) (χ * unrChar k β)) (detChar (Fin (d b)) (unrChar k α)) =
        detRep (Fin (d b)) (χ * unrChar k (β * α)) := by
      rw [twist_detRep, unrChar_mul, mul_assoc]
    have ψ' := LocGL.twistEquiv ψ (detChar (Fin (d b)) (unrChar k α))
    rw [e1] at ψ'
    exact ha (Finset.mem_filter.2 ⟨Finset.mem_univ _, h.trans hb1, β * α,
      nonempty_equiv_of_cast h (σ a) _ ⟨φ.trans ψ'⟩⟩)
  obtain ⟨π₁, π₂, s₁, s₂, ι₁, ι₂, m1, m2, hc1, hc2, hsub⟩ :=
    reorder hB hG hU k r t s π d σ S hc hS1 hlink hr ht
  have hirr := hU k r t s₁ s₂ π₁ π₂ (fun a => d (ι₁ a)) (fun b => d (ι₂ b)) (fun a => σ (ι₁ a))
    (fun b => σ (ι₂ b)) hc1 hc2 fun a b h α => hlink _ _ (m1 a) (m2 b) h α
  obtain ⟨φ⟩ := IsSubquotient.nonempty_equiv hsub π.irr hirr
  refine ⟨π₁, π₂, ⟨φ.symm⟩, fun α hα => ?_⟩
  obtain ⟨a, ha1, hψ⟩ := exists_eq_of_inSupport hG π₁.π (fun a => d (ι₁ a)) (fun a => σ (ι₁ a)) _ hc1 hα
  exact m1 a (Finset.mem_filter.2 ⟨Finset.mem_univ _, ha1, α, hψ⟩)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSplitExactTwistCountProductStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_split_exact_twistCount_product : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsSmoothChar χ → IsCuspSupport π.π d (fun a => (σ a).π) → Set.ncard {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (detRep (Fin (d a)) (χ * unrChar k α)))} = t → ∃ (π₁ : Irr k r) (π₂ : Irr k t), Nonempty (π.π.Equiv (prod₂ π₁.π π₂.π)) ∧ ∀ α : ℂˣ, ¬ InSupport π₁.π (χ * unrChar k α) := by
  first | exact @GlobalTheory.BlockSplitProd.main | exact GlobalTheory.BlockSplitProd.main | (intros; apply GlobalTheory.BlockSplitProd.main <;> assumption)
end
end
