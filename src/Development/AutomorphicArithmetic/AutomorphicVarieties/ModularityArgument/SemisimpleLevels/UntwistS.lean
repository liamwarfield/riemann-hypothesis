module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.UntwistS
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Lev.untwistS :
    GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.AlgebraicCharacterWD → GlobalTheory.Published.DeRhamPotSemistable →
                 ∀ (K Ω : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
                 (R : G K Ω →* GL (Fin n) (Qbar l)), Continuous R → ∀ (art : Ideles K →* Gab K Ω) (κ : HChar K) (m : (K →+* ℂ) → ℤ)
                 (μ : G K Ω →* (Qbar l)ˣ), IsGlobalArtin art → IsAlgPos κ m → Continuous μ → IsLAdicOf art ι κ m μ →
                 ∀ (w : HeightOneSpectrum (𝓞 K)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l K Ω (Dec (F := K) A) O) (hj : Induces Bw),
                   IsPstAt (Loc.PP l) Bw (R.comp (Dec (F := K) A).subtype) → IsPstAt (Loc.PP l) Bw ((tw R μ).comp (Dec (F := K) A).subtype) →
                   ∀ (σ : SmIrr (GL (Fin n) (w.adicCompletion K))) rc, IsRec h rc →
                     Lev.SsCmp (wdAt (Loc.PP l) ι Bw h hj ((tw R μ).comp (Dec (F := K) A).subtype))
                       (rc (algNorm (σ.twist (CuspSub.locDet n κ w) (CuspSub.isOpen_ker_locDet κ w)))) →
                     Lev.SsCmp (wdAt (Loc.PP l) ι Bw h hj (R.comp (Dec (F := K) A).subtype)) (rc (algNorm σ)) := by
  intro hA hW hD K Ω _ _ _ _ _ _ l _ ι n R hR art κ m μ hart hκ hμ hL w A h O _ _ _ Bw hj hP hP' σ rc hrc H
  obtain ⟨T⟩ := Loc.tiedP l
  have hdet : Matrix.GeneralLinearGroup.det.comp ((GlobalTheory.TripleGal.rk1 μ).comp (Dec (F := K) A).subtype)
      = μ.comp (Dec (F := K) A).subtype := by
    ext g
    simp [GlobalTheory.TripleGal.rk1, Matrix.det_unique]
  have htw : (tw R μ).comp (Dec (F := K) A).subtype =
      Formalism.MainNotions.SumRepresentations.At.twGL (R.comp (Dec (F := K) A).subtype)
        (Matrix.GeneralLinearGroup.det.comp ((GlobalTheory.TripleGal.rk1 μ).comp (Dec (F := K) A).subtype)) := by
    rw [hdet]
    ext g i j
    simp [Formalism.MainNotions.SumRepresentations.At.twGL, tw_val, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]
  have hcR : Continuous fun g : ↥(Dec (F := K) A) =>
      ((R.comp (Dec (F := K) A).subtype g : GL (Fin n) (Loc.Om l)) : Matrix (Fin n) (Fin n) (Loc.Om l)) :=
    Units.continuous_val.comp (hR.comp continuous_subtype_val)
  have hcμ : Continuous fun g : ↥(Dec (F := K) A) =>
      (((GlobalTheory.TripleGal.rk1 μ).comp (Dec (F := K) A).subtype g : GL (Fin 1) (Loc.Om l)) :
        Matrix (Fin 1) (Fin 1) (Loc.Om l)) := by
    refine continuous_matrix fun i j => ?_
    fin_cases i; fin_cases j
    have := Units.continuous_val.comp (hμ.comp (continuous_subtype_val (p := fun x => x ∈ Dec (F := K) A)))
    simpa [GlobalTheory.TripleGal.rk1, Function.comp_def] using this
  have hdR := (GlobalTheory.Published.heckeLAdicCharacterAbove_iff.1 hA K Ω l _ _ ⟨T⟩ ι art hart κ m μ hκ hμ hL w A h O Bw hj).1
  have hPμ := GlobalTheory.Published.DeRhamPotSemistable.isPstAt hD T Bw _ hcμ hdR
  have hc := GlobalTheory.Published.ParamAboveModel.isComp_loc (w := w) κ
  rw [htw] at H hP'
  rw [GlobalTheory.T.fontaineParameter_twist_potentiallySemistable l _ _ ⟨T⟩ ι K Ω A w h O Bw hj n _ _ hcR hcμ hP hPμ hP', rec_algNorm hrc] at H
  rw [rec_algNorm hrc]
  obtain ⟨a, ha, ε, -, HL⟩ := hrc
  rw [hW K Ω l _ _ ⟨T⟩ ι art hart κ m μ hκ hμ hL w A h O Bw hj _ hc a ha, ← HL.one _ hc.1] at H
  have e : rc (IrrGL.of (σ.twist (CuspSub.locDet n κ w) (CuspSub.isOpen_ker_locDet κ w)).ρ
      (σ.twist (CuspSub.locDet n κ w) (CuspSub.isOpen_ker_locDet κ w)).smooth
      (σ.twist (CuspSub.locDet n κ w) (CuspSub.isOpen_ker_locDet κ w)).irred) =
      (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).lpChar (rc (.ofChar (κ.loc w) hc.1)) := by
    rw [← HL.twist]
    exact congrArg _ (GlobalTheory.LocGL.IrrGL.tw_of σ.ρ σ.smooth σ.irred _ hc.1).symm
  rw [e, ← GlobalTheory.NuShift.lpChar_lpTw] at H
  exact ((Lev.ssCalc K Ω A w h).2.2 _ _ _ (HL.dim _)).1 H
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.RecMove
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.SsMoveP
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

theorem UpperTheory.V.Lev.ssMove :
    UpperTheory.V.Lev.SsMove := by
  intro F K Ω _ _ _ _ _ _ _ _ _ A v w h h' j i hP x y x' y' hx hy H
  obtain ⟨c, hc, -⟩ := GlobalTheory.T.place_over_transport_ring_iso F Ω A v h K Ω A w h' _ _ i hP
  have key : ∀ (z : WD h) (z' : WD h'), WDRel (RingEquiv.refl Ω) z z' →
      (∀ s, z.charPol s = z'.charPol (c s)) ∧ z.lpDim = z'.lpDim := by
    rintro _ _ ⟨n, b, b', rfl, rfl, -, hρ⟩
    refine ⟨fun s => ?_, ?_⟩
    · rw [WD.charPol_mk, WD.charPol_mk, hρ s (c s) ((hc s (c s)).mpr rfl)]
    · rw [WD.lpDim_mk, WD.lpDim_mk]
  have ab : ∀ (z : WD h) (z' : WD h'), WDRel (RingEquiv.refl Ω) z z' →
      UpperTheory.V.Lev.AbW z → UpperTheory.V.Lev.AbW z' := by
    intro z z' hz a g g'
    obtain ⟨h1, h2⟩ := key z z' hz
    obtain ⟨g, rfl⟩ := c.surjective g
    obtain ⟨g', rfl⟩ := c.surjective g'
    rw [← h2, ← a g g', h1, map_mul, map_mul, map_mul, map_inv, map_inv]
  intro hab s
  rw [(key x x' hx).1, (key y y' hy).1]
  exact H (hab.imp (ab x x' hx) (ab y y' hy)) (c s)
end

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Lev.recMove :
    GlobalTheory.Published.LocalLanglandsGL → ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F Ω] [Algebra K Ω]
                 [IsAlgClosure F Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v)
                 (h' : IsPlaceOver A w) (j : F →+* K) (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) j i →
                 ∀ (n : ℕ) (σ : SmIrr (GL (Fin n) (v.adicCompletion F))) (σ' : SmIrr (GL (Fin n) (w.adicCompletion K))) (e : σ.V ≃ₗ[ℂ] σ'.V),
                   (∀ g x, e (σ.ρ g x) = σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x)) → ∀ rc rc', IsRec h rc → IsRec h' rc' →
                   ∀ (y : WD h) (y' : WD h'), WDRel (RingEquiv.refl Ω) y y' → Lev.SsCmp y' (rc' (algNorm σ')) →
                     Lev.SsCmp y (rc (algNorm σ)) := by
  intro hL F K Ω _ _ _ _ _ _ _ _ _ A v w h h' j i P n σ σ' e he rc rc' hrc hrc' y y' hy hc
  obtain ⟨S, hS, -, -, -, -, hSt, -⟩ := GlobalTheory.WDTransport.exists_equiv_wd F Ω A v h K Ω A w h' (RingEquiv.refl Ω) j i P
  have hF := hL.2 F Ω A v h K Ω A w h' rc rc' hrc hrc' (RingEquiv.refl Ω) j i P.mem P.ext P.cont P.loc n
    { V := σ.V, ρ := σ.ρ, smooth := σ.smooth, irr := σ.irred }
    { V := σ'.V, ρ := σ'.ρ, smooth := σ'.smooth, irr := σ'.irred } e he
  have h1 : S (rc (IrrGL.of σ.ρ σ.smooth σ.irred)) = rc' (IrrGL.of σ'.ρ σ'.smooth σ'.irred) :=
    (hS _ _).1 ⟨n, hF⟩
  refine Lev.ssMove F K Ω A v w h h' j i P _ _ _ _ hy ((hS _ _).2 ?_) hc
  rw [rec_algNorm hrc, rec_algNorm hrc', hSt, h1]
end
