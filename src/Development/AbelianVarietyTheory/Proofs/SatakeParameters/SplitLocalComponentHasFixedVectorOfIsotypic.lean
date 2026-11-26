module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoupledStepChartLevelAtBadPrimes

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitLocalComponentHasFixedVectorOfIsotypic
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitLocalComponentHasFixedVectorOfIsotypic
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IsoTypFixLoc

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem rt_rt (h h' : GAf L n) (f : GAf L n → W) : NG.rt L n h (NG.rt L n h' f) = NG.rt L n (h * h') f := by
  funext g; simp [NG.rt, mul_assoc]

def LocEq (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T : τ.V →ₗ[ℂ] (GAf L n → W)) : Prop :=
  ∀ x : GAf L n, TrivOutside {s.v} x → ∀ a, T (τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) a) = NG.rt L n x (T a)

theorem le_iSup_range (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)) (hS : NG.IsIrrRep ρ S)
    (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T0 : τ.V →ₗ[ℂ] (GAf L n → W))
    (hT0inj : Function.Injective T0) (hT0S : ∀ a, T0 a ∈ S) (hT0eq : LocEq s τ i T0) :
    S ≤ ⨆ T : {T : τ.V →ₗ[ℂ] (GAf L n → W) // LocEq s τ i T}, LinearMap.range T.1 := by
  obtain ⟨hdec, hcomm, -⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
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
  let Good : (τ.V →ₗ[ℂ] (GAf L n → W)) → Prop := fun T => LocEq s τ i T ∧ ∀ u, T u ∈ S
  let Wd : Submodule ℂ (GAf L n → W) := ⨆ T : {T // Good T}, LinearMap.range T.1
  have hWdS : Wd ≤ S := by
    refine iSup_le fun T => ?_
    rintro _ ⟨u, rfl⟩
    exact T.2.2 u
  have hWdle : Wd ≤ ⨆ T : {T : τ.V →ₗ[ℂ] (GAf L n → W) // LocEq s τ i T}, LinearMap.range T.1 :=
    iSup_le fun T => le_iSup_of_le (⟨T.1, T.2.1⟩ : {T : τ.V →ₗ[ℂ] (GAf L n → W) // LocEq s τ i T}) le_rfl
  have htr : ∀ (T : τ.V →ₗ[ℂ] (GAf L n → W)) (y : GAf L n), Good T → TrivOutside {s.v}ᶜ y → Good ((NG.rt L n y).comp T) := by
    intro T y hT hy
    refine ⟨fun x hx u => ?_, fun u => hS.1.stable y _ (hT.2 u)⟩
    simp only [LinearMap.comp_apply]
    rw [hT.1 x hx u, rt_rt, rt_rt, (hcomm x y hx hy).eq]
  have hstab : ∀ h, ∀ f ∈ Wd, NG.rt L n h f ∈ Wd := by
    intro h f hf
    refine Submodule.iSup_induction _ (motive := fun f => NG.rt L n h f ∈ Wd) hf ?_ ?_ ?_
    · rintro T _ ⟨u, rfl⟩
      obtain ⟨x, y, hx, hy, he⟩ := hdec h
      have e : NG.rt L n h (T.1 u) = ((NG.rt L n y).comp T.1) (τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) u) := by
        rw [LinearMap.comp_apply, T.2.1 x hx u, rt_rt, he, (hcomm x y hx hy).eq]
      rw [e]
      exact Submodule.mem_iSup_of_mem (⟨_, htr T.1 y T.2 hy⟩ : {T // Good T}) ⟨_, rfl⟩
    · simp
    · intro f₁ f₂ h₁ h₂; rw [map_add (f := _)]; exact Submodule.add_mem _ h₁ h₂
  have hT0 : Good T0 := ⟨hT0eq, hT0S⟩
  rcases hS.2.2 Wd ⟨hWdS.trans hS.1.le, hstab⟩ hWdS with h0 | h0
  · exfalso
    obtain ⟨u, hu⟩ := exists_ne (0 : τ.V)
    have hmem : T0 u ∈ Wd := Submodule.mem_iSup_of_mem (⟨T0, hT0⟩ : {T // Good T}) ⟨u, rfl⟩
    rw [h0, Submodule.mem_bot] at hmem
    exact hu (hT0inj (hmem.trans (map_zero T0).symm))
  · rw [← h0]
    exact hWdle

theorem isoTyp_le (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W))
    (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T0 : τ.V →ₗ[ℂ] (GAf L n → W))
    (hT0inj : Function.Injective T0) (hT0S : ∀ a, T0 a ∈ S) (hT0eq : LocEq s τ i T0) :
    NG.isoTyp ρ S ≤ ⨆ T : {T : τ.V →ₗ[ℂ] (GAf L n → W) // LocEq s τ i T}, LinearMap.range T.1 := by
  refine sSup_le ?_
  rintro S' ⟨hS', E, hE⟩
  let T1 : τ.V →ₗ[ℂ] (GAf L n → W) := S'.subtype ∘ₗ (E : S →ₗ[ℂ] S') ∘ₗ LinearMap.codRestrict S T0 hT0S
  refine le_iSup_range ρ S' hS' s τ i T1 ?_ (fun a => (E _).2) ?_
  · intro a b hab
    apply hT0inj
    have := E.injective (Subtype.ext hab)
    exact congrArg Subtype.val this
  · intro x hx a
    exact hE x ⟨T0 a, hT0S a⟩ ⟨_, hT0S _⟩ (hT0eq x hx a)

end GlobalTheory.IsoTypFixLoc


open GlobalTheory.IsoTypFixLoc in
theorem GlobalTheory.IsoTypFixLoc.main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)), NG.IsIrrRep ρ S → ∀ (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s τ → ∀ (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous i → (∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ f ∈ NG.isoTyp ρ S, f ≠ 0 → (∀ κ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, NG.rt L n κ f = f) → ∃ a : τ.V, a ≠ 0 ∧ ∀ κ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n κ)) a = a := by
  intro L _ _ _ n W _ _ ρ S hS s τ hloc i hi hiL f hf hf0 hfix
  classical
  obtain ⟨i', T0, hi', hi'L, hT0inj, hT0S, hT0eq⟩ := hloc
  obtain rfl := GlobalTheory.splitPlace_completion_equiv_unique L s i' i hi' hi hi'L hiL
  have hspan := isoTyp_le ρ S s τ i' T0 hT0inj hT0S hT0eq hf
  have hI := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  let H : Subgroup (GAf L n) :=
    { carrier := {x | TrivOutside {s.v} x}
      mul_mem' := fun hx hy => GlobalTheory.HeckeScalarSph.triv_mul hx hy
      one_mem' := GlobalTheory.HeckeScalarSph.triv_one
      inv_mem' := fun hx => GlobalTheory.HeckeScalarSph.triv_inv hx }
  let φ : H →* GL (Fin n) (s.w.adicCompletion L) :=
    (Matrix.GeneralLinearGroup.map i'.toRingHom).comp ((s.loc n).comp H.subtype)
  have hφ : Function.Surjective φ := by
    intro h
    obtain ⟨x, ⟨hx, e⟩, -⟩ := hI.2.2 (Matrix.GeneralLinearGroup.map i'.symm.toRingHom h)
    refine ⟨⟨x, hx⟩, ?_⟩
    change Matrix.GeneralLinearGroup.map i'.toRingHom (s.loc n x) = h
    rw [e]
    exact Units.ext (Matrix.ext fun a b => i'.apply_symm_apply _)
  let σ' : Representation ℂ H τ.V := τ.ρ.comp φ
  have hσ' : σ'.IsIrreducible := GlobalTheory.LocCompSplit.isIrreducible_comp_of_surjective τ.ρ φ hφ τ.irr
  let ρ' : Representation ℂ H (GAf L n → W) :=
    { toFun := fun x => NG.rt L n (x : GAf L n)
      map_one' := by
        apply LinearMap.ext
        intro g
        funext a
        simp [NG.rt]
      map_mul' := fun x y => by
        apply LinearMap.ext
        intro g
        funext a
        simp [NG.rt, mul_assoc] }
  rw [Submodule.mem_iSup_iff_exists_finset] at hspan
  obtain ⟨t, ht⟩ := hspan
  let T : t → σ'.IntertwiningMap ρ' := fun j =>
    ⟨j.1.1, fun g => LinearMap.ext fun a => j.1.2 g.1 g.2 a⟩
  have hf' : f ∈ ⨆ j, LinearMap.range (T j).toLinearMap := by
    rw [iSup_subtype'] at ht
    exact ht
  let K : Subgroup H := (GlobalTheory.HeckeScalarSph.locK n s.v).comap H.subtype
  have hfixK : ∀ k ∈ K, ρ' k f = f := fun k hk => hfix k.1 hk
  have hne := GlobalTheory.UnrLoc.fixed_ne_bot_of_mem_iSup_range hσ' T K hf' hf0 hfixK
  rw [Submodule.ne_bot_iff] at hne
  obtain ⟨y, hy, hy0⟩ := hne
  refine ⟨y, hy0, fun κ hκ => ?_⟩
  exact (GlobalTheory.Parabolic.mem_fixed.1 hy) ⟨κ, hκ.2⟩ hκ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitLocalComponentHasFixedVectorOfIsotypicStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitLocalComponent_has_fixedVector_of_isotypic : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)), NG.IsIrrRep ρ S → ∀ (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s τ → ∀ (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous i → (∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ f ∈ NG.isoTyp ρ S, f ≠ 0 → (∀ κ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, NG.rt L n κ f = f) → ∃ a : τ.V, a ≠ 0 ∧ ∀ κ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n κ)) a = a := by
  first | exact @GlobalTheory.IsoTypFixLoc.main | exact GlobalTheory.IsoTypFixLoc.main | (intros; apply GlobalTheory.IsoTypFixLoc.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumTypePrimeInvariantFramesCongruentOn
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumTypePrimeInvariantFramesCongruentOn
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.AwayTopG

open GlobalTheory.TopStep GlobalTheory.LastSteps GlobalTheory.TopLaw

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem hom_mem_stdAt {n m : ℕ} (f : HomE E n m) (hf : ∀ j l, IntAt P (f (Pi.single j 1) l)) {v : Sp E n}
    (hv : v ∈ stdAt E n P) : f v ∈ stdAt E m P :=
  mem_stdAt.2 fun l => by
    have h := intAt_form_of_mem_stdAt (1 : E) (LinearMap.proj l ∘ₗ f) (fun i => by simpa using hf i l) hv
    simpa using h

theorem symm_mem_stdAt {n : ℕ} {κ : Sp E n ≃ₗ[E] Sp E n} (hκ : κ ∈ GLint E n P) {w : Sp E n} (hw : w ∈ stdAt E n P) :
    κ.symm w ∈ stdAt E n P :=
  (hκ (κ.symm w)).1 (by rw [LinearEquiv.apply_symm_apply]; exact hw)

theorem symm_near {n D : ℕ} {κ : Sp E n ≃ₗ[E] Sp E n} (hκ : κ ∈ GLint E n P)
    (hD : ∀ w ∈ stdAt E n P, ((qOf P : E) ^ D)⁻¹ • (κ w - w) ∈ stdAt E n P) {w : Sp E n} (hw : w ∈ stdAt E n P) :
    ((qOf P : E) ^ D)⁻¹ • (κ.symm w - w) ∈ stdAt E n P := by
  have h := hD _ (symm_mem_stdAt hκ hw)
  rw [LinearEquiv.apply_symm_apply] at h
  have e : ((qOf P : E) ^ D)⁻¹ • (κ.symm w - w) = -(((qOf P : E) ^ D)⁻¹ • (w - κ.symm w)) := by
    rw [← smul_neg, neg_sub]
  rw [e]
  exact Submodule.neg_mem _ h

end SlopeTestRemainingChoices

theorem topDat_frames_vGs : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (P : SB t μ), P.1 ∈ t.Pr.vGs →
  ∀ (κ : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1)))
    (κ' : Sp t.X.E (D.R.N (t.m2 + 1 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1 + 1))),
  κ ∈ GLint t.X.E _ P.1 → (∀ w ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ w - w) ∈ stdAt t.X.E _ P.1) →
  κ' ∈ GLint t.X.E _ P.1 → (∀ w ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ' w - w) ∈ stdAt t.X.E _ P.1) →
  ∀ (y : HomE t.X.E (D.R.N (t.m2 + 1)) (D.R.N (t.m2 + 1 + 1))) (y'' : Sp t.X.E (D.R.N (t.m2 + 1))),
  (∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * y'' l)) →
  topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
    topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y y'') := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie P hP κ κ' hκ hκD hκ' hκ'D y y'' hy''
  have hok := t.idx_ok μ
  have hc := hok.cst_ok
  have hn : TopNum D.R (t.m2 + 1) := topNum_of (m_eq t μ)
  have hX : t.X.Ok := hPin.fields.ok
  have hPr := t.pr_ok
  have hq0 : (qOf P.1 : t.X.E) ≠ 0 := qOf_ne_zero
  obtain ⟨d, hd⟩ : ∃ d, (t.cst μ).D P = d + 1 := ⟨(t.cst μ).D P - 1, by have := hc.D_pos P; omega⟩
  by_cases hI : ∀ j l, IntAt P.1 (y (Pi.single j 1) l)
  ·
    have hA : topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
        topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y (κ.symm y'') := by
      refine topDat_congr t.Ch t.sel (t.tup μ) (t.cst μ) hX hPr hc hn P hP _ _ _ ?_ ?_
      · have h1 : κ.symm ((qOf P.1 : t.X.E) • y'') ∈ stdAt t.X.E _ P.1 := symm_mem_stdAt hκ (mem_stdAt.2 hy'')
        rw [map_smul] at h1
        intro j
        simpa using mem_stdAt.1 h1 j
      · intro j
        have hkj : κ (Pi.single j 1) ∈ stdAt t.X.E _ P.1 := (hκ _).2 (single_mem_stdAt j)
        have hv : y (κ (Pi.single j 1)) ∈ stdAt t.X.E _ P.1 := hom_mem_stdAt y hI hkj
        have hz : κ'.symm (y (κ (Pi.single j 1))) ∈ stdAt t.X.E _ P.1 := symm_mem_stdAt hκ' hv
        have hzI : ∀ l, IntAt P.1 ((κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (Pi.single j 1) l) := fun l => mem_stdAt.1 hz l
        refine ⟨iff_of_true hzI (hI j), fun _ l => ?_⟩
        set s := ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ (Pi.single j 1) - Pi.single j 1) with hs
        set s' := ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ'.symm (y (κ (Pi.single j 1))) - y (κ (Pi.single j 1))) with hs'
        have hsI : s ∈ stdAt t.X.E _ P.1 := hκD _ (single_mem_stdAt j)
        have hs'I : s' ∈ stdAt t.X.E _ P.1 := symm_near hκ' hκ'D hv
        have hys : IntAt P.1 (y s l) := mem_stdAt.1 (hom_mem_stdAt y hI hsI) l
        have e1 : y s l = ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ * (y (κ (Pi.single j 1)) l - y (Pi.single j 1) l) := by
          rw [hs, map_smul, map_sub]
          rfl
        have e2 : s' l = ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ * (κ'.symm (y (κ (Pi.single j 1))) l - y (κ (Pi.single j 1)) l) := by
          rw [hs']
          rfl
        have key : (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (Pi.single j 1) l =
            y (Pi.single j 1) l + (qOf P.1 : t.X.E) * ((qOf P.1 : t.X.E) ^ d * (y s l + s' l)) := by
          rw [e1, e2, hd]
          show κ'.symm (y (κ (Pi.single j 1))) l = _
          field_simp
          ring
        rw [key, redP_add_q ((intAt_pow (intAt_nat _) d).mul (hys.add (mem_stdAt.1 hs'I l)))]
    have hB : topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y (κ.symm y'') =
        topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y y'' := by
      unfold topDat
      congr 1
      have hw : (qOf P.1 : t.X.E) • y'' ∈ stdAt t.X.E _ P.1 := mem_stdAt.2 hy''
      have hsw := symm_near hκ hκD hw
      have hdiff : κ.symm y'' - y'' ∈ stdAt t.X.E _ P.1 := by
        refine mem_stdAt.2 fun i => ?_
        have hi := mem_stdAt.1 hsw i
        have e : (κ.symm y'' - y'') i = (qOf P.1 : t.X.E) ^ d *
            ((((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ.symm ((qOf P.1 : t.X.E) • y'') - (qOf P.1 : t.X.E) • y'')) i) := by
          rw [map_smul, hd]
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          field_simp
          ring
        rw [e]
        exact (intAt_pow (intAt_nat _) d).mul hi
      have h := ftY_comp_glint t.sel (t.tup μ) (t.cst μ) hc P (fun h => absurd hP h) (κ := 1)
        (atNL t.X.E (D.R.N (t.m2 + 1 + 1)) (D.R.N (t.m2 + 1 + 1) - 1) ∘ₗ y) y'' (κ.symm y'')
        (fun _ => hy'') (fun h => absurd hP h) (fun _ => hdiff) (fun h => absurd hP h)
      exact h
    exact hA.trans hB
  ·
    push_neg at hI
    obtain ⟨j, l, hjl⟩ := hI
    have h0 : topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y y'' = 0 := by
      by_contra h
      exact hjl (topDat_int t.Ch t.sel (t.tup μ) (t.cst μ) hn P hP y y'' h j l)
    have h1 : topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') = 0 := by
      by_contra h
      have hzI := topDat_int t.Ch t.sel (t.tup μ) (t.cst μ) hn P hP _ _ h
      apply hjl
      have hm : (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm (Pi.single j 1)) ∈ stdAt t.X.E _ P.1 :=
        hom_mem_stdAt _ hzI (symm_mem_stdAt hκ (single_mem_stdAt j))
      have e : (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm (Pi.single j 1)) = κ'.symm (y (Pi.single j 1)) := by
        simp
      rw [e] at hm
      have hm' := (hκ' _).2 hm
      rw [LinearEquiv.apply_symm_apply] at hm'
      exact mem_stdAt.1 hm' l
    rw [h0, h1]

end GlobalTheory.TwV.AwayTopG

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumTypePrimeInvariantFramesCongruentOnStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStepDatum_typePrime_invariant_frames_congruent_one : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (P : SB t μ), P.1 ∈ t.Pr.vGs →
  ∀ (κ : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1)))
    (κ' : Sp t.X.E (D.R.N (t.m2 + 1 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1 + 1))),
  κ ∈ GLint t.X.E _ P.1 → (∀ w ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ w - w) ∈ stdAt t.X.E _ P.1) →
  κ' ∈ GLint t.X.E _ P.1 → (∀ w ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ' w - w) ∈ stdAt t.X.E _ P.1) →
  ∀ (y : HomE t.X.E (D.R.N (t.m2 + 1)) (D.R.N (t.m2 + 1 + 1))) (y'' : Sp t.X.E (D.R.N (t.m2 + 1))),
  (∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * y'' l)) →
  topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
    topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y y'') := by
  first | exact @GlobalTheory.TwV.AwayTopG.topDat_frames_vGs | exact GlobalTheory.TwV.AwayTopG.topDat_frames_vGs | (intros; apply GlobalTheory.TwV.AwayTopG.topDat_frames_vGs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsoTypeSpaceMaximalCompact
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SplitSatLoc

section Local
variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => NumberField.maximalRealSubfield L

def rtHom (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] : GAf L n →* Module.End ℂ (GAf L n → W) where
  toFun x := NG.rt L n x
  map_one' := LinearMap.ext fun f => funext fun g => by simp [NG.rt]
  map_mul' x y := LinearMap.ext fun f => funext fun g => by simp [NG.rt, mul_assoc]

theorem map_symm_map (s : SplitPlace L) (c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L) {n : ℕ} (g : GL (Fin n) (s.v.adicCompletion L⁺)) :
    Matrix.GeneralLinearGroup.map c.symm.toRingHom
      (Matrix.GeneralLinearGroup.map c.toRingHom g : GL (Fin n) (s.w.adicCompletion L)) = g :=
  Units.ext (Matrix.ext fun a b => by simp)

theorem map_map_symm (s : SplitPlace L) (c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L) {n : ℕ} (g : GL (Fin n) (s.w.adicCompletion L)) :
    Matrix.GeneralLinearGroup.map c.toRingHom
      (Matrix.GeneralLinearGroup.map c.symm.toRingHom g : GL (Fin n) (s.v.adicCompletion L⁺)) = g :=
  Units.ext (Matrix.ext fun a b => by simp)

theorem mem_Ov_iff {s : SplitPlace L} {c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L} (hc : Continuous c) (hcL : ∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x)
    (a : s.v.adicCompletion L⁺) :
    c a ∈ Formalism.UG.Ov L s.w ↔ a ∈ (s.v.adicCompletionIntegers L⁺).toSubring := by
  show c a ∈ s.w.adicCompletionIntegers L ↔ a ∈ s.v.adicCompletionIntegers L⁺
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
    GlobalTheory.SplitConjVal.valuation_eq s c hc hcL]

theorem map_mem_KGL_iff {s : SplitPlace L} {c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L} (hc : Continuous c) (hcL : ∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) {n : ℕ}
    (g : GL (Fin n) (s.v.adicCompletion L⁺)) :
    Matrix.GeneralLinearGroup.map c.toRingHom g ∈ GlobalTheory.LFun.KGL s.w (n := n) ↔
      g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers L⁺).toSubring := by
  rw [GlobalTheory.LFun.KGL, GlobalTheory.HeckeScalarSph.mem_GLint_iff, GlobalTheory.HeckeScalarSph.mem_GLint_iff, ← map_inv]
  simp only [Matrix.GeneralLinearGroup.map_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, mem_Ov_iff hc hcL]

theorem isUnifV_map {s : SplitPlace L} {c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L} (hc : Continuous c) (hcL : ∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x)
    {ϖ : s.v.adicCompletion L⁺} (hϖ : IsUnif L s.v ϖ) : Formalism.UG.IsUnifV L s.w (c ϖ) := by
  show Valued.v (c ϖ) = _
  rw [GlobalTheory.SplitConjVal.valuation_eq s c hc hcL]
  exact hϖ

theorem coe_glMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {n : ℕ} (g : GL (Fin n) A) :
    ((Matrix.GeneralLinearGroup.map f g : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) = (g : Matrix (Fin n) (Fin n) A).map f :=
  rfl

theorem diagJ_map {A B : Type} [Field A] [Field B] (f : A →+* B) (n : ℕ) (ϖ : A) (k : ℕ) :
    (Formalism.UG.diagJ n ϖ k).map f = Formalism.UG.diagJ n (f ϖ) k := by
  simp only [Formalism.UG.diagJ, Matrix.diagonal_map (map_zero f)]
  congr 1
  funext i
  split_ifs <;> simp

end Local

section Key
variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => NumberField.maximalRealSubfield L

def locAct (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (s : SplitPlace L)
    (c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L) (e : GL (Fin n) (s.v.adicCompletion L⁺) →* GAf L n) :
    Representation ℂ (GL (Fin n) (s.w.adicCompletion L)) (GAf L n → W) :=
  (rtHom n W).comp (e.comp (Matrix.GeneralLinearGroup.map c.symm.toRingHom))

theorem locAct_apply (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (s : SplitPlace L)
    (c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L) (e : GL (Fin n) (s.v.adicCompletion L⁺) →* GAf L n)
    (g : GL (Fin n) (s.w.adicCompletion L)) (f : GAf L n → W) :
    locAct n W s c e g f = NG.rt L n (e (Matrix.GeneralLinearGroup.map c.symm.toRingHom g)) f := rfl

theorem heckeD_eq_heckeVec {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (s : SplitPlace L)
    (c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L) (hc : Continuous c)
    (hcL : ∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x)
    (e : GL (Fin n) (s.v.adicCompletion L⁺) →* GAf L n) (he1 : ∀ g, TrivOutside {s.v} (e g))
    (he2 : ∀ g, s.loc n (e g) = g) (J : Subgroup (GAf L n))
    (hJ : ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) {ϖ : s.v.adicCompletion L⁺} (hϖ : IsUnif L s.v ϖ)
    (k : ℕ) {F : GAf L n → W} (hF : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ F = F) :
    NG.heckeD J (tSet L n s ϖ k) F =
      GlobalTheory.LFun.heckeVec (locAct n W s c e) (GlobalTheory.LFun.KGL s.w (n := n)) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov L s.w) (c ϖ) k) F := by
  classical
  have hψφ : ∀ g : GL (Fin n) (s.v.adicCompletion L⁺),
      Matrix.GeneralLinearGroup.map c.symm.toRingHom
        (Matrix.GeneralLinearGroup.map c.toRingHom g : GL (Fin n) (s.w.adicCompletion L)) = g := map_symm_map s c
  have hφψ : ∀ g : GL (Fin n) (s.w.adicCompletion L),
      Matrix.GeneralLinearGroup.map c.toRingHom
        (Matrix.GeneralLinearGroup.map c.symm.toRingHom g : GL (Fin n) (s.v.adicCompletion L⁺)) = g := map_map_symm s c
  obtain ⟨α0, -, hT0⟩ := GlobalTheory.HeckeScalarSph.exists_tSet_eq (n := n) s ϖ k hϖ
  obtain ⟨R, hR1, hR2⟩ := GlobalTheory.HeckeScalarSph.exists_repsU (n := n) s.v α0
  have hR1' : ∀ γ ∈ R, γ ∈ tSet L n s ϖ k := fun γ hγ => (hT0 γ).2 (hR1 γ hγ)
  have hR2' : ∀ x ∈ tSet L n s ϖ k, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n := fun x hx => hR2 x ((hT0 x).1 hx)
  have hD : ∀ x ∈ tSet L n s ϖ k, TrivOutside {s.v} x := fun x hx => hx.1
  rw [GlobalTheory.HeckeEigConj.heckeD_eq_sum_of_agree J hJ hD hR1' hR2' hF]
  have hU := isUnifV_map hc hcL hϖ
  rw [GlobalTheory.SatHecke.Tj_eq_dosetInd hU k]
  have hK : ∀ x, TrivOutside {s.v} x →
      (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) ∈ GlobalTheory.LFun.KGL s.w (n := n) ↔ x ∈ Umax L n) := fun x hx =>
    (map_mem_KGL_iff hc hcL _).trans (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hx)
  have hFK : F ∈ GlobalTheory.PRep.fixed (locAct n W s c e) (GlobalTheory.LFun.KGL s.w (n := n)) := by
    refine GlobalTheory.LGrp.mem_fixed.2 fun A hA => ?_
    rw [locAct_apply]
    refine hF _ ((hK _ (he1 _)).1 ?_) (he1 _)
    rw [he2, hφψ]; exact hA
  have hdiag : ∀ a b x : GL (Fin n) (s.v.adicCompletion L⁺),
      (x : Matrix (Fin n) (Fin n) _) = (a : Matrix (Fin n) (Fin n) _) * Formalism.UG.diagJ n ϖ k * (b : Matrix (Fin n) (Fin n) _) →
      (Matrix.GeneralLinearGroup.map c.toRingHom x : GL (Fin n) (s.w.adicCompletion L)) =
        Matrix.GeneralLinearGroup.map c.toRingHom a *
          Matrix.GeneralLinearGroup.mkOfDetNeZero (Formalism.UG.diagJ n (c ϖ) k) (GlobalTheory.SatHecke.diagJ_det_ne hU k) *
            Matrix.GeneralLinearGroup.map c.toRingHom b := by
    intro a b x h
    refine Units.ext ?_
    simp only [Units.val_mul, coe_glMap, h, Matrix.map_mul, diagJ_map,
      Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    rfl
  have hinj : Set.InjOn (fun γ => (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n γ) :
      GL (Fin n) (s.w.adicCompletion L))) R := by
    intro γ hγ δ hδ h
    have h' : s.loc n γ = s.loc n δ := by
      have := congrArg (Matrix.GeneralLinearGroup.map c.symm.toRingHom) h
      simpa only [hψφ] using this
    exact GlobalTheory.SplitLocEq.eq_of_trivOutside_of_loc_eq L n s γ δ (hD γ (hR1' γ hγ)) (hD δ (hR1' δ hδ)) h'
  have hmem : ∀ γ ∈ R, (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n γ) : GL (Fin n) (s.w.adicCompletion L)) ∈
      DoubleCoset.doubleCoset (Matrix.GeneralLinearGroup.mkOfDetNeZero (Formalism.UG.diagJ n (c ϖ) k)
        (GlobalTheory.SatHecke.diagJ_det_ne hU k)) (GlobalTheory.LFun.KGL s.w (n := n) : Set (GL (Fin n) (s.w.adicCompletion L)))
        (GlobalTheory.LFun.KGL s.w (n := n)) := by
    intro γ hγ
    obtain ⟨-, a, ha, b, hb, h⟩ := hR1' γ hγ
    exact DoubleCoset.mem_doubleCoset.2 ⟨_, (map_mem_KGL_iff hc hcL a).2 ha, _, (map_mem_KGL_iff hc hcL b).2 hb,
      hdiag a b _ h⟩
  have huniq : ∀ g ∈ DoubleCoset.doubleCoset (Matrix.GeneralLinearGroup.mkOfDetNeZero (Formalism.UG.diagJ n (c ϖ) k)
        (GlobalTheory.SatHecke.diagJ_det_ne hU k)) (GlobalTheory.LFun.KGL s.w (n := n) : Set (GL (Fin n) (s.w.adicCompletion L)))
        (GlobalTheory.LFun.KGL s.w (n := n)),
      ∃! r, r ∈ R.image (fun γ => (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n γ) :
        GL (Fin n) (s.w.adicCompletion L))) ∧ r⁻¹ * g ∈ GlobalTheory.LFun.KGL s.w (n := n) := by
    intro g hg
    obtain ⟨y, hy, z, hz, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
    obtain ⟨x, hx⟩ : ∃ x, x = e (Matrix.GeneralLinearGroup.map c.symm.toRingHom (y *
        Matrix.GeneralLinearGroup.mkOfDetNeZero (Formalism.UG.diagJ n (c ϖ) k) (GlobalTheory.SatHecke.diagJ_det_ne hU k) * z)) :=
      ⟨_, rfl⟩
    have hxt : TrivOutside {s.v} x := hx ▸ he1 _
    have hxT : x ∈ tSet L n s ϖ k := by
      refine ⟨hxt, Matrix.GeneralLinearGroup.map c.symm.toRingHom y, ?_,
        Matrix.GeneralLinearGroup.map c.symm.toRingHom z, ?_, ?_⟩
      · exact (map_mem_KGL_iff hc hcL _).1 (by rw [hφψ]; exact hy)
      · exact (map_mem_KGL_iff hc hcL _).1 (by rw [hφψ]; exact hz)
      · rw [hx, he2, map_mul, map_mul, Units.val_mul, Units.val_mul]
        congr 2
        rw [coe_glMap, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, diagJ_map]
        simp
    obtain ⟨γ, ⟨hγR, hγx⟩, hγu⟩ := hR2' x hxT
    have hkey : ∀ δ ∈ R, ((Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n δ) :
        GL (Fin n) (s.w.adicCompletion L))⁻¹ * (y * Matrix.GeneralLinearGroup.mkOfDetNeZero (Formalism.UG.diagJ n (c ϖ) k)
          (GlobalTheory.SatHecke.diagJ_det_ne hU k) * z) ∈ GlobalTheory.LFun.KGL s.w (n := n) ↔ δ⁻¹ * x ∈ Umax L n) := by
      intro δ hδ
      have e1 : (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n δ) : GL (Fin n) (s.w.adicCompletion L))⁻¹ *
          (y * Matrix.GeneralLinearGroup.mkOfDetNeZero (Formalism.UG.diagJ n (c ϖ) k) (GlobalTheory.SatHecke.diagJ_det_ne hU k) * z) =
          Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (δ⁻¹ * x)) := by
        rw [map_mul, map_mul, map_inv, map_inv, hx, he2, hφψ]
      rw [e1]
      exact hK _ (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hD δ (hR1' δ hδ))) hxt)
    refine ⟨_, ⟨Finset.mem_image_of_mem _ hγR, (hkey γ hγR).2 hγx⟩, ?_⟩
    rintro r ⟨hr, hr'⟩
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hr
    rw [hγu δ ⟨hδ, (hkey δ hδ).1 hr'⟩]
  rw [GlobalTheory.LFun.heckeVec_dosetInd hFK (R := R.image fun γ => (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n γ) :
    GL (Fin n) (s.w.adicCompletion L))) (fun r hr => ?_) huniq, Finset.sum_image hinj]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    rw [locAct_apply, hψφ, GlobalTheory.SplitLocEq.eq_of_trivOutside_of_loc_eq L n s (e (s.loc n γ)) γ (he1 _)
      (hD γ (hR1' γ hγ)) (he2 _)]
  · obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hr
    exact hmem γ hγ

end Key
section Main


end Main

end GlobalTheory.SplitSatLoc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetInvMulFrameReadingCongruentOneModNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetInvMulFrameReadingCongruentOneModNorm
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
open GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.FramesDet

open Matrix
open scoped TensorProduct

section Cong

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
  {P : HeightOneSpectrum (𝓞 E)}

def intAtSub (P : HeightOneSpectrum (𝓞 E)) :
    Subring (E ⊗[F] FiniteAdeleRing (𝓞 F) F) where
  carrier := {a | IntAtA (F := F) P a}
  mul_mem' := GlobalTheory.CplPt.intAtA_mul
  one_mem' := by simpa using GlobalTheory.CplPt.intAtA_int (F := F) (P := P) 1
  add_mem' := GlobalTheory.CplPt.intAtA_add
  zero_mem' := by simpa using GlobalTheory.CplPt.intAtA_int (F := F) (P := P) 0
  neg_mem' := by
    intro a ha
    have := GlobalTheory.CplPt.intAtA_mul (GlobalTheory.CplPt.intAtA_int (F := F) (P := P) (-1)) ha
    simpa using this

theorem det_congAt {d : ℕ} (hd : 1 ≤ d) {k : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (h : CongAt P d k) :
    IntAtA (F := F) P (iA F E ((qOf P : ℕ) : E)⁻¹ *
      (((Matrix.GeneralLinearGroup.det k : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) - 1)) := by
  classical
  set S := intAtSub (F := F) P with hS
  have hq : ((qOf P : ℕ) : E) ≠ 0 := by
    have : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  set Q := iA F E ((qOf P : ℕ) : E) with hQ
  have hcQ : iA F E ((qOf P : ℕ) : E)⁻¹ * Q = 1 := by rw [hQ, ← map_mul, inv_mul_cancel₀ hq, map_one]
  have hQS : Q ∈ S := by
    have := GlobalTheory.CplPt.intAtA_int (F := F) (P := P) ((qOf P : ℕ) : 𝓞 E)
    simpa [hQ] using this
  have hZ : ∀ a b, Q ^ (d - 1) * (iA F E (((qOf P : ℕ) : E) ^ d)⁻¹ *
      ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b) ∈ S :=
    fun a b => S.mul_mem (S.pow_mem hQS _) (h a b)
  have hZe : ∀ a b, Q * (Q ^ (d - 1) * (iA F E (((qOf P : ℕ) : E) ^ d)⁻¹ *
      ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b)) =
      ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b := by
    intro a b
    have e : Q * Q ^ (d - 1) * iA F E (((qOf P : ℕ) : E) ^ d)⁻¹ = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hd, hQ, ← map_pow, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one]
    rw [← mul_assoc, ← mul_assoc, e, one_mul]
  let Z : Matrix (Fin N) (Fin N) S := fun a b => ⟨_, hZ a b⟩
  let q' : S := ⟨Q, hQS⟩
  let M : Matrix (Fin N) (Fin N) S := 1 + q' • Z
  have hM : M.map S.subtype = (k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := by
    ext a b
    have e1 : S.subtype ((1 : Matrix (Fin N) (Fin N) S) a b) = (1 : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [Matrix.map_apply]
    simp only [M]
    rw [Matrix.add_apply, map_add (f := _), e1, Matrix.smul_apply, smul_eq_mul, map_mul]
    show _ + Q * (Q ^ (d - 1) * _) = _
    rw [hZe, Matrix.sub_apply]
    ring_nf
  set I : Ideal S := Ideal.span {q'}
  have hMI : M.map (Ideal.Quotient.mk I) = 1 := by
    ext a b
    have hq0 : Ideal.Quotient.mk I q' = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    rw [Matrix.map_apply]
    simp only [M]
    rw [Matrix.add_apply, map_add (f := _), Matrix.smul_apply, smul_eq_mul, map_mul, hq0, zero_mul, add_zero,
      Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : Ideal.Quotient.mk I M.det = Ideal.Quotient.mk I 1 := by
    rw [RingHom.map_det, map_one]
    show (M.map (Ideal.Quotient.mk I)).det = 1
    rw [hMI, Matrix.det_one]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hdet)
  have hk : ((Matrix.GeneralLinearGroup.det k : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) =
      S.subtype M.det := by
    rw [RingHom.map_det, Matrix.GeneralLinearGroup.val_det_apply]
    exact congrArg Matrix.det hM.symm
  have e2 : iA F E ((qOf P : ℕ) : E)⁻¹ *
      (((Matrix.GeneralLinearGroup.det k : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) - 1) = (w : _) := by
    rw [hk, show S.subtype M.det - 1 = S.subtype (M.det - 1) by simp, ← hw, map_mul]
    show iA F E ((qOf P : ℕ) : E)⁻¹ * ((w : _) * Q) = _
    rw [mul_comm (w : E ⊗[F] FiniteAdeleRing (𝓞 F) F), ← mul_assoc, hcQ, one_mul]
  rw [e2]
  exact w.2

end Cong

section Rat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem det_ratA (g : GL (Fin n) E) :
    ((Matrix.GeneralLinearGroup.det (ratA F g) : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) =
      iA F E ((Matrix.GeneralLinearGroup.det g : Eˣ) : E) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rfl

end Rat

section Frame

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Fields} (s : Seam D X)

theorem det_seamGL {n : ℕ} (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) :
    ((Matrix.GeneralLinearGroup.det (seamGL s g) : D.host.Eˣ) : D.host.E) = s.iE ((LinearEquiv.det g : X.Eˣ) : X.E) := by
  have h : ((seamGL s g : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) =
      (LinearMap.toMatrix' g.toLinearMap).map (s.iE : X.E →+* D.host.E) := rfl
  rw [Matrix.GeneralLinearGroup.val_det_apply, h, ← RingHom.mapMatrix_apply, ← RingHom.map_det, LinearMap.det_toMatrix',
    LinearEquiv.coe_det]
  rfl

variable {i : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} (fb : SB → GL (Fin (D.R.N i)) D.host.E) (dep : SB → ℕ)

theorem det_inFrame {P : SB} {κ : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    {g : Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)} (hd : 1 ≤ dep P) (h : InFrame s fb dep P κ g) :
    IntAtA (F := D.host.F) (seamP s P.1) (iA D.host.F D.host.E ((qOf (seamP s P.1) : D.host.E))⁻¹ *
      ((((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
        iA D.host.F D.host.E (s.iE ((LinearEquiv.det g : X.Eˣ) : X.E)) - 1)) := by
  have H := det_congAt hd h
  have e : ((Matrix.GeneralLinearGroup.det (((ratA D.host.F (fb P))⁻¹ * κ * ratA D.host.F (fb P))⁻¹ *
      ratA D.host.F (seamGL s g)) : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) =
      (((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
        iA D.host.F D.host.E (s.iE ((LinearEquiv.det g : X.Eˣ) : X.E)) := by
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, Units.val_mul, det_ratA, det_seamGL]
    congr 2
    rw [mul_comm, mul_inv_cancel_left]
  rw [← e]
  exact H

theorem det_inFrame_mul {P : SB} (hd : 1 ≤ dep P)
    (κ : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (g C : Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)) (h : InFrame s fb dep P κ g)
    (hC : CongAt (F := D.host.F) (seamP s P.1) (dep P) (ratA D.host.F (seamGL s C))) :
    IntAtA (F := D.host.F) (seamP s P.1) (iA D.host.F D.host.E ((qOf (seamP s P.1) : D.host.E))⁻¹ *
      ((((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
        iA D.host.F D.host.E (s.iE ((LinearEquiv.det (g * C) : X.Eˣ) : X.E)) - 1)) := by
  have hα := det_inFrame s fb dep hd h
  have hβ := det_congAt hd hC
  rw [det_ratA, det_seamGL] at hβ
  set U := (((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E)
  set G := iA D.host.F D.host.E (s.iE ((LinearEquiv.det g : X.Eˣ) : X.E))
  set W := iA D.host.F D.host.E (s.iE ((LinearEquiv.det C : X.Eˣ) : X.E))
  set qi := iA D.host.F D.host.E ((qOf (seamP s P.1) : D.host.E))⁻¹
  set Q := iA D.host.F D.host.E ((qOf (seamP s P.1) : D.host.E))
  have hq : ((qOf (seamP s P.1) : ℕ) : D.host.E) ≠ 0 := by
    have : qOf (seamP s P.1) ≠ 0 := fun h0 => (seamP s P.1).ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  have hcQ : qi * Q = 1 := by
    simp only [qi, Q]; rw [← map_mul, inv_mul_cancel₀ hq, map_one]
  have hQ : IntAtA (F := D.host.F) (seamP s P.1) Q := by
    have := GlobalTheory.CplPt.intAtA_int (F := D.host.F) (P := seamP s P.1) ((qOf (seamP s P.1) : ℕ) : 𝓞 D.host.E)
    simpa [Q] using this
  have hdet : iA D.host.F D.host.E (s.iE ((LinearEquiv.det (g * C) : X.Eˣ) : X.E)) = G * W := by
    simp only [G, W]; rw [map_mul, Units.val_mul, map_mul, map_mul]
  have hW : W = Q * (qi * (W - 1)) + 1 := by
    linear_combination (1 - W) * hcQ
  have hWi : IntAtA (F := D.host.F) (seamP s P.1) W := by
    rw [hW]
    exact GlobalTheory.CplPt.intAtA_add (GlobalTheory.CplPt.intAtA_mul hQ hβ) (by simpa using GlobalTheory.CplPt.intAtA_int (F := D.host.F) (P := seamP s P.1) 1)
  have e : qi * (U * (G * W) - 1) = qi * (U * G - 1) * W + qi * (W - 1) := by ring
  rw [hdet, e]
  exact GlobalTheory.CplPt.intAtA_add (GlobalTheory.CplPt.intAtA_mul hα hWi) hβ

end Frame

end GlobalTheory.FramesDet

theorem GlobalTheory.FramesDet.det_frame_mul_congAt : ∀ {D : D7} {X : Fields} (s : Seam D X) {i : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 X.E))}
    (fb : SB → GL (Fin (D.R.N i)) D.host.E) (dep : SB → ℕ) (P : SB), 1 ≤ dep P →
    ∀ (κ : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (g C : Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)), InFrame s fb dep P κ g →
    CongAt (F := D.host.F) (seamP s P.1) (dep P) (ratA D.host.F (seamGL s C)) →
    IntAtA (F := D.host.F) (seamP s P.1) (iA D.host.F D.host.E ((qOf (seamP s P.1) : D.host.E))⁻¹ *
      ((((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
        iA D.host.F D.host.E (s.iE ((LinearEquiv.det (g * C) : X.Eˣ) : X.E)) - 1)) := by
  intro D X s i SB fb dep P hd κ g C h hC
  exact GlobalTheory.FramesDet.det_inFrame_mul s fb dep hd κ g C h hC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetInvMulFrameReadingCongruentOneModNormStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
open GlobalTheory.TopStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_inv_mul_frame_reading_congruent_one_mod_norm : ∀ {D : D7} {X : Fields} (s : Seam D X) {i : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 X.E))}
    (fb : SB → GL (Fin (D.R.N i)) D.host.E) (dep : SB → ℕ) (P : SB), 1 ≤ dep P →
    ∀ (κ : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (g C : Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)), InFrame s fb dep P κ g →
    CongAt (F := D.host.F) (seamP s P.1) (dep P) (ratA D.host.F (seamGL s C)) →
    IntAtA (F := D.host.F) (seamP s P.1) (iA D.host.F D.host.E ((qOf (seamP s P.1) : D.host.E))⁻¹ *
      ((((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
        iA D.host.F D.host.E (s.iE ((LinearEquiv.det (g * C) : X.Eˣ) : X.E)) - 1)) := by
  first | exact @GlobalTheory.FramesDet.det_frame_mul_congAt | exact GlobalTheory.FramesDet.det_frame_mul_congAt | (intros; apply GlobalTheory.FramesDet.det_frame_mul_congAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruentOneMemStepLevelsCharacterOne
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruentOneMemStepLevelsCharacterOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

noncomputable section

namespace GlobalTheory.LevOneAt

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory _root_.Formalism.L2.DIV _root_.Formalism.L2.Col

theorem cong_mem_level_chr_one' : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.Ok → Pr.Ok → L.Ok Ch sel mu cst G m2 → ∀ (j : ℕ), j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu)
    (k : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E (R.N j)) l))) →
    ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (L.h j b P),
      (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (k x)) ∧ chiInv Ch sel mu cst j P (L.h j b P) r = 1 := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hL j hj b P k hk
  classical
  obtain ⟨hkG, hkC⟩ := GlobalTheory.T.mem_integralGL_principalCongruence_of_cols_cong P.1 (cst.D P) k (hL.cst_ok.D_pos P) hk
  set κ : GLint X.E (R.N j) P.1 := ⟨k, hkG⟩ with hκdef
  have hψ : cst.psi P (Loc.n1Arg (GlobalTheory.CongLevel.extE (cOf R j) k)) = 1 := by
    rw [GlobalTheory.Mem.Col2.LevMod.unipotentArg_extendByIdOnLastCoords]
    exact hL.cst_ok.psi_int P 0 (by simpa using GlobalTheory.CongLevel.intAt_nat P.1 0)
  have hq : ((qOf P.1 : ℕ) : X.E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
  by_cases hP : P.1 ∈ Pr.vGs
  · have hD1 : cst.D P = 1 := hL.depthG P hP
    have hdu := GlobalTheory.Mem.Col2.degOneUnram_of_mem_vGs hX hPr hP
    have hd : ∀ a : X.E, IntAt P.1 a → redP P.1 a = 0 → IntAt P.1 (a / (qOf P.1 : X.E)) :=
      fun a ha h0 => GlobalTheory.TopStep.intAt_div_of_redP hdu.2 ha h0
    have hred : ∀ x ∈ stdAt X.E (R.N j) P.1, redV P.1 (k x) = redV P.1 x := by
      have h1 := GlobalTheory.TopStep.redGL_of_prinCong (by omega : 0 < cst.D P) hkC
      intro x hx
      have h2 := GlobalTheory.TopStep.redV_redGL κ hx
      rw [h1, Units.val_one, Matrix.one_mulVec] at h2
      exact h2
    have hh := hL.stabG j b P hP
    refine ⟨GlobalTheory.CongLevel.extE (cOf R j) k, GlobalTheory.Mem.Col2.LevMod.extE_mem_Cbe cst.sharp j P.1 hP hd (L.h j b P) hh k hkG hred, GlobalTheory.CongLevel.extE_inX _ k, ?_⟩
    have hh' := hh
    unfold lamYat at hh'
    rw [if_pos hP] at hh'
    have hcong := GlobalTheory.CongLevel.conj_cong (qOf P.1) _ _ (L.h j b P) hh'
      (GlobalTheory.CongLevel.extE_cong P.1 (qOf P.1) (cOf R j) (fun i => i + 1) hd k hkG hred)
    have h1 := GlobalTheory.T.rowCharacter_id_add_q_smul_latticePreserving_eq_one Ch mu cst.sharp j P.1 hP ((qOf P.1 : X.E)⁻¹ •
      (((L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) k * L.h j b P : AutY X R j).toLinearMap - LinearMap.id))
      fun x hx => by
        have hx' := hx
        unfold lamYat at hx' ⊢
        rw [if_pos hP] at hx' ⊢
        have h2 := hcong x hx'
        rw [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe]
        exact h2
    rw [smul_inv_smul₀ hq, add_sub_cancel] at h1
    unfold chiInv
    rw [h1, hψ, inv_one, one_mul]
  · have hstd : ∀ x, x ∈ lamYat (Pr := Pr) (R := R) j P.1 ↔ x ∈ stdAt X.E (R.N j + cOf R j) P.1 := by
      intro x
      unfold lamYat
      rw [if_neg hP]
      unfold LocE.lamY
      rw [GlobalTheory.CongLevel.mem_sclLat, GlobalTheory.TopStep.mem_stdAt]
      simp only [LocE.scE, Pi.zero_apply, Nat.cast_zero, ite_self, zpow_zero, inv_one, one_mul]
    have hbd := hL.boundQ j b P hP
    have hbd' : ∀ x ∈ stdAt X.E (R.N j + cOf R j) P.1, (L.h j b P)⁻¹ x ∈ stdAt X.E (R.N j + cOf R j) P.1 ∧
        ((qOf P.1 : X.E) ^ j) • (L.h j b P) x ∈ stdAt X.E (R.N j + cOf R j) P.1 := fun x hx => by
      have h1 := hbd x ((hstd x).2 hx)
      exact ⟨(hstd _).1 h1.1, (hstd _).1 h1.2⟩
    have hjD : j + 1 ≤ cst.D P := by
      have h1 := hL.depthQ' P hP
      have h2 := hL.hm
      omega
    have hg := GlobalTheory.T.conj_extend_principalCongruence_cong_one_mod_q P.1 (cOf R j) j (cst.D P) (L.h j b P) κ hkC hjD hbd'
    have hginv := GlobalTheory.T.conj_extend_principalCongruence_cong_one_mod_q P.1 (cOf R j) j (cst.D P) (L.h j b P) κ⁻¹ (inv_mem hkC) hjD hbd'
    have einv : ((L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) κ.1 * L.h j b P)⁻¹ =
        (L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) (κ⁻¹).1 * L.h j b P := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, GlobalTheory.CongLevel.extE_inv, mul_assoc]
      rfl
    refine ⟨GlobalTheory.CongLevel.extE (cOf R j) k, ⟨GlobalTheory.CongLevel.extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup _ k, ?_⟩, GlobalTheory.CongLevel.extE_inX _ k, ?_⟩
    · have e : (MulAut.conj (L.h j b P)⁻¹).toMonoidHom (GlobalTheory.CongLevel.extE (cOf R j) k) =
          (L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) k * L.h j b P := by simp
      show (MulAut.conj (L.h j b P)⁻¹).toMonoidHom (GlobalTheory.CongLevel.extE (cOf R j) k) ∈ Jat (Pr := Pr) cst.sharp j P.1
      rw [e]
      unfold Jat
      rw [if_neg hP]
      refine GlobalTheory.T.mem_parahoric_of_cong_one_mod_q P.1 (R.k + j) (R.N j) (cOf R j) _ hg ?_
      rw [einv]
      exact hginv
    · unfold chiInv
      rw [hψ, inv_one, one_mul]
      unfold lamRow
      rw [if_neg hP]
      exact GlobalTheory.T.blockDetResidueChar_eq_one_of_cong_mod_q P.1 _ (R.k + j) (R.N j) (R.N j + cOf R j) _ (by omega) hg

theorem levAt_one : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.Ok → Pr.Ok → ChIdx.Ok Ch sel mu cst L G m2 → ∀ j (b : L.β j) (P : rowSG Pr sel mu) (k : GLint X.E (R.N j) P.1), j ≤ m2 + 1 →
    (∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : X.E) ^ (cst.D P))⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp X.E (R.N j)) l))) →
    GlobalTheory.TopLaw.LevAt (L.levG j b) (L.levQ j b) P k 1 := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hL j b P k hj hk
  obtain ⟨r, hr, hrx, hchi⟩ := cong_mem_level_chr_one' Ch sel mu cst L G m2 hX hPr hL j hj b P k.1 hk
  obtain ⟨c, hc, ec⟩ := GlobalTheory.CplLev.levAt_of_lift hL b P k r hr hrx
  have : c = 1 := Units.ext (by rw [ec, hchi, Units.val_one])
  rwa [this] at hc

end GlobalTheory.LevOneAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruentOneMemStepLevelsCharacterOneStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruent_one_mem_step_levels_character_one : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.Ok → Pr.Ok → ChIdx.Ok Ch sel mu cst L G m2 → ∀ j (b : L.β j) (P : rowSG Pr sel mu) (k : GLint X.E (R.N j) P.1), j ≤ m2 + 1 →
    (∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : X.E) ^ (cst.D P))⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp X.E (R.N j)) l))) →
    GlobalTheory.TopLaw.LevAt (L.levG j b) (L.levQ j b) P k 1 := by
  first | exact @GlobalTheory.LevOneAt.levAt_one | exact GlobalTheory.LevOneAt.levAt_one | (intros; apply GlobalTheory.LevOneAt.levAt_one <;> assumption)
end
end
