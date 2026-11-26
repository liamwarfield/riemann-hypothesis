module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

abbrev cls {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (π : IrrRep (GL (Fin n) k)) : IrrGL (k := k) := ⟨n, π.cl⟩

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def sumList (l : List (WD h)) : WD h := l.foldr WD.lpSum (WD.lpZero (h := h))

def IsIrrWD (x : WD h) : Prop := ∃ (n : ℕ) (a : WDRep h (Fin n → ℂ)), WD.mk a = x ∧ a.ρ.IsIrreducible

def IsTameWD (x : WD h) : Prop :=
  ∃ (n : ℕ) (a : WDRep h (Fin n → ℂ)), WD.mk a = x ∧
    ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → a.ρ σ = 1

structure Laws (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (ε : EpsFamily A)
    (rc : IrrGL (k := w.adicCompletion E) → WD h) : Prop where

  bij : Function.Bijective rc

  dim : ∀ x, (rc x).lpDim = x.1

  one : ∀ χ hχ, rc (.ofChar χ hχ) = WD.lpOfChar h (χ.comp a) (ha.smooth hχ)

  eps : ∀ ψ : AddChar (w.adicCompletion E) Circle, Continuous ψ → ψ ≠ 1 →
    ∀ (m : ℕ) (π : IrrRep (GL (Fin (m + 1)) (w.adicCompletion E))) (τ : IrrRep (GL (Fin m) (w.adicCompletion E))),
      IsCuspidal π.ρ → HasPairEps ψ π.ρ τ.ρ (ε E w h ψ ((rc (cls π)).lpChar (rc (cls τ))))

  twist : ∀ x χ hχ, rc (x.tw χ hχ) = (rc x).lpChar (rc (.ofChar χ hχ))

  central : ∀ (x : IrrGL (k := w.adicCompletion E)) ω, HasCentralChar x.rep ω →
    ∀ σ, ((rc x).eig σ).prod = (ω (a σ) : ℂ)

  dual : ∀ (n : ℕ) (π π' : IrrRep (GL (Fin n) (w.adicCompletion E))), Nonempty (π'.ρ.Equiv (contra π.ρ)) →
    rc (cls π') = (rc (cls π)).lpDual

  cusp : ∀ x, x.IsCusp ↔ IsIrrWD (rc x)

  langlands : ∀ (l : List (Segment (w.adicCompletion E))) (x : IrrGL (k := w.adicCompletion E)),
    IsL (l : Multiset (Segment (w.adicCompletion E))) x.rep →
    rc x = sumList (l.map fun Δ =>
      ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len))

  det : ∀ (t : ℕ) χ hχ, rc (cls (IrrRep.det (Fin t) χ hχ)) =
    sumList ((List.range t).map fun j : ℕ => (rc (.ofChar χ hχ)).lpTw (((t : ℝ) - 1) / 2 - j))

  prod : ∀ (r t : ℕ) (σ : IrrRep (GL (Fin r) (w.adicCompletion E))) (τ : IrrRep (GL (Fin t) (w.adicCompletion E)))
    (π : IrrRep (GL (Fin (r + t)) (w.adicCompletion E))), Nonempty (π.ρ.Equiv (prod₂ σ.ρ τ.ρ)) →
    rc (cls π) = (rc (cls σ)).lpSum (rc (cls τ))

  supp : ∀ (x : IrrGL (k := w.adicCompletion E)) s, HasSupport x.rep s →
    ∀ σ, (rc x).charPol σ = (s.map fun y => (rc y).charPol σ).prod

  sph : ∀ x : IrrGL (k := w.adicCompletion E), IsSpherical x.rep ↔ (rc x).unr

  sat : ∀ (x : IrrGL (k := w.adicCompletion E)) (α : Fin x.1 → ℂˣ), HasSatake x.rep α →
    rc x = WD.mk (WDRep.diag h fun i => (α i)⁻¹)

  depth : ∀ x : IrrGL (k := w.adicCompletion E),
    fixed x.rep (KOne (w.adicCompletion E) (Fin x.1)) ≠ ⊥ ↔ IsTameWD (rc x)

variable (h) in
def IsRec (rc : IrrGL (k := w.adicCompletion E) → WD h) : Prop :=
  ∃ (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (ε : EpsFamily A), IsDeligneEps ε ∧ Laws a ha ε rc

def FieldCompatible {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
    (rc : IrrGL (k := w.adicCompletion E) → WD h) (rc' : IrrGL (k := w'.adicCompletion E') → WD h') : Prop :=
  ∀ (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'),
    (∀ z, φ z ∈ A' ↔ z ∈ A) → (∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x)) → Continuous i →
    (∀ x, i (algebraMap E _ x) = algebraMap E' _ (j x)) →
    ∀ (n : ℕ) (π : IrrRep (GL (Fin n) (w.adicCompletion E))) (π' : IrrRep (GL (Fin n) (w'.adicCompletion E')))
      (e : π.V ≃ₗ[ℂ] π'.V), (∀ g v, e (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (e v)) →
      ∃ (b : WDRep h (Fin n → ℂ)) (b' : WDRep h' (Fin n → ℂ)), WD.mk b = rc (cls π) ∧ WD.mk b' = rc' (cls π') ∧
        b.N = b'.N ∧ ∀ (σ : Weil h) (σ' : Weil h'), (∀ z, φ ((σ : G E Ω) z) = (σ' : G E' Ω') (φ z)) → b.ρ σ = b'.ρ σ'

end GlobalTheory.LocLanglands

namespace GlobalTheory.Published

open GlobalTheory.LocLanglands

def LocalLanglandsGL : Prop :=
  (∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), ∃! rc : IrrGL (k := w.adicCompletion E) → WD h, IsRec h rc) ∧
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω')
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w')
    (rc : IrrGL (k := w.adicCompletion E) → WD h) (rc' : IrrGL (k := w'.adicCompletion E') → WD h'),
    IsRec h rc → IsRec h' rc' → FieldCompatible rc rc'

end GlobalTheory.Published

namespace GlobalTheory.LocLanglands

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem lpChar_lpOfChar (x : WD h) (ξ : Weil h →* ℂˣ) (hξ : WeilDeligne.IsSmooth ξ) :
    x.lpChar (WD.lpOfChar h ξ hξ) = x.lpTwist ξ hξ := by
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  rw [WD.lpOfChar, WD.lpChar_mk, WD.lpTwist_mk]
  refine WD.sound ⟨(TensorProduct.congr (.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)).trans
    (TensorProduct.rid ℂ _), fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.inductionOn with
    | tmul x y => simp [smul_smul, mul_comm]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · induction v using TensorProduct.inductionOn with
    | tmul x y => simp [WDRep.twist]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]


variable (w) in
theorem resCard_eq_normV : resCard (w.adicCompletion E) = normV w := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  have hO : 𝒪[w.adicCompletion E] = (w.adicCompletionIntegers E).toSubring := by
    ext y
    rw [Valuation.mem_integer_iff, he.le_one_iff_le_one]
    exact Iff.rfl
  have hq : resCard (w.adicCompletion E) = Formalism.UG.qV E w := by
    rw [← Formalism.UG.P.tjcosets_card_residue]
    exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv (RingEquiv.subringCongr hO)).toEquiv
  simpa only [normV, Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hq

variable {a : Weil h →* (w.adicCompletion E)ˣ}

theorem IsLocalArtin.unrChar_comp (ha : IsLocalArtin h a) (c : ℂˣ) :
    (SmGL.unrChar (w.adicCompletion E) c).comp a = WeilDeligne.unrChar h c⁻¹ := by
  refine MonoidHom.ext fun σ => ?_
  rw [MonoidHom.comp_apply, SmGL.unrChar_apply, ha.ord_eq, WeilDeligne.unrChar_apply, _root_.zpow_neg, _root_.inv_zpow]

theorem IsLocalArtin.absPow_comp (ha : IsLocalArtin h a) (s : ℝ) :
    (absPow (w.adicCompletion E) s).comp a = WeilDeligne.unrChar h (qPow w s) := by
  refine MonoidHom.ext fun σ => Units.ext ?_
  have hq : (0 : ℝ) ≤ ((normV w : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [MonoidHom.comp_apply, val_absPow_ofReal, GlobalTheory.LGrp.nabs_eq_zpow, ha.ord_eq, neg_neg, resCard_eq_normV,
    WeilDeligne.unrChar_apply, Units.val_zpow_eq_zpow_val, coe_qPow, ← Real.rpow_intCast, ← Real.rpow_mul hq, mul_comm,
    Real.rpow_mul hq, Real.rpow_intCast, Complex.ofReal_zpow, Complex.ofReal_cpow hq, Complex.ofReal_natCast]

variable {ha : IsLocalArtin h a} {ε : EpsFamily A} {rc : IrrGL (k := w.adicCompletion E) → WD h}

theorem Laws.tw_eq (H : Laws a ha ε rc) (x : IrrGL (k := w.adicCompletion E)) (χ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hχ : IsSmoothChar χ) : rc (x.tw χ hχ) = (rc x).lpTwist (χ.comp a) (ha.smooth hχ) := by
  rw [H.twist, H.one, lpChar_lpOfChar]

theorem Laws.nu_eq (H : Laws a ha ε rc) (x : IrrGL (k := w.adicCompletion E)) (s : ℝ) : rc (x.nu s) = (rc x).lpTw s := by
  rw [IrrGL.nu, H.tw_eq, WD.lpTw]
  congr 1
  exact ha.absPow_comp s

theorem Laws.eq_iff (H : Laws a ha ε rc) {n : ℕ} (π π' : IrrRep (GL (Fin n) (w.adicCompletion E))) :
    rc (cls π) = rc (cls π') ↔ Nonempty (π.ρ.Equiv π'.ρ) :=
  H.bij.1.eq_iff.trans (IrrGL.of_eq_of (π := π.ρ) (σ := π'.ρ) (hs := π.smooth) (hi := π.irr) (hs' := π'.smooth)
    (hi' := π'.irr))

end GlobalTheory.LocLanglands
end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsCuspFunOnePlane
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies MeasureTheory Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspDecay.Model

variable {D : D7}

theorem isCuspFun_zero (V : HSp D) : IsCuspFun V fun _ => 0 := fun _ _ _ _ _ _ _ _ => by simp

def line (D : D7) : HSp D := Examples₂.posSpace Examples₂.star_isIntegral 1

def plane (D : D7) : HSp D := Examples₂.stdSpace Examples₂.star_isIntegral 2 ![false, true] 1 1

theorem isIsoFrame_plane (D : D7) : IsIsoFrame (plane D) (r := 1) (Matrix.of fun _ _ => 1) := by
  refine ⟨one_pos, ?_, ?_⟩
  · refine linearIndependent_unique_iff.2 fun h => ?_
    have := congrFun h (0 : Fin 2)
    exact one_ne_zero this
  · have hg : ∀ i j : Fin 2, (plane D).gram i j = if i = j then (Examples₂.sgn (![false, true] i) : D.host.E) else 0 :=
      Examples₂.stdSpace_gram_apply Examples₂.star_isIntegral 2 ![false, true] 1 1
    funext a b
    change ∑ j : Fin 2, (∑ i : Fin 2, D.sp.cm.sig 1 * (plane D).gram i j) * 1 = 0
    simp [Fin.sum_univ_two, hg, Examples₂.sgn]

theorem isClosed_NI (V : HSp D) {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E} (hC : IsIsoFrame V C) :
    IsClosed (NI V C : Set (GA D V)) := by
  obtain ⟨L, hL, -⟩ := GlobalTheory.AutFunCompare.exists_dual D.sp.cm V C hC.2.1 hC.2.2
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : T2Space (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField _
  have : T2Space (AF D.host.F ⊗[D.host.F] D.host.E) :=
    .of_injective_continuous (f := (Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).equivFun)
      (LinearEquiv.injective _) (IsModuleTopology.continuous_of_linearMap
        (Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).equivFun.toLinearMap)
  have hm : Continuous fun g : GA D V => (HA.mat _ D.sp.cm.sig V.gram g).1 :=
    Units.continuous_val.comp continuous_subtype_val
  rw [GlobalTheory.AutFunCompare.NI_eq]
  have hcl : IsClosed {g : GA D V |
      ((HA.mat _ D.sp.cm.sig V.gram g).1 - 1) * (C * L).map (inclR (F := D.host.F) (AF D.host.F)) = 0 ∧
      (1 - (C * L).map (inclR (F := D.host.F) (AF D.host.F))) * ((HA.mat _ D.sp.cm.sig V.gram g).1 - 1) *
        (1 - GlobalTheory.AutFunCompare.adj D.sp.cm V ((C * L).map (inclR (F := D.host.F) (AF D.host.F)))) = 0} :=
    (isClosed_eq ((hm.sub continuous_const).matrix_mul continuous_const) continuous_const).inter
    (isClosed_eq ((continuous_const.matrix_mul (hm.sub continuous_const)).matrix_mul continuous_const) continuous_const)
  convert hcl using 1
  exact Set.ext fun g => GlobalTheory.AutFunCompare.mem_unipRad_idem D.sp.cm V C L hL g

theorem not_isCuspFun_const (V : HSp D) {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E} (hC : IsIsoFrame V C)
    {c : ℂ} (hc : c ≠ 0) : ¬ IsCuspFun V fun _ => c := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have : LocallyCompactSpace (NI V C) := (isClosed_NI V hC).locallyCompactSpace
  let i : NIQ V C → GQ V := fun x => ⟨x.1.1, x.2⟩
  have hi : Function.Injective i := fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : GQ V => z.1) h))
  have : DiscreteTopology (NIQ V C) := DiscreteTopology.of_continuous_injective (f := i)
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) hi
  have : Countable (NIQ V C) := hi.countable
  have : SecondCountableTopology (NI V C) := TopologicalSpace.Subtype.secondCountableTopology _
  let μ : Measure (NI V C) := Measure.haar
  obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain (NIQ V C) μ
  have h0 := h r C hC μ 𝓕 inferInstance h𝓕 1
  have hne : μ 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne μ)
  have hint : IntegrableOn (fun _ : NI V C => c) 𝓕 μ := by
    have key : ∀ N : Subgroup (GA D V), N = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) (GlobalTheory.AutFunCompare.colSpan V C) →
        ∀ Q : Subgroup (GA D V), Q = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.ratPts D.sp.cm V →
        ∀ (μ : Measure N) (𝓕 : Set N), μ.IsHaarMeasure → IsFundamentalDomain (Q.subgroupOf N) 𝓕 μ →
          IntegrableOn (fun _ : N => c) 𝓕 μ := by
      rintro N rfl Q rfl μ 𝓕 hμ h𝓕
      exact GlobalTheory.AutFunCompare.integrableOn_constTerm D.sp.cm V _ ((GlobalTheory.AutFunCompare.isIsoFrame_iff V C).1 hC).2
        (fun _ => c) continuous_const (fun _ _ _ => rfl) μ hμ 𝓕 h𝓕 1
    exact key _ (GlobalTheory.AutFunCompare.NI_eq V C) _ (GlobalTheory.AutFunCompare.GQ_eq V) μ 𝓕 inferInstance h𝓕
  have hlt : μ 𝓕 ≠ ⊤ := by
    rcases (integrableOn_const_iff (C := c)).1 hint with h | h
    · exact absurd (by simpa using h) hc
    · exact h.ne
  rw [setIntegral_const, smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact ENNReal.toReal_ne_zero.2 ⟨hne, hlt⟩ h0
  · exact hc h0

theorem not_isCuspFun_one_plane (D : D7) : ¬ IsCuspFun (plane D) fun _ => 1 :=
  not_isCuspFun_const _ (isIsoFrame_plane D) one_ne_zero

end GlobalTheory.CuspDecay.Model

end
end
