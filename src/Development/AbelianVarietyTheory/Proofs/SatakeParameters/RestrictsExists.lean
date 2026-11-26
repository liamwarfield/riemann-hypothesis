module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDet
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterTwistPotentiallySemistable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RestrictsExists
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValSubLtIff
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DelEps.WeilRes

open Pointwise

variable {Ω : Type} [Field Ω]

theorem mem_Dec_iff {F : Type} [Field F] [NumberField F] [Algebra F Ω] {A : ValuationSubring Ω} {σ : G F Ω} :
    σ ∈ Dec (F := F) A ↔ ∀ x, (σ x ∈ A ↔ x ∈ A) := by
  refine ⟨fun h x => apply_mem_iff_of_mem_Dec h x, fun h => ?_⟩
  show σ • A = A
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← h, mul_inv_apply]

theorem normV_eq_pow {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)) :
    normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isPrime
  simpa only [normV, Ideal.absNorm_eq_natCard] using
    (Ideal.absNorm_pow_inertiaDeg (w.under (𝓞 K)).asIdeal w.asIdeal).symm

theorem under_eq {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A v)
    (h' : IsPlaceOver A w) : w.under (𝓞 K) = v := by
  refine eq_of_isPlaceOver (A := A) ?_ h
  intro x
  show _ ↔ algebraMap (𝓞 K) (𝓞 L) x ∈ w.asIdeal
  rw [← h' (algebraMap (𝓞 K) (𝓞 L) x), IsScalarTower.algebraMap_apply K L Ω]
  rfl

section Res

variable {L : Type} [Field L] [NumberField L] [Algebra L Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)}

end Res

end GlobalTheory.DelEps.WeilRes
end
end

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G Dec IsPlaceOver
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL.ResEx

variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}

theorem res_mem_Dec {σ : G L Ω} (hσ : σ ∈ Dec (F := L) A) :
    AlgEquiv.restrictScalarsHom K σ ∈ Dec (F := K) A :=
  GlobalTheory.DelEps.WeilRes.mem_Dec_iff.2 fun x => GlobalTheory.DelEps.WeilRes.mem_Dec_iff.1 hσ x

theorem res_mem_Ine {σ : G L Ω} (hσ : σ ∈ Ine (F := L) A) :
    AlgEquiv.restrictScalarsHom K σ ∈ Ine (F := K) A :=
  ⟨res_mem_Dec hσ.1, fun x hx => hσ.2 x hx⟩

theorem res_mem_Weil (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (σ : Weil h') :
    AlgEquiv.restrictScalarsHom K (σ : G L Ω) ∈ Weil h := by
  obtain ⟨a, b, hab⟩ := (mem_Weil h').1 σ.2
  have hQ : normV v' = normV v ^ v'.asIdeal.inertiaDeg (𝓞 K) := by
    rw [GlobalTheory.DelEps.WeilRes.normV_eq_pow (K := K) v', GlobalTheory.DelEps.WeilRes.under_eq h h']
  refine ⟨v'.asIdeal.inertiaDeg (𝓞 K) * a, v'.asIdeal.inertiaDeg (𝓞 K) * b, res_mem_Dec hab.1,
    fun x hx => ?_⟩
  have h2 := hab.2 x hx
  rw [hQ, ← pow_mul, ← pow_mul] at h2
  exact h2

def resW (h : IsPlaceOver A v) (h' : IsPlaceOver A v') : Weil h' →* Weil h where
  toFun σ := ⟨AlgEquiv.restrictScalarsHom K (σ : G L Ω), res_mem_Weil h h' σ⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' σ τ := Subtype.ext (map_mul _ _ _)

def resI : Ine (F := L) A →* Ine (F := K) A :=
  ((AlgEquiv.restrictScalarsHom K).comp (Ine (F := L) A).subtype).codRestrict (Ine (F := K) A)
    fun σ => res_mem_Ine σ.2

theorem continuous_resI : Continuous (resI (K := K) (L := L) (Ω := Ω) (A := A)) :=
  ((UpperTheory.V.Af.continuous_restrictScalarsHom K L Ω).comp continuous_subtype_val).subtype_mk _

theorem resW_ineIncl (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (τ : Ine (F := L) A) :
    resW h h' (ineIncl h' τ) = ineIncl h (resI τ) := Subtype.ext rfl

def resRep (h : IsPlaceOver A v) (h' : IsPlaceOver A v') {n : ℕ} (a : WDRep h (Fin n → ℂ)) :
    WDRep h' (Fin n → ℂ) where
  ρ := a.ρ.comp (resW h h')
  N := a.N
  smooth := by
    show IsOpen {τ : Ine (F := L) A | a.ρ (resW h h' (ineIncl h' τ)) = 1}
    simp_rw [resW_ineIncl]
    exact a.smooth.preimage continuous_resI
  semisimple σ := a.semisimple _
  nilpotent := a.nilpotent
  comm σ := by
    have hR := normV_zpow_deg_eq σ (resW h h' σ) (fun z => rfl)
    have hC : ((normV v' : ℕ) : ℂ) ^ deg σ = ((normV v : ℕ) : ℂ) ^ deg (resW h h' σ) := by
      have := congrArg (fun r : ℝ => (r : ℂ)) hR
      push_cast at this
      exact this
    show a.ρ (resW h h' σ) * a.N = _ • (a.N * a.ρ (resW h h' σ))
    rw [hC]
    exact a.comm _

end GlobalTheory.AboveL.ResEx

namespace GlobalTheory.AboveL

end GlobalTheory.AboveL

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDoubleCosetOperatorEqInertHeckeOperator
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDoubleCosetOperatorEqInertHeckeOperator
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertDCOp

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

theorem loc_mul (Dv : InertDatum L n v w) (x y : GAf L n) : Dv.loc (x * y) = Dv.loc x * Dv.loc y :=
  (GlobalTheory.SatInd.CosetFin.locHom Dv).map_mul x y

theorem mem_dc_iff (Dv : InertDatum L n v w) (h1 : ∀ x : GAf L n, Dv.loc x ∈ Formalism.UG.GU Dv.σw n)
    (h2 : ∀ κ : GAf L n, κ ∈ Umax L n → ∀ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n,
      (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n)
    (h3 : ∀ k : GL (Fin n) (w.adicCompletion L), k ∈ Formalism.UG.GU Dv.σw n →
      ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = k)
    (h4 : ∀ x y : GAf L n, TrivOutside {v} x → TrivOutside {v} y → Dv.loc x = Dv.loc y → x = y)
    {a x : GAf L n} (ha : TrivOutside {v} a) (hx : TrivOutside {v} x) :
    (⟨Dv.loc x, h1 x⟩ : Formalism.UG.GU Dv.σw n) ∈ DoubleCoset.doubleCoset (⟨Dv.loc a, h1 a⟩ : Formalism.UG.GU Dv.σw n)
        (Formalism.UG.KU Dv.σw n : Set (Formalism.UG.GU Dv.σw n)) (Formalism.UG.KU Dv.σw n : Set (Formalism.UG.GU Dv.σw n)) ↔
      ∃ k₁ ∈ InertSph.Kv L n v, ∃ k₂ ∈ InertSph.Kv L n v, x = k₁ * a * k₂ := by
  rw [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨k₁, hk₁, k₂, hk₂, e⟩
    obtain ⟨κ₁, t₁, e₁⟩ := h3 k₁.1 k₁.2
    obtain ⟨κ₂, t₂, e₂⟩ := h3 k₂.1 k₂.2
    have u₁ : κ₁ ∈ Umax L n := GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv κ₁ t₁
      (fun i j => by rw [e₁]; exact GlobalTheory.SatInd.CosetFin.entries_int hk₁ i j)
    have u₂ : κ₂ ∈ Umax L n := GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv κ₂ t₂
      (fun i j => by rw [e₂]; exact GlobalTheory.SatInd.CosetFin.entries_int hk₂ i j)
    refine ⟨κ₁, ⟨u₁, t₁⟩, κ₂, ⟨u₂, t₂⟩, h4 _ _ hx
      (GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_mul t₁ ha) t₂) ?_⟩
    calc Dv.loc x = k₁.1 * Dv.loc a * k₂.1 := congrArg Subtype.val e
      _ = Dv.loc κ₁ * Dv.loc a * Dv.loc κ₂ := by rw [e₁, e₂]
      _ = Dv.loc (κ₁ * a * κ₂) := by rw [loc_mul, loc_mul]
  · rintro ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    refine ⟨⟨Dv.loc k₁, h1 k₁⟩, h2 k₁ hk₁.1 (h1 k₁), ⟨Dv.loc k₂, h1 k₂⟩,
      h2 k₂ hk₂.1 (h1 k₂), ?_⟩
    apply Subtype.ext
    show Dv.loc (k₁ * a * k₂) = Dv.loc k₁ * Dv.loc a * Dv.loc k₂
    rw [loc_mul, loc_mul]

end GlobalTheory.InertDCOp

namespace GlobalTheory.InertDCOp

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

theorem exists_reps (Dv : InertDatum L n v w) (h1 : ∀ x : GAf L n, Dv.loc x ∈ Formalism.UG.GU Dv.σw n)
    (h2 : ∀ κ : GAf L n, κ ∈ Umax L n → ∀ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n,
      (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n)
    {a : GAf L n} (ha : TrivOutside {v} a) :
    ∃ R : Finset (GAf L n), GlobalTheory.SphLabelOps.Reps (InertSph.Kv L n v) a R := by
  classical
  set K := InertSph.Kv L n v
  let p : GAf L n → Prop := fun x => ∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * a * k₂
  have tp : ∀ x, p x → TrivOutside {v} x := by
    rintro _ ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    exact GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_mul hk₁.2 ha) hk₂.2
  have hfin : Set.Finite {c : GAf L n ⧸ K | ∃ x : GAf L n, (x : GAf L n ⧸ K) = c ∧ p x} := by
    refine GlobalTheory.SatInd.CosetFin.finite_cosets (GlobalTheory.SatInd.CosetFin.locHom Dv) (Formalism.UG.GU Dv.σw n)
      (Formalism.UG.KU Dv.σw n) K p _
      (GlobalTheory.SatInd.DCoset.finite_dcoset Dv.ϖ Dv.σw _ n Dv.unram ⟨Dv.loc a, h1 a⟩) ?_ ?_
    · rintro x ⟨k₁, hk₁, k₂, hk₂, rfl⟩
      refine ⟨h1 _, ⟨Dv.loc k₁, h1 k₁⟩, h2 k₁ hk₁.1 (h1 k₁), ?_⟩
      have e : (⟨GlobalTheory.SatInd.CosetFin.locHom Dv (k₁ * a * k₂), h1 _⟩ : Formalism.UG.GU Dv.σw n) =
          (⟨Dv.loc k₁, h1 k₁⟩ * ⟨Dv.loc a, h1 a⟩ : Formalism.UG.GU Dv.σw n) * ⟨Dv.loc k₂, h1 k₂⟩ := by
        apply Subtype.ext
        show Dv.loc (k₁ * a * k₂) = Dv.loc k₁ * Dv.loc a * Dv.loc k₂
        rw [loc_mul, loc_mul]
      rw [e]
      exact (QuotientGroup.mk_mul_of_mem _ (h2 k₂ hk₂.1 (h1 k₂))).symm
    · intro x y hx hy hz hk
      have ht : TrivOutside {v} (x⁻¹ * y) :=
        GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_inv (tp x hx)) (tp y hy)
      exact ⟨GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv _ ht
        (fun i j => GlobalTheory.SatInd.CosetFin.entries_int hk i j), ht⟩
  refine ⟨hfin.toFinset.image (fun c => c.out), ?_, ?_⟩
  · intro γ hγ
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hγ
    obtain ⟨x, hxc, k₁, hk₁, k₂, hk₂, rfl⟩ := (Set.Finite.mem_toFinset hfin).1 hc
    have hm : (k₁ * a * k₂)⁻¹ * c.out ∈ K := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq', hxc]
    exact ⟨k₁, hk₁, k₂ * ((k₁ * a * k₂)⁻¹ * c.out), mul_mem hk₂ hm, by group⟩
  · intro x hx
    have hc : (x : GAf L n ⧸ K) ∈ hfin.toFinset := (Set.Finite.mem_toFinset hfin).2 ⟨x, rfl, hx⟩
    refine ⟨(x : GAf L n ⧸ K).out, ⟨Finset.mem_image_of_mem _ hc, ?_⟩, ?_⟩
    · rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    · rintro γ ⟨hγ, hγx⟩
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hγ
      have : c = (x : GAf L n ⧸ K) := by
        rw [← QuotientGroup.out_eq' c]
        exact QuotientGroup.eq.2 hγx
      rw [this]

end GlobalTheory.InertDCOp

namespace GlobalTheory.InertDCOp

theorem dcOp_eq_heckeFunI : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), (∀ x : GAf L n, Dv.loc x ∈ Formalism.UG.GU Dv.σw n) → (∀ κ : GAf L n, κ ∈ Umax L n → ∀ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n, (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n) → (∀ k : GL (Fin n) (w.adicCompletion L), k ∈ Formalism.UG.GU Dv.σw n → ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = k) → (∀ x y : GAf L n, TrivOutside {v} x → TrivOutside {v} y → Dv.loc x = Dv.loc y → x = y) → ∀ a : GAf L n, TrivOutside {v} a → ∃ (R : Finset (GAf L n)) (ha : Formalism.UG.GU Dv.σw n → ℂ), GlobalTheory.SphLabelOps.Reps (GlobalTheory.InertSph.Kv L n v) a R ∧ ha ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) ∧ ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (φ : GAf L n → W), (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ φ = φ) → ∑ γ ∈ R, NG.rt L n γ φ = heckeFunI L n (Umax L n) Dv ha φ := by
  intro L _ _ _ n v w Dv h1 h2 h3 h4 a ha
  classical
  set K := InertSph.Kv L n v
  obtain ⟨R, hR⟩ := exists_reps Dv h1 h2 ha
  have tR : ∀ γ ∈ R, TrivOutside {v} γ := by
    intro γ hγ
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hR.1 γ hγ
    exact GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_mul hk₁.2 ha) hk₂.2
  refine ⟨R, Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) ⟨Dv.loc a, h1 a⟩, hR,
    Formalism.UG.P.double_coset_indicator_mem _ _ _ _, fun W _ _ φ hφ => ?_⟩

  have hv1 : ∀ x : GAf L n, TrivOutside {v} x → (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * a * k₂) →
      Dv.hval (Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) ⟨Dv.loc a, h1 a⟩) (Dv.loc x) = 1 := by
    intro x hx hp
    unfold Formalism.AUTREP.InertDatum.hval
    rw [dite_eq_left (h1 x)]
    exact Formalism.UG.P.dosetInd_of_mem ℂ _ _ _ ((mem_dc_iff Dv h1 h2 h3 h4 ha hx).2 hp)
  have hv0 : ∀ x : GAf L n, TrivOutside {v} x →
      Dv.hval (Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) ⟨Dv.loc a, h1 a⟩) (Dv.loc x) ≠ 0 →
      ∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * a * k₂ := by
    intro x hx h0
    unfold Formalism.AUTREP.InertDatum.hval at h0
    rw [dite_eq_left (h1 x)] at h0
    refine (mem_dc_iff Dv h1 h2 h3 h4 ha hx).1 ?_
    by_contra hn
    exact h0 (Formalism.UG.P.dosetInd_of_not_mem ℂ _ _ _ hn)
  funext g
  rw [Finset.sum_apply]
  unfold heckeFunI
  rw [finsum_eq_sum_of_support_subset (s := R.image (QuotientGroup.mk : GAf L n → GAf L n ⧸ Umax L n))]
  · rw [Finset.sum_image]
    · refine Finset.sum_congr rfl fun γ hγ => ?_
      have hc : ∃ x : GAf L n, (x : GAf L n ⧸ Umax L n) = (γ : GAf L n ⧸ Umax L n) ∧ TrivOutside {v} x :=
        ⟨γ, rfl, tR γ hγ⟩
      rw [dite_eq_left hc]
      obtain ⟨e, hxt⟩ := hc.choose_spec
      have hU : γ⁻¹ * hc.choose ∈ Umax L n := QuotientGroup.eq.1 e.symm
      have hT : TrivOutside {v} (γ⁻¹ * hc.choose) :=
        GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_inv (tR γ hγ)) hxt
      have hp : ∃ k₁ ∈ K, ∃ k₂ ∈ K, hc.choose = k₁ * a * k₂ := by
        obtain ⟨k₁, hk₁, k₂, hk₂, e'⟩ := hR.1 γ hγ
        exact ⟨k₁, hk₁, k₂ * (γ⁻¹ * hc.choose), mul_mem hk₂ ⟨hU, hT⟩, by rw [← mul_assoc, ← e']; group⟩
      rw [hv1 _ hxt hp, one_smul]
      have := congrFun (hφ _ hU hT) (g * γ)
      show φ (g * γ) = φ (g * hc.choose)
      rw [← this]
      show φ (g * γ * (γ⁻¹ * hc.choose)) = φ (g * hc.choose)
      group
    · intro γ hγ γ' hγ' e
      have hU : γ⁻¹ * γ' ∈ Umax L n := QuotientGroup.eq.1 e
      have hT : TrivOutside {v} (γ⁻¹ * γ') :=
        GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_inv (tR γ hγ)) (tR γ' hγ')
      exact (hR.2 γ' (hR.1 γ' hγ')).unique ⟨hγ, hU, hT⟩ ⟨hγ', by rw [inv_mul_cancel]; exact one_mem _⟩
  · intro c hc0
    rw [Function.mem_support] at hc0
    by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ Umax L n) = c ∧ TrivOutside {v} x
    · rw [dite_eq_left hc] at hc0
      obtain ⟨e, hxt⟩ := hc.choose_spec
      have h0 : Dv.hval (Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) ⟨Dv.loc a, h1 a⟩) (Dv.loc hc.choose) ≠ 0 := by
        intro h0; rw [h0, zero_smul] at hc0; exact hc0 rfl
      obtain ⟨γ, ⟨hγ, hγx⟩, -⟩ := hR.2 _ (hv0 _ hxt h0)
      rw [Finset.coe_image]
      refine ⟨γ, hγ, ?_⟩
      show (γ : GAf L n ⧸ Umax L n) = c
      rw [← e]
      exact QuotientGroup.eq.2 hγx.1
    · exact absurd (dif_neg hc) hc0

end GlobalTheory.InertDCOp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDoubleCosetOperatorEqInertHeckeOperatorStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertDoubleCosetOperator_eq_inertHeckeOperator : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), (∀ x : GAf L n, Dv.loc x ∈ Formalism.UG.GU Dv.σw n) → (∀ κ : GAf L n, κ ∈ Umax L n → ∀ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n, (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n) → (∀ k : GL (Fin n) (w.adicCompletion L), k ∈ Formalism.UG.GU Dv.σw n → ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = k) → (∀ x y : GAf L n, TrivOutside {v} x → TrivOutside {v} y → Dv.loc x = Dv.loc y → x = y) → ∀ a : GAf L n, TrivOutside {v} a → ∃ (R : Finset (GAf L n)) (ha : Formalism.UG.GU Dv.σw n → ℂ), GlobalTheory.SphLabelOps.Reps (GlobalTheory.InertSph.Kv L n v) a R ∧ ha ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) ∧ ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (φ : GAf L n → W), (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ φ = φ) → ∑ γ ∈ R, NG.rt L n γ φ = heckeFunI L n (Umax L n) Dv ha φ := by
  first | exact @GlobalTheory.InertDCOp.dcOp_eq_heckeFunI | exact GlobalTheory.InertDCOp.dcOp_eq_heckeFunI | (intros; apply GlobalTheory.InertDCOp.dcOp_eq_heckeFunI <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTrivOutsideInertDatumLocalEq
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTrivOutsideInertDatumLocalEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open TensorProduct

namespace GlobalTheory.InertLift

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

def sglL (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    v.adicCompletion (maximalRealSubfield L) →ₗ[maximalRealSubfield L] AFplus L where
  toFun := GlobalTheory.InertUmax.sgl L v
  map_add' a b := (GlobalTheory.SplitLift.sgl_add v a b).symm
  map_smul' c r := by
    simp only [RingHom.id_apply, Algebra.smul_def]
    exact (GlobalTheory.SplitLift.alg_mul_sgl v c r).symm

def lift (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →ₗ[maximalRealSubfield L] AL L :=
  TensorProduct.map LinearMap.id (sglL v)

theorem lift_tmul (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (a : L)
    (r : v.adicCompletion (maximalRealSubfield L)) :
    lift v (a ⊗ₜ r) = a ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L v r := rfl

theorem lift_mul (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (x y : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :
    lift v (x * y) = lift v x * lift v y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a r =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b s =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, lift_tmul, lift_tmul, lift_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.SplitLift.sgl_mul]
    | add y y' hy hy' => rw [mul_add, map_add (f := _), hy, hy', map_add (f := _), mul_add]
  | add x x' hx hx' => rw [add_mul, map_add (f := _), hx, hx', map_add (f := _), add_mul]

theorem compAt_lift_same (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (x : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :
    ReciprocityTheory.Aut.compAt L v (lift v x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a r => rw [lift_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same]
  | add x x' hx hx' => rw [map_add (f := _), map_add (f := _), hx, hx']

theorem compAt_lift_ne (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    {u : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (hu : u ≠ v)
    (x : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :
    ReciprocityTheory.Aut.compAt L u (lift v x) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a r => rw [lift_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L v r hu, tmul_zero]
  | add x x' hx hx' => rw [map_add (f := _), map_add (f := _), hx, hx', add_zero]

theorem conj_lift (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (x : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :
    conjAL L (lift v x) =
      lift v (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L)) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a r =>
    rw [lift_tmul, GlobalTheory.SplitLift.conjAL_tmul]
    simp [Formalism.UG.sigR, Algebra.TensorProduct.map_tmul, lift_tmul]
  | add x x' hx hx' => rw [map_add (f := _), map_add (f := _), hx, hx', map_add (f := _), map_add (f := _)]

def idem (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : AL L := lift v 1

theorem lift_mul_idem (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (x : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :
    lift v x * idem v = lift v x := by
  rw [idem, ← lift_mul, mul_one]

end GlobalTheory.InertLift

namespace GlobalTheory.InertLift

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem idem_mul_idem (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : idem v * idem v = (idem v : AL L) :=
  lift_mul_idem v 1

def glue (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) × AL L →+* AL L where
  toFun q := lift v q.1 + (1 - idem v) * q.2
  map_one' := by simp only [Prod.fst_one, Prod.snd_one, mul_one]; rw [← idem]; ring
  map_mul' q q' := by
    simp only [Prod.fst_mul, Prod.snd_mul, lift_mul]
    have h1 := lift_mul_idem v q.1
    have h2 := lift_mul_idem v q'.1
    have h3 := idem_mul_idem v
    linear_combination q'.2 * h1 + q.2 * h2 - (q.2 * q'.2) * h3
  map_zero' := by simp
  map_add' q q' := by simp only [Prod.fst_add, Prod.snd_add, map_add (f := _)]; ring

theorem glue_apply (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (q : (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) × AL L) :
    glue v q = lift v q.1 + (1 - idem v) * q.2 := rfl

theorem compAt_glue_same (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (q : (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) × AL L) :
    ReciprocityTheory.Aut.compAt L v (glue v q) = q.1 := by
  rw [glue_apply, map_add (f := _), map_mul, map_sub, map_one, idem, compAt_lift_same, compAt_lift_same]; ring

theorem compAt_glue_ne (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    {u : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (hu : u ≠ v)
    (q : (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) × AL L) :
    ReciprocityTheory.Aut.compAt L u (glue v q) = ReciprocityTheory.Aut.compAt L u q.2 := by
  rw [glue_apply, map_add (f := _), map_mul, map_sub, map_one, idem, compAt_lift_ne v hu, compAt_lift_ne v hu]; ring

theorem conj_glue (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (q : (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) × AL L) :
    conjAL L (glue v q) = glue v
      (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L)) q.1,
        conjAL L q.2) := by
  rw [glue_apply, glue_apply, map_add (f := _), map_mul, map_sub, map_one, idem, conj_lift, conj_lift, map_one]

theorem matrix_pair_ext {n : ℕ} {R₁ R₂ : Type*} (A B : Matrix (Fin n) (Fin n) (R₁ × R₂))
    (h₁ : A.map Prod.fst = B.map Prod.fst) (h₂ : A.map Prod.snd = B.map Prod.snd) : A = B :=
  Matrix.ext fun i j => Prod.ext (congrFun (congrFun h₁ i) j) (congrFun (congrFun h₂ i) j)

end GlobalTheory.InertLift

namespace GlobalTheory.InertLift

theorem exists_trivOutside_loc_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w)
    (k : GL (Fin n) (w.adicCompletion L)), k ∈ Formalism.UG.GU Dv.σw n →
      ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = k := by
  intro L _ _ _ n v w Dv k hk
  have hk' : Formalism.UG.cT Dv.σw (k : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
      Formalism.UG.antiJ (w.adicCompletion L) n * (k : Matrix (Fin n) (Fin n) (w.adicCompletion L)) =
      Formalism.UG.antiJ (w.adicCompletion L) n := hk
  set Pm : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) with hPm
  set Pi : Matrix (Fin n) (Fin n) (w.adicCompletion L) := ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L))
    with hPi
  set km : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (k : Matrix (Fin n) (Fin n) (w.adicCompletion L)) with hkm
  set m : Matrix (Fin n) (Fin n) (w.adicCompletion L) := Pm * km * Pi with hm
  have hPP : Pm * Pi = 1 := by rw [hPm, hPi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have key : Formalism.UG.cT Dv.σw m * m = 1 := by
    calc Formalism.UG.cT Dv.σw m * m
        = Formalism.UG.cT Dv.σw Pi * ((Formalism.UG.cT Dv.σw km * (Formalism.UG.cT Dv.σw Pm * Pm) * km) * Pi) := by
          simp only [hm, Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = Formalism.UG.cT Dv.σw Pi * ((Formalism.UG.cT Dv.σw Pm * Pm) * Pi) := by rw [Dv.Panti, hk']
      _ = Formalism.UG.cT Dv.σw (Pm * Pi) * (Pm * Pi) := by simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hPP, Formalism.UG.cT_one, Matrix.one_mul]
  have hm1 : m * Formalism.UG.cT Dv.σw m = 1 := mul_eq_one_comm.mp key
  set sig := Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L)) with hsig
  set eR : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L :=
    (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L) with heR
  let M : Matrix (Fin n) (Fin n) (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :=
    m.map Dv.e.symm
  have hMe : M.map eR = m := by
    ext i j; simp [M, heR]
  have hM : M * conjT sig M = 1 := by
    apply Matrix.map_injective (f := eR) Dv.e.injective
    show (M * conjT sig M).map eR = (1 : Matrix (Fin n) (Fin n) _).map eR
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    have hc : (conjT sig M).map eR = Formalism.UG.cT Dv.σw (M.map eR) := by
      refine Matrix.ext fun i j => ?_
      show eR (sig (M j i)) = Dv.σw (eR (M j i))
      exact Dv.comm _
    rw [hc, hMe, hm1]
  let Z : Matrix (Fin n) (Fin n)
      ((L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) × AL L) :=
    fun i j => (M i j, (1 : Matrix (Fin n) (Fin n) (AL L)) i j)
  let W : Matrix (Fin n) (Fin n)
      ((L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) × AL L) :=
    fun i j => (conjT sig M i j, (1 : Matrix (Fin n) (Fin n) (AL L)) i j)
  have hZW : Z * W = 1 := by
    apply matrix_pair_ext
    · have e := Matrix.map_mul (L := Z) (M := W)
        (f := RingHom.fst (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) (AL L))
      refine e.trans ?_
      rw [Matrix.map_one _ rfl rfl]
      exact hM
    · have e := Matrix.map_mul (L := Z) (M := W)
        (f := RingHom.snd (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) (AL L))
      refine e.trans ?_
      rw [Matrix.map_one _ rfl rfl]
      exact Matrix.mul_one _
  let X : Matrix (Fin n) (Fin n) (AL L) := Z.map (glue v)
  have hconj : conjT (conjAL L) X = W.map (glue v) := by
    refine Matrix.ext fun i j => ?_
    simp only [conjT, X, Matrix.transpose_apply, Matrix.map_apply]
    rw [conj_glue]
    congr 1
    refine Prod.ext rfl ?_
    simp only [Z, W, Matrix.one_apply, eq_comm]
    split_ifs <;> simp
  have hX : X * conjT (conjAL L) X = 1 := by
    rw [hconj]
    show Z.map (glue v) * W.map (glue v) = 1
    rw [← Matrix.map_mul, hZW, Matrix.map_one _ (map_zero _) (map_one _)]
  let g : GL (Fin n) (AL L) := ⟨X, conjT (conjAL L) X, hX, mul_eq_one_comm.mp hX⟩
  refine ⟨⟨g, hX⟩, ?_, ?_⟩
  · intro u hu
    have hu' : u ≠ v := hu
    refine Matrix.ext fun i j => ?_
    change ReciprocityTheory.Aut.compAt L u (glue v (Z i j)) = (1 : Matrix (Fin n) (Fin n) _) i j
    rw [compAt_glue_ne v hu']
    simp only [Z, Matrix.one_apply]
    split_ifs <;> simp
  · have hb : Formalism.UG.bc (n := Fin n) eR
        (Matrix.GeneralLinearGroup.map (ReciprocityTheory.Aut.compAt L v) g) = Dv.P * k * Dv.P⁻¹ := by
      refine Units.ext (Matrix.ext fun i j => ?_)
      change eR (ReciprocityTheory.Aut.compAt L v (glue v (Z i j))) = m i j
      rw [compAt_glue_same]
      simp [Z, M, heR]
    show Dv.P⁻¹ * Formalism.UG.bc (n := Fin n) eR (Matrix.GeneralLinearGroup.map (ReciprocityTheory.Aut.compAt L v) g) * Dv.P = k
    rw [hb]; group

end GlobalTheory.InertLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTrivOutsideInertDatumLocalEqStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trivOutside_inertDatum_local_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (k : GL (Fin n) (w.adicCompletion L)), k ∈ Formalism.UG.GU Dv.σw n → ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = k := by
  first | exact @GlobalTheory.InertLift.exists_trivOutside_loc_eq | exact GlobalTheory.InertLift.exists_trivOutside_loc_eq | (intros; apply GlobalTheory.InertLift.exists_trivOutside_loc_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelJetsOfTranslateJets
noncomputable section

namespace GlobalTheory.LiftTypePrime.Jets

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions GlobalTheory.GalTheta

section Integral

theorem norm_le_one_of_isIntegral {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : @IsIntegral ℤ C _ _ (Ring.toIntAlgebra C) x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

variable {p : ℕ} [Fact p.Prime] {lam : Qbar →+* ℂ_[p]}

theorem intAt_iff {x : ℂ} : IntAt lam x ↔ ∃ h : x ∈ Qbar, ‖lam ⟨x, h⟩‖ ≤ 1 := by
  unfold IntAt lamC
  exact ⟨fun ⟨h, h1⟩ => ⟨h, by rwa [dite_eq_left h] at h1⟩, fun ⟨h, h1⟩ => ⟨h, by rwa [dite_eq_left h]⟩⟩

theorem intAt_mul {x y : ℂ} (hx : IntAt lam x) (hy : IntAt lam y) : IntAt lam (x * y) := by
  obtain ⟨h, h1⟩ := intAt_iff.1 hx
  obtain ⟨h', h2⟩ := intAt_iff.1 hy
  refine intAt_iff.2 ⟨mul_mem h h', ?_⟩
  change ‖lam (⟨x, h⟩ * ⟨y, h'⟩)‖ ≤ 1
  rw [map_mul, norm_mul]
  exact mul_le_one₀ h1 (norm_nonneg _) h2

theorem intAt_add {x y : ℂ} (hx : IntAt lam x) (hy : IntAt lam y) : IntAt lam (x + y) := by
  obtain ⟨h, h1⟩ := intAt_iff.1 hx
  obtain ⟨h', h2⟩ := intAt_iff.1 hy
  refine intAt_iff.2 ⟨add_mem h h', ?_⟩
  change ‖lam (⟨x, h⟩ + ⟨y, h'⟩)‖ ≤ 1
  rw [map_add (f := _)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

theorem intAt_of_isIntegral {x : ℂ} (hx : IsIntegral ℤ x) : IntAt lam x := by
  have h : x ∈ Qbar := mem_algebraicClosure_iff'.2 hx.tower_top
  refine intAt_iff.2 ⟨h, ?_⟩
  have h1 : IsIntegral ℤ (⟨x, h⟩ : Qbar) :=
    (isIntegral_algHom_iff ((algebraMap Qbar ℂ).toIntAlgHom) Subtype.val_injective).1 hx
  exact norm_le_one_of_isIntegral (map_isIntegral_int lam h1)

theorem intAt_sum {ι : Type} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, IntAt lam (f i)) : IntAt lam (∑ i ∈ s, f i) :=
  Finset.sum_induction f (IntAt lam) (fun _ _ => intAt_add) (intAt_of_isIntegral isIntegral_zero) h

end Integral

theorem isIntegral_exp (k : ℤ) (x : ℝ) (n : ℕ) (hn : 0 < n) (m : ℤ) (h : (n : ℝ) * x = m) :
    IsIntegral ℤ (Complex.exp ((k : ℂ) * ((Real.pi : ℂ) * Complex.I) * (x : ℂ))) := by
  have h' : (n : ℂ) * (x : ℂ) = m := by exact_mod_cast h
  refine IsIntegral.of_pow (n := 2 * n) (by omega) ?_
  rw [← Complex.exp_nat_mul]
  have : ((2 * n : ℕ) : ℂ) * ((k : ℂ) * ((Real.pi : ℂ) * Complex.I) * (x : ℂ)) =
      ((k * m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    linear_combination (2 * (k : ℂ) * ((Real.pi : ℂ) * Complex.I)) * h'
  rw [this, Complex.exp_int_mul_two_pi_mul_I]
  exact isIntegral_one

variable {D : D7} {N N' : ℕ}

theorem taylor_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → VC D N N' → ℂ)
    (hf : ∀ i, Differentiable ℂ (f i)) (α : Mono D N N') :
    TaylorLogMetric.taylor D (fun z => ∑ i ∈ s, c i * f i z) α = ∑ i ∈ s, c i * TaylorLogMetric.taylor D (f i) α := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact GlobalTheory.ThetaConj.taylor_zero D α
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [← ih, ← GlobalTheory.ThetaConj.taylor_mul D _ (hf i)]
    exact GlobalTheory.ThetaConj.taylor_add D ((hf i).const_mul _) (by fun_prop) α

theorem applyAt0_comb {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → VC D N N' → ℂ)
    (hf : ∀ i, Differentiable ℂ (f i)) (P : MvPolynomial (Idx D N N') ℂ) :
    applyAt0 D P (fun z => ∑ i ∈ s, c i * f i z) = ∑ i ∈ s, c i * applyAt0 D P (f i) := by
  unfold applyAt0
  simp only [taylor_sum s c f hf, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun α _ => by ring

end GlobalTheory.LiftTypePrime.Jets

namespace GlobalTheory.LiftTypePrime

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions GlobalTheory.GalTheta Jets

end GlobalTheory.LiftTypePrime

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorLevelIndependent
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorLevelIndependent
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertLevel


open Classical in
theorem finsum_cosets_eq {G W : Type} [Group G] [AddCommMonoid W] (S K U : Subgroup G)
    (hU : ∀ κ ∈ S, (κ ∈ U ↔ κ ∈ K)) (F : G → W)
    (hF : ∀ x ∈ S, ∀ κ ∈ S, κ ∈ K → F (x * κ) = F x) :
    (∑ᶠ c : G ⧸ U, if hc : ∃ x : G, (x : G ⧸ U) = c ∧ x ∈ S then F hc.choose else 0) =
      ∑ᶠ q : S ⧸ (K.subgroupOf S), F ((q.out : S) : G) := by

  have key : ∀ x y : G, x ∈ S → y ∈ S → (x⁻¹ * y ∈ U ↔ x⁻¹ * y ∈ K) := fun x y hx hy =>
    hU _ (S.mul_mem (S.inv_mem hx) hy)
  let ι : S ⧸ (K.subgroupOf S) → G ⧸ U := fun q => (((q.out : S) : G) : G ⧸ U)
  have hinj : Function.Injective ι := by
    intro q q' h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    apply QuotientGroup.eq.2
    rw [Subgroup.mem_subgroupOf]
    have h1 := QuotientGroup.eq.1 h
    have h2 := (key _ _ (q.out).2 (q'.out).2).1 h1
    simpa using h2
  have hsupp : (Function.support fun c : G ⧸ U =>
      if hc : ∃ x : G, (x : G ⧸ U) = c ∧ x ∈ S then F hc.choose else 0) ⊆ Set.range ι := by
    intro c hc
    by_cases hc' : ∃ x : G, (x : G ⧸ U) = c ∧ x ∈ S
    · obtain ⟨x, hxc, hxS⟩ := hc'
      refine ⟨((⟨x, hxS⟩ : S) : S ⧸ (K.subgroupOf S)), ?_⟩
      set q : S ⧸ (K.subgroupOf S) := ((⟨x, hxS⟩ : S) : S ⧸ (K.subgroupOf S))
      have h1 := QuotientGroup.eq.1 (QuotientGroup.out_eq' q)
      rw [Subgroup.mem_subgroupOf] at h1
      have h1' : ((q.out : S) : G)⁻¹ * x ∈ K := by simpa using h1
      rw [← hxc]
      exact QuotientGroup.eq.2 ((key _ _ (q.out).2 hxS).2 h1')
    · exact absurd (dif_neg hc') hc
  have hsum := finsum_mem_inter_support (fun c : G ⧸ U =>
      if hc : ∃ x : G, (x : G ⧸ U) = c ∧ x ∈ S then F hc.choose else 0) (Set.range ι)
  rw [Set.inter_eq_right.2 hsupp, finsum_mem_support, finsum_mem_range hinj] at hsum
  rw [hsum]
  refine finsum_congr fun q => ?_
  have hc : ∃ x : G, (x : G ⧸ U) = ι q ∧ x ∈ S := ⟨((q.out : S) : G), rfl, (q.out).2⟩
  rw [dite_eq_left hc]
  obtain ⟨h1, h2⟩ := hc.choose_spec
  have hm : ((q.out : S) : G)⁻¹ * hc.choose ∈ K :=
    (key _ _ (q.out).2 h2).1 (QuotientGroup.eq.1 h1.symm)
  have e : hc.choose = ((q.out : S) : G) * (((q.out : S) : G)⁻¹ * hc.choose) := by group
  rw [e, hF _ (q.out).2 _ (S.mul_mem (S.inv_mem (q.out).2) h2) hm]

end GlobalTheory.InertLevel

namespace GlobalTheory.InertLevel

theorem heckeFunI_level_indep : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), (∀ κ : GAf L n, κ ∈ Umax L n → TrivOutside {v} κ → ∃ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n, (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n) → ∀ (U U' : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → (∀ κ, TrivOutside {v} κ → (κ ∈ U' ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (h : Formalism.UG.GU Dv.σw n → ℂ), Formalism.UG.IsBiInv (Formalism.UG.KU Dv.σw n) h → ∀ φ : GAf L n → W, (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ φ = φ) → heckeFunI L n U Dv h φ = heckeFunI L n U' Dv h φ := by
  intro L _ _ _ n v w Dv hKU U U' hU hU' W _ _ h hbi φ hφ
  funext g

  let F : GAf L n → W := fun x => Dv.hval h (Dv.loc x) • φ (g * x)
  have hF : ∀ x ∈ GlobalTheory.InertSph.Gv L n v, ∀ κ ∈ GlobalTheory.InertSph.Gv L n v, κ ∈ Umax L n → F (x * κ) = F x := by
    intro x _ κ hκS hκU
    obtain ⟨hκ, hk⟩ := hKU κ hκU hκS
    have hloc : Dv.loc (x * κ) = Dv.loc x * Dv.loc κ := (GlobalTheory.SatInd.CosetFin.locHom Dv).map_mul x κ
    have hφκ : φ (g * x * κ) = φ (g * x) := congrFun (hφ κ hκU hκS) (g * x)
    have hval : Dv.hval h (Dv.loc x * Dv.loc κ) = Dv.hval h (Dv.loc x) := by
      unfold InertDatum.hval
      by_cases hy : Dv.loc x ∈ Formalism.UG.GU Dv.σw n
      · have hyk : Dv.loc x * Dv.loc κ ∈ Formalism.UG.GU Dv.σw n := (Formalism.UG.GU Dv.σw n).mul_mem hy hκ
        rw [dite_eq_left hyk, dite_eq_left hy]
        have e := hbi 1 ⟨⟨Dv.loc κ, hκ⟩, hk⟩ ⟨Dv.loc x, hy⟩
        simp only [OneMemClass.coe_one, one_mul] at e
        exact e
      · have hyk : Dv.loc x * Dv.loc κ ∉ Formalism.UG.GU Dv.σw n := fun hm => hy (by
          simpa using (Formalism.UG.GU Dv.σw n).mul_mem hm ((Formalism.UG.GU Dv.σw n).inv_mem hκ))
        rw [dif_neg hyk, dif_neg hy]
    show Dv.hval h (Dv.loc (x * κ)) • φ (g * (x * κ)) = Dv.hval h (Dv.loc x) • φ (g * x)
    rw [hloc, hval, ← mul_assoc, hφκ]
  have e1 := finsum_cosets_eq (GlobalTheory.InertSph.Gv L n v) (Umax L n) U (fun κ hκ => hU κ hκ) F hF
  have e2 := finsum_cosets_eq (GlobalTheory.InertSph.Gv L n v) (Umax L n) U' (fun κ hκ => hU' κ hκ) F hF
  exact e1.trans e2.symm

end GlobalTheory.InertLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorLevelIndependentStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertHeckeOperator_level_independent : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), (∀ κ : GAf L n, κ ∈ Umax L n → TrivOutside {v} κ → ∃ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n, (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n) → ∀ (U U' : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → (∀ κ, TrivOutside {v} κ → (κ ∈ U' ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (h : Formalism.UG.GU Dv.σw n → ℂ), Formalism.UG.IsBiInv (Formalism.UG.KU Dv.σw n) h → ∀ φ : GAf L n → W, (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ φ = φ) → heckeFunI L n U Dv h φ = heckeFunI L n U' Dv h φ := by
  first | exact @GlobalTheory.InertLevel.heckeFunI_level_indep | exact GlobalTheory.InertLevel.heckeFunI_level_indep | (intros; apply GlobalTheory.InertLevel.heckeFunI_level_indep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamWeightTwistCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgeTateJumpsTwistByDeRhamCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgeTateJumpsTwistByDeRhamCharacter
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.TwistJumpsW
open Formalism.BasicNotions.Loc

theorem jumpsW_twist : ∀ (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (i : D.nd.Loc) (ι : Qbar (D.nd.l i) ≃+* ℂ) (a : ℕ) (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))) (χ : G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i))), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ → Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i χ → ∀ (τ : D.host.E →+* Qbar (D.nd.l i)) (c : ℤ), (∀ w, InducesW D.nd i τ w → W.IsdRW (D.nd.l i) ι ρ w ∧ W.IsdRW (D.nd.l i) ι χ w) → W.jumpsW (D.nd.l i) ι χ τ = {c} → W.jumpsW (D.nd.l i) ι (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) τ = (W.jumpsW (D.nd.l i) ι ρ τ).map (· + c) := by
  intro D T W i ι a ρ χ hρ hχ τ c hdR hc
  let w := PI.CompDegEF.plOf τ
  have hw : w ∈ placesOver D.host.E (D.nd.l i) := PI.CompDegEF.natCast_mem_plIdeal τ
  have hIW : InducesW D.nd i τ w := fun x => Iff.rfl
  obtain ⟨hdρ, hdχ⟩ := hdR w hIW
  have hj : GlobalTheory.Pst.Induces (D.nbr i w hw) := D.nbr_ind i w hw
  obtain ⟨L₁, hL₁, hm₁⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem (D.nd.l i) (G D.host.E D.nd.Om) a ρ hρ
    (D.nbr i w hw).LL
  obtain ⟨L, hL, hm⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem (D.nd.l i) (G D.host.E D.nd.Om) 1 χ hχ L₁
  have hBL : (D.nbr i w hw).LL.1 ≤ L.1 := hL₁.trans hL
  obtain ⟨τ', hτ'⟩ := GlobalTheory.EmbExt.main D (D.nd.l i) w _ (D.nbr i w hw) hj τ hIW L hBL
  obtain ⟨ρ₁, cρ, rfl⟩ := GlobalTheory.DeRhamRead.exists_model_of_mem ρ hρ L (fun g i j => hL (hm₁ g i j))
  obtain ⟨χ₁, cχ, rfl⟩ := GlobalTheory.DeRhamRead.exists_model_of_mem χ hχ L hm
  obtain ⟨-, H⟩ := W.loc (D.nd.l i) ι w hw _ (D.nbr i w hw) hj
    ((algebraMap ↥(D.nbr i w hw).LL.1 (Om (D.nd.l i))).comp (D.nbr i w hw).toLL) (fun _ => rfl)
  let tw₁ : G D.host.E D.nd.Om →* GL (Fin a) ↥L.1 := GlobalTheory.TwistAbove.twGL (Matrix.GeneralLinearGroup.det.comp χ₁) ρ₁
  have htw : Formalism.MainNotions.SumRepresentations.At.twGL (mapRep (algebraMap ↥L.1 (Qbar (D.nd.l i))) ρ₁)
      (Matrix.GeneralLinearGroup.det.comp (mapRep (algebraMap ↥L.1 (Qbar (D.nd.l i))) χ₁)) =
      mapRep (algebraMap ↥L.1 (Qbar (D.nd.l i))) tw₁ := by
    refine MonoidHom.ext fun g => Units.ext ?_
    ext p q
    simp [tw₁, mapRep, Formalism.MainNotions.SumRepresentations.At.twGL, Matrix.det_unique, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_mul]
  have ctw : Continuous (fun g => ((tw₁ g : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1)) := by
    have h1 : Continuous (fun g => ((χ₁ g : GL (Fin 1) ↥L.1) : Matrix (Fin 1) (Fin 1) ↥L.1).det) := cχ.matrix_det
    refine continuous_matrix fun p q => ?_
    refine (h1.mul (cρ.matrix_elem p q)).congr fun g => ?_
    simp [tw₁, GlobalTheory.TwistAbove.twGL_val, Matrix.GeneralLinearGroup.val_det_apply]
  rw [htw]
  have Hρ := H L hBL a ρ₁ cρ
  have Hχ := H L hBL 1 χ₁ cχ
  have Htw := H L hBL a tw₁ ctw
  have dρ := Hρ.2.1.1 hdρ
  have dχ := Hχ.2.1.1 hdχ
  have hcom := GlobalTheory.TwistAbove.twist_common (D.nbr i w hw) (ρ₁.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype)
    (χ₁.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) (D.locT (D.nd.l i))
  have dtw : (D.nbr i w hw).IsdRE (D.loc (D.nd.l i)) L (tw₁.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) :=
    hcom.1 dρ dχ
  have mχ : ∀ n, (D.nbr i w hw).multE (D.loc (D.nd.l i)) L (χ₁.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) τ' n =
      if n = c then 1 else 0 := by
    intro n
    rw [← (Hχ.2.2.2 τ τ' hτ').2 dχ n, hc, Multiset.count_singleton]
    split_ifs <;> simp
  ext n
  have e1 := (Htw.2.2.2 τ τ' hτ').2 dtw n
  have e2 := hcom.2.2.2 τ' c dχ mχ (n - c)
  have e3 := (Hρ.2.2.2 τ τ' hτ').2 dρ (n - c)
  have e4 := Multiset.count_map_eq_count' (fun x : ℤ => x + c) (W.jumpsW (D.nd.l i) ι (mapRep (algebraMap ↥L.1 (Qbar (D.nd.l i))) ρ₁) τ)
    (add_left_injective c) (n - c)
  simp only [sub_add_cancel] at e2 e4
  rw [e4]
  exact_mod_cast e1.trans (e2.trans e3.symm)

end GlobalTheory.TwistJumpsW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgeTateJumpsTwistByDeRhamCharacterStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTateJumps_twist_by_deRham_character : ∀ (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (i : D.nd.Loc) (ι : Qbar (D.nd.l i) ≃+* ℂ) (a : ℕ) (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))) (χ : G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i))), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ → Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i χ → ∀ (τ : D.host.E →+* Qbar (D.nd.l i)) (c : ℤ), (∀ w, InducesW D.nd i τ w → W.IsdRW (D.nd.l i) ι ρ w ∧ W.IsdRW (D.nd.l i) ι χ w) → W.jumpsW (D.nd.l i) ι χ τ = {c} → W.jumpsW (D.nd.l i) ι (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) τ = (W.jumpsW (D.nd.l i) ι ρ τ).map (· + c) := by
  exact GlobalTheory.TwistJumpsW.jumpsW_twist
end
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TwistGal

theorem twGL_coe {Γ k : Type} [Group Γ] [CommRing k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (χ : Γ →* kˣ) (g : Γ) :
    ((Formalism.MainNotions.SumRepresentations.At.twGL ρ χ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
      ((χ g : kˣ) : k) • (ρ g : Matrix (Fin a) (Fin a) k) := by
  rw [Algebra.smul_def]
  rfl

theorem cont_twGL {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [CommRing k] [TopologicalSpace k] [IsTopologicalRing k] {a : ℕ}
    (ρ : Γ →* GL (Fin a) k) (χ : Γ →* GL (Fin 1) k)
    (hρ : Continuous fun g => ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (hχ : Continuous fun g => ((χ g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k)) :
    Continuous fun g => ((Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ) g : GL (Fin a) k) :
      Matrix (Fin a) (Fin a) k) := by
  simp only [twGL_coe]
  refine Continuous.smul (M := k) ?_ hρ
  exact hχ.matrix_det

theorem comp_twGL {Γ Γ' k : Type} [Group Γ] [Group Γ'] [CommRing k] {a : ℕ} (ρ : Γ →* GL (Fin a) k)
    (χ : Γ →* GL (Fin 1) k) (f : Γ' →* Γ) :
    (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)).comp f =
      Formalism.MainNotions.SumRepresentations.At.twGL (ρ.comp f) (Matrix.GeneralLinearGroup.det.comp (χ.comp f)) :=
  MonoidHom.ext fun _ => rfl

end GlobalTheory.TwistGal

end
end
