module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ScalarOfCommute
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasCharSub
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsIsoOfHighest
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ContinuousUnitsRenSymm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqIntIrrPerm

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsWeightOfIntertwine
noncomputable section

namespace GlobalTheory.CompanionTheory.RgIso

open _root_.CompanionTheory.RgExh
open Formalism.REAL (GlRel qdet qminor Tm KHighest IsWeight)
open CompanionTheory.D.LK (LocFin IsMin)
open CompanionTheory.D.DSIC (KStab)

variable {n : ℕ}

theorem iso_refl (X : GMod n) : Iso X X := by
  exact ⟨LinearEquiv.refl ℂ X.V, fun a b x => rfl⟩

theorem intertwine_symm {X Y : GMod n} (e : X.V ≃ₗ[ℂ] Y.V) (he : ∀ a b x, e (X.E a b x) = Y.E a b (e x))
    (a b : Fin n) (y : Y.V) : e.symm (Y.E a b y) = X.E a b (e.symm y) := by
  apply e.injective
  rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]

theorem iso_symm {X Y : GMod n} : Iso X Y → Iso Y X := by
  rintro ⟨e, he⟩
  exact ⟨e.symm, intertwine_symm e he⟩

theorem iso_trans {X Y Z : GMod n} : Iso X Y → Iso Y Z → Iso X Z := by
  rintro ⟨e, he⟩ ⟨f, hf⟩
  exact ⟨e.trans f, fun a b x => by rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, he, hf]⟩

def cj {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W) :
    Module.End ℂ V →+* Module.End ℂ W where
  toFun f := e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap
  map_one' := by ext; simp
  map_mul' f g := by ext; simp
  map_zero' := by ext; simp
  map_add' f g := by ext; simp

theorem cj_apply {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)
    (f : Module.End ℂ V) (w : W) : cj e f w = e (f (e.symm w)) := rfl

theorem cj_smul_one {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)
    (c : ℂ) : cj e (c • (1 : Module.End ℂ V)) = c • (1 : Module.End ℂ W) := by
  refine LinearMap.ext fun w => ?_
  rw [cj_apply]
  simp

theorem cj_algebraMap {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)
    (c : ℂ) : cj e (algebraMap ℂ (Module.End ℂ V) c) = algebraMap ℂ (Module.End ℂ W) c := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, cj_smul_one]

theorem cj_E {X Y : GMod n} (e : X.V ≃ₗ[ℂ] Y.V) (he : ∀ a b x, e (X.E a b x) = Y.E a b (e x)) (a b : Fin n) :
    cj e (X.E a b) = Y.E a b := by
  refine LinearMap.ext fun w => ?_
  rw [cj_apply, he, LinearEquiv.apply_symm_apply]

theorem cj_Tm {X Y : GMod n} (e : X.V ≃ₗ[ℂ] Y.V) (he : ∀ a b x, e (X.E a b x) = Y.E a b (e x)) (u : ℂ)
    (a b : Fin n) : cj e (Tm X.E u a b) = Tm Y.E u a b := by
  unfold Formalism.REAL.Tm
  rw [map_add (f := _), cj_E e he]
  split_ifs
  · rw [cj_algebraMap]
  · rw [map_zero]

theorem cj_qdet {X Y : GMod n} (e : X.V ≃ₗ[ℂ] Y.V) (he : ∀ a b x, e (X.E a b x) = Y.E a b (e x)) (u : ℂ) :
    cj e (qdet X.E u) = qdet Y.E u := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn, Function.comp_def, cj_Tm e he]

theorem scalChar_of_iso {X Y : GMod n} (h : Iso X Y) (χ : Fin n → ℂ) (hX : ScalChar X χ) : ScalChar Y χ := by
  obtain ⟨e, he⟩ := h
  intro t
  rw [← cj_qdet e he, hX t, cj_smul_one]

theorem hasChar_of_iso {X Y : GMod n} (h : Iso X Y) (χ : Fin n → ℂ) (hX : HasChar X χ) : HasChar Y χ := by
  obtain ⟨e, he⟩ := h
  obtain ⟨k, hk⟩ := hX
  refine ⟨k, fun t => ?_⟩
  rw [← cj_qdet e he, ← cj_smul_one e, ← map_sub, ← map_pow, hk t, map_zero]

theorem isSimple_of_iso {X Y : GMod n} (h : Iso X Y) (hX : IsSimple X) : IsSimple Y := by
  obtain ⟨e, he⟩ := h
  refine ⟨?_, fun S hS => ?_⟩
  · haveI := hX.1
    exact e.symm.toEquiv.nontrivial
  · have hS' : ∀ a b, ∀ x ∈ S.comap (e : X.V →ₗ[ℂ] Y.V), X.E a b x ∈ S.comap (e : X.V →ₗ[ℂ] Y.V) := by
      intro a b x hx
      simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hx ⊢
      rw [he]
      exact hS a b _ hx
    rcases hX.2 _ hS' with h0 | h1
    · left
      rw [eq_bot_iff]
      intro y hy
      rw [Submodule.mem_bot]
      have hy' : e.symm y ∈ S.comap (e : X.V →ₗ[ℂ] Y.V) := by simpa using hy
      rw [h0, Submodule.mem_bot] at hy'
      simpa using hy'
    · right
      rw [eq_top_iff]
      intro y _
      have hy' : e.symm y ∈ S.comap (e : X.V →ₗ[ℂ] Y.V) := by
        rw [h1]
        trivial
      simpa using hy'

theorem locFin_of_iso {X Y : GMod n} (ε : Fin n → Bool) (h : Iso X Y) (hX : LocFin ε X.E) : LocFin ε Y.E := by
  obtain ⟨e, he⟩ := h
  intro y
  obtain ⟨S, hfd, hst, hx⟩ := hX (e.symm y)
  refine ⟨S.map (e : X.V →ₗ[ℂ] Y.V), ?_, ?_, ?_⟩
  · haveI := hfd
    exact Module.Finite.map S _
  · intro a b hab v hv
    obtain ⟨x, hxS, rfl⟩ := Submodule.mem_map.mp hv
    have hm := Submodule.mem_map_of_mem (f := (e : X.V →ₗ[ℂ] Y.V)) (hst a b hab x hxS)
    simpa [he] using hm
  · exact ⟨e.symm y, hx, by simp⟩

theorem isWeight_of_intertwine {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : V ≃ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ W)
    (he : ∀ a b x, e (E a b x) = F a b (e x)) {μ : Fin n → ℝ} {x : V} (h : IsWeight E μ x) :
    IsWeight F μ (e x) := by
  intro a
  rw [← he, h a, map_smul]

theorem kHighest_of_intertwine {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : V ≃ₗ[ℂ] W) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ W)
    (he : ∀ a b x, e (E a b x) = F a b (e x)) {μ : Fin n → ℝ} {x : V} (h : KHighest ε E μ x) :
    KHighest ε F μ (e x) := by
  exact ⟨isWeight_of_intertwine e E F he h.1, fun a b hab hε => by rw [← he, h.2 a b hab hε, map_zero]⟩

theorem intWt_of_iso {X Y : GMod n} (h : Iso X Y) (hX : IntWt X) : IntWt Y := by
  obtain ⟨e, he⟩ := h
  intro μ y hy hw
  have hx : e.symm y ≠ 0 := by simpa using hy
  exact hX μ (e.symm y) hx (isWeight_of_intertwine e.symm Y.E X.E (fun a b z => intertwine_symm e he a b z) hw)

theorem algDS_of_iso {X Y : GMod n} (ε : Fin n → Bool) (h : Iso X Y) (s : Equiv.Perm (Fin n)) (mu : Fin n → ℝ)
    (hX : AlgDS ε X s mu) : AlgDS ε Y s mu := by
  obtain ⟨e, he⟩ := h
  obtain ⟨h1, h2, h3, v, hv, hk⟩ := hX
  refine ⟨h1, h2, ?_, e v, by simpa using hv,
    kHighest_of_intertwine e _ (fun a b => X.E (s a) (s b)) (fun a b => Y.E (s a) (s b))
      (fun a b x => he (s a) (s b) x) hk⟩
  intro μ y hy hky
  exact h3 μ (e.symm y) (by simpa using hy)
    (kHighest_of_intertwine e.symm _ (fun a b => Y.E (s a) (s b)) (fun a b => X.E (s a) (s b))
      (fun a b z => intertwine_symm e he (s a) (s b) z) hky)

theorem coneDS_of_iso {X Y : GMod n} (ε : Fin n → Bool) (h : Iso X Y) (s : Equiv.Perm (Fin n)) (mu : Fin n → ℝ)
    (hX : CompanionTheory.RgExh.Fin.ConeDS ε X s mu) : CompanionTheory.RgExh.Fin.ConeDS ε Y s mu := by
  obtain ⟨e, he⟩ := h
  intro ν y hy hky
  exact hX ν (e.symm y) (by simpa using hy)
    (kHighest_of_intertwine e.symm _ (fun a b => Y.E (s a) (s b)) (fun a b => X.E (s a) (s b))
      (fun a b z => intertwine_symm e he (s a) (s b) z) hky)

theorem isoFacts : CompanionTheory.RgExh.Fin.IsoFacts := by
  intro n ε X Y Z
  exact ⟨iso_refl X, iso_symm, iso_trans, fun h => ⟨isSimple_of_iso h, isSimple_of_iso (iso_symm h)⟩,
    fun h χ => ⟨scalChar_of_iso h χ, scalChar_of_iso (iso_symm h) χ⟩,
    fun h χ => ⟨hasChar_of_iso h χ, hasChar_of_iso (iso_symm h) χ⟩,
    fun h => ⟨locFin_of_iso ε h, locFin_of_iso ε (iso_symm h)⟩,
    fun h => ⟨intWt_of_iso h, intWt_of_iso (iso_symm h)⟩,
    fun h s mu => ⟨algDS_of_iso ε h s mu, algDS_of_iso ε (iso_symm h) s mu⟩,
    fun h s mu => ⟨coneDS_of_iso ε h s mu, coneDS_of_iso ε (iso_symm h) s mu⟩⟩

end GlobalTheory.CompanionTheory.RgIso
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasCharOfScalChar
section -- merged from CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.Development
namespace CompanionTheory.RgExh

def Finish : Prop := StepChar → Hecke → Decay → FarReg → GlobalTheory.Dec.DSExhaust

end CompanionTheory.RgExh
end

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgExhFin

open _root_.CompanionTheory.RgExh CompanionTheory.RgExh.Fin
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open CompanionTheory.D.LK (IsKMod LocFin IsMin)

variable {n : ℕ}

theorem hasChar_path (hS : StepChar) (ss : List (Fin n)) :
    ∀ (X : GMod n) (χ : Fin n → ℂ), HasChar X χ → HasChar (path X χ ss) (pathEnd χ ss) := by
  induction ss with
  | nil => intro X χ h; exact h
  | cons s ss ih => intro X χ h; exact ih _ _ (hS n X χ s h)

theorem hasChar_of_scalChar {X : GMod n} {χ : Fin n → ℂ} (h : ScalChar X χ) : HasChar X χ :=
  ⟨1, fun Y => by rw [pow_one, h Y, sub_self]⟩

theorem capelliPoly_eq_of_perm {χ χ₂ : Fin n → ℂ} (τ τ₂ : Equiv.Perm (Fin n)) (h : ∀ a, χ (τ a) = χ₂ (τ₂ a)) :
    Formalism.QuantumDeterminants.capP χ = Formalism.QuantumDeterminants.capP χ₂ := by
  funext Y
  delta Formalism.QuantumDeterminants.capP
  rw [← Equiv.prod_comp τ (fun s => Y + χ s), ← Equiv.prod_comp τ₂ (fun s => Y + χ₂ s)]
  exact Finset.prod_congr rfl fun a _ => by rw [h a]

def EndOf (ε : Fin n → Bool) (M : GMod n) (χ : Fin n → ℂ) (ss : List (Fin n))
    (d : Equiv.Perm (Fin n) × (Fin n → ℝ)) : Prop :=
  ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V) (E : Fin n → Fin n → Module.End ℂ V)
    (hE : GlRel E), IsUnitary ε E ∧ LocFin ε E ∧ IsSimple ⟨V, E, hE⟩ ∧ AlgDS ε ⟨V, E, hE⟩ d.1 d.2 ∧
      Iso (path M χ ss) ⟨V, E, hE⟩

theorem iso_of_ends (hH : Hecke) (hI : IsoFacts) (hU : AlgUniq) {ε : Fin n → Bool} {M M' : GMod n}
    {χ : Fin n → ℂ} {ss : List (Fin n)} {d : Equiv.Perm (Fin n) × (Fin n → ℝ)}
    (hg : GoodPath χ ss) (hM : IsSimple M) (hM' : IsSimple M') (hc : HasChar M χ) (hc' : HasChar M' χ)
    (hs : ScalChar (path M χ ss) (pathEnd χ ss)) (e : EndOf ε M χ ss d) (e' : EndOf ε M' χ ss d) :
    Iso M M' := by
  obtain ⟨V, i1, i2, E, hE, u, l, sm, a, iso⟩ := e
  obtain ⟨V', j1, j2, E', hE', u', l', sm', a', iso'⟩ := e'
  have h := hU n ε V V' E E' hE hE' d.1 d.2 u u' l l' sm sm' a a'
  have h1 := (hI n ε (path M χ ss) ⟨V, E, hE⟩ ⟨V', E', hE'⟩).2.2.1 iso h
  have h2 := (hI n ε (path M' χ ss) ⟨V', E', hE'⟩ (path M' χ ss)).2.1 iso'
  have h3 := (hI n ε (path M χ ss) ⟨V', E', hE'⟩ (path M' χ ss)).2.2.1 h1 h2
  exact (hH n M χ ss hg hM hc hs).2.2 M' hM' hc' h3

theorem finish : StartMod → PathFin → PathExists → PathEndNat → SimpleDistinct → ScalarCharacterOfL2Embedding → UnitarizableOfL2Embedding →
    IsoFacts → CharOfAlgDS → AlgUniq → DataUniq → DSOfArr → DSOfData → KModOf → ArrCount → Finish := by
  intro hSM hPF hPE hPN hSD hSc hUn hI hCh hU hDU hDA hDD hKM hAC hS hH hDec hFR n ε H _ _ σ hσ
  obtain ⟨hcpl, hnt, hur, hir, hsq⟩ := id hσ
  haveI := hcpl
  obtain ⟨D, E, hK⟩ := hKM n ε H σ hur hir
  obtain ⟨hsim, ⟨χ, hχ⟩, hiw⟩ := hSM n ε H σ hur hir hnt D E hK
  obtain ⟨B, hB⟩ := hDec n
  obtain ⟨C, δ, hδ, hP⟩ := hPE n χ B
  obtain ⟨N₀, hN₀⟩ := hFR n C δ hδ
  obtain ⟨ss, N, hN, hg, hfar, hall, hgap, hbd⟩ := hP N₀
  have key : ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (D' : Submodule ℂ H')
      (E' : Fin n → Fin n → Module.End ℂ D') (hK' : IsKMod ε σ' D' E'), GlobalTheory.Dec.IsSqIntIrr ε σ' →
      IsSimple ⟨D', E', hK'.gl⟩ → ScalChar ⟨D', E', hK'.gl⟩ χ → IntWt ⟨D', E', hK'.gl⟩ →
      SimplePath χ ss ∧ ScalChar (path ⟨D', E', hK'.gl⟩ χ ss) (pathEnd χ ss) ∧
        ∃ d : Equiv.Perm (Fin n) × (Fin n → ℝ), EndOf ε ⟨D', E', hK'.gl⟩ χ ss d ∧
          Formalism.QuantumDeterminants.IsHCParam d.2 ∧ (∀ a b, a < b → ε (d.1 a) = ε (d.1 b) → d.1 a < d.1 b) ∧
          ∃ τ : Equiv.Perm (Fin n), ∀ a, ((d.2 a : ℝ) : ℂ) = pathEnd χ ss (τ a) := by
    intro H' _ _ _ σ' D' E' hK' hs' hsm' hsc' hiw'
    obtain ⟨_, _, ur, ir, sq⟩ := id hs'
    have hcX := hasChar_of_scalChar hsc'
    have hL := hB ε H' σ' D' E' hK' χ ss ur ir sq hcX hg hfar
    have hce := hasChar_path hS ss _ χ hcX
    have hse := hSc n ε _ _ hL hce
    obtain ⟨sp, sm, -⟩ := hH n _ χ ss hg hsm' hcX hse
    obtain ⟨V, i1, i2, EV, hEV, hun, iso⟩ := hUn n ε _ hL sm
    have facts := hI n ε (path ⟨D', E', hK'.gl⟩ χ ss) ⟨V, EV, hEV⟩ ⟨V, EV, hEV⟩
    have smV : IsSimple ⟨V, EV, hEV⟩ := (facts.2.2.2.1 iso).1 sm
    have scV : ScalChar ⟨V, EV, hEV⟩ (pathEnd χ ss) := (facts.2.2.2.2.1 iso _).1 hse
    have lfV : LocFin ε EV := (facts.2.2.2.2.2.2.1 iso).1 ((hPF n ε _ χ ss).1 hK'.locFin)
    have iwV : IntWt ⟨V, EV, hEV⟩ := (facts.2.2.2.2.2.2.2.1 iso).1 ((hPF n ε _ χ ss).2 hiw')
    obtain ⟨s', mu', hAlg⟩ := hN₀ ε V EV hEV (pathEnd χ ss) N smV.1 hun lfV iwV scV hN hgap hbd
    obtain ⟨τ, hτ⟩ := hCh n ε V EV hEV (pathEnd χ ss) s' mu' hun lfV scV hAlg
    exact ⟨sp, hse, (s', mu'), ⟨V, i1, i2, EV, hEV, hun, lfV, smV, hAlg, iso⟩, hAlg.1, hAlg.2.1, τ, hτ⟩
  obtain ⟨sp, hse, d₀, e₀, hc₀, ho₀, τ₀, hτ₀⟩ := key H σ D E hK hσ hsim hχ hiw
  have hend : ∀ a, pathEnd χ ss a = ((d₀.2 (τ₀.symm a) : ℝ) : ℂ) := fun a => by
    rw [hτ₀, Equiv.apply_symm_apply]
  have hinj' : Function.Injective (pathEnd χ ss) := fun a b h => by
    rw [hend, hend] at h
    exact τ₀.symm.injective (hc₀.1.injective (Complex.ofReal_injective h))
  have hr' : ∀ a, (pathEnd χ ss a).im = 0 ∧ ∃ m : ℤ, (pathEnd χ ss a).re - ((n : ℝ) - 1) / 2 = m := fun a => by
    rw [hend]
    exact ⟨Complex.ofReal_im _, by simpa using hc₀.2 (τ₀.symm a)⟩
  obtain ⟨m, hm, -⟩ := hPN n χ ss
  have hχa : ∀ a, χ a = pathEnd χ ss a - (m a : ℂ) := fun a => by
    rw [hm]; simp
  have hr : ∀ a, (χ a).im = 0 ∧ ∃ m : ℤ, (χ a).re - ((n : ℝ) - 1) / 2 = m := fun a => by
    obtain ⟨h1, k, h2⟩ := hr' a
    refine ⟨by rw [hχa]; simp [h1], k - m a, ?_⟩
    rw [hχa]
    simp only [Complex.sub_re, Complex.natCast_re]
    push_cast
    linarith
  have hinj := hSD n χ ss sp hall
  obtain ⟨A, A', hcard, hA, hA'⟩ := hAC n ε χ (pathEnd χ ss) hinj hinj' hr hr'
  have per : ∀ d : Equiv.Perm (Fin n) × (Fin n → ℝ), ∃ (M : GMod n) (e : Equiv.Perm (Fin n) × (Fin n → ℝ)),
      d ∈ A → e ∈ A' ∧ IsSimple M ∧ HasChar M χ ∧ ScalChar (path M χ ss) (pathEnd χ ss) ∧
        EndOf ε M χ ss e ∧ AlgDS ε M d.1 d.2 ∧ ConeDS ε M d.1 d.2 := by
    intro d
    by_cases hd : d ∈ A
    · obtain ⟨hhc, hord, τ, hτ⟩ := (hA d).1 hd
      obtain ⟨H', i1, i2, i3, σ', hsi, hall'⟩ := hDA n ε d.1 d.2 hhc hord
      obtain ⟨_, hnt', ur', ir', _⟩ := id hsi
      obtain ⟨D', E', hK'⟩ := hKM n ε H' σ' ur' ir'
      obtain ⟨s1, ⟨χd, hχd⟩, iw⟩ := hSM n ε H' σ' ur' ir' hnt' D' E' hK'
      obtain ⟨hAlg, hCone⟩ := hall' D' E' hK'
      obtain ⟨τ', hτ'⟩ := hCh n ε D' E' hK'.gl χd d.1 d.2 hK'.unit hK'.locFin hχd hAlg
      have hcap : Formalism.QuantumDeterminants.capP χd = Formalism.QuantumDeterminants.capP χ :=
        capelliPoly_eq_of_perm τ' τ fun a => by rw [← hτ', ← hτ]
      have hsc : ScalChar ⟨D', E', hK'.gl⟩ χ := fun Y => by rw [hχd Y, hcap]
      obtain ⟨-, hse', e, he, hce, hoe, τe, hτe⟩ := key H' σ' D' E' hK' hsi s1 hsc iw
      exact ⟨⟨D', E', hK'.gl⟩, e, fun _ => ⟨(hA' e).2 ⟨hce, hoe, τe, hτe⟩, s1, hasChar_of_scalChar hsc, hse', he,
        hAlg, hCone⟩⟩
    · exact ⟨triv n, d, fun h => absurd h hd⟩
  haveI : Nonempty (GMod n) := ⟨triv n⟩
  choose! M e hMe using per
  have hmaps : Set.MapsTo e (A : Set _) (A' : Set _) := fun d hd => (hMe d hd).1
  have hinjA : Set.InjOn e (A : Set _) := by
    intro d₁ h₁ d₂ h₂ heq
    obtain ⟨-, s1, c1, p1, n1, a1, k1⟩ := hMe d₁ h₁
    obtain ⟨-, s2, c2, p2, n2, a2, k2⟩ := hMe d₂ h₂
    rw [← heq] at n2
    have hiso := iso_of_ends hH hI hU hg s1 s2 c1 c2 p1 n1 n2
    have a2' : AlgDS ε (M d₁) d₂.1 d₂.2 :=
      ((hI n ε (M d₁) (M d₂) (M d₁)).2.2.2.2.2.2.2.2.1 hiso _ _).2 a2
    obtain ⟨q1, q2⟩ := hDU n ε (M d₁) _ _ _ _ a1 k1 a2'
    exact Prod.ext q1 q2
  have hsurj := Finset.surjOn_of_injOn_of_card_le e hmaps hinjA hcard.symm.le
  obtain ⟨d, hd, hde⟩ := hsurj ((hA' d₀).2 ⟨hc₀, ho₀, τ₀, hτ₀⟩)
  obtain ⟨-, s2, c2, p2, n2, a2, -⟩ := hMe d hd
  rw [hde] at n2
  have hiso := iso_of_ends hH hI hU hg hsim s2 (hasChar_of_scalChar hχ) c2 hse e₀ n2
  have aX : AlgDS ε ⟨D, E, hK.gl⟩ d.1 d.2 :=
    ((hI n ε ⟨D, E, hK.gl⟩ (M d) ⟨D, E, hK.gl⟩).2.2.2.2.2.2.2.2.1 hiso _ _).2 a2
  obtain ⟨hhc, hord, -⟩ := (hA d).1 hd
  exact ⟨d.1, d.2, hhc, hord, hDD n ε H σ D E hK d.1 d.2 hσ aX⟩

end GlobalTheory.CompanionTheory.RgExhFin
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KHighestOfPerm
noncomputable section

namespace GlobalTheory.CompanionTheory.DSData

open Formalism.REAL (KHighest)
open _root_.CompanionTheory.RgExh CompanionTheory.RgExh.Fin

variable {n : ℕ}

theorem kHighest_of_perm {V : Type} [AddCommGroup V] [Module ℂ V] {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) {E : Fin n → Fin n → Module.End ℂ V}
    {μ : Fin n → ℝ} {x : V} (h : KHighest (ε ∘ s) (fun a b => E (s a) (s b)) μ x) :
    KHighest ε E (μ ∘ s.symm) x := by
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · simpa using h.1 (s.symm a)
  · have h1 : (ε ∘ s) (s.symm a) = (ε ∘ s) (s.symm b) := by simpa using he
    simpa using h.2 (s.symm a) (s.symm b) (GlobalTheory.DSId.PermK.mono_symm hs a b hab h1) h1

theorem kHighest_perm {V : Type} [AddCommGroup V] [Module ℂ V] {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) {E : Fin n → Fin n → Module.End ℂ V}
    {μ : Fin n → ℝ} {x : V} (h : KHighest ε E (μ ∘ s.symm) x) :
    KHighest (ε ∘ s) (fun a b => E (s a) (s b)) μ x := by
  refine ⟨fun a => ?_, fun a b hab he => h.2 _ _ (hs a b hab he) he⟩
  simpa using h.1 (s a)

theorem dsOfData : DSOfData := by
  intro n ε H _ _ σ D E hK s mu hSq hA
  obtain ⟨-, hord, hmin, v, hv0, hv⟩ := hA
  obtain ⟨hT, -, -, hS, -⟩ := GlobalTheory.DSId.PermK.permKType n ε s H σ hord
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS.1 hSq
  have e : ∀ f : Fin n → ℝ, (f ∘ s.symm) ∘ s = f := fun f => by funext a; simp
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_⟩
  · obtain ⟨T, hT'⟩ := hK.ty _ v hv0 (kHighest_of_perm hord hv)
    refine ⟨T, ?_⟩
    have h6 := (hT _ T).1 hT'
    rwa [e] at h6
  · intro μ S hS'
    have h6 : Formalism.MainNotions.S.IsKTypeOf ε σ (μ ∘ s.symm) S := by
      refine (hT _ S).2 ?_
      rwa [e]
    obtain ⟨w, hw0, -, hw⟩ := hK.hw _ S h6
    exact hmin μ w hw0 (kHighest_perm hord hw)

end GlobalTheory.CompanionTheory.DSData
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsPermOfCapPEq
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.ExistsIsAlgebraicRatFuncFractionRingDedekind
open Formalism.REAL Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

namespace GlobalTheory.CompanionTheory.HolCoef.CapLW

section perm

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

omit [Algebra ℂ A] in
theorem glRel_perm {E : Fin n → Fin n → A} (hE : GlRel E) (σ : Equiv.Perm (Fin n)) :
    GlRel fun a b => E (σ a) (σ b) := by
  intro a b c d
  simpa only [σ.injective.eq_iff] using hE (σ a) (σ b) (σ c) (σ d)

theorem qdet_perm {E : Fin n → Fin n → A} (hE : GlRel E) (σ : Equiv.Perm (Fin n)) (u : ℂ) :
    qdet (fun a b => E (σ a) (σ b)) u = qdet E u := by
  let P : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun c a => if c = σ a then 1 else 0
  let Q : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun b d => if d = σ b then 1 else 0
  have hQP : Q * P = 1 := by
    ext b a
    simp [P, Q, Matrix.mul_apply, Matrix.one_apply, eq_comm]
  have h := (Formalism.FourierDecayAlt.P.contractions_covariant A n E P Q hE hQP (mul_eq_one_comm.1 hQP) u 0 0 0 0).1
  rw [← h]
  congr 1
  funext a b
  simp [Formalism.FourierDecayAlt.Q.Econj, P, Q, ite_smul]

end perm

section order

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

end order

end GlobalTheory.CompanionTheory.HolCoef.CapLW
end
end

open Formalism.REAL

noncomputable section

namespace GlobalTheory.CompanionTheory.CharOfLowK

theorem charOfAlgDS : CompanionTheory.RgExh.Fin.CharOfAlgDS := by
  intro n ε V _ _ E hE χ s mu hU hLF hSC hDS
  obtain ⟨hHC, -, hMin, v, hv0, hKH⟩ := hDS
  obtain ⟨S, hSfin, hSK, hvS⟩ := hLF v
  have hU' : Formalism.REAL.IsUnitary (ε ∘ s) (fun a b => E (s a) (s b)) := fun a b x y => hU (s a) (s b) x y
  have hSK' : CompanionTheory.D.DSIC.KStab (ε ∘ s) (fun a b => E (s a) (s b)) S :=
    fun a b hab w hw => hSK (s a) (s b) hab w hw
  have hcap : ∀ Y, Formalism.QuantumDeterminants.capP (fun a => (mu a : ℂ)) Y = Formalism.QuantumDeterminants.capP χ Y := by
    intro Y
    have h1 := CompanionTheory.D.DSIC.hAlgCore n (ε ∘ s) mu V (fun a b => E (s a) (s b)) v S hHC
      (GlobalTheory.CompanionTheory.HolCoef.CapLW.glRel_perm hE s) hU' hKH hSfin hSK' hvS hMin Y
    rw [GlobalTheory.CompanionTheory.HolCoef.CapLW.qdet_perm hE s] at h1
    have h2 : Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2) = Formalism.QuantumDeterminants.capP χ Y • 1 := hSC Y
    have h3 : Formalism.QuantumDeterminants.capP χ Y • v = Formalism.QuantumDeterminants.capP (fun a => (mu a : ℂ)) Y • v := by
      rw [← h1, h2]
      simp
    exact (smul_left_injective ℂ hv0 h3).symm
  exact exists_perm_of_capelliPolynomial_eq (fun a => (mu a : ℂ)) χ hcap

end GlobalTheory.CompanionTheory.CharOfLowK
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KModOf
namespace GlobalTheory.CompanionTheory.KModOfStep

theorem kModOf : CompanionTheory.RgExh.Fin.KModOf := by
  intro n ε H _ _ _ σ hU hI
  exact CompanionTheory.D.LK.hKModExists n ε H σ hU hI

end GlobalTheory.CompanionTheory.KModOfStep
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KHighestRenumber
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.LowestData

open Formalism.REAL (KHighest)
open _root_.CompanionTheory.RgExh (GMod AlgDS)
open _root_.CompanionTheory.RgDs (InCone)
open GlobalTheory.LowestKTypeDetermines (lt_of_perm_lt rhoC_perm lowK_add strictAnti_add_rho nsq_add_cone eq_zero_of_nsq nsq_comp)

variable {n : ℕ}

theorem kHighest_renumber {V : Type} [AddCommGroup V] [Module ℂ V] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) {s s' : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b)
    (hs' : ∀ a b, a < b → ε (s' a) = ε (s' b) → s' a < s' b) {Λ : Fin n → ℝ} {v : V}
    (h : KHighest (ε ∘ s') (fun a b => E (s' a) (s' b)) Λ v) :
    KHighest (ε ∘ s) (fun a b => E (s a) (s b)) (Λ ∘ s'.symm ∘ s) v := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · have := h1 (s'.symm (s a))
    simpa using this
  · have hlt := hs a b hab he
    have key : s'.symm (s a) < s'.symm (s b) := by
      refine lt_of_perm_lt (s := s') hs' ?_ ?_
      · simpa only [Equiv.apply_symm_apply] using hlt
      · simpa only [Function.comp_apply, Equiv.apply_symm_apply] using he
    have := h2 _ _ key (by simpa using he)
    simpa using this

-- Unfold DataUniq and ConeDS to depend directly on AlgDS and InCone.
theorem dataUniq (n : ℕ) (ε : Fin n → Bool) (X : GMod n)
    (s s' : Equiv.Perm (Fin n)) (mu mu' : Fin n → ℝ)
    (h : AlgDS ε X s mu)
    (hc : ∀ (ν : Fin n → ℝ) (x : X.V), x ≠ 0 →
      KHighest (ε ∘ s) (fun a b => X.E (s a) (s b)) ν x →
      InCone (PI.UpqRep.lowK (ε ∘ s) mu) ν)
    (h' : AlgDS ε X s' mu') : s = s' ∧ mu = mu' := by
  obtain ⟨hl, hs, -, v, hv0, hv⟩ := h
  obtain ⟨hl', hs', hmin', v', hv0', hv'⟩ := h'
  have add : ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ),
      PI.UpqRep.lowK ε lam + (2 : ℝ) • Formalism.REAL.rhoC ε = lam + Formalism.QuantumDeterminants.rhoStd n := fun ε lam => lowK_add ε lam
  have k1 := kHighest_renumber ε X.E hs hs' hv'
  have k2 := kHighest_renumber ε X.E hs' hs hv
  obtain ⟨c, hc1, e⟩ := hc _ v' hv0' k1
  have m2 := hmin' _ v hv0 k2
  set x := mu + Formalism.QuantumDeterminants.rhoStd n with hx
  set x' := mu' + Formalism.QuantumDeterminants.rhoStd n with hx'
  set Q : Fin n → ℝ := ∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b with hQ
  have hsx : StrictAnti x := strictAnti_add_rho hl.1
  have hsx' : StrictAnti x' := strictAnti_add_rho hl'.1
  have r1 : x' ∘ s'.symm ∘ s = x + Q := by
    have e1 : x = PI.UpqRep.lowK (ε ∘ s) mu + (2 : ℝ) • Formalism.REAL.rhoC (ε ∘ s) := (add _ _).symm
    have e2 : x' = PI.UpqRep.lowK (ε ∘ s') mu' + (2 : ℝ) • Formalism.REAL.rhoC (ε ∘ s') := (add _ _).symm
    funext a
    have ea := congrFun e a
    rw [e1, e2, rhoC_perm s hs, rhoC_perm s' hs']
    simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, Equiv.apply_symm_apply] at ea ⊢
    rw [ea]; ring
  have r2 : x ∘ s.symm ∘ s' =
      PI.UpqRep.lowK (ε ∘ s) mu ∘ s.symm ∘ s' + (2 : ℝ) • Formalism.REAL.rhoC (ε ∘ s') := by
    have e1 : x = PI.UpqRep.lowK (ε ∘ s) mu + (2 : ℝ) • Formalism.REAL.rhoC (ε ∘ s) := (add _ _).symm
    rw [e1, rhoC_perm s hs, rhoC_perm s' hs']
    funext a
    simp
  have m3 : Formalism.REAL.nsq x' ≤ Formalism.REAL.nsq x := by
    have a1 : Formalism.REAL.nsq x' =
        PI.UpqRep.vNormSq (ε ∘ s') (PI.UpqRep.lowK (ε ∘ s') mu') := by
      rw [hx', ← add]; rfl
    have a2 : Formalism.REAL.nsq x = PI.UpqRep.vNormSq (ε ∘ s')
        (PI.UpqRep.lowK (ε ∘ s) mu ∘ s.symm ∘ s') := by
      have := nsq_comp (s.symm * s') x
      have e3 : x ∘ ⇑(s.symm * s') = x ∘ s.symm ∘ s' := rfl
      rw [e3, r2] at this
      rw [← this]; rfl
    rw [a1, a2]; exact m2
  have m4 : Formalism.REAL.nsq (x + Q) = Formalism.REAL.nsq x' := by
    rw [← r1]
    exact nsq_comp (s'.symm * s) x'
  have h4 := nsq_add_cone hsx.antitone hc1
  have hQ0 : Q = 0 := eq_zero_of_nsq (by linarith)
  rw [hQ0, add_zero] at r1
  have hm : StrictMono (s'.symm * s) := fun a b hab => by
    have h5 := hsx hab
    rw [← r1] at h5
    exact hsx'.lt_iff_gt.1 h5
  have h6 : s'.symm * s = 1 := by
    have := Subsingleton.elim (hm.orderIsoOfSurjective _ (s'.symm * s).surjective) (OrderIso.refl _)
    exact Equiv.ext fun a => DFunLike.congr_fun this a
  have h7 : s = s' := by
    refine Equiv.ext fun a => ?_
    have := congrArg (fun t : Equiv.Perm (Fin n) => s' (t a)) h6
    simpa using this
  subst h7
  refine ⟨rfl, ?_⟩
  have h8 : x' = x := by
    simpa using r1
  exact (add_right_cancel h8).symm

end GlobalTheory.CompanionTheory.LowestData
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UnitarizableOfSeparatingSmoothL2Maps
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsUnitaryImage
noncomputable section

open ReciprocityTheory.ChartRestriction.DS

namespace GlobalTheory.CompanionTheory.Unitarize

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {X : Type*} [AddCommGroup X] [Module ℂ X]

theorem injective_of_simple {M : Type*} [AddCommGroup M] [Module ℂ M]
    {E : Fin n → Fin n → Module.End ℂ X} {F : Fin n → Fin n → Module.End ℂ M}
    (hS : ∀ W : Submodule ℂ X, (∀ a b, ∀ x ∈ W, E a b x ∈ W) → W = ⊥ ∨ W = ⊤)
    (c : X →ₗ[ℂ] M) (hc : ∀ a b x, c (E a b x) = F a b (c x)) (h0 : c ≠ 0) :
    Function.Injective c := by
  have hst : ∀ a b, ∀ x ∈ LinearMap.ker c, E a b x ∈ LinearMap.ker c := by
    intro a b x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hc, hx, map_zero]
  rcases hS _ hst with h | h
  · exact LinearMap.ker_eq_bot.1 h
  · exact absurd (LinearMap.ker_eq_top.1 h) h0

theorem adjSign_eq_sgn (ε : Fin n → Bool) (a b : Fin n) :
    adjSign ε a b = ((Formalism.REAL.sgn ε a b : ℝ) : ℂ) := by
  unfold adjSign Formalism.REAL.sgn
  split_ifs <;> simp

theorem exists_unitary_image {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {E : Fin n → Fin n → Module.End ℂ X}
    (hS : ∀ W : Submodule ℂ X, (∀ a b, ∀ x ∈ W, E a b x ∈ W) → W = ⊥ ∨ W = ⊤)
    (c : X →ₗ[ℂ] smD ε σ) (hc : ∀ a b x, c (E a b x) = smE ε σ a b (c x)) (h0 : c ≠ 0) :
    ∃ (V : Submodule ℂ H) (E' : Fin n → Fin n → Module.End ℂ V) (e : X ≃ₗ[ℂ] V),
      (∀ x, ((e x : V) : H) = ((c x : smD ε σ) : H)) ∧
      Formalism.REAL.GlRel E' ∧ Formalism.REAL.IsUnitary ε E' ∧
      ∀ a b x, e (E a b x) = E' a b (e x) := by
  have hinj : Function.Injective c := injective_of_simple hS c hc h0
  set d : X →ₗ[ℂ] H := (smD ε σ).subtype ∘ₗ c with hd
  have hdinj : Function.Injective d := Subtype.val_injective.comp hinj
  let e : X ≃ₗ[ℂ] LinearMap.range d := LinearEquiv.ofInjective d hdinj
  have he : ∀ x, ((e x : LinearMap.range d) : H) = ((c x : smD ε σ) : H) := fun x => rfl
  let E' : Fin n → Fin n → Module.End ℂ (LinearMap.range d) := fun a b =>
    e.toLinearMap ∘ₗ E a b ∘ₗ e.symm.toLinearMap
  have hE' : ∀ a b x, E' a b (e x) = e (E a b x) := by
    intro a b x
    simp [E']
  have hcoe : ∀ a b x, ((E' a b (e x) : LinearMap.range d) : H) =
      ((smE ε σ a b (c x) : smD ε σ) : H) := by
    intro a b x
    rw [hE', he, hc]
  have hgl : IsGlRep (smE ε σ) := (isDerivedOn_smE hσ).glRep
  have hU : IsInfUnitary ε (smE ε σ) := isInfUnitary_of_isDerivedOn hσ (isDerivedOn_smE hσ)
  refine ⟨LinearMap.range d, E', e, he, ?_, ?_, fun a b x => (hE' a b x).symm⟩
  · intro a b c' d'
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := e.surjective y
    have h := LinearMap.congr_fun (hgl a b c' d') (c x)
    have h' := congrArg (Subtype.val) h
    apply Subtype.ext
    have hEE : ∀ a b c' d', ((E' a b (E' c' d' (e x)) : LinearMap.range d) : H) =
        ((smE ε σ a b (smE ε σ c' d' (c x)) : smD ε σ) : H) := by
      intro a b c' d'
      rw [hE', hcoe, hc]
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Submodule.coe_sub] at h' ⊢
    rw [hEE, hEE, h']
    split_ifs <;> simp [hcoe]
  · intro a b y z
    obtain ⟨u, rfl⟩ := e.surjective y
    obtain ⟨v, rfl⟩ := e.surjective z
    have h := hU a b (c u) (c v)
    rw [← adjSign_eq_sgn]
    rw [Submodule.coe_inner, Submodule.coe_inner, hcoe, hcoe, he, he]
    simpa [Submodule.coe_inner] using h

end GlobalTheory.CompanionTheory.Unitarize
end
end

noncomputable section

namespace GlobalTheory.CompanionTheory.RgExhFin

open _root_.CompanionTheory.RgExh ReciprocityTheory.ChartRestriction.DS
open Formalism.REAL (GlRel IsUnitary)

theorem unitarizable_of_separating_smooth_l2_maps :
    ∀ (n : ℕ) (ε : Fin n → Bool) (X : GMod n), L2Embedding ε X → IsSimple X →
      ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V)
        (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E),
        IsUnitary ε E ∧ Iso X ⟨V, E, hE⟩ := by
  intro n ε X hL hS
  obtain ⟨hnt, hsub⟩ := hS
  obtain ⟨u, hu⟩ := exists_ne (0 : X.V)
  obtain ⟨c, hc, hcu⟩ := hL u hu
  have h0 : c ≠ 0 := fun h => hcu (by simp [h])
  obtain ⟨V, E', e, -, hgl, hU, he⟩ :=
    GlobalTheory.CompanionTheory.Unitarize.exists_unitary_image (rreg_isURepOn ε) hsub c hc h0
  exact ⟨V, inferInstance, inferInstance, E', hgl, hU, e, he⟩

end GlobalTheory.CompanionTheory.RgExhFin
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteDimensionalComapSubtype
noncomputable section

namespace GlobalTheory.CompanionTheory.RgSteps

open _root_.CompanionTheory.RgExh
open Formalism.REAL (IsWeight)
open CompanionTheory.D.LK (LocFin)

variable {n : ℕ}

theorem locFin_tens (ε : Fin n → Bool) (X : GMod n) (h : LocFin ε X.E) : LocFin ε (tens X).E := by
  intro u
  choose S hSfd hSst hSmem using fun i => h (u i)
  haveI : ∀ i, FiniteDimensional ℂ (S i) := hSfd
  have hTst : ∀ a b, ε a = ε b → ∀ x ∈ ⨆ i, S i, X.E a b x ∈ ⨆ i, S i := by
    intro a b hab x hx
    refine Submodule.iSup_induction S (motive := fun y => X.E a b y ∈ ⨆ i, S i) hx
      (fun i y hy => (le_iSup S i) (hSst i a b hab y hy)) (by simp) ?_
    intro y w hy hw
    rw [(X.E a b).map_add]
    exact Submodule.add_mem _ hy hw
  have hfd : FiniteDimensional ℂ (Submodule.pi Set.univ fun _ : Fin n => ⨆ i, S i) := by
    let f : (Submodule.pi Set.univ fun _ : Fin n => ⨆ i, S i) →ₗ[ℂ] (Fin n → ↥(⨆ i, S i)) :=
      { toFun := fun v i => ⟨v.1 i, v.2 i (Set.mem_univ i)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact FiniteDimensional.of_injective f
      (fun v w hvw => Subtype.ext (funext fun i => congrArg Subtype.val (congrFun hvw i)))
  refine ⟨Submodule.pi Set.univ (fun _ : Fin n => ⨆ i, S i), hfd, ?_, ?_⟩
  · intro a b hab v hv i _
    have hv' : ∀ j, v j ∈ ⨆ i, S i := fun j => hv j (Set.mem_univ j)
    change X.E a b (v i) + (if i = a then v b else 0) ∈ ⨆ i, S i
    refine Submodule.add_mem _ (hTst a b hab _ (hv' i)) ?_
    split_ifs
    · exact hv' b
    · exact Submodule.zero_mem _
  · intro i _
    exact (le_iSup S i) (hSmem i)

theorem finiteDimensional_comap_subtype {V : Type} [AddCommGroup V] [Module ℂ V]
    (S T : Submodule ℂ V) [FiniteDimensional ℂ T] : FiniteDimensional ℂ (T.comap S.subtype) := by
  refine FiniteDimensional.of_injective
    (LinearMap.codRestrict T (S.subtype ∘ₗ (T.comap S.subtype).subtype) fun x => x.2) ?_
  intro x y hxy
  have hv : ((x : S) : V) = ((y : S) : V) := congrArg (fun w : T => (w : V)) hxy
  exact Subtype.ext (Subtype.ext hv)

theorem locFin_sub (ε : Fin n → Bool) (X : GMod n) (S : Submodule ℂ X.V)
    (h : ∀ a b, ∀ x ∈ S, X.E a b x ∈ S) (hX : LocFin ε X.E) : LocFin ε (X.sub S h).E := by
  intro x
  obtain ⟨F, hF, hst, hx⟩ := hX x.1
  haveI := hF
  refine ⟨F.comap S.subtype, finiteDimensional_comap_subtype S F, ?_, hx⟩
  intro a b hab v hv
  exact hst a b hab v.1 hv

theorem intWt_tens (X : GMod n) (h : IntWt X) : IntWt (tens X) := by
  intro μ u hu hw a
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra hc
    exact hu (funext fun j => by_contra fun hj => hc ⟨j, hj⟩)
  have hw' : Formalism.REAL.IsWeight X.E (fun b => if b = i then μ b - 1 else μ b) (u i) := by
    intro b
    have hb : X.E b b (u i) + (if i = b then u b else 0) = (μ b : ℂ) • u i := congrFun (hw b) i
    by_cases hbi : b = i
    · subst hbi
      simp only [if_true] at hb ⊢
      rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul, ← hb]
      exact (add_sub_cancel_right _ _).symm
    · simp only [if_neg hbi, if_neg (Ne.symm hbi), add_zero] at hb ⊢
      exact hb
  obtain ⟨m, hm⟩ := h _ (u i) hi hw' a
  by_cases hai : a = i
  · subst hai
    simp only [if_true] at hm
    exact ⟨m + 1, by push_cast; linarith⟩
  · simp only [if_neg hai] at hm
    exact ⟨m, hm⟩

theorem intWt_sub (X : GMod n) (S : Submodule ℂ X.V) (h : ∀ a b, ∀ x ∈ S, X.E a b x ∈ S)
    (hX : IntWt X) : IntWt (X.sub S h) := by
  intro μ x hx hw a
  exact hX μ x.1 (fun h0 => hx (Subtype.ext h0)) (fun b => congrArg Subtype.val (hw b)) a

theorem locFin_step (ε : Fin n → Bool) (X : GMod n) (z : ℂ) (h : LocFin ε X.E) :
    LocFin ε (step X z).E := by
  exact locFin_sub ε (CompanionTheory.RgExh.tens X) _ _ (locFin_tens ε X h)

theorem intWt_step (X : GMod n) (z : ℂ) (h : IntWt X) : IntWt (step X z) := by
  exact intWt_sub (CompanionTheory.RgExh.tens X) _ _ (intWt_tens X h)

theorem pathFin :
    ∀ (n : ℕ) (ε : Fin n → Bool) (X : GMod n) (χ : Fin n → ℂ) (ss : List (Fin n)),
      (LocFin ε X.E → LocFin ε (path X χ ss).E) ∧ (IntWt X → IntWt (path X χ ss)) := by
  intro n ε X χ ss
  induction ss generalizing X χ with
  | nil => exact ⟨id, id⟩
  | cons s ss ih =>
    have h := ih (step X (χ s)) (χ + Pi.single s 1)
    exact ⟨fun hX => h.1 (locFin_step ε X (χ s) hX),
      fun hX => h.2 (intWt_step X (χ s) hX)⟩

end GlobalTheory.CompanionTheory.RgSteps
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SimpleDistinct
namespace GlobalTheory.CompanionTheory.RgExhFin

open _root_.CompanionTheory.RgExh

private theorem simplePath_cons_iff {n : ℕ} (χ : Fin n → ℂ) (a : Fin n) (l : List (Fin n)) :
    SimplePath χ (a :: l) ↔ (∀ r, r ≠ a → χ r ≠ χ a) ∧ SimplePath (χ + Pi.single a 1) l :=
  Iff.rfl

theorem simplePath_ne {n : ℕ} (ss : List (Fin n)) :
    ∀ χ : Fin n → ℂ, SimplePath χ ss → ∀ r s, r ≠ s → (r ∈ ss ∨ s ∈ ss) → χ r ≠ χ s := by
  induction ss with
  | nil =>
    intro χ _ r s _ h
    simp at h
  | cons a l ih =>
    intro χ hp r s hrs hmem
    rw [simplePath_cons_iff] at hp
    obtain ⟨h1, h2⟩ := hp
    by_cases hra : r = a
    · subst hra
      exact (h1 s (Ne.symm hrs)).symm
    by_cases hsa : s = a
    · subst hsa
      exact h1 r hrs
    have hmem' : r ∈ l ∨ s ∈ l := by
      simp only [List.mem_cons] at hmem
      tauto
    have h3 := ih _ h2 r s hrs hmem'
    simpa [Pi.single_apply, hra, hsa] using h3

theorem simpleDistinct (n : ℕ) (χ : Fin n → ℂ) (ss : List (Fin n))
    (hp : SimplePath χ ss) (hall : ∀ s, s ∈ ss) : Function.Injective χ := by
  intro r s heq
  by_contra hne
  exact simplePath_ne ss χ hp r s hne (Or.inl (hall r)) heq

end GlobalTheory.CompanionTheory.RgExhFin
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PathEndEqAddNat
namespace GlobalTheory.CompanionTheory.RgPath

open _root_.CompanionTheory.RgExh

theorem pathEnd_eq_add_nat {n : ℕ} (ss : List (_root_.Fin n)) :
    ∀ χ : _root_.Fin n → ℂ, ∃ m : _root_.Fin n → ℕ, pathEnd χ ss = χ + (fun a => (m a : ℂ)) ∧
      ∀ a, a ∈ ss → 1 ≤ m a := by
  induction ss with
  | nil =>
    intro χ
    refine ⟨0, ?_, by simp⟩
    funext a
    change χ a = χ a + (↑(0 : ℕ) : ℂ)
    simp
  | cons s ss ih =>
    intro χ
    obtain ⟨m', h, hm⟩ := ih (χ + Pi.single s 1)
    refine ⟨m' + Pi.single s 1, ?_, ?_⟩
    · change pathEnd (χ + Pi.single s 1) ss = _
      rw [h]
      funext a
      by_cases e : a = s
      · subst a
        simp only [Pi.add_apply, Pi.single_eq_same, Nat.cast_add, Nat.cast_one]
        ac_rfl
      · simp only [Pi.add_apply, Pi.single_eq_of_ne e, add_zero]
    · intro a ha
      rcases List.mem_cons.1 ha with e | ha
      · subst a
        simpa only [Pi.add_apply, Pi.single_eq_same] using Nat.succ_le_succ (Nat.zero_le (m' s))
      · exact (hm a ha).trans (Nat.le_add_right _ _)

theorem pathEndNat (n : ℕ) (χ : _root_.Fin n → ℂ) (ss : List (_root_.Fin n)) :
    ∃ m : _root_.Fin n → ℕ, pathEnd χ ss = χ + (fun a => (m a : ℂ)) ∧
      ∀ a, a ∈ ss → 1 ≤ m a :=
  pathEnd_eq_add_nat ss χ

end GlobalTheory.CompanionTheory.RgPath
end

namespace CompanionTheory.RgExh.Fin

theorem exhaustion_finite_length : CompanionTheory.RgExh.Finish :=
  GlobalTheory.CompanionTheory.RgExhFin.finish
    GlobalTheory.CompanionTheory.RgStart.startMod
    GlobalTheory.CompanionTheory.RgSteps.pathFin
    GlobalTheory.CompanionTheory.RgPath.pathExists
    GlobalTheory.CompanionTheory.RgPath.pathEndNat
    GlobalTheory.CompanionTheory.RgExhFin.simpleDistinct
    GlobalTheory.CompanionTheory.AdjointSignNormality.scalar_of_separating_smooth_l2_maps
    GlobalTheory.CompanionTheory.RgExhFin.unitarizable_of_separating_smooth_l2_maps
    GlobalTheory.CompanionTheory.RgIso.isoFacts
    GlobalTheory.CompanionTheory.CharOfLowK.charOfAlgDS
    GlobalTheory.CompanionTheory.LowestDataIso.algUniq
    GlobalTheory.CompanionTheory.LowestData.dataUniq
    GlobalTheory.CompanionTheory.RenumDS.dsOfArr
    GlobalTheory.CompanionTheory.DSData.dsOfData
    GlobalTheory.CompanionTheory.KModOfStep.kModOf
    GlobalTheory.CompanionTheory.ArrCount.arrCount

end CompanionTheory.RgExh.Fin
