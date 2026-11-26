module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameSupportCompatible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalSatakeEqLanglandsQuotientUnramified
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsProductsCosocles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionLocalGenerationInertPlaceOffLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProductSpehSatake
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace GlobalTheory.FormDict.RecTLaws

section Core

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {rc : IrrGL (k := w.adicCompletion E) → WD h}

theorem locProd_eq (H : IsRec h rc) : ∀ {c n : ℕ} {d : Fin c → ℕ} (hd : ∑ i, d i = n)
    (σ : ∀ i, SmIrr (GL (Fin (d i)) (w.adicCompletion E))) (σ' : SmIrr (GL (Fin n) (w.adicCompletion E))),
    Nonempty (σ'.ρ.Equiv (GlobalTheory.UnitaryBC.locProd hd w σ)) →
      rc (cls (ParLaws.toRep σ')) = sumList (List.ofFn fun i => rc (cls (ParLaws.toRep (σ i)))) := by
  obtain ⟨a, ha, ε, -, L⟩ := H
  intro c
  induction c with
  | zero =>
    intro n d hd σ σ' e
    obtain rfl : n = 0 := by simpa using hd.symm
    obtain ⟨e⟩ := e
    obtain ⟨φ⟩ := GlobalTheory.LocGL.SupportRing.nonempty_equiv_unit (k := w.adicCompletion E) (stdBlocks d hd) fun i => (σ i).ρ
    have h1 := L.det 0 1 isSmoothChar_one
    simp only [List.range_zero, List.map_nil] at h1
    rw [List.ofFn_zero]
    refine ((L.eq_iff (ParLaws.toRep σ') (IrrRep.det (Fin 0) 1 isSmoothChar_one)).2 ⟨e.trans φ⟩).trans ?_
    exact h1
  | succ s ih =>
    intro n d hd σ σ' e
    obtain rfl : n = d 0 + ∑ i : Fin s, d i.succ := hd.symm.trans (Fin.sum_univ_succ d)
    obtain ⟨e⟩ := e
    obtain ⟨E₁⟩ := MultiIrr.nonempty_prod₂_equiv_multiProd_succ (k := w.adicCompletion E) d hd fun i => (σ i).ρ
    have hs : IsSmooth (multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i : Fin s => (σ i.succ).ρ) :=
      isSmooth_parInd _ _
    have hi := GlobalTheory.T.isIrreducible_second_factor_of_irreducible_product _ _ _ _ _ _ (σ 0).ρ _ σ'.ρ (σ 0).smooth (σ 0).irred hs σ'.irred ⟨e.trans E₁.symm⟩
    let σ'' : SmIrr (GL (Fin (∑ i : Fin s, d i.succ)) (w.adicCompletion E)) := ⟨_, _, hs, hi⟩
    have h1 := L.prod (d 0) _ (ParLaws.toRep (σ 0)) (ParLaws.toRep σ'') (ParLaws.toRep σ') ⟨e.trans E₁.symm⟩
    have h2 := ih (d := fun i : Fin s => d i.succ) rfl (fun i => σ i.succ) σ'' ⟨.refl _⟩
    rw [List.ofFn_succ]
    exact h1.trans (congrArg _ h2)

end Core

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
  (T : GlobalTheory.RowTie.WDTie N A) (hL : GlobalTheory.Published.LocalLanglandsGL)

theorem e_lpSumList (w : PlE H) (L : List (A.LP w)) : T.e w (lpSumList L) = sumList (L.map (T.e w)) := by
  induction L with
  | nil => exact T.zero w
  | cons x L ih =>
    change T.e w (A.lpSum x (lpSumList L)) = (T.e w x).lpSum (sumList (L.map (T.e w)))
    rw [T.sum, ih]

end Record

end GlobalTheory.FormDict.RecTLaws
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonFactorRecCompatible
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonFactorRecCompatible
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.SatakeLaw

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def consEquiv (n : ℕ) : ((Fin 1 → ℂ) × (Fin n → ℂ)) ≃ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun v := Fin.cons (v.1 0) v.2
  invFun f := (fun _ => f 0, Fin.tail f)
  map_add' x y := funext fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c x := funext fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp
  left_inv v := Prod.ext (funext fun i => by rw [Subsingleton.elim i 0]; simp) (funext fun j => by simp [Fin.tail])
  right_inv f := funext fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.tail]

theorem diag_sum_iso {n : ℕ} (c : Fin (n + 1) → ℂˣ) :
    ((WDRep.diag h fun _ : Fin 1 => c 0).sum (WDRep.diag h fun i : Fin n => c i.succ)).Iso (WDRep.diag h c) := by
  refine ⟨consEquiv n, fun σ v => ?_, fun v => ?_⟩
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [consEquiv]
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [consEquiv]

theorem sumList_cons (x : WD h) (l : List (WD h)) : sumList (x :: l) = x.lpSum (sumList l) := rfl

theorem sumList_ofFn_diag : ∀ (n : ℕ) (c : Fin n → ℂˣ),
    sumList (List.ofFn fun i => WD.mk (WDRep.diag h fun _ : Fin 1 => c i)) = WD.mk (WDRep.diag h c)
  | 0, c => by
      rw [List.ofFn_zero]
      show WD.lpZero (h := h) = _
      unfold WD.lpZero
      congr 2
      funext i
      exact i.elim0
  | n + 1, c => by
      rw [List.ofFn_succ]
      rw [sumList_cons]
      rw [sumList_ofFn_diag n (fun i => c i.succ), WD.lpSum_mk]
      exact WD.sound (diag_sum_iso c)

end GlobalTheory.LocLanglands.SatakeLaw

namespace GlobalTheory.LocLanglands.SatakeLaw

theorem sat_of_lawsLit : LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing →
    GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ)
    (rc : IrrGL (k := w.adicCompletion E) → WD h), LawsLit a ha e rc → ∀ (x : IrrGL (k := w.adicCompletion E)) (α : Fin x.1 → ℂˣ),
    HasSatake x.rep α → rc x = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  intro h1 h2 h3 h4 h5 h6 E Ω _ _ _ _ _ A w h a ha e rc H x α hα
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have hL := GlobalTheory.T.spherical_satake_eq_langlandsQuotient_unramified h1 h2 h3 h4 h5 h6 (w.adicCompletion E) x α hα
  rw [Fin.univ_val_map] at hL
  rw [H.langlands _ x hL, segSum, List.map_ofFn, ← sumList_ofFn_diag]
  congr 1
  refine List.ofFn_inj.mpr (funext fun i => ?_)
  simp only [Function.comp_apply, Segment.single, Segment.first_ofFirst, Segment.len_ofFirst, Nat.cast_one, sub_self,
    zero_div, WD.lpTw_zero, Test.lpChar_lpSp_one, H.one]
  exact Test.lpOfChar_unrChar ha (α i) _

end GlobalTheory.LocLanglands.SatakeLaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonFactorRecCompatibleStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.epsilon_factor_rec_compatible : LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (k := w.adicCompletion E) → WD h), LawsLit a ha e rc → ∀ (x : IrrGL (k := w.adicCompletion E)) (α : Fin x.1 → ℂˣ), HasSatake x.rep α → rc x = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  first | exact @GlobalTheory.LocLanglands.SatakeLaw.sat_of_lawsLit | exact GlobalTheory.LocLanglands.SatakeLaw.sat_of_lawsLit | (intros; apply GlobalTheory.LocLanglands.SatakeLaw.sat_of_lawsLit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsDataTransportLocalFieldIso
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsDataTransportLocalFieldIso
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.LocLanglands.isL_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (l : List (Segment k)) (l' : List (Segment k')) (x : IrrGL (k := k)) (x' : IrrGL (k := k')), List.Forall₂ (fun (Δ : Segment k) (Δ' : Segment k') => RepRel i Δ.first Δ'.first ∧ Δ.len = Δ'.len) l l' → RepRel i x x' → IsL (l : Multiset (Segment k)) x.rep → IsL (l' : Multiset (Segment k')) x'.rep := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi l l' x x' hl hx hL
  obtain ⟨T, hT, hTd⟩ := GlobalTheory.T.transportIrrGL_bijective_degree_charZero k k' i hi
  have hC := (GlobalTheory.T.transport_keeps_cuspidal_twists_characters k k' i hi).1
  have hprod := GlobalTheory.T.transport_keeps_products_cosocles k k' i hi
  have hcusp : ∀ y, y.IsCusp → (T y).IsCusp := fun y hy => (hC y (T y) ((hT _ _).2 rfl)).1.1 hy
  have hnu : ∀ (y : IrrGL (k := k)) (s : ℂ), T (y.nu s) = (T y).nu s := fun y s =>
    (hT _ _).1 ((hC y (T y) ((hT _ _).2 rfl)).2 s)
  have hcls : ∀ {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
      (y : IrrGL (k := K)), GlobalTheory.LocLanglands.cls y.2.rep = y := by
    intro K _ _ _ _ y
    obtain ⟨n, c⟩ := y
    unfold GlobalTheory.LocLanglands.cls
    exact congrArg (Sigma.mk n) c.cl_rep

  have H : ∀ (y : IrrGL (k := k)) (y' : IrrGL (k := k')), RepRel i y y' → ∀ (r r' : ℕ) (e : r = r') (xs : Fin r → IrrGL (k := k))
      (xs' : Fin r' → IrrGL (k := k')) (hd : ∑ a, (xs a).1 = y.1) (hd' : ∑ a, (xs' a).1 = y'.1),
      (∀ a, RepRel i (xs a) (xs' (Fin.cast e a))) →
      IsCosocle y.rep (prodIrr xs hd) → IsCosocle y'.rep (prodIrr xs' hd') := by
    intro y y' hy r r' e xs xs' hd hd' hxs hc
    subst e
    obtain ⟨n, c⟩ := y
    obtain ⟨n', c'⟩ := y'
    have e : n' = n := by
      have := hTd ⟨n, c⟩
      rw [(hT _ _).1 hy] at this
      exact this
    subst e
    exact hprod r n' xs xs' hd hd' c.rep c'.rep (fun a => hxs a)
      (by rw [hcls ⟨n', c⟩, hcls ⟨n', c'⟩]; exact hy) hc

  obtain ⟨S, hS1, hS2⟩ : ∃ S : Segment k → Segment k', (∀ Δ, (S Δ).first = T Δ.first) ∧ ∀ Δ, (S Δ).len = Δ.len :=
    ⟨fun Δ => Segment.ofFirst (T Δ.first) (hcusp _ Δ.isCusp_first) Δ.len Δ.len_pos,
      fun Δ => Segment.first_ofFirst _ _ _ _, fun Δ => Segment.len_ofFirst _ _ _ _⟩
  have key : ∀ (m : List (Segment k)) (m' : List (Segment k')),
      List.Forall₂ (fun (Δ : Segment k) (Δ' : Segment k') => RepRel i Δ.first Δ'.first ∧ Δ.len = Δ'.len) m m' →
      m' = m.map S := by
    intro m m' hm
    induction hm with
    | nil => rfl
    | @cons Δ Δ' _ _ h _ ih =>
      rw [List.map_cons, ih]
      exact congrArg (· :: _) (Segment.ext_first (by rw [hS1]; exact ((hT _ _).1 h.1).symm)
        (by rw [hS2]; exact h.2.symm))
  have hl' := key l l' hl
  have hprec : ∀ Δ Δ' : Segment k, (S Δ).Precedes (S Δ') → Δ.Precedes Δ' := by
    intro Δ Δ' h
    rw [Segment.precedes_iff, hS2, hS2, hS1, hS1] at h
    rw [Segment.precedes_iff]
    obtain ⟨j, h1, h2, h3, e⟩ := h
    exact ⟨j, h1, h2, h3, T.injective (by rw [hnu]; exact e)⟩
  have hseg : ∀ (Δ : Segment k) (y : IrrGL (k := k)), IsLSeg Δ y.rep → IsLSeg (S Δ) (T y).rep := by
    intro Δ y hy
    unfold IsLSeg at hy ⊢
    obtain ⟨hd, hc⟩ := hy
    have ht : ∀ a, T (Δ.term a) = (S Δ).term (Fin.cast (hS2 Δ).symm a) := fun a => by
      simp only [Segment.term, Fin.val_cast, hS1, hnu]
    have hd' : ∑ a, ((S Δ).term a).1 = (T y).1 := by
      rw [hTd, ← hd]
      refine Fintype.sum_equiv (finCongr (hS2 Δ)) _ _ fun a => ?_
      rw [← hTd (Δ.term _), ht]
      rfl
    exact ⟨hd', H y (T y) ((hT _ _).2 rfl) Δ.len (S Δ).len (hS2 Δ).symm Δ.term (S Δ).term hd hd'
      (fun a => (hT _ _).2 (ht a)) hc⟩
  obtain ⟨r, xs, hd, ⟨Δ, hord, hΔ⟩, hc⟩ := hL
  have hx' : T x = x' := (hT _ _).1 hx
  have hd' : ∑ a, (T (xs a)).1 = x'.1 := by
    rw [← hx', hTd, ← hd]
    exact Finset.sum_congr rfl fun a _ => hTd _
  refine ⟨r, fun a => T (xs a), hd', ⟨fun a => S (Δ a), ⟨?_, fun a b hab hp => hord.2 a b hab (hprec _ _ hp)⟩,
    fun a => hseg _ _ (hΔ a)⟩, H x x' hx r r rfl xs _ hd hd' (fun a => (hT _ _).2 rfl) hc⟩
  rw [hl', ← Multiset.map_coe, ← hord.1, Multiset.map_map]
  rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsDataTransportLocalFieldIsoStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLanglandsData_transport_localFieldIso : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (l : List (Segment k)) (l' : List (Segment k')) (x : IrrGL (k := k)) (x' : IrrGL (k := k')), List.Forall₂ (fun (Δ : Segment k) (Δ' : Segment k') => RepRel i Δ.first Δ'.first ∧ Δ.len = Δ'.len) l l' → RepRel i x x' → IsL (l : Multiset (Segment k)) x.rep → IsL (l' : Multiset (Segment k')) x'.rep := by
  first | exact @GlobalTheory.LocLanglands.isL_transport | exact GlobalTheory.LocLanglands.isL_transport | (intros; apply GlobalTheory.LocLanglands.isL_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CmPlaceOperatorPreservesTypeAveragesShape
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CmPlaceOperatorPreservesTypeAveragesShape
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit

open GlobalTheory.IdemSupport GlobalTheory.DownLift.GenFinite.Inert

section Op

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

def opP (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (c : WO S T →₀ ℂ) (h : GA D T) : Module.End ℂ (WO S T → ℂ) :=
  ∑ y ∈ c.support, c y • (GlobalTheory.SplitScalar.heisL ψ S T y * om (1, h))

theorem opP_apply (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (c : WO S T →₀ ℂ) (h : GA D T)
    (f : WO S T → ℂ) : opP ψ S T om c h f = comb ψ S T c (om (1, h) f) := by
  simp only [opP, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, GlobalTheory.SplitScalar.heisL_apply, comb,
    Finsupp.sum]

theorem opP_comm {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hpres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (om p f)) {e : AE D} {c : WO S T →₀ ℂ}
    (hc : ∀ y ∈ c.support, IsHalf e y) (h : GA D T) {B : Module.End ℂ (WO S T → ℂ)} (hB : CommAt ψ S T e B)
    (hBh : ∀ f, IsThetaFunO ψ S T f → B (om (1, h) f) = om (1, h) (B f)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    B (opP ψ S T om c h f) = opP ψ S T om c h (B f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [opP, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [GlobalTheory.SplitScalar.heisL_apply, GlobalTheory.SplitScalar.heisL_apply, (hB _ (hpres _ _ hf)).2 y (hc y hy), hBh f hf]

theorem fin_of_half {e : AE D} (he : infPart D e = 0) {y : WO S T} (hy : IsHalf e y) : y.map (infPart D) = 0 :=
  Matrix.ext fun a b => by
    rw [Matrix.map_apply, ← hy a b, RingHom.map_mul, he, zero_mul]
    rfl

theorem opP_theta {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hpres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (om p f)) (hψ : IsStdChar D ψ (-1)) {e : AE D}
    (he : infPart D e = 0) {c : WO S T →₀ ℂ} (hc : ∀ y ∈ c.support, IsHalf e y) (h : GA D T) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (opP ψ S T om c h f) := by
  rw [opP_apply, comb, Finsupp.sum]
  exact theta_sum _ _ f hf fun y hy =>
    theta_smul _ (GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (fin_of_half he (hc y hy)) (hpres _ _ hf))

end Op

end GlobalTheory.DownLift.GenSplit

namespace GlobalTheory.DownLift.GenSplit

open GlobalTheory.IdemSupport GlobalTheory.DownLift.GenFinite.Inert


set_option maxHeartbeats 800000 in
theorem placeOp_keep : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.thP_ωP → ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (FinPl D)) (v : FinPl D), v ∈ Sb → ∀ (h : GA D (Wc D i)), (∀ a b, idem D (.inl v) * (Formalism.L2.Theta.mt (Wc D i) h - 1) a b = (Formalism.L2.Theta.mt (Wc D i) h - 1) a b) → ∀ (c : WO (Vc D i) (Wc D i) →₀ ℂ), (∀ y ∈ c.support, IsHalf (idem D (.inl v)) y) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), TypeIn R i t Sb f → CleanIn R i t Sb f → LikeOff R i t Sb f → TypeIn R i t (dropPl Sb v) (comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h) f)) ∧ CleanIn R i t (dropPl Sb v) (comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h) f)) ∧ LikeOff R i t Sb (comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h) f)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hω i t Sb v hv h hh c hc f hT hCl hL
  have hW := hω i t
  obtain ⟨-, -, hcA, hfin, -⟩ := GlobalTheory.PlaceTensor.idem_spec D
  have hε := (hfin v).2.2
  have hεe := placeIdem_eq hε
  have hinf := (hfin v).1
  have hce := hcA (.inl v)
  have hpres := hW.om_pres

  have hk : ∀ κ : GA D (Vc D i), SuppIn (dropPl Sb v) (Vc D i) κ → ∀ φ, IsThetaFunO R.ψ (Vc D i) (Wc D i) φ →
      R.ωP i t (κ⁻¹, 1) (opP R.ψ _ _ (R.ωP i t) c h φ) = opP R.ψ _ _ (R.ωP i t) c h (R.ωP i t (κ⁻¹, 1) φ) ∧
      R.ωP i t (κ, 1) (opP R.ψ _ _ (R.ωP i t) c h φ) = opP R.ψ _ _ (R.ωP i t) c h (R.ωP i t (κ, 1) φ) := by
    intro κ hs φ hφ
    have h1 := suppF_of_drop hs hε
    rw [hεe] at h1
    have h2 := (suppGroup _ (1 - idem D (.inl v))).inv_mem h1
    have hcomm : ∀ k : GA D (Vc D i), ∀ ψ', R.ωP i t (k, 1) (R.ωP i t (1, h) ψ') = R.ωP i t (1, h) (R.ωP i t (k, 1) ψ') := by
      intro k ψ'
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, mul_one,
        one_mul, mul_one, one_mul]
    exact ⟨opP_comm hpres hc h (commAt_om hW h2) (fun ψ' _ => hcomm _ ψ') hφ,
      opP_comm hpres hc h (commAt_om hW h1) (fun ψ' _ => hcomm _ ψ') hφ⟩
  have hth := opP_theta hpres hW.std hinf hc h hT.1
  rw [← opP_apply]
  refine ⟨⟨hth, fun κ hκ hs => ?_⟩, fun PP a ha tr z hz hov κ hκ hsup => ?_, ⟨hth, fun c' hc' h0 => ?_⟩⟩
  · rw [(hk κ hs f hT.1).2, hT.2 κ hκ (suppIn_of_drop hs), map_smul]
  · obtain ⟨w, hw, how⟩ := hov
    have h0 := hCl PP a ha tr z hz ⟨w, (mem_dropPl.1 hw).2, how⟩ κ hκ fun g hg => suppIn_of_drop (hsup g hg)
    unfold avgW at h0 ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_zero (opP R.ψ _ _ (R.ωP i t) c h), ← h0, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hg : mirC R i PP a tr z g = 0
    · rw [hg, zero_mul, zero_smul, zero_smul, map_zero]
    · rw [map_smul, (hk (κ g) (hsup g hg) f hT.1).1]
  ·
    have hu : ∀ u ∈ c'.support, ∀ φ, IsThetaFunO R.ψ (Vc D i) (Wc D i) φ →
        heisO R.ψ _ _ u (opP R.ψ _ _ (R.ωP i t) c h φ) = opP R.ψ _ _ (R.ωP i t) c h (heisO R.ψ _ _ u φ) := by
      intro u hu φ hφ
      have hoff := hc' u hu
      have he0 : idem D (.inl v) • u = 0 := Matrix.ext fun a b => by
        rw [Matrix.smul_apply, smul_eq_mul, ← hεe]
        exact hoff.2 v hv _ hε a b
      have hact : actO (Vc D i) (Wc D i) 1 h u = u := by
        have hM : Formalism.L2.Theta.mt (Wc D i) h - 1 = idem D (.inl v) • (Formalism.L2.Theta.mt (Wc D i) h - 1) :=
          Matrix.ext fun a b => (hh a b).symm
        rw [actO, inv_one, mt_one, Matrix.mul_one]
        conv_lhs => rw [← sub_add_cancel (Formalism.L2.Theta.mt (Wc D i) h) 1]
        rw [Matrix.add_mul, Matrix.one_mul, hM, Matrix.smul_mul, ← Matrix.mul_smul, he0, Matrix.mul_zero, zero_add]
      have := opP_comm hpres hc h (commAt_heis hW.std hce hoff.1 he0)
        (fun ψ' hψ' => by rw [GlobalTheory.SplitScalar.heisL_apply, GlobalTheory.SplitScalar.heisL_apply, hW.om_heis _ _ _ _ hψ', hact]) hφ
      rwa [GlobalTheory.SplitScalar.heisL_apply, GlobalTheory.SplitScalar.heisL_apply] at this
    have h1 := hL.2 c' hc' h0
    rw [← map_zero (opP R.ψ _ _ (R.ωP i t) c h), ← h1, map_finsuppSum]
    refine Finset.sum_congr rfl fun u hu' => ?_
    dsimp only
    rw [map_smul, hu u hu' f hT.1]

end GlobalTheory.DownLift.GenSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CmPlaceOperatorPreservesTypeAveragesShapeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmPlaceOperator_preserves_type_averages_shape : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.thP_ωP → ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (FinPl D)) (v : FinPl D), v ∈ Sb → ∀ (h : GA D (Wc D i)), (∀ a b, idem D (.inl v) * (Formalism.L2.Theta.mt (Wc D i) h - 1) a b = (Formalism.L2.Theta.mt (Wc D i) h - 1) a b) → ∀ (c : WO (Vc D i) (Wc D i) →₀ ℂ), (∀ y ∈ c.support, IsHalf (idem D (.inl v)) y) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), TypeIn R i t Sb f → CleanIn R i t Sb f → LikeOff R i t Sb f → TypeIn R i t (dropPl Sb v) (comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h) f)) ∧ CleanIn R i t (dropPl Sb v) (comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h) f)) ∧ LikeOff R i t Sb (comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h) f)) := by
  first | exact @GlobalTheory.DownLift.GenSplit.placeOp_keep | exact GlobalTheory.DownLift.GenSplit.placeOp_keep | (intros; apply GlobalTheory.DownLift.GenSplit.placeOp_keep <;> assumption)
end
end
