module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRowThetaModule
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesIntegralFormsEqSpanDedekindCoefRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientVanishesOffLevelGroupAtBadPrime

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPairThetaLowest
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

noncomputable section

namespace GlobalTheory.RefPair


set_option maxHeartbeats 1000000 in
theorem thetaPair_of_hasThetaAt (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (D : D7) {μt : D.what₂.Tup} {j : ℕ}
    (Mr : MtReal D μt j) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} (X : RowMod D rep j) (μ η : HChar D.host.E)
    (hΘ : HasThetaAt D Mr X μ η) (σ : D.what₂.FT) (S : Submodule ℂ (GAf D.host.E D.R.nV → Mr.wt.W))
    (hS : NG.IsIrrRep Mr.wt.ρ S)
    (hPair : ∃ y ∈ D.what₂.isot j σ, ∃ F ∈ (NG.isoTyp Mr.wt.ρ S).comap Mr.real, inner ℂ F (D.what₂.thetaT μt j y) ≠ 0)
    (s : SplitPlace D.host.E) (π : GlobalTheory.SmGL.IrrRep (GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E)))
    (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E)))
    (hπ : IsLocS (n := D.R.nV) S s π) (hτ : IsLocS (rep σ).S s τ) (hU : GlobalTheory.SmGL.IsUnitarisable τ.ρ) :
    GlobalTheory.ThetaGL.ThetaPair (μ.loc s.w) τ.ρ (GlobalTheory.SmGL.twist π.ρ (GlobalTheory.SmGL.detChar (Fin (D.R.r + D.R.t)) (η.loc s.w))) := by
  obtain ⟨Ω, _, _, ω, Λ, φ₀, hinv, hread, hloc⟩ := hΘ
  obtain ⟨f, hf, F, hF, hne⟩ := hPair
  have hFmem : Mr.real F ∈ NG.AFall D.host.E D.R.nV Mr.wt.ρ := by
    have : Mr.real F ∈ LinearMap.range Mr.real := LinearMap.mem_range_self _ _
    rw [Mr.real_range] at this
    exact this.1
  let Fp : ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ) := ⟨_, hFmem⟩
  let yp : ↥X.C := ⟨X.φ f, X.φ_mem f⟩
  have h0 : Λ φ₀ Fp yp ≠ 0 := by
    rw [← hread F f Fp rfl]
    intro h
    apply hne
    show inner ℂ F (LinearMap.adjoint (D.what₂.thetaP μt j) f) = 0
    rw [LinearMap.adjoint_inner_right, ← inner_conj_symm, h, map_zero]
  have hμc : IsComp μ s.w (μ.loc s.w) := ⟨GlobalTheory.HeckeComp.smooth_loc μ s.w, fun _ => rfl⟩
  have hηc : IsComp η s.w (η.loc s.w) := ⟨GlobalTheory.HeckeComp.smooth_loc η s.w, fun _ => rfl⟩
  have hl := hloc s _ _ hμc hηc
  let ℓ0 : Ω →+ ℂ := AddMonoidHom.mk' (fun φ => Λ φ Fp yp) (by intro a b; simp)
  obtain ⟨ι, φ1, hφ1, hℓ1⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup _ ℓ0 hl h0
  obtain ⟨hLin, φ2, ⟨Φ0, rfl⟩, hℓ2⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup _ ℓ0 hφ1 hℓ1
  obtain ⟨c, hc, hci, hιeq⟩ := hLin

  have hFiso : (Fp : GAf D.host.E D.R.nV → Mr.wt.W) ∈ NG.isoTyp Mr.wt.ρ S := hF
  have hspan := GlobalTheory.SpanLoc.main D.host.E D.R.nV Mr.wt S hS s π hπ c hc hci
  let ℓF : ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ) →+ ℂ :=
    AddMonoidHom.mk' (fun F' => Λ (ι Φ0) F' yp) (by intro a b; simp)
  obtain ⟨T1, F1, hF1, hℓF1⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub _ _
    (fun T => iSup_le fun hT1 => by rintro _ ⟨v, rfl⟩; exact hT1.1 v) ℓF Fp (hspan hFiso) hℓ2
  obtain ⟨hT1, F2, ⟨a0, ha0⟩, hℓF2⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub _ _
    (fun hT1 => by rintro _ ⟨v, rfl⟩; exact hT1.1 v) ℓF F1 hF1 hℓF1

  have hyI : (yp : X.A) ∈ Formalism.IndefR.principalLevelFrame.isotIn (D := D) X.ρ X.C (rep σ) := (X.isot σ f).1 hf
  unfold Formalism.IndefR.principalLevelFrame.isotIn at hyI
  let ℓy : ↥X.C →+ ℂ := (Λ (ι Φ0) F2).toAddMonoidHom
  obtain ⟨Φe, y1, hy1, hℓy1⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub X.C _
    (fun Φe => iSup_le fun h => h.2) ℓy yp hyI hℓF2
  obtain ⟨hΦe, y2, ⟨f2, hf2⟩, hℓy2⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub X.C _
    (fun h => h.2) ℓy y1 hy1 hℓy1
  have hΦC : ∀ g : ↥(rep σ).S, Φe g ∈ X.C := fun g => hΦe.2 (LinearMap.mem_range_self _ _)
  have hspan2 := GlobalTheory.FinTypSpanLoc.main D.host.E D.R.r (rep σ) s τ hτ c hc hci
  let ℓ2 : ↥(rep σ).S →+ ℂ :=
    AddMonoidHom.mk' (fun g => Λ (ι Φ0) F2 ⟨Φe g, hΦC g⟩) (by
      intro a b
      have e : (⟨Φe (a + b), hΦC (a + b)⟩ : ↥X.C) = ⟨Φe a, hΦC a⟩ + ⟨Φe b, hΦC b⟩ := by
        apply Subtype.ext; simp
      show Λ (ι Φ0) F2 ⟨Φe (a + b), hΦC (a + b)⟩ = Λ (ι Φ0) F2 ⟨Φe a, hΦC a⟩ + Λ (ι Φ0) F2 ⟨Φe b, hΦC b⟩
      rw [e, map_add (f := _)])
  have hℓ2f2 : ℓ2 f2 ≠ 0 := by
    have e : (⟨Φe f2, hΦC f2⟩ : ↥X.C) = y2 := Subtype.ext hf2
    show Λ (ι Φ0) F2 ⟨Φe f2, hΦC f2⟩ ≠ 0
    rw [e]; exact hℓy2
  obtain ⟨T2, g1, hg1, hℓg1⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub _ _
    (fun T => iSup_le fun hT2 => by rintro _ ⟨v, rfl⟩; exact hT2.1 v) ℓ2 f2 (hspan2 f2.2) hℓ2f2
  obtain ⟨hT2, g2, ⟨c0, hc0⟩, hℓg2⟩ := GlobalTheory.PairReadPf.exists_ne_of_mem_iSup_sub _ _
    (fun hT2 => by rintro _ ⟨v, rfl⟩; exact hT2.1 v) ℓ2 g1 hg1 hℓg1

  let T' : π.V →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ) := T1.codRestrict _ hT1.1
  let T'' : τ.V →ₗ[ℂ] ↥X.C := (Φe ∘ₗ T2.codRestrict _ hT2.1).codRestrict X.C (fun v => hΦC _)
  have hT'eq : ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → ∀ a,
      ((T' (π.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) a) :
        ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ)) : GAf D.host.E D.R.nV → Mr.wt.W) =
        NG.rt D.host.E D.R.nV x (T' a : GAf D.host.E D.R.nV → Mr.wt.W) :=
    fun x hx a => hT1.2 x hx a
  have hT''eq : ∀ x : GAf D.host.E D.R.r, TrivOutside {s.v} x → ∀ a,
      ((T'' (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r x)) a) : ↥X.C) : X.A) =
        X.ρ x (T'' a) := by
    intro x hx a
    have e : (⟨T2 (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r x)) a), hT2.1 _⟩ : ↥(rep σ).S) =
        ⟨NG.rt D.host.E D.R.r x (T2 a), (rep σ).stable x _ (hT2.1 a)⟩ := Subtype.ext (hT2.2 x hx a)
    show Φe ⟨_, _⟩ = X.ρ x (Φe ⟨T2 a, hT2.1 a⟩)
    rw [e]
    exact hΦe.1 x ⟨T2 a, hT2.1 a⟩
  let b := ((Λ ∘ₗ ι).compl₂ T').compr₂ (GlobalTheory.PairReadPf.precompₛ T'')
  have hb0 : b Φ0 a0 c0 ≠ 0 := by
    have e1 : T' a0 = F2 := Subtype.ext ha0
    have e2 : T'' c0 = ⟨Φe g2, hΦC g2⟩ := by
      apply Subtype.ext
      show Φe ⟨T2 c0, hT2.1 c0⟩ = Φe g2
      congr 1
      exact Subtype.ext hc0
    show Λ (ι Φ0) (T' a0) (T'' c0) ≠ 0
    rw [e1, e2]
    exact hℓg2
  refine GlobalTheory.ThetaRiesz.thetaPair_of_invariant_form _ D.R.r (D.R.r + D.R.t) _ _ (μ.loc s.w) τ.ρ
    (GlobalTheory.SmGL.twist π.ρ (GlobalTheory.SmGL.detChar (Fin (D.R.r + D.R.t)) (η.loc s.w)))
    ((hBZ _).1 (Fin D.R.r) _ _ τ.smooth τ.irr) hU (GlobalTheory.HeckeComp.smooth_loc μ s.w) b
    (fun h => hb0 (by rw [h]; rfl)) ?_
  intro g h Φ Φ' hΦ' a c'
  obtain ⟨xh, hxh, exh⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.nV s
    (Matrix.GeneralLinearGroup.map c.symm.toRingHom h)
  obtain ⟨xg, hxg, exg⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.r s
    (Matrix.GeneralLinearGroup.map c.symm.toRingHom g)
  have back : ∀ (n : ℕ) (A : GL (Fin n) (s.w.adicCompletion D.host.E)),
      Matrix.GeneralLinearGroup.map c.toRingHom (Matrix.GeneralLinearGroup.map c.symm.toRingHom A) = A := by
    intro n A
    ext k l
    simp
  have eh : (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV xh) :
      GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E)) = h := by rw [exh]; exact back _ h
  have eg : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r xg) = g := by rw [exg]; exact back _ g
  subst eh eg
  have hω := hιeq xh xg hxh hxg Φ Φ' hΦ'
  have key := hinv xh xg (ι Φ) (T' a) (T' (π.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV xh)) a))
    (T'' c') (T'' (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r xg)) c'))
    (hT'eq xh hxh a) (hT''eq xg hxg c')
  rw [hω] at key
  show Λ (ι Φ') (T' (GlobalTheory.SmGL.twist π.ρ (GlobalTheory.SmGL.detChar (Fin (D.R.r + D.R.t)) (η.loc s.w)) _ a)) (T'' (τ.ρ _ c')) =
    Λ (ι Φ) (T' a) (T'' c')
  rw [twist_apply, detChar_apply, map_smul, LinearMap.map_smul, LinearMap.smul_apply]
  rw [LinearMap.map_smul, LinearMap.smul_apply, LinearMap.smul_apply] at key
  exact key

end GlobalTheory.RefPair

namespace GlobalTheory.RefPair

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin


end GlobalTheory.RefPair

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteFormReadingInjectiveLatticeIntegralForms
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteFormReadingInjectiveLatticeIntegralForms
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

noncomputable section

namespace GlobalTheory.PlaceExp

section Alg

variable {R K E V A : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] [Field E] [Algebra R E]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] [AddCommGroup A] [Module ℂ A]

theorem span_one_tmul (hE : Function.Injective (algebraMap R E)) {I : Type} (v : I → V)
    (hv : Submodule.span K (Set.range v) = ⊤) :
    Submodule.span E (Set.range fun i => ((1 : E) ⊗ₜ[R] v i : E ⊗[R] V)) = ⊤ := by
  have key : ∀ f : V, ((1 : E) ⊗ₜ[R] f : E ⊗[R] V) ∈
      Submodule.span E (Set.range fun i => ((1 : E) ⊗ₜ[R] v i : E ⊗[R] V)) := fun f => by
    have hf : f ∈ Submodule.span K (Set.range v) := hv ▸ Submodule.mem_top
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => rw [TensorProduct.tmul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add]; exact add_mem hx hy
    | smul a x _ hx =>
      obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := R) a
      have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
      have hqK : algebraMap R K q ≠ 0 := by simpa using hq0
      have hqE : algebraMap R E q ≠ 0 := fun h => hq0 (hE (h.trans (map_zero _).symm))
      rw [← Submodule.smul_mem_iff _ hqE, algebraMap_smul, ← TensorProduct.tmul_smul, ← algebraMap_smul K q, smul_smul,
        mul_div_cancel₀ _ hqK, algebraMap_smul, TensorProduct.tmul_smul, ← algebraMap_smul E p]
      exact Submodule.smul_mem _ _ hx
  refine Submodule.eq_top_iff'.2 fun y => ?_
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => exact add_mem hx hy
  | tmul a f =>
    have : (a ⊗ₜ[R] f : E ⊗[R] V) = a • ((1 : E) ⊗ₜ[R] f) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (key f)

theorem injective_of_indep {W : Type} [AddCommGroup W] [Module E W] {ε : E →+* ℂ} (φ : W →ₛₗ[ε] A) {I : Type} (u : I → W)
    (hu : Submodule.span E (Set.range u) = ⊤) (hi : LinearIndependent ℂ fun i => φ (u i)) : Function.Injective φ := by
  refine (injective_iff_map_eq_zero φ).2 fun y hy => ?_
  have hy' : y ∈ Submodule.span E (Set.range u) := hu ▸ Submodule.mem_top
  obtain ⟨l, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hy'
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finsupp.sum, map_sum] at hy
  simp only [map_smulₛₗ] at hy
  have h := linearIndependent_iff'.1 hi _ _ hy
  refine Finset.sum_eq_zero fun i hi' => ?_
  have : l i = 0 := ε.injective ((h i hi').trans (map_zero _).symm)
  simp only [this, zero_smul]

theorem indep_fieldRange {e : K →+* ℂ} (g : V →ₛₗ[e] A) (hg : Function.Injective g) {I : Type} {v : I → V}
    (hv : LinearIndependent K v) : LinearIndependent e.fieldRange fun i => g (v i) := by
  refine linearIndependent_iff'.2 fun t c h i hi => ?_
  choose d hd using fun i => RingHom.mem_fieldRange.1 (c i).2
  have h1 : g (∑ i ∈ t, d i • v i) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ, hd]
    rfl
  have h2 := linearIndependent_iff'.1 hv _ _ (hg (h1.trans (map_zero _).symm)) i hi
  exact Subtype.ext ((hd i).symm.trans (by rw [h2, map_zero]; rfl))

end Alg

theorem rdE_injective_lattice : ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (ρ : Setup D.ntw) (hρ : ρ.Good) (j : Fin D.R.m) (rd : Rd ρ D.nexp (c.twI w) j (c.sd w)) (T : CellTie hρ D.nexp rd) (ε : KE c w →+* ℂ) (hε : Extends ρ ε), TwOK (c.twI w) (c.k' w) (c.Q w) (chr c w) → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) →
  Function.Injective (rdE T hε) ∧ ∀ F : Amb D j, F ∈ (ρ.B (c.twI w) j (c.sd w)).mtLat (embLL0 D) (labLL0 D) (ringOf ε) (twVia ρ ε) ↔ ∃ y ∈ latT c w (j.1 + 1), rdE T hε y = F := by
  intro D c w ρ hρ j rd T ε hε hok hr
  refine ⟨?_, ?_⟩
  · obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent (FractionRing (D.ntw.Ok (c.twI w) (c.k' w)))
      (D.nexp.MtLat (c.twI w) (j.1 + 1) (c.sd w) (c.k' w) (c.Q w) (chr c w) :
        Set (D.nexp.MtV (c.twI w) (j.1 + 1) (c.sd w) (c.k' w) (c.Q w) (chr c w)))
    rw [D.nexp.MtLat_span] at hspan
    have hE : Function.Injective (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (KE c w)) := fun a b h =>
      ρ.eOk_injective (c.twI w) (c.sd w) (c.k' w) (by rw [← hε.apply, ← hε.apply, h])
    refine injective_of_indep (rdE T hε) _ (span_one_tmul (K := FractionRing (D.ntw.Ok (c.twI w) (c.k' w))) hE
      (Subtype.val : s → _) (by rw [Subtype.range_coe]; exact hspan)) ?_
    have h1 := indep_fieldRange _ (T.rdV_inj _ _ _ hok) hli
    have h2 := GlobalTheory.T.linearIndependent_complex_of_subfield_coeffLattice D _ _ _ (hρ.base (c.twI w) j (c.sd w)) _ _ _ _ (hρ.isCoefRing_k (c.twI w) (c.sd w) (c.k' w))
      (ρ.ek (c.twI w) (c.sd w) (c.k' w)).fieldRange (by rintro _ ⟨x, rfl⟩; exact ⟨_, rfl⟩) _ _
      (fun a h => ((Base.mem_mtLat _ _ _ _).1 ((T.rdV_mem hok).1 (hs a.2))).2 h) h1
    simpa only [rdE_tmul, map_one, one_smul] using h2
  · obtain ⟨hg, hadm, -⟩ := GlobalTheory.TwistGood.tw_good D _ _ ρ hρ (c.twI w) j (c.sd w) _ _ _ hok
    have hle : (ρ.eOk (c.twI w) (c.sd w) (c.k' w)).range ≤ ringOf ε := by
      rintro _ ⟨x, rfl⟩
      refine ⟨algebraMap _ _ x, ?_⟩
      rw [← hε.apply, IsScalarTower.algebraMap_apply (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w) (KE c w)]
      rfl
    have hbc := GlobalTheory.T.thetaSeriesIntegralForms_eq_span_dedekindCoefRing D _ _ _ (hρ.base (c.twI w) j (c.sd w)) _ hg hadm _ _ _ _ _
      (ρ.eOk_injective (c.twI w) (c.sd w) (c.k' w)) (hρ.isCoefRing_k (c.twI w) (c.sd w) (c.k' w))
      (levLam_mem_eOk hr T hok) _ hle
    have hsm : ∀ (a : c.Oe w) (y : Tgt c w (j.1 + 1)), rdE T hε (a • y) = ε (algebraMap _ _ a) • rdE T hε y := fun a y => by
      rw [← algebraMap_smul (KE c w) a y, map_smulₛₗ]
    intro F
    rw [hε.twVia_eq, hbc]
    constructor
    · intro hF
      induction hF using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, hf, rfl⟩ := (T.mtLat_iff _ _ _ hok x).1 hx
        refine ⟨_, Submodule.subset_span ⟨f, hf, rfl⟩, ?_⟩
        rw [TensorProduct.mk_apply, rdE_tmul, map_one, one_smul]
      | zero => exact ⟨0, zero_mem _, map_zero _⟩
      | add x y _ _ hx hy =>
        obtain ⟨x', hx, rfl⟩ := hx
        obtain ⟨y', hy, rfl⟩ := hy
        exact ⟨x' + y', add_mem hx hy, map_add _ _ _⟩
      | smul a x _ hx =>
        obtain ⟨x', hx, rfl⟩ := hx
        obtain ⟨_, a, rfl⟩ := a
        exact ⟨a • x', Submodule.smul_mem _ _ hx, hsm a x'⟩
    · rintro ⟨y, hy, rfl⟩
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, hf, rfl⟩ := hx
        rw [TensorProduct.mk_apply, rdE_tmul, map_one, one_smul]
        exact Submodule.subset_span ((T.rdV_mem hok).1 hf)
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x _ hx =>
        rw [hsm]
        exact Submodule.smul_mem _ (⟨ε (algebraMap _ _ a), a, rfl⟩ : ringOf ε) hx

end GlobalTheory.PlaceExp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteFormReadingInjectiveLatticeIntegralFormsStatement
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteFormReading_injective_lattice_integralForms : ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (ρ : Setup D.ntw) (hρ : ρ.Good) (j : Fin D.R.m) (rd : Rd ρ D.nexp (c.twI w) j (c.sd w)) (T : CellTie hρ D.nexp rd) (ε : KE c w →+* ℂ) (hε : Extends ρ ε), TwOK (c.twI w) (c.k' w) (c.Q w) (chr c w) → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) →
  Function.Injective (rdE T hε) ∧ ∀ F : Amb D j, F ∈ (ρ.B (c.twI w) j (c.sd w)).mtLat (embLL0 D) (labLL0 D) (ringOf ε) (twVia ρ ε) ↔ ∃ y ∈ latT c w (j.1 + 1), rdE T hε y = F := by
  first | exact @GlobalTheory.PlaceExp.rdE_injective_lattice | exact GlobalTheory.PlaceExp.rdE_injective_lattice | (intros; apply GlobalTheory.PlaceExp.rdE_injective_lattice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivAtOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixCoeffFinitePlaceOffLevelConstMul
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixCoeffFinitePlaceOffLevelConstMul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.GoodFactor

theorem mt_mul' {D : D7} (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := by
  unfold Formalism.L2.Theta.mt
  rw [map_mul, Units.val_mul]

theorem mt_one' {D : D7} (V : HSp D) : mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [map_one, Units.val_one]

theorem mt_inj {D : D7} (V : HSp D) {a b : GA D V} (h : mt V a = mt V b) : a = b :=
  Subtype.val_injective (Units.ext h)

theorem comm_of_supp_triv {D : D7} {V : HSp D} {f : AE D} {a b : GA D V} (ha : SuppF V f a) (hb : TrivAt V f b) :
    a * b = b * a := by
  apply mt_inj
  have hAB : (mt V a - 1) * (mt V b - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← ha i l, mul_assoc, mul_left_comm, hb l j, mul_zero]
  have hBA : (mt V b - 1) * (mt V a - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← ha l j, mul_left_comm, ← mul_assoc, hb i l, zero_mul]
  have e1 : mt V a * mt V b = (mt V a - 1) * (mt V b - 1) + mt V a + mt V b - 1 := by noncomm_ring
  have e2 : mt V b * mt V a = (mt V b - 1) * (mt V a - 1) + mt V b + mt V a - 1 := by noncomm_ring
  rw [mt_mul', mt_mul', e1, e2, hAB, hBA, zero_add, zero_add, add_comm (mt V a)]

theorem actO_one_of_trivAt {D : D7} {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {v : HeightOneSpectrum (𝓞 D.host.F)} {f : AE D} (hf : IsFinIdem D v f) {γ : GA D T} (hγ : TrivAt T f γ)
    {u : WO S T} (hu : u ∈ latO S T LS LT fun w => w = v) : actO S T 1 γ u = u := by
  obtain ⟨ε, hε, rfl⟩ := hf
  have hu' := GlobalTheory.VecInvInert.idem_smul_eq hε hu
  have hz : algebraMap (AF D.host.F) (AE D) ε • (mt T γ - 1) = 0 := by
    ext a b
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    exact hγ a b
  have h0 : HMul.hMul (mt T γ - 1) (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = (0 : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
    rw [← hu', Matrix.mul_smul, ← Matrix.smul_mul, hz, Matrix.zero_mul]
  unfold actO
  rw [inv_one, mt_one', Matrix.mul_one]
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h0
  exact h0

theorem vacFin_om_trivAt {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {f : AE D} (hf : IsFinIdem D v f) {γ : GA D T} (hγ : TrivAt T f γ)
    {x : WO S T → ℂ} (hx : GlobalTheory.FinZeta.VacFin ψ S T v x) : GlobalTheory.FinZeta.VacFin ψ S T v (om (1, γ) x) := by
  obtain ⟨hth, hl1, hl2⟩ := hx
  refine ⟨hW.om_pres _ _ hth, fun u hu => ?_, fun e he u hu hh => ?_⟩
  · rw [← actO_one_of_trivAt hf hγ (nsmul_mem hu 2), ← hW.om_heis 1 γ _ x hth, hl1 u hu]
  · rw [← actO_one_of_trivAt hf hγ hu, ← hW.om_heis 1 γ _ x hth, hl2 e he u hu hh]

theorem thetaInner_eq_star_l2 {D : D7} {S T' : HSp D} (μ : Measure (WO S T')) (𝓕 : Set (WO S T')) (x y : WO S T' → ℂ) :
    thetaIP μ 𝓕 x y = star (GlobalTheory.AdelicScalar.l2 μ 𝓕 x y) := by
  unfold thetaIP GlobalTheory.AdelicScalar.l2 Formalism.IndefR.Lift.pet
  show _ = (starRingEnd ℂ) _
  rw [← integral_conj]
  congr 1; funext w
  simp [mul_comm]

theorem finmult_good : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v f, IsFinIdem D v f → (∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f) → ∀ k, SuppF (Wc D i) f k → ∃ c : ℂ, ∀ γ ∈ GfC (Wc D i), TrivAt (Wc D i) f γ → thetaIP μ 𝓕 (R.ωP i t (1, γ * k) (R.vP i t)) (R.vP i t) = c * thetaIP μ 𝓕 (R.ωP i t (1, γ) (R.vP i t)) (R.vP i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL _ i t μ 𝓕 hμ v f hf hoff k hk
  obtain ⟨a, rfl⟩ := GlobalTheory.T.exists_local_preimage_of_supportedAtPlace D (Wc D i) v f hf k hk
  have hW := hL.thP.ωP i t
  have hvac := GlobalTheory.T.pairFixedVector_latticeVacuum_offLevels D G Pl0 T A Ks R F hL i t v f hf hoff
  have hunr := GlobalTheory.T.weilDatumCharacters_unramified_offLevels D G Pl0 T A Ks R F hL i t v f hf hoff
  obtain ⟨φ, -, hc⟩ := GlobalTheory.VacCoef.vac_coef D R.ψ (Vc D i) (Wc D i) _ _ (R.ωP i t) hW μ 𝓕 hμ v hunr
  refine ⟨star (φ a), fun γ _ hγ => ?_⟩
  have hcomm := comm_of_supp_triv hk hγ
  have hv' := vacFin_om_trivAt hW hf hγ hvac
  have e : R.ωP i t (1, γ * GlobalTheory.FinZeta.embV (Wc D i) v a) (R.vP i t) =
      R.ωP i t (1, GlobalTheory.FinZeta.embV (Wc D i) v a) (R.ωP i t (1, γ) (R.vP i t)) := by
    rw [← hcomm]
    show _ = (R.ωP i t (1, _) * R.ωP i t (1, γ)) (R.vP i t)
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  rw [e, thetaInner_eq_star_l2, thetaInner_eq_star_l2 μ 𝓕 (R.ωP i t (1, γ) (R.vP i t)), hc a _ _ hv' hvac, star_mul']

end GlobalTheory.RawLift.GoodFactor

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixCoeffFinitePlaceOffLevelConstMulStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixCoeff_finitePlace_offLevel_const_mul : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v f, IsFinIdem D v f → (∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f) → ∀ k, SuppF (Wc D i) f k → ∃ c : ℂ, ∀ γ ∈ GfC (Wc D i), TrivAt (Wc D i) f γ → thetaIP μ 𝓕 (R.ωP i t (1, γ * k) (R.vP i t)) (R.vP i t) = c * thetaIP μ 𝓕 (R.ωP i t (1, γ) (R.vP i t)) (R.vP i t) := by
  first | exact @GlobalTheory.RawLift.GoodFactor.finmult_good | exact GlobalTheory.RawLift.GoodFactor.finmult_good | (intros; apply GlobalTheory.RawLift.GoodFactor.finmult_good <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.LocalFactor

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem pureTensor_one (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : R.ptP i t 1 = R.vP i t := by
  unfold RealDat.ptP pureTensorO pureTensorL
  have : (1 : MvPolynomial (FVar D (Wc D i).rank (Vc D i).rank) ℂ) = MvPolynomial.basisMonomials _ ℂ 0 := by
    simp
  rw [this, Module.Basis.constr_basis]
  simp [opPow]

theorem trivAt_one (V : HSp D) (f : AE D) : TrivAt V f 1 := by
  have : Formalism.L2.Theta.mt V 1 = 1 := rfl
  intro a b
  simp [this]

theorem finMult : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    Laws R F → R.FullP → ∀ i t, FinMult R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t μ 𝓕 hμ v f hf γ hγ hγt k hk
  have hmul : ∀ g : GA D (Wc D i),
      R.ωP i t (1, g * k) (R.vP i t) = R.ωP i t (1, g) (R.ωP i t (1, k) (R.vP i t)) := by
    intro g
    have e : ((1 : GA D (Vc D i)), g * k) = (1, g) * (1, k) := by simp
    rw [e, map_mul, Module.End.mul_apply]
  have hone : R.ωP i t (1, 1) = 1 := map_one _
  unfold coef
  by_cases hbad : ∃ P, (P ∈ R.Pg ∨ P ∈ R.Q t) ∧ ∃ e, IsPrimeIdem P e f
  · obtain ⟨P, hP, e, he⟩ := hbad
    by_cases hkl : k ∈ levW R i
    · have hfix : R.ωP i t (1, k) (R.vP i t) = R.vP i t := by
        have := GlobalTheory.T.coeffSpaceLevel_fixes_fockVectors D G Pl0 T A Ks R F hL hF i t k hkl 1
        rwa [pureTensor_one] at this
      rw [hmul γ, hfix]
      by_cases hN : thetaIP μ 𝓕 (R.vP i t) (R.vP i t) = 0
      · simp [hN]
      · rw [div_self hN, mul_one]
    · have h0 := GlobalTheory.T.coefficient_vanishes_off_level_group_at_bad_prime D G Pl0 T A Ks R F hL hF i t μ 𝓕 hμ P hP e f he γ hγ hγt k hk hkl
      have h1 := GlobalTheory.T.coefficient_vanishes_off_level_group_at_bad_prime D G Pl0 T A Ks R F hL hF i t μ 𝓕 hμ P hP e f he 1 (one_mem _) (trivAt_one _ f) k hk hkl
      rw [one_mul] at h1
      rw [h0, h1]
      simp
  · have hgood : ∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f :=
      fun P hP e f' he hff => hbad ⟨P, hP, e, hff ▸ he⟩
    obtain ⟨c, hc⟩ := GlobalTheory.T.matrixCoeff_finitePlace_offLevel_const_mul D G Pl0 T A Ks R F hL hF i t μ 𝓕 hμ v f hf hgood k hk
    have h1 := hc 1 (one_mem _) (trivAt_one _ f)
    rw [one_mul, hone, Module.End.one_apply] at h1
    rw [hc γ hγ hγt, h1]
    by_cases hN : thetaIP μ 𝓕 (R.vP i t) (R.vP i t) = 0
    · simp [hN]
    · field_simp

end GlobalTheory.RawLift.LocalFactor

end
end
