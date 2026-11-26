module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiniteDimensionalSpan

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmQAdmissibleConjugatePairPlaces
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF Vc Wc)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
open Formalism.MainNotions.NAdm (TWSet AdmQ)
open GlobalTheory.UnivChar (IsUnivChar withUnivChar)
open Formalism.L2.Host (embLL0)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

namespace Setup

variable (ρ : Setup X) (i : X.Tw) (j : Fin D.R.m) (b : Bool)

structure IsHeckeDatum (k : ℕ) (P : Pl D.host.E) (α : GA D (Wc D j)) (R : Finset (GA D (Wc D j))) (z : (AE D)ˣ) : Prop where
  elt : Links.IsHeckeAt (Wc D j) P k α
  reps : Bridge.IsDC (ρ.levK i j b) α R
  det : IsDetAt (idemAt P) (Wc D j) α z

def hecke (k : ℕ) (P : Pl D.host.E) (R : Finset (GA D (Wc D j))) (z : (AE D)ˣ) :
    (GA D (Wc D j) → ℂ) →ₗ[ℂ] (GA D (Wc D j) → ℂ) :=
  ((((ρ.B i j b).mu z : Circle) : ℂ)⁻¹ * (((normV P : ℕ) : ℂ) ^ (k * ((Vc D j).rank / 2)))⁻¹) •
    ∑ γ ∈ R, LinearMap.funLeft ℂ ℂ fun x => x * γ

theorem hecke_apply (k : ℕ) (P : Pl D.host.E) (R : Finset (GA D (Wc D j))) (z : (AE D)ˣ) (F : GA D (Wc D j) → ℂ)
    (x : GA D (Wc D j)) : ρ.hecke i j b k P R z F x = (((ρ.B i j b).mu z : Circle) : ℂ)⁻¹ *
      (((normV P : ℕ) : ℂ) ^ (k * ((Vc D j).rank / 2)))⁻¹ * ∑ γ ∈ R, F (x * γ) := by
  simp only [hecke, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.funLeft_apply]

end Setup

section Hecke

variable {ρ : Setup X} {Y : NExp D.R D.host D.what₂ D.LL0 N X} {i : X.Tw} {j : Fin D.R.m} {b : Bool} (rd : Rd ρ Y i j b)

def HeckeAt (k : ℕ) (P : Pl D.host.E) (f g : Y.Fm i ((j : ℕ) + 1) b) : Prop :=
  ∀ α R z, ρ.IsHeckeDatum i j b k P α R z → rd g = ρ.hecke i j b k P R z (rd f)

def HeckeTie : Prop :=
  ∀ k P, HkIdx i k P → ∀ f, (∃ g, HeckeAt rd k P f g) → HeckeAt rd k P f (Y.hkF i _ b k P f)

def RatHecke : Prop := ∀ k P, HkIdx i k P → ∀ f, ∃ g, HeckeAt rd k P f g

variable {rd}

theorem heckeRead_iff : HeckeRead rd ↔ ∀ k P, HkIdx i k P → ∀ f, HeckeAt rd k P f (Y.hkF i _ b k P f) :=
  ⟨fun h k P hk f α R z d => funext fun x => (h k P hk α R z d.1 d.2 d.3 f x).trans (ρ.hecke_apply ..).symm,
    fun h k P hk α R z h1 h2 h3 f x => (congrFun (h k P hk f α R z ⟨h1, h2, h3⟩) x).trans (ρ.hecke_apply ..)⟩

theorem heckeRead_iff_tie : HeckeRead rd ↔ HeckeTie rd ∧ RatHecke rd := by
  rw [heckeRead_iff]
  exact ⟨fun h => ⟨fun k P hk f _ => h k P hk f, fun k P hk f => ⟨_, h k P hk f⟩⟩,
    fun h k P hk f => h.1 k P hk f (h.2 k P hk f)⟩

theorem HeckeTie.heckeRead (h : HeckeTie rd) (hR : RatHecke rd) : HeckeRead rd := heckeRead_iff_tie.2 ⟨h, hR⟩

theorem HeckeTie.eq (h : HeckeTie rd) (hinj : Function.Injective rd) {k P} (hk : HkIdx i k P) {α R z}
    (d : ρ.IsHeckeDatum i j b k P α R z) {f g : Y.Fm i ((j : ℕ) + 1) b} (hg : HeckeAt rd k P f g) : Y.hkF i _ b k P f = g :=
  hinj ((h k P hk f ⟨g, hg⟩ α R z d).trans (hg α R z d).symm)

theorem CellTie.injective_rdK {hρ : ρ.Good} (T : CellTie hρ Y rd) (k : ℕ) : Function.Injective (rdK rd hρ k) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨d⟩ := T.nonempty_dat
  have h := (T.thPsi_iff k ∅ 1 (twOK_one i k) d ((1 : X.Ok i k) ⊗ₜ[X.O i] Y.th i _ b d + x)).2 (by
    rw [map_add (f := _), hx, add_zero, rdK_tmul, map_one, one_smul, T.th_eq, Setup.gens_one]
    rfl)
  rw [Y.thPsi_one] at h
  exact add_eq_left.1 h

end Hecke

section Univ

theorem twSet_of_twOK {i : X.Tw} {k : ℕ} {Q : Finset (Pl D.host.E)} {ψ} (h : TwOK (X := X) i k Q ψ) : TWSet X i Q :=
  fun v hv => ⟨h.1 v hv, fun hl => Finset.disjoint_left.1 h.2.1 hv (X.twistExcludedPlaces_contains_residueChar i hl)⟩

variable {Y : NExp D.R D.host D.what₂ D.LL0 N X} (hY : IsUnivChar Y) {i : X.Tw} {Q : Finset (Pl D.host.E)} {M : ℕ}
include hY

theorem delU_off (hQ : TWSet X i Q) (σ : G D.host.E N.Om) (v : ↥Q) (hv : v.1 ∉ admissibleConjugatePairPlaces X i Q M) :
    Multiplicative.toAdd (Y.delU i Q M σ) v = 0 := by
  classical
  rw [hY, GalChar.delU_apply, GalChar.delCoord]
  split_ifs with h
  · rw [GalChar.delOf, dif_neg]
    · rfl
    rintro ⟨d, h1, h2, h3, h4, h5⟩
    obtain ⟨P', hc⟩ := GlobalTheory.TwistDet.exists_isConjPl v.1
    have hP' : P' ∈ Q := h (Or.inr hc)
    have key : ∀ P, GalChar.pair D.host P = GalChar.pair D.host v.1 →
        ∃ χ : G D.host.E N.Om →* Multiplicative (ZMod (X.l i ^ M)), IsOpen (χ.ker : Set (G D.host.E N.Om)) ∧ AntiHom X.cc χ ∧
        (∀ w ∈ placesOver D.host.E (X.l i), ∀ A : ValuationSubring N.Om, IsPlaceOver A w →
          ∀ σ ∈ Dec (F := D.host.E) A, χ σ = 1) ∧
        (∀ w : PlE D.host, w ≠ P → ¬ IsConjPl D.host P w → ∀ A : ValuationSubring N.Om, IsPlaceOver A w →
          ∀ σ ∈ Ine (F := D.host.E) A, χ σ = 1) ∧
        ∀ A : ValuationSubring N.Om, IsPlaceOver A P →
          Function.Surjective fun σ : Ine (F := D.host.E) A => Multiplicative.toAdd (χ σ) := fun P e =>
      ⟨d, h1, h2, h3, fun w a c => h4 w (e ▸ fun t => t.elim a c), fun A hA x => by
        obtain ⟨σ, hσ, hx⟩ := h5 P (e ▸ Or.inl rfl) A hA (Multiplicative.ofAdd x)
        exact ⟨⟨σ, hσ⟩, congrArg Multiplicative.toAdd hx⟩⟩
    refine hv (mem_admissibleConjugatePairPlaces_iff.2 ⟨v.2, P', hP', hc, fun w hw => ?_, fun w hw => ?_⟩)
    · rcases Finset.mem_insert.1 hw with rfl | hw
      · exact hQ _ v.2
      · exact Finset.mem_singleton.1 hw ▸ hQ _ hP'
    · rcases Finset.mem_insert.1 hw with rfl | hw
      · exact ⟨⟨P', by simp, hc⟩, key _ rfl⟩
      · obtain rfl := Finset.mem_singleton.1 hw
        exact ⟨⟨v.1, by simp, GalChar.isConjPl_symm hc⟩, key _ (GalChar.pair_eq hc)⟩
  · rfl

theorem delU_on (σ : G D.host.E N.Om) (v : ↥Q) (hv : v.1 ∈ admissibleConjugatePairPlaces X i Q M) :
    Multiplicative.toAdd (Y.delU i Q M σ) v =
      Multiplicative.toAdd (GalChar.delOf D.host X.cc (X.l i) M (GalChar.pair D.host v.1) σ) := by
  rw [hY, GalChar.delU_apply, GalChar.delCoord, if_pos]
  rintro w (rfl | hw)
  · exact v.2
  · exact admissibleConjugatePairPlaces_subset i Q M (conj_mem_admissibleConjugatePairPlaces hv hw)

theorem delU_eq_coord (hQ : TWSet X i Q) (σ : G D.host.E N.Om) (v : ↥Q) :
    Multiplicative.toAdd (Y.delU i Q M σ) v = Multiplicative.toAdd (coord Y i (admissibleConjugatePairPlaces X i Q M) M v.1 σ) := by
  by_cases hv : v.1 ∈ admissibleConjugatePairPlaces X i Q M
  · rw [delU_on hY σ v hv, coord_apply _ _ _ _ hv, hY, GalChar.delU_apply,
      GalChar.delCoord_of_closed _ _ _ (fun _ h _ hc => conj_mem_admissibleConjugatePairPlaces h hc) M hv]
  · rw [delU_off hY hQ σ v hv, coord, dif_neg hv]
    rfl

theorem delU_eq_spread (hQ : TWSet X i Q) {ch : Set (Pl D.host.E)} (hch : IsChoice ch) (σ : G D.host.E N.Om) :
    Multiplicative.toAdd (Y.delU i Q M σ) =
      spread Y i Q M ch fun P => Multiplicative.toAdd (coord Y i (admissibleConjugatePairPlaces X i Q M) M P.1 σ) :=
  funext fun v => (delU_eq_coord hY hQ σ v).trans (spread_coord Y i Q M hch σ v).symm

end Univ

section Full

variable {ρ : Setup X} (hρ : ρ.Good) {Y : NExp D.R D.host D.what₂ D.LL0 N X} (rd : Rds Y ρ)

structure FullTie : Type where

  tie : Comparison₂ hρ rd

  hecke : ∀ i j b, HeckeTie (rd i j b)

  univ : IsUnivChar Y

variable (hF : ∀ i j b, Faithful (rd i j b))


variable (hL : ρ.LatFG)

end Full

end GlobalTheory.SeriesTie

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
open Formalism.L2.Host (embLL0)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd)

structure RealPin (ρ : Setup D.ntw) : Prop where
  psi : ∀ i j b, (ρ.B i j b).F.ψ = Rl.ψ
  inf : ∀ i j b, (ρ.B i j b).F.θ = Rl.θ
  cartT : ∀ i j b, (ρ.B i j b).F.sT = cart (Rl.MW j (sg0 D A3.A))
  onbS : ∀ i j b τ, ((ρ.B i j b).F.BS τ).val = Rl.BV j τ
  onbT : ∀ i j b, (ρ.B i j b).F.BT = onb (Rl.MW j (sg0 D A3.A))
  latS : ∀ i j b, (ρ.B i j b).F.ΛS = Rl.ΛV j
  latT : ∀ i j b, (ρ.B i j b).F.ΛT = Rl.ΛW j
  frS : ∀ i j b, (ρ.B i j b).F.βS = Rl.βV j
  frT : ∀ i j b, (ρ.B i j b).F.βT = Rl.βW j
  vac : ∀ i j b, (ρ.B i j b).F.f₀ = Rl.vacP j
  Pg : ∀ i j b, (ρ.B i j b).G.Pg = Rl.Pg
  grp : ∀ i j b (g : G0g D.nd) (P : Pl D.host.E) (h : P ∈ (ρ.B i j b).G.Pg) (h' : P ∈ Rl.Pg) (a c : Fin (Wc D j).rank),
    (ρ.eG i j b g ⟨P, h⟩).val a c = (cG.symm g ⟨P, h'⟩).val (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c)
  mu0 : ∀ i j b, (ρ.B i j b).mu0 = Rl.mu0 ((j : ℕ) + 1)
  eta : ∀ i j b, (ρ.B i j b).eta = Rl.eta
  delta : ∀ i j b, ChrEq (ρ.B i j b).de.chi (Rl.C.delAt (D.ntw.l i))
  deltaPl : ∀ i t, ∀ P ∈ Rl.Q t, P ∈ D.ntw.pD i → P ∈ ρ.ch i
  ap : ∀ i j b τ, (ρ.B i j b).w.ap τ = aPl D j ((Wc D j).sig (tauE D τ)).1 τ
  am : ∀ i j b τ, (ρ.B i j b).w.am τ = aMi D j ((Wc D j).sig (tauE D τ)).1 ((Wc D j).sig (tauE D τ)).2 τ

variable {Rl cG} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)

def evW (j : Fin D.R.m) : S.WL ((j : ℕ) + 1) →+ (GA D (Wc D j) → ℂ) where
  toFun x := (Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e x)) (v₀ j _)
  map_zero' := by rw [map_zero, map_zero, map_zero]; rfl
  map_add' x y := by rw [map_add (f := _), map_add (f := _), map_add (f := _)]; rfl

theorem evW_smul (j : Fin D.R.m) (c : D.what₂.LL) (x : S.WL ((j : ℕ) + 1)) :
    evW YS v₀ j (c • x) = D.what₂.embLL c • evW YS v₀ j x := by
  change (Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e (c • x))) (v₀ j _) = _
  rw [map_smul, map_smulₛₗ, map_smul, show sg0 D A3.A c = D.what₂.embLL c from
    congrArg (fun f : D.what₂.LL →+* ℂ => f c) (sgAt_mk _ Rl.hv0)]
  rfl

section Read

variable {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

def evK : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1) →+ (GA D (Wc D j) → ℂ) :=
  TensorProduct.liftAddHom
    { toFun := fun a => (DistribSMul.toAddMonoidHom _ (ρ.e i b a)).comp
        ((evW YS v₀ j).comp (S.A ((j : ℕ) + 1)).WK.subtype.toAddMonoidHom)
      map_zero' := by ext; simp [show ρ.e i b (0 : NX.KB S i b) = 0 from map_zero _]
      map_add' := fun x y => by ext; simp [show ρ.e i b (x + y : NX.KB S i b) = ρ.e i b x + ρ.e i b y from map_add _ _ _, add_mul] }
    fun c a f => by
      change ρ.e i b (sideEmb D.ntw i b (S.kKs c) * (show FractionRing (D.ntw.O i) from a)) • evW YS v₀ j (Subtype.val f) =
        ρ.e i b a • evW YS v₀ j (c • Subtype.val f)
      rw [← algebraMap_smul D.what₂.LL c, evW_smul, map_mul, hρ.e_LL0, smul_smul, mul_comm, ← S.kKs_spec]
      rfl

theorem evK_tmul (a : NX.KB S i b) (f : NX.FmK S ((j : ℕ) + 1)) :
    evK YS v₀ hρ i j b (a ⊗ₜ f) = ρ.e i b a • evW YS v₀ j (Subtype.val f) := rfl

def realRd (ν : ℂ) : Rd ρ D.nexp i j b where
  toFun f := ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)
  map_add' f f' := by
    rw [map_add (f := _), ← smul_add]
    exact congrArg _ ((evK YS v₀ hρ i j b).map_add _ _)
  map_smul' c f := by
    rw [map_smul, smul_comm]
    congr 1
    generalize YS.eF i _ b (Nat.le_add_left _ _) j.2 f = x
    have key : ∀ (c : NX.KB S i b) (x : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)),
        evK YS v₀ hρ i j b (c • x) = ρ.e i b c • evK YS v₀ hρ i j b x := fun c x => by
      induction x using TensorProduct.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]
      | tmul a f =>
        rw [TensorProduct.smul_tmul', evK_tmul, evK_tmul, smul_smul]
        exact congrArg (· • _) (map_mul (ρ.e i b) c a)
    exact key c x

theorem realRd_tmul (ν : ℂ) (a : NX.KB S i b) (f : NX.FmK S ((j : ℕ) + 1)) :
    realRd YS v₀ hρ i j b ν ((YS.eF i _ b (Nat.le_add_left _ _) j.2).symm (a ⊗ₜ[S.Ks] f : NX.KB S i b ⊗[S.Ks] _)) =
      (ν⁻¹ * ρ.e i b a) • evW YS v₀ j (Subtype.val f) := by
  change ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b _ j.2 ((YS.eF i _ b _ j.2).symm _)) = _
  rw [mul_smul]
  exact congrArg (fun x => ν⁻¹ • evK YS v₀ hρ i j b x) ((YS.eF i _ b (Nat.le_add_left _ _) j.2).apply_symm_apply _)

theorem realRd_apply (ν : ℂ) (f : D.nexp.Fm i ((j : ℕ) + 1) b) :
    realRd YS v₀ hρ i j b ν f = ν⁻¹ • realRd YS v₀ hρ i j b 1 f := by
  change _ = ν⁻¹ • (1 : ℂ)⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)
  rw [inv_one, one_smul]
  rfl

end Read


variable (Rl) in
def IsScale {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) (c : ℂ) : Prop :=
  ∃ gramR c0R c0L, Bridge.FamTie Rl.B Rl.pl (Rl.Sb : Set (Pl D.host.E)) Rl.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
      (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L ∧
    ∃ u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ, (∀ τ, (u τ : (Rl.MW j (sg0 D A3.A)).sm τ) = v₀ j _ τ) ∧
      ∀ F : VV D.what₂.LL (FWT.lamV D j),
        harmFn (Wc D j).rank B.w B.F.BS (Rl.ioP j (PiTensorProduct.tprod ℂ u) (c0L j F)) =
          c • coefFn D.what₂.embLL (FWT.lamV D j) (F : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank)


variable (Rl) in
def IsNorm {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) (ν : ℂ) : Prop :=
  ν ≠ 0 ∧ ∃ c, IsScale Rl v₀ B c ∧ ∃ n : ℕ, n ≠ 0 ∧ ν ^ n = (cj (twAt D.what₂.embLL A3.A.v0) (Rl.phs j) * c) ^ n

theorem heckeAt_realRd {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) {ν : ℂ} (hν : ν ≠ 0) (k P f g) :
    HeckeAt (realRd YS v₀ hρ i j b ν) k P f g ↔ HeckeAt (realRd YS v₀ hρ i j b 1) k P f g := by
  refine forall₃_congr fun α R z => imp_congr_right fun _ => ?_
  rw [realRd_apply YS v₀ hρ i j b ν, realRd_apply YS v₀ hρ i j b ν f, map_smul]
  exact (smul_right_injective _ (inv_ne_zero hν)).eq_iff

def RatRow {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) : Prop :=
  ∃ ν, IsNorm Rl v₀ (ρ.B i j b) ν ∧ Rat hρ (realRd YS v₀ hρ i j b ν)

structure IsScalar {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ) : Prop where
  ne : ν ≠ 0
  norm : (∃ ν', IsNorm Rl v₀ (ρ.B i j b) ν') → IsNorm Rl v₀ (ρ.B i j b) ν
  rat : RatRow YS v₀ hρ i j b → Rat hρ (realRd YS v₀ hρ i j b ν)

theorem exists_isScalar {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) :
    ∃ ν, IsScalar YS v₀ hρ i j b ν := by
  by_cases h : RatRow YS v₀ hρ i j b
  · obtain ⟨ν, h1, h2⟩ := h
    exact ⟨ν, h1.1, fun _ => h1, fun _ => h2⟩
  · by_cases h' : ∃ ν', IsNorm Rl v₀ (ρ.B i j b) ν'
    · obtain ⟨ν, h1⟩ := h'
      exact ⟨ν, h1.1, fun _ => h1, fun h2 => absurd h2 h⟩
    · exact ⟨1, one_ne_zero, fun h1 => absurd h1 h', fun h2 => absurd h2 h⟩

structure ExportTie : Type 1 where

  ρ : Setup D.ntw
  good : ρ.Good
  pin : RealPin Rl cG ρ

  vec : ∀ j, FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _)

  ν : D.ntw.Tw → Fin D.R.m → Bool → ℂ
  scalar : ∀ i j b, IsScalar YS v₀ good i j b (ν i j b)

  tie : Comparison₂ good (Y := D.nexp) fun i j b => realRd YS v₀ good i j b (ν i j b)

  hecke : ∀ i j b, HeckeTie (realRd YS v₀ good i j b (ν i j b))

  univ : GlobalTheory.UnivChar.IsUnivChar D.nexp

namespace ExportTie

variable {YS v₀} (Z : ExportTie YS v₀)

abbrev rd : Rds D.nexp Z.ρ := fun i j b => realRd YS v₀ Z.good i j b (Z.ν i j b)

def full : FullTie Z.good Z.rd := ⟨Z.tie, Z.hecke, Z.univ⟩

theorem heckeRead {i j b} (h : RatHecke (Z.rd i j b)) : HeckeRead (Z.rd i j b) := (Z.hecke i j b).heckeRead h



theorem rat {i j b} (h : RatRow YS v₀ Z.good i j b) : Rat Z.good (Z.rd i j b) := (Z.scalar i j b).rat h


end ExportTie

end GlobalTheory.SeriesTie

end
