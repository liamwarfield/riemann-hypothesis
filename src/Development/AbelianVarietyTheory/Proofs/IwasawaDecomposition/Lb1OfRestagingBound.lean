module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeSameMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameCharacterParahoricInvariant
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TieMove
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtremalVectorMemLowestKType
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesAtThetaTwist

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsExtremalVectorOfRealSideBaseChange
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs.Move

theorem isExtremalVector_of_realSideBaseChange : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι), (∀ j, FWT.IsChosenExtremalVector X.R.toRealDat j (sg0 D X.A3.A) (X.geo.v₀ j _)) →
    ∀ j, FWT.IsChosenExtremalVector X'.R.toRealDat j (sg0 D' X'.A3.A) (X'.geo.v₀ j _) := by
  intro D D' ι e h X X' m _ j
  exact X'.geo.fw.hv₀ j _

end GlobalTheory.TwInputs.Move
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingRelationTransferIdentity
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnivCharCopy

theorem ring_relation_transfer_identity {R R' : Formalism.BasicNotions.Ranks} {H : Formalism.BasicNotions.Host R} {H' : Formalism.BasicNotions.Host R'} {Ω Ω' : Type}
    [iΩ : Field Ω] [iΩ' : Field Ω'] [aΩ : Algebra H.E Ω] [aΩ' : Algebra H'.E Ω'] {T T' : Type}
    {cc : Ω ≃+* Ω} {cc' : Ω' ≃+* Ω'} {l : T → ℕ} {l' : T' → ℕ}
    {d : ∀ i (Q : Finset (PlE H)) (M : ℕ), G H.E Ω →* Multiplicative (DelQM H (l i) Q M)}
    {d' : ∀ i (Q : Finset (PlE H')) (M : ℕ), G H'.E Ω' →* Multiplicative (DelQM H' (l' i) Q M)}
    (hR : R = R') (hH : HEq H H') (hΩ : Ω = Ω') (hi : HEq iΩ iΩ') (ha : HEq aΩ aΩ') (hcc : HEq cc cc')
    (hT : T = T') (hl : HEq l l') (hd : HEq d d')
    (h : ∀ i Q M, d i Q M = GlobalTheory.GalChar.delU H cc (l i) Q M) :
    ∀ i Q M, d' i Q M = GlobalTheory.GalChar.delU H' cc' (l' i) Q M := by
  subst hR; cases hH; subst hΩ; cases hi; cases ha; cases hcc; subst hT; cases hl; cases hd
  exact h

theorem isUnivChar_copy : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e), GlobalTheory.UnivChar.IsUnivChar D.nexp → GlobalTheory.UnivChar.IsUnivChar D'.nexp := by
  intro D D' ι e h hU
  exact ring_relation_transfer_identity h.gal.R h.gal.host (eq_of_heq h.gal.Om) h.gal.instOm h.gal.algOm h.set.cc
    (eq_of_heq h.set.Tw) h.set.l h.delU hU

end GlobalTheory.UnivCharCopy

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExportTieMove
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeepsMatHeqRefl
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadingInjective
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2 (NExpTied)
open Formalism.AUTREP (GAf)
open GlobalTheory.HeightCounting GlobalTheory.HeightCounting.SideCopy GlobalTheory.TwInputs.Move.Forms

namespace GlobalTheory.HeightCounting.SerCarry

variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

def HkAd (X : RealSide D) (Sb : Finset (PlE D.host))
    (hL : ∀ j : ℕ, ℕ → PlE D.host → Module.End D.what₂.LL (Fin (X.R.nW (NX.idxOf D j)) → D.what₂.LL)) : Prop :=
  ∀ j k P α Rr, 1 ≤ j → j ≤ D.R.m → HkDat X.R Sb (NX.idxOf D j) k P α Rr → ∀ x,
    evidence X (NX.idxOf D j) (hL j k P x) =
      hkNorm X.R (NX.idxOf D j) k P • Mult.heckeOn (model X (NX.idxOf D j)) Rr (evidence X (NX.idxOf D j) x)

def HkLaw (D : D7) (S : NX.RatDat D.ntw)
    (eF : ∀ i j b, 1 ≤ j → j ≤ D.R.m → D.nexp.Fm i j b ≃ₗ[FractionRing (D.ntw.O i)] NX.Fm S i j b)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (hs : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ k P (x : S.WL j), x ∈ (S.A j).WK → hL j k P x ∈ (S.A j).WK)
    (c : ∀ (i : D.ntw.Tw) (_b : Bool) (_P : PlE D.host), (D.ntw.O i)ˣ) : Prop :=
  ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (k : ℕ) (P : PlE D.host) (x : D.nexp.Fm i j b), P ∉ D.ntw.S0 i →
    IsSplitPl D.host P → k ≤ D.R.r → eF i j b h1 h2 (D.nexp.hkF i j b k P x) =
      algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (c i b P) ^ k • hkF D S i j b (hL j) (hs j h1 h2) k P (eF i j b h1 h2 x)

def LowIn (D : D7) : Prop := ∀ i, ∀ p ∈ lowAll D, placesOver D.host.E p ⊆ ↑(D.ntw.S0 i)

theorem HkAd.at {X : RealSide D} {Sb hL} (H : HkAd X Sb hL) (j : Fin D.R.m)
    (f : (Fin (X.R.nW (NX.idxOf D ((j : ℕ) + 1))) → D.what₂.LL) → Fin (X.R.nW j) → D.what₂.LL) (hf : ∀ x, HEq (f x) x)
    {k P α Rr} (hd : HkDat X.R Sb j k P α Rr) (x) :
    evidence X j (f (hL ((j : ℕ) + 1) k P x)) = hkNorm X.R j k P • Mult.heckeOn (model X j) Rr (evidence X j (f x)) := by
  have key : ∀ (a : Fin D.R.m), a = j → ∀ (u : (Fin (X.R.nW a) → D.what₂.LL) → Fin (X.R.nW a) → D.what₂.LL)
      (f : (Fin (X.R.nW a) → D.what₂.LL) → Fin (X.R.nW j) → D.what₂.LL), (∀ x, HEq (f x) x) →
      (∀ α Rr, HkDat X.R Sb a k P α Rr → ∀ x, evidence X a (u x) = hkNorm X.R a k P • Mult.heckeOn (model X a) Rr (evidence X a x)) →
      ∀ x, evidence X j (f (u x)) = hkNorm X.R j k P • Mult.heckeOn (model X j) Rr (evidence X j (f x)) := by
    intro a haj
    subst haj
    intro u f hf hu x
    rw [eq_of_heq (hf _), eq_of_heq (hf _)]
    exact hu α Rr hd x
  exact key _ (NX.idxOf_succ D j) _ f hf (fun α Rr hd => H _ k P α Rr (Nat.le_add_left _ _) j.2 hd) x

theorem reading_injective (X : RealSide D) (j : Fin D.R.m) : Function.Injective (evidence X j) := by
  refine (X.char.models.HW j _).1.comp ((injective_iff_map_eq_zero _).2 fun x hx => by_contra fun h0 => ?_)
  exact ((X.unif j (sg0 D X.A3.A)).1 1 (fun _ => x) (linearIndependent_unique_iff.2 h0)).ne_zero 0 hx

theorem fiOfEq_heq (X : RealSide D) {a b : Fin D.R.m} (hab : a = b) (x) : HEq ((fiOfEq X hab).e x) x := by
  subst hab; rfl

theorem exists_hkDat (X : RealSide D) (hl : LowIn D) {Sb} (hSb : OverSet D Sb (lowAll D)) {i : D.ntw.Tw} {v : PlE D.host}
    (hv : v ∉ D.ntw.S0 i) (hsp : IsSplitPl D.host v) : v ∉ Sb ∧ ((2 : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal ∧
      ∀ (j : Fin D.R.m) (k : ℕ), k ≤ D.R.r → ∃ α Rr, HkDat X.R Sb j k v α Rr := by
  have hlow : ∀ p ∈ lowAll D, ((p : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := fun p hp hm => hv (hl i p hp hm)
  have hgP : ∀ kk : Fin 2, ((D.host.g kk : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := fun kk =>
    hlow _ (by fin_cases kk <;> simp [lowAll])
  have hso : Bridge.SplitOff v (X.R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) := by
    have hAll : X.R.Sb = X.R.Pg := X.char.allPl
    have hPg := X.char.lev.Pg
    refine ⟨(GlobalTheory.HeckeTieCompare.isSplitPl_iff v).1 hsp, fun h => ?_, fun Q hQ h => ?_⟩
    · rw [Finset.mem_coe, hAll] at h
      obtain ⟨kk, hkk⟩ := (hPg v).1 h
      exact hgP kk (GlobalTheory.StepLaw.typePrime_mem_of_div hkk)
    · rw [Finset.mem_coe, hAll] at hQ
      obtain ⟨kk, hkk⟩ := (hPg Q).1 hQ
      have hm := GlobalTheory.StepLaw.typePrime_mem_of_div hkk
      rw [h, Formalism.L2.Col.conjIdeal_asIdeal, Formalism.L2.Col.mem_conjP, map_natCast] at hm
      exact hgP kk hm
  have h1 : v ∉ Sb := fun hh => hv (hSb.subset (hl i) hh)
  have h2 := hlow 2 (by simp [lowAll, Formalism.L2.lowPr])
  refine ⟨h1, h2, fun j k hk => ?_⟩
  obtain ⟨α, Rc, ha, hR⟩ := GlobalTheory.HeckeSupSt.exists_heckeElt X.char.lev X.char.fam j hso hk
  exact ⟨α, Rc, hsp, h1, h2, hk, ha, hR⟩

theorem units_cast {A B : Type} [iA : CommRing A] [iB : CommRing B] (h : A = B) (hi : HEq iA iB) {u : Aˣ} {v : Bˣ} (hu : HEq v u) :
    ringCast h hi (u : A) = v := by
  subst h; cases hi; cases hu; rfl

section Law

variable (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {kKs hk}
  (YS : NX.NExpRealS X.R X.cG (NX.ratDatR X.R X.cG kKs hk)) (hfi : ∀ i x, HEq ((YS.fi i).e x) x)
  (hl : LowIn D) (hl' : LowIn D') {Sb Sb'} (hSb : OverSet D Sb (lowAll D)) (hSb' : OverSet D' Sb' (lowAll D'))
  {hL hL'} (H : HkAd X Sb hL) (H' : HkAd X' Sb' hL')


include hfi hl hl' hSb hSb' H H' in
theorem hk_intertwine {i : D.ntw.Tw} {i' : D'.ntw.Tw} (j : Fin D.R.m) (k : ℕ) {P : PlE D.host} {P' : PlE D'.host} (hP : HEq P P')
    (p0 : P ∉ D.ntw.S0 i) (p1 : P' ∉ D'.ntw.S0 i') (p2 : IsSplitPl D'.host P') (p3 : k ≤ D'.R.r)
    (y : ((NX.ratDatR X.R X.cG kKs hk).A ((j : ℕ) + 1)).WK) (hy) :
    ((ks h m YS j).φ ⟨hL ((j : ℕ) + 1) k P y.1, hy⟩).1 = hL' ((j : ℕ) + 1) k P' ((ks h m YS j).φ y).1 := by
  obtain ⟨q1, q2, q3⟩ := (place_geo h.gal.R h.gal.host).2 P P' hP
  obtain ⟨α', R', hd'⟩ := (exists_hkDat X' hl' hSb' p1 p2).2.2 (h.cm j) k p3
  obtain ⟨r1, r2, -⟩ := exists_hkDat X hl hSb p0 (q1.2 p2)
  obtain ⟨α, R, ha0, hR0, hF⟩ := (hecke_geo h.gal.R h.gal.host h.sp j (h.cm j) rfl).2.2 _ _ (m.βW j (h.cm j) rfl) _ _ m.Pg P P' hP
    k α' R' hd'.elt hd'.reps
  have e0 := H.at j (YS.fi j).e (hfi j) ⟨q1.2 p2, r1, r2, by rw [h.gal.R]; exact p3, ha0, hR0⟩ y.1
  have e0' := H'.at (h.cm j) (fiOfEq X' (NX.idxOf_succ D' (h.cm j))).e (fiOfEq_heq X' _) hd' ((ks h m YS j).φ y).1
  have hnV : D.R.nV = D'.R.nV := by rw [h.gal.R]
  have e1 : hkNorm X.R j k P = hkNorm X'.R (h.cm j) k P' := by
    unfold hkNorm
    rw [q3 _ _ (m.Cmu0 j (h.cm j) rfl), q2, hnV]
  have e2 := hecke_sameMap h m j hF (read_move h m YS j ⟨_, hy⟩) (read_move h m YS j y) (e0.trans (congrArg (· • _) e1))
  exact (fiOfEq X' (NX.idxOf_succ D' (h.cm j))).e.injective (reading_injective X' _ (e2.trans e0'.symm))


include hfi hl hl' hSb hSb' H H' in
theorem hkLaw_move (hsup) {hs c} (hs') {c'} (hc : SameUnits c c') (L : HkLaw D _ YS.eF hL hs c) :
    HkLaw D' (dat h m YS) (tie h m YS hsup).eF hL' hs' c' := by
  intro i' j b h1 h2 k P' x p1 p2 p3
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
  have hi := back_heq h i'
  have hP : HEq (cast (place_geo h.gal.R h.gal.host).1.symm P') P' := cast_heq _ _
  generalize cast (place_geo h.gal.R h.gal.host).1.symm P' = P at hP ⊢
  obtain ⟨x, rfl⟩ := (h.fmCast hi _ b).surjective x
  obtain ⟨r1, -, r3⟩ := record_heq h.gal h.set h.frm h.Bsup h.delta hi
  have e1 : D'.nexp.hkF i' (n + 1) b k P' (h.fmCast hi _ b x) = h.fmCast hi _ b (D.nexp.hkF _ (n + 1) b k P x) :=
    eq_of_heq (((r1 _ b _ _ (h.fmCast_heq hi _ b x).symm).2.2 k _ _ hP).symm.trans (h.fmCast_heq hi _ b _).symm)
  have p0 : P ∉ D.ntw.S0 (back h i') := fun hh => p1 ((r3 P P' hP).1.1 hh)
  change eFm h m YS i' (n + 1) b h1 h2 _ = _ • hkF D' (dat h m YS) i' (n + 1) b (hL' (n + 1)) (hs' (n + 1) h1 h2) k P'
    (eFm h m YS i' (n + 1) b h1 h2 _)
  rw [e1, eFm_cast h m YS hi ⟨n, lt_m h h2⟩ b h1 h2, eFm_cast h m YS hi ⟨n, lt_m h h2⟩ b h1 h2,
    L _ _ b _ _ k P x p0 (((place_geo h.gal.R h.gal.host).2 P P' hP).1.2 p2) (by rw [h.gal.R]; exact p3), fmOf_smul]
  refine congrArg₂ (· • ·) ?_ (fmOf_restrict (S' := dat h m YS) (h.scal hi b) (ks h m YS ⟨n, lt_m h h2⟩) _ _ _ (hs' (n + 1) h1 h2 k P')
    (fun y => hk_intertwine h m YS hfi hl hl' hSb hSb' H H' ⟨n, lt_m h h2⟩ k hP p0 p1 p2 p3 y _) _)
  rw [map_pow, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  exact congrArg (fun z => algebraMap _ _ z ^ k) (units_cast _ _ (hc _ _ b _ _ hi hP))

end Law

end GlobalTheory.HeightCounting.SerCarry

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2 (NExpTied)
open Formalism.AUTREP (GAf)
open GlobalTheory.HeightCounting GlobalTheory.HeightCounting.SideCopy GlobalTheory.TwInputs.Move.Forms

namespace GlobalTheory.HeightCounting.SerCarry

variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

def KeepsMat {D : D7} (p : ∀ i : Fin D.R.m, GAf D.host.E D.R.nV → GA D (Vc D i)) : Prop :=
  ∃ hF : D.host.F = maximalRealSubfield D.host.E, ∀ i : Fin D.R.m, ∃ hn : (Vc D i).rank = D.R.nV, ∀ κ a b,
    finMat D.sp.cm.sig (Vc D i).gram (p i κ) a b = (GlobalTheory.Mem.R3.swapCast hF).symm
      ((κ.1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast hn a) (Fin.cast hn b))

theorem keepsMat_heq_refl (D : D7) : ∀ (p : ∀ i : Fin D.R.m, GAf D.host.E D.R.nV → GA D (Vc D i)) (p' : ∀ i : Fin D.R.m, GAf D.host.E D.R.nV → GA D (Vc D i)),
    KeepsMat p → KeepsMat p' → ∀ (j : Fin D.R.m) (j' : Fin D.R.m), (j : ℕ) = j' →
    HEq (fun g => (finHom (Vc D j)).rangeRestrict (p j g)) fun g => (finHom (Vc D j')).rangeRestrict (p' j' g) := by
  rintro p p' ⟨hF, hp⟩ ⟨hF', hp'⟩ j j' hj
  cases Fin.ext hj
  obtain ⟨hn, hp⟩ := hp j
  obtain ⟨hn', hp'⟩ := hp' j
  exact heq_of_eq (funext fun g => Subtype.ext (Units.ext (Matrix.ext fun a b => (hp g a b).trans (hp' g a b).symm)))

theorem keepsMat_heq (h : CopyTw D D' ι e) : ∀ (p : ∀ i : Fin D.R.m, GAf D.host.E D.R.nV → GA D (Vc D i)) (p' : ∀ i : Fin D'.R.m, GAf D'.host.E D'.R.nV → GA D' (Vc D' i)),
    KeepsMat p → KeepsMat p' → ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' →
    HEq (fun g => (finHom (Vc D j)).rangeRestrict (p j g)) fun g => (finHom (Vc D' j')).rangeRestrict (p' j' g) := by
  obtain ⟨r, rfl⟩ := h.exists_rest
  exact (by with_unfolding_all exact ((keepsMat_heq_refl D) :))

theorem low_copy_refl (D : D7) : (LowIn D → LowIn D) ∧
    (∀ (bad : D.ntw.Tw → ℕ) (bad' : D.ntw.Tw → ℕ), HEq bad bad' → (∀ i, bad i = normProd (D.ntw.S0 i)) →
      ∀ i, bad' i = normProd (D.ntw.S0 i)) ∧
    ((∀ i j b, ¬ (1 ≤ j ∧ j ≤ D.R.m) → Subsingleton (D.nexp.Fm i j b)) →
      ∀ i j b, ¬ (1 ≤ j ∧ j ≤ D.R.m) → Subsingleton (D.nexp.Fm i j b)) := by
  refine ⟨id, fun _ _ hb H => ?_, id⟩
  subst hb; exact H

theorem low_copy (h : CopyTw D D' ι e) : (LowIn D → LowIn D') ∧
    (∀ (bad : D.ntw.Tw → ℕ) (bad' : D'.ntw.Tw → ℕ), HEq bad bad' → (∀ i, bad i = normProd (D.ntw.S0 i)) →
      ∀ i, bad' i = normProd (D'.ntw.S0 i)) ∧
    ((∀ i j b, ¬ (1 ≤ j ∧ j ≤ D.R.m) → Subsingleton (D.nexp.Fm i j b)) →
      ∀ i j b, ¬ (1 ≤ j ∧ j ≤ D'.R.m) → Subsingleton (D'.nexp.Fm i j b)) := by
  obtain ⟨r, rfl⟩ := h.exists_rest
  exact (by with_unfolding_all exact ((low_copy_refl D) :))

theorem pq_copy_refl (D : D7) : ∀ (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host)
      (Pq' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host), HEq Pq Pq' →
      (∀ (ch : D.ntw.Tw → Set (Pl D.host.E)) (ch' : D.ntw.Tw → Set (Pl D.host.E)), HEq ch ch' →
        (∀ i P, IsSplitPl D.host P → (P ∈ ch i ↔ P ∈ Set.range Pq)) → ∀ i P, IsSplitPl D.host P → (P ∈ ch' i ↔ P ∈ Set.range Pq')) ∧
      ∀ (i' : D.ntw.Tw) (k : ℕ) (Q' : Finset (PlE D.host)) (ψ' : G D.host.E D.nd.Om →* (D.ntw.Ok i' k)ˣ),
        ∃ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), HEq i i' ∧ HEq Q Q' ∧ HEq ψ ψ' ∧
          HEq (NX.qpOf D Pq Q) (NX.qpOf D Pq' Q') ∧ HEq (NX.qpOf D Pq (D.ntw.pD i)) (NX.qpOf D Pq' (D.ntw.pD i')) := by
  refine fun Pq Pq' hPq => ⟨fun _ _ hc H => ?_, fun i k Q ψ => ?_⟩
  · subst hPq; subst hc; exact H
  · subst hPq; exact ⟨i, Q, ψ, .rfl, .rfl, .rfl, .rfl, .rfl⟩

theorem pq_copy (h : CopyTw D D' ι e) : ∀ (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host)
      (Pq' : HeightOneSpectrum (𝓞 (maximalRealSubfield D'.host.E)) → PlE D'.host), HEq Pq Pq' →
      (∀ (ch : D.ntw.Tw → Set (Pl D.host.E)) (ch' : D'.ntw.Tw → Set (Pl D'.host.E)), HEq ch ch' →
        (∀ i P, IsSplitPl D.host P → (P ∈ ch i ↔ P ∈ Set.range Pq)) → ∀ i P, IsSplitPl D'.host P → (P ∈ ch' i ↔ P ∈ Set.range Pq')) ∧
      ∀ (i' : D'.ntw.Tw) (k : ℕ) (Q' : Finset (PlE D'.host)) (ψ' : G D'.host.E D'.nd.Om →* (D'.ntw.Ok i' k)ˣ),
        ∃ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), HEq i i' ∧ HEq Q Q' ∧ HEq ψ ψ' ∧
          HEq (NX.qpOf D Pq Q) (NX.qpOf D' Pq' Q') ∧ HEq (NX.qpOf D Pq (D.ntw.pD i)) (NX.qpOf D' Pq' (D'.ntw.pD i')) := by
  obtain ⟨r, rfl⟩ := h.exists_rest
  exact (by with_unfolding_all exact ((pq_copy_refl D) :))

theorem join_copy_refl (D : D7) : ∀ (i' : D.ntw.Tw) (j : Fin D.R.m) (j' : Fin D.R.m), (j : ℕ) = j' → ∀ (b : Bool) (k : ℕ)
    (Q' : Finset (PlE D.host)) (ψ' : G D.host.E D.nd.Om →* (D.ntw.Ok i' k)ˣ), TwOK i' k Q' ψ' →
    ∃ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), HEq i i' ∧ HEq Q Q' ∧ HEq ψ ψ' ∧
      TwOK i k Q ψ ∧ PolF D (Wc D j).rank (Vc D j).rank = PolF D (Wc D j').rank (Vc D j').rank ∧
      HEq (inferInstance : AddCommGroup (PolF D (Wc D j).rank (Vc D j).rank))
        (inferInstance : AddCommGroup (PolF D (Wc D j').rank (Vc D j').rank)) ∧
      HEq (inferInstance : Module ℂ (PolF D (Wc D j).rank (Vc D j).rank))
        (inferInstance : Module ℂ (PolF D (Wc D j').rank (Vc D j').rank)) ∧
      ∀ (ek : ∀ i, Bool → ∀ k, FractionRing (D.ntw.Ok i k) →+* ℂ) (ek' : ∀ i, Bool → ∀ k, FractionRing (D.ntw.Ok i k) →+* ℂ),
        HEq ek ek' → HEq (ek i b k) (ek' i' b k) ∧
        ∀ (r : ∀ k Q ψ, D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₛₗ[ek i b k] (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank))
          (r' : ∀ k Q ψ, D.nexp.MtV i' ((j' : ℕ) + 1) b k Q ψ →ₛₗ[ek' i' b k]
            (Bridge.Gf (Vc D j') → PolF D (Wc D j').rank (Vc D j').rank)), HEq r r' →
          ∀ (p : GAf D.host.E D.R.nV → Bridge.Gf (Vc D j)) (p' : GAf D.host.E D.R.nV → Bridge.Gf (Vc D j')), HEq p p' →
            HEq (fun f g => r k Q ψ f (p g)) fun f g => r' k Q' ψ' f (p' g) := by
  intro i j j' hj b k Q ψ hT
  cases Fin.ext hj
  refine ⟨i, Q, ψ, .rfl, .rfl, .rfl, hT, rfl, .rfl, .rfl, fun _ _ hek => ?_⟩
  subst hek
  refine ⟨.rfl, fun _ _ hr _ _ hp => ?_⟩
  subst hr; subst hp
  rfl

theorem join_copy (h : CopyTw D D' ι e) : ∀ (i' : D'.ntw.Tw) (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → ∀ (b : Bool) (k : ℕ)
    (Q' : Finset (PlE D'.host)) (ψ' : G D'.host.E D'.nd.Om →* (D'.ntw.Ok i' k)ˣ), TwOK i' k Q' ψ' →
    ∃ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), HEq i i' ∧ HEq Q Q' ∧ HEq ψ ψ' ∧
      TwOK i k Q ψ ∧ PolF D (Wc D j).rank (Vc D j).rank = PolF D' (Wc D' j').rank (Vc D' j').rank ∧
      HEq (inferInstance : AddCommGroup (PolF D (Wc D j).rank (Vc D j).rank))
        (inferInstance : AddCommGroup (PolF D' (Wc D' j').rank (Vc D' j').rank)) ∧
      HEq (inferInstance : Module ℂ (PolF D (Wc D j).rank (Vc D j).rank))
        (inferInstance : Module ℂ (PolF D' (Wc D' j').rank (Vc D' j').rank)) ∧
      ∀ (ek : ∀ i, Bool → ∀ k, FractionRing (D.ntw.Ok i k) →+* ℂ) (ek' : ∀ i, Bool → ∀ k, FractionRing (D'.ntw.Ok i k) →+* ℂ),
        HEq ek ek' → HEq (ek i b k) (ek' i' b k) ∧
        ∀ (r : ∀ k Q ψ, D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₛₗ[ek i b k] (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank))
          (r' : ∀ k Q ψ, D'.nexp.MtV i' ((j' : ℕ) + 1) b k Q ψ →ₛₗ[ek' i' b k]
            (Bridge.Gf (Vc D' j') → PolF D' (Wc D' j').rank (Vc D' j').rank)), HEq r r' →
          ∀ (p : GAf D.host.E D.R.nV → Bridge.Gf (Vc D j)) (p' : GAf D'.host.E D'.R.nV → Bridge.Gf (Vc D' j')), HEq p p' →
            HEq (fun f g => r k Q ψ f (p g)) fun f g => r' k Q' ψ' f (p' g) := by
  obtain ⟨r, rfl⟩ := h.exists_rest
  exact (by with_unfolding_all exact ((join_copy_refl D) :))

def ExpMove (X : NExpTied D) (X' : NExpTied D') : Prop :=
  ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (Q' : Finset (PlE D'.host)),
    HEq Q Q' → ∀ (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (ψ' : G D'.host.E D'.nd.Om →* (D'.ntw.Ok i' k)ˣ), HEq ψ ψ' →
    ∀ (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (h2' : j ≤ D'.R.m) (hA' : Formalism.L2.NX.AdmTw D' i' k Q' ψ'), ∃ hA : Formalism.L2.NX.AdmTw D i k Q ψ,
      HEq (X.mtV i j b k Q ψ h1 h2 hA).QP (X'.mtV i' j b k Q' ψ' h1 h2' hA').QP ∧
      HEq (X.mtV i j b k Q ψ h1 h2 hA).DP (X'.mtV i' j b k Q' ψ' h1 h2' hA').DP ∧
      ∀ (ε : FractionRing (D.ntw.Ok i k) →+* ℂ) (ε' : FractionRing (D'.ntw.Ok i' k) →+* ℂ), HEq ε ε' →
        ∀ (V V' : Type) [aV : AddCommGroup V] [mV : Module ℂ V] [aV' : AddCommGroup V'] [mV' : Module ℂ V'], V = V' → HEq aV aV' →
          HEq mV mV' → ∀ (r : D.nexp.MtV i j b k Q ψ → GAf D.host.E D.R.nV → V) (r' : D'.nexp.MtV i' j b k Q' ψ' → GAf D'.host.E D'.R.nV → V'),
            HEq r r' → GlobalTheory.HeightCounting.Reads X i j b k Q ψ h1 h2 hA ε V r → GlobalTheory.HeightCounting.Reads X' i' j b k Q' ψ' h1 h2' hA' ε' V' r'

def PqLaw (X : NExpTied D) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) : Prop :=
  ∀ i j b k Q ψ (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hadm : Formalism.L2.NX.AdmTw D i k Q ψ),
    (X.mtV i j b k Q ψ h1 h2 hadm).QP = NX.qpOf D Pq Q ∧ (X.mtV i j b k Q ψ h1 h2 hadm).DP = NX.qpOf D Pq (D.ntw.pD i)

theorem pqLaw_move (h : CopyTw D D' ι e) {X : NExpTied D} {X' : NExpTied D'} (hX : ExpMove X X') {Pq Pq'} (hPq : HEq Pq Pq')
    (L : PqLaw X Pq) : PqLaw X' Pq' := by
  intro i' j b k Q' ψ' h1 h2' hA'
  have h2 : j ≤ D.R.m := by rw [h.gal.R]; exact h2'
  obtain ⟨i, Q, ψ, hi, hQ, hψ, e1, e2⟩ := (pq_copy h Pq Pq' hPq).2 i' k Q' ψ'
  obtain ⟨hA, q1, q2, -⟩ := hX i i' hi j b k Q Q' hQ ψ ψ' hψ h1 h2 h2' hA'
  obtain ⟨l1, l2⟩ := L i j b k Q ψ h1 h2 hA
  exact ⟨eq_of_heq (q1.symm.trans ((heq_of_eq l1).trans e1)), eq_of_heq (q2.symm.trans ((heq_of_eq l2).trans e2))⟩

end GlobalTheory.HeightCounting.SerCarry

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpTiedCopy
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move GlobalTheory.HeightCounting.SideCopy
open Formalism.L2.DIV Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.HeightCounting.ExpCopy

open GlobalTheory.Mem.R3.Tr

theorem sig_heq {R R' : Ranks} (hR : R = R') {H : Host R} {H' : Host R'} (hH : HEq H H') {T T' : Type} (hT : T = T')
    {f : T ≃ R.Psi} {f' : T' ≃ R'.Psi} (hf : HEq f f') {t : T} {t' : T'} (ht : HEq t t')
    {x : H.E} {x' : H'.E} (hx : HEq x x') :
    HEq (H.sigmaOf ((f t : R.Psi) : R.GG) x)
      (H'.sigmaOf ((f' t' : R'.Psi) : R'.GG) x') := by
  subst hR; cases hH; subst hT; cases hf; cases ht; cases hx; rfl

section
variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

theorem kEmb_heq (h : CopyTw D D' ι e) {i : D.ntw.Tw} {i' : D'.ntw.Tw} (hi : HEq i i') (b : Bool) {t : D.what₂.Tau}
    {t' : D'.what₂.Tau} (ht : HEq t t') {x : D.host.E} {x' : D'.host.E} (hx : HEq x x') :
    HEq (Formalism.L2.NX.kEmb D i b t x) (Formalism.L2.NX.kEmb D' i' b t' x') := by
  have hσ := sig_heq h.gal.R h.gal.host h.Tau h.eTau ht hx
  have hy : e (Formalism.L2.NX.embEL0 D' (D'.host.sigmaOf ((D'.eTau t' : D'.R.Psi) : D'.R.GG) x')) =
      Formalism.L2.NX.embEL0 D (D.host.sigmaOf ((D.eTau t : D.R.Psi) : D.R.GG) x) :=
    Subtype.ext (ι.injective ((h.LL0 _).trans (h.map_embE hσ).symm))
  have := h.sideEmb_heq hi b (Formalism.L2.NX.embEL0 D' (D'.host.sigmaOf ((D'.eTau t' : D'.R.Psi) : D'.R.GG) x'))
  rw [hy] at this
  exact this

theorem side_heq (h : CopyTw D D' ι e) {i : D.ntw.Tw} {i' : D'.ntw.Tw} (hi : HEq i i') (b : Bool) (z : ↥D.LL0) :
    HEq (GlobalTheory.SeriesTie.sideEmb D.ntw i b z) (GlobalTheory.SeriesTie.sideEmb D'.ntw i' b (e.symm z)) := by
  have := h.sideEmb_heq hi b (e.symm z)
  rw [e.apply_symm_apply] at this
  exact this

end

theorem infG_eta {D : D7} {cf : CharFrame D} (hcs : CharSide D cf) (t : D.what₂.Tau) :
    D.naut.infG D.naut.etaT (Formalism.L2.Host.embPsi D.host (D.eTau t)) = {(((1 / 2 : ℚ)) : ℂ)} :=
  (hcs.infG D.naut.etaT (fun _ => 1 / 2) (by rw [hcs.etaT]; exact ⟨fun _ => 1, fun _ => by norm_num, cf.isEta.inf⟩) (D.eTau t)).1


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem core (D : D7) (r : Rest D) (X : NExpTied D) (hpl : HEq D.naut.plGw (overD D r).naut.plGw)
    (hhw : ∀ i j b (t : D.what₂.Tau), 1 ≤ j → j ≤ D.R.m →
      ∃ lam : Fin D.R.nV → ℤ, Formalism.L2.NX.HWAtF (Formalism.L2.NX.cE D) (X.rhoW i j b).dual ((by exact NX.kEmb (overD D r) i b t)) lam)
    (hwt : ∀ i j b (t : D.what₂.Tau) (hj : 1 ≤ j) (hjm : j ≤ D.R.m) (sh : ℂ) (lam : Fin D.R.nV → ℤ),
      (overD D r).naut.infG (overD D r).naut.etaT ((by exact embPsi D.host (D.eTau t))) = {sh} →
      Formalism.L2.NX.HWAtF (Formalism.L2.NX.cE D) (X.rhoW i j b).dual ((by exact NX.kEmb (overD D r) i b t)) lam →
      NG.infOf lam = NG.paramV D.R (D.hc t) ⟨j - 1, by omega⟩ sh) :
    ∃ X' : NExpTied (overD D r), HEq X.tauG X'.tauG ∧ ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
      (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hA : NX.AdmTw D i k Q ψ),
      HEq (X.mtV i j b k Q ψ h1 h2 hA).QP (X'.mtV ((by exact i)) j b k ((by exact Q)) ((by exact ψ)) h1 ((by exact h2)) ((by exact hA))).QP ∧
      HEq (X.mtV i j b k Q ψ h1 h2 hA).DP (X'.mtV ((by exact i)) j b k ((by exact Q)) ((by exact ψ)) h1 ((by exact h2)) ((by exact hA))).DP ∧
      ∀ (ε : FractionRing (D.ntw.Ok i k) →+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
        (ρ : D.nexp.MtV i j b k Q ψ → Formalism.AUTREP.GAf D.host.E D.R.nV → V),
        GlobalTheory.HeightCounting.Reads X i j b k Q ψ h1 h2 hA ε V ρ →
          GlobalTheory.HeightCounting.Reads X' ((by exact i)) j b k ((by exact Q)) ((by exact ψ)) h1 ((by exact h2)) ((by exact hA)) ((by exact ε)) V ((by exact ρ)) := by
  cases r
  rename NAut _ => n
  cases n
  dsimp only [overD] at hpl
  cases hpl
  refine ⟨@Formalism.L2.NExpTied.mk (_)
      (U_eq := (X.U_eq))
      (psiU_gen := (X.psiU_gen))
      (psiU_side := (X.psiU_side))
      (psiU_xi := (X.psiU_xi))
      (delU_cont := (X.delU_cont))
      (delU_ine := (X.delU_ine))
      (thU_empty := (X.thU_empty))
      (sgnT := (X.sgnT))
      (sgnT_one := (X.sgnT_one))
      (Wt := (X.Wt))
      (acgWt := (X.acgWt))
      (modWt := (X.modWt))
      (fdWt := (X.fdWt))
      (rhoW := (X.rhoW))
      (rhoW_irr := (X.rhoW_irr))
      (rhoW_alg := (X.rhoW_alg))
      (tauG := (X.tauG))
      (sgnG := (X.sgnG))
      (sgnG_one := (X.sgnG_one))
      (tau_galois_first_character := (X.tau_galois_first_character))
      (mtV := fun x1 x2 x3 x4 x5 x6 x7 x8 x9 => @Formalism.L2.NX.MtVReal.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
        (W := (@NX.MtVReal.W D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (acg := (@NX.MtVReal.acg D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (mod := (@NX.MtVReal.mod D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (fd := (@NX.MtVReal.fd D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (ρ := (@NX.MtVReal.ρ D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (irr := (@NX.MtVReal.irr D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (alg := (@NX.MtVReal.alg D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (bc := (@NX.MtVReal.bc D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (J := (@NX.MtVReal.J D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (χ := (@NX.MtVReal.χ D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (J_open := (@NX.MtVReal.J_open D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (hyp := (@NX.MtVReal.hyp D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (QP := (@NX.MtVReal.QP D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (QP_sub := (@NX.MtVReal.QP_sub D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (QP_cover := (@NX.MtVReal.QP_cover D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (QP_nconj := (@NX.MtVReal.QP_nconj D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (DP := (@NX.MtVReal.DP D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (DP_sub := (@NX.MtVReal.DP_sub D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (DP_cover := (@NX.MtVReal.DP_cover D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (DP_nconj := (@NX.MtVReal.DP_nconj D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (sp := (@NX.MtVReal.sp D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (sp_w := (@NX.MtVReal.sp_w D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (redG := (@NX.MtVReal.redG D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (J_mem := (@NX.MtVReal.J_mem D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (chi_eq := (@NX.MtVReal.chi_eq D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (real := (@NX.MtVReal.real D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9))))
      (rhoW_hw := (hhw))
      (rhoW_wt := (hwt)), (HEq.refl X.tauG), fun i j b k Q ψ h1 h2 hA => ⟨?_, ?_, fun ε V _ _ ρ hR => ?_⟩⟩
  · exact (HEq.refl (X.mtV i j b k Q ψ h1 h2 hA).QP)
  · exact (HEq.refl (X.mtV i j b k Q ψ h1 h2 hA).DP)
  · exact (hR)


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem expTied_copy : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}, CopyAll D D' ι e → ∀ {cf : CharFrame D} {cf' : CharFrame D'}, SameFrame cf cf' → CharSide D cf → CharSide D' cf' → ∀ X : NExpTied D, ∃ X' : NExpTied D', (TauTrue X → TauTrue X') ∧ ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (Q' : Finset (PlE D'.host)), HEq Q Q' → ∀ (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (ψ' : G D'.host.E D'.nd.Om →* (D'.ntw.Ok i' k)ˣ), HEq ψ ψ' → ∀ (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (h2' : j ≤ D'.R.m) (hA' : NX.AdmTw D' i' k Q' ψ'), ∃ hA : NX.AdmTw D i k Q ψ, HEq (X.mtV i j b k Q ψ h1 h2 hA).QP (X'.mtV i' j b k Q' ψ' h1 h2' hA').QP ∧ HEq (X.mtV i j b k Q ψ h1 h2 hA).DP (X'.mtV i' j b k Q' ψ' h1 h2' hA').DP ∧ ∀ (ε : FractionRing (D.ntw.Ok i k) →+* ℂ) (ε' : FractionRing (D'.ntw.Ok i' k) →+* ℂ), HEq ε ε' → ∀ (V V' : Type) [aV : AddCommGroup V] [mV : Module ℂ V] [aV' : AddCommGroup V'] [mV' : Module ℂ V'], V = V' → HEq aV aV' → HEq mV mV' → ∀ (r : D.nexp.MtV i j b k Q ψ → Formalism.AUTREP.GAf D.host.E D.R.nV → V) (r' : D'.nexp.MtV i' j b k Q' ψ' → Formalism.AUTREP.GAf D'.host.E D'.R.nV → V'), HEq r r' → GlobalTheory.HeightCounting.Reads X i j b k Q ψ h1 h2 hA ε V r → GlobalTheory.HeightCounting.Reads X' i' j b k Q' ψ' h1 h2' hA' ε' V' r' := by
  intro D D' ι e h cf cf' _ hcs hcs' X
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  have hk : ∀ i b t, Formalism.L2.NX.kEmb D i b t = (by with_unfolding_all exact ((Formalism.L2.NX.kEmb (overD D r) ((by with_unfolding_all exact (i :))) b ((by with_unfolding_all exact (t :)))) :)) := fun i b t =>
    RingHom.ext fun x => (by with_unfolding_all exact (eq_of_heq (α := FractionRing (D.ntw.O i)) (a := Formalism.L2.NX.kEmb D i b t x)
        (a' := (by with_unfolding_all exact ((Formalism.L2.NX.kEmb (overD D r) ((i)) b ((t)) ((x))) : _)))
        ((by with_unfolding_all exact ((kEmb_heq h.cp (i := i) (i' := (i)) (((HEq.refl i))) b (t := t) (t' := (t)) (((HEq.refl t)))
          (x := x) (x' := (x)) (((HEq.refl x)))) : _))) :))
  obtain ⟨X', hτ, hM⟩ := core D r X h.pl
    (fun i j b t h1 h2 => by
      have := X.rhoW_hw i j b t h1 h2
      rw [hk] at this
      exact this)
    (fun i j b t h1 h2 sh lam hsh hw => by
      refine X.rhoW_wt i j b t h1 h2 sh lam ?_ ?_
      · have h3 : ({(((1 / 2 : ℚ)) : ℂ)} : Multiset ℂ) = {sh} := (infG_eta hcs' ((by with_unfolding_all exact (t :)))).symm.trans (c := {sh}) ((by with_unfolding_all exact (hsh :)))
        exact (infG_eta hcs t).trans h3
      · rw [hk]
        exact hw)
  refine ⟨X', fun ⟨τ, hτ'⟩ => ?_, fun i i' hi j b k Q Q' hQ ψ ψ' hψ h1 h2 h2' hA' => ?_⟩
  · have hτ2 : X'.tauG = (by with_unfolding_all exact (X.tauG :)) := (by with_unfolding_all exact ((eq_of_heq (a := X'.tauG) (a' := (by with_unfolding_all exact (X.tauG :))) ((by with_unfolding_all exact (hτ.symm :)))) :))
    refine ⟨fun j kv => (Units.map e.symm.toRingHom.toMonoidHom).comp ((by with_unfolding_all exact ((τ j ((by with_unfolding_all exact (kv :)))) :))), fun i j b kv x h1 h2 => ?_⟩
    rw [hτ2]
    exact (by with_unfolding_all exact ((hτ' ((by with_unfolding_all exact (i :))) j b ((by with_unfolding_all exact (kv :))) ((by with_unfolding_all exact (x :))) h1 ((by with_unfolding_all exact (h2 :)))).trans (eq_of_heq (α := FractionRing (D.ntw.O ((by with_unfolding_all exact (i :)))))
      (a' := (by with_unfolding_all exact ((GlobalTheory.SeriesTie.sideEmb (overD D r).ntw i b (e.symm ((τ j ((kv)) ((x)) : (↥D.LL0)ˣ) : ↥D.LL0))) : _)))
      ((by with_unfolding_all exact ((side_heq h.cp (i := (i)) (i' := i) (((HEq.refl i))) b ((τ j ((kv)) ((x)) : (↥D.LL0)ˣ) : ↥D.LL0)) : _)))) :))
  · cases hi; cases hQ; cases hψ
    refine ⟨(by with_unfolding_all exact (hA' :)), (hM i j b k Q ψ h1 h2 ((by with_unfolding_all exact (hA' :)))).1, (hM i j b k Q ψ h1 h2 ((by with_unfolding_all exact (hA' :)))).2.1, ?_⟩
    intro ε ε' hε V V' aV mV aV' mV' hV haV hmV ρ ρ' hρ hR
    subst hV; cases haV; cases hmV; cases hε; cases hρ
    exact (by with_unfolding_all exact (((hM i j b k Q ψ h1 h2 ((by with_unfolding_all exact (hA' :)))).2.2 ε V ρ hR) :))

end GlobalTheory.HeightCounting.ExpCopy

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamCopy
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move GlobalTheory.HeightCounting.SideCopy
open Formalism.L2.DIV Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HeightCounting.SideCopy.LamCopy
open GlobalTheory.Mem.R3.Tr


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem lam_copy : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}, CopyAll D D' ι e → ∀ {cf : CharFrame D} {cf' : CharFrame D'}, SameFrame cf cf' → (∃ Z : GlobalTheory.LamTie.LamDat D, Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw Z) → ∃ Z : GlobalTheory.LamTie.LamDat D', Z.Ok ∧ Z.Teich ∧ Z.C = cf' ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D' ∧ GlobalTheory.LamTie.IsLamTieFull D'.ntw Z := by
  rintro D D' ι e h cf cf' ⟨f1, f2, f3, f4⟩ ⟨⟨C, q, w0, c, chi⟩, hOk, hT, rfl, hq, hF⟩
  have he : ∀ x : ↥D'.LL0, D'.what₂.embLL (x : D'.what₂.LL) = D.what₂.embLL (e x : D.what₂.LL) := fun x => (h.cp.embLL0_eq x).symm
  have nOm := h.cp.gal.Om
  have ninstOm := h.cp.gal.instOm
  have nalgOm := h.cp.gal.algOm
  have nplOm := h.cp.gal.plOm
  have nPlG := h.cp.gal.PlG
  have hR := h.cp.gal.R
  have hhost := h.cp.gal.host
  have hTau := h.cp.Tau
  have heTau := h.cp.eTau
  have hhc := h.cp.hc
  have hinW1 := h.cp.inW1
  have hemb0 := h.cp.emb0
  have hTw := h.cp.set.Tw
  obtain ⟨xcc, _, _, _, _, xalgO0, xtopO0, _, _, _, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, _, xhEig, _, _, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h.cp.set
  have hjL := h.jL
  have hs2 := h.s2
  have hlamG := h.lamG
  have hXv := h.Xv
  have hqs := h.qs
  have hl := h.cp.set.l
  have hO0 := h.cp.set.O0
  have hcrO0 := h.cp.set.crO0
  have hab := h.cp.set.abelian₂
  have hsideL := h.cp.set.sideL
  have hO := h.cp.set.O
  have hcrO := h.cp.set.crO
  have halgO := h.cp.set.algO
  have hS0 := h.cp.set.S0
  cases D; cases D'
  dsimp only at hR hhost
  subst hR; subst hhost
  rename Rows.Data _ => r1; cases r1; rename Rows.Data _ => r2; cases r2
  dsimp only at hTau
  subst hTau
  dsimp only at heTau hhc
  subst heTau; subst hhc
  rename NData _ _ _ => nd1; cases nd1
  rename NData _ _ _ => nd2; cases nd2
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  rename NTw _ _ _ _ _ => n1; cases n1
  rename NTw _ _ _ _ _ => n2; cases n2
  dsimp only at xcc
  subst xcc
  dsimp only at hTw hl hO0 hcrO0 hab hsideL hO hcrO halgO hS0
  subst hTw; subst hl; subst hO0; subst hcrO0; subst hab; subst hsideL; subst hO; subst hcrO; subst hS0
  dsimp only at xalgO0 xtopO0 xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS xhEig xRCG xgrpRCG xfinRCG xart xth hjL hs2 hlamG hXv hqs halgO
  subst xalgO0; subst xtopO0; subst halgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst xhEig; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  subst hjL; subst hs2; subst hlamG; subst hXv; subst hqs
  cases C; cases cf'  
  dsimp only at f1 f2 f3 f4
  subst f1; subst f2; subst f3; subst f4
  refine ⟨⟨_, q, w0, c, chi⟩, ⟨(by with_unfolding_all exact (hOk.places :)), (by with_unfolding_all exact (hOk.aux :)), (by with_unfolding_all exact (hOk.big :))⟩, (by with_unfolding_all exact (hT :)), rfl, (by with_unfolding_all exact (hq :)), fun i hi => ?_⟩
  obtain ⟨t0, j, t1, t2⟩ := hF i ((hinW1 i i HEq.rfl).2 hi)
  refine ⟨(by with_unfolding_all exact (t0 :)), (by with_unfolding_all exact (j :)), fun x => ?_, (by with_unfolding_all exact (t2 :))⟩
  exact (congrArg j (he x)).trans ((t1 (e x)).trans ((by with_unfolding_all exact ((congrArg (GlobalTheory.ToricDenom.toBar _ i) (eq_of_heq (hemb0 i i HEq.rfl x))) :))))

end GlobalTheory.HeightCounting.SideCopy.LamCopy
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsScalarScale
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.HeightCounting
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SerVec

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {v₀ v₁ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

theorem evW_scale {j : Fin D.R.m} {c : D.what₂.Tau → ℂ}
    (h : ∀ τ, v₁ j (sg0 D A3.A) τ = c τ • v₀ j (sg0 D A3.A) τ) (x : S.WL ((j : ℕ) + 1)) :
    evW YS v₁ j x = (∏ τ, c τ) • evW YS v₀ j x := by
  change (Rl.HW j (sg0 D A3.A)).e _ (v₁ j _) = (∏ τ, c τ) • (Rl.HW j (sg0 D A3.A)).e _ (v₀ j _)
  rw [show v₁ j (sg0 D A3.A) = fun τ => c τ • v₀ j (sg0 D A3.A) τ from funext h]
  exact MultilinearMap.map_smul_univ _ _ _

theorem realRd_scale {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) {j : Fin D.R.m} (b : Bool) {C : ℂ} (hC : C ≠ 0)
    (h : ∀ x, evW YS v₁ j x = C • evW YS v₀ j x) (ν : ℂ) :
    realRd YS v₁ hρ i j b (C * ν) = realRd YS v₀ hρ i j b ν := by
  have key : ∀ x, evK YS v₁ hρ i j b x = C • evK YS v₀ hρ i j b x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, smul_zero]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, smul_add]
    | tmul a f => rw [evK_tmul, evK_tmul, h, smul_comm]
  refine LinearMap.ext fun f => ?_
  change (C * ν)⁻¹ • evK YS v₁ hρ i j b _ = ν⁻¹ • evK YS v₀ hρ i j b _
  refine (congrArg _ (key _)).trans ?_
  rw [smul_smul, mul_inv, mul_right_comm, inv_mul_cancel₀ hC, one_mul]

theorem isScale_scale {j : Fin D.R.m} {c : D.what₂.Tau → ℂ}
    (h : ∀ τ, v₁ j (sg0 D A3.A) τ = c τ • v₀ j (sg0 D A3.A) τ) (B : GlobalTheory.ExportSeries.Base (Vc D j) (Wc D j)) {s : ℂ}
    (hs : IsScale Rl v₀ B s) : IsScale Rl v₁ B ((∏ τ, c τ) * s) := by
  obtain ⟨gramR, c0R, c0L, ht, u, hu, hF⟩ := hs
  refine ⟨gramR, c0R, c0L, ht, fun τ => c τ • u τ, fun τ => ?_, fun F => ?_⟩
  · rw [h, ← hu]; rfl
  · rw [MultilinearMap.map_smul_univ, map_smul, mul_smul, ← hF]
    exact map_smul (GlobalTheory.ExportSeries.harmFn (Wc D j).rank B.w B.F.BS) _ _

theorem isNorm_scale {j : Fin D.R.m} {c : D.what₂.Tau → ℂ} (hc : ∀ τ, c τ ≠ 0)
    (h : ∀ τ, v₁ j (sg0 D A3.A) τ = c τ • v₀ j (sg0 D A3.A) τ) (B : GlobalTheory.ExportSeries.Base (Vc D j) (Wc D j)) {ν : ℂ}
    (hν : IsNorm Rl v₀ B ν) : IsNorm Rl v₁ B ((∏ τ, c τ) * ν) := by
  obtain ⟨h0, s, hs, n, hn, he⟩ := hν
  refine ⟨mul_ne_zero (Finset.prod_ne_zero_iff.2 fun τ _ => hc τ) h0, _, isScale_scale h B hs, n, hn, ?_⟩
  rw [mul_pow, he, ← mul_pow, mul_left_comm]

theorem scale_symm {j : Fin D.R.m} {c : D.what₂.Tau → ℂ} (hc : ∀ τ, c τ ≠ 0)
    (h : ∀ τ, v₁ j (sg0 D A3.A) τ = c τ • v₀ j (sg0 D A3.A) τ) (τ : D.what₂.Tau) :
    v₀ j (sg0 D A3.A) τ = (c τ)⁻¹ • v₁ j (sg0 D A3.A) τ := by
  rw [h, smul_smul, inv_mul_cancel₀ (hc τ), one_smul]

theorem isScalar_scale {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) {j : Fin D.R.m} (b : Bool) {c : D.what₂.Tau → ℂ}
    (hc : ∀ τ, c τ ≠ 0) (h : ∀ τ, v₁ j (sg0 D A3.A) τ = c τ • v₀ j (sg0 D A3.A) τ) {ν : ℂ}
    (hν : IsScalar YS v₀ hρ i j b ν) : IsScalar YS v₁ hρ i j b ((∏ τ, c τ) * ν) := by
  have hC : (∏ τ, c τ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => hc τ
  have hc' : ∀ τ, (c τ)⁻¹ ≠ 0 := fun τ => inv_ne_zero (hc τ)
  have h' := scale_symm hc h
  refine ⟨mul_ne_zero hC hν.ne, fun ⟨ν', h1⟩ => isNorm_scale hc h _ (hν.norm ⟨_, isNorm_scale hc' h' _ h1⟩), fun ⟨ν', h1, h2⟩ => ?_⟩
  rw [realRd_scale YS hρ i b hC (evW_scale YS h)]
  refine hν.rat ⟨_, isNorm_scale hc' h' _ h1, ?_⟩
  rw [realRd_scale YS hρ i b (Finset.prod_ne_zero_iff.2 fun τ _ => hc' τ) (evW_scale YS h')]
  exact h2

theorem exists_cell {ρ : Setup D.ntw} {hρ : ρ.Good} {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} {rd rd' : Rd ρ D.nexp i j b}
    (e : rd' = rd) (t : CellTie hρ D.nexp rd) : ∃ t' : CellTie hρ D.nexp rd', t'.rdV = t.rdV := by
  subst e
  exact ⟨t, rfl⟩

theorem serAt_scale {c : Fin D.R.m → D.what₂.Tau → ℂ} (hc : ∀ j τ, c j τ ≠ 0)
    (h : ∀ j τ, v₁ j (sg0 D A3.A) τ = c j τ • v₀ j (sg0 D A3.A) τ)
    (hv : ∀ j, FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₁ j _)) {Xe : Formalism.L2.NExpTied D}
    {PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV} {cf : Formalism.L2.Host.CharFrame D}
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} (Z : SerAt YS v₀ Xe PV cf Pq) :
    Nonempty (SerAt YS v₁ Xe PV cf Pq) := by
  have e : ∀ i j b, realRd YS v₁ Z.ex.good i j b ((∏ τ, c j τ) * Z.ex.ν i j b) = realRd YS v₀ Z.ex.good i j b (Z.ex.ν i j b) :=
    fun i j b => realRd_scale YS _ i b (Finset.prod_ne_zero_iff.2 fun τ _ => hc j τ) (evW_scale YS (h j)) _
  choose t ht using fun i j b => exists_cell (e i j b) (Z.ex.tie i j b)
  refine ⟨{ ex :=
              { ρ := Z.ex.ρ
                good := Z.ex.good
                pin := Z.ex.pin
                vec := hv
                ν := fun i j b => (∏ τ, c j τ) * Z.ex.ν i j b
                scalar := fun i j b => isScalar_scale YS _ i b (hc j) (h j) (Z.ex.scalar i j b)
                tie := t
                hecke := fun i j b => by rw [e]; exact Z.ex.hecke i j b
                univ := Z.ex.univ }
            bad := Z.bad
            ch := Z.ch
            join := fun i j b k Q ψ hA hT => ?_
            sup := Z.sup
            off := Z.off
            lam := Z.lam
            lam_ok := Z.lam_ok
            lam_teich := Z.lam_teich
            lam_C := Z.lam_C
            lam_q := Z.lam_q
            lam_tie := Z.lam_tie }⟩
  obtain ⟨ω, h1, h2⟩ := Z.join i j b k Q ψ hA hT
  refine ⟨ω, h1, fun f g => ?_⟩
  rw [← h2 f g, ← ht i j b]

theorem serAt_vec : ∀ {D : D7} (X : RealSide D) (g₀ g₁ : GlobalTheory.RealGeo.GeoHalf X.core X.R.toRealDat fun _ => 1) {S : NX.RatDat D.ntw} (YS : NX.NExpRealS X.R X.cG S) (Xe : Formalism.L2.NExpTied D) (PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV) (cf : Formalism.L2.Host.CharFrame D) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host), SerAt YS g₀.v₀ Xe PV cf Pq → Nonempty (SerAt YS g₁.v₀ Xe PV cf Pq) := by
  intro D X g₀ g₁ S YS Xe PV cf Pq Z
  have hL : ∀ j, FWT.ExtLine (X.R.MW j (sg0 D X.A3.A)) := fun j =>
    GlobalTheory.HolLowOnce.extLine_of_holShape D _ _ _
      (GlobalTheory.DefLift.holShape_fixed D X.Γ X.Pl0 X.T X.A3.A _ X.R.toRealDat X.char.models.order j).1
  choose c hc h using fun j τ => hL j _ _ (g₀.fw.hv₀ j _).1 (g₁.fw.hv₀ j _).1 τ
  exact serAt_scale YS (fun j τ h0 => by simpa [h0] using hc j τ) h (fun j => g₁.fw.hv₀ j _) Z

end GlobalTheory.SerVec
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2 (NExpTied)
open Formalism.AUTREP (GAf)
open GlobalTheory.HeightCounting GlobalTheory.HeightCounting.SideCopy GlobalTheory.TwInputs.Move.Forms

namespace GlobalTheory.HeightCounting.SerCarry

variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

theorem exportTie_move (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {S : NX.RatDat D.ntw}
    (YS : NX.NExpRealS X.R X.cG S)
    (hsup : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : D.nexp.Fm i j b), x ∈ D.nexp.Bsup i j b ↔ YS.eF i j b h1 h2 x ∈ NX.Bsup S i j b)
    (Z : ExportTie YS X.geo.v₀) :
    ∃ Z' : ExportTie (Forms.tie h m YS hsup) X'.geo.v₀, SameSetup Z.ρ Z'.ρ ∧
      ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : Fin D.R.m) b,
        Z'.ν i' (h.cm j) b = Z.ν i j b ∧ HEq (Z.tie i j b).rdV (Z'.tie i' (h.cm j) b).rdV := by
  obtain ⟨ρ', hs, hg, hp⟩ := setup_move h m Z.ρ Z.good Z.pin
  have hrd := Forms.rdRel_move h m YS hsup Z.ρ ρ' hs Z.good hg
  have hm : D'.R.m = D.R.m := (congrArg Ranks.m h.gal.R).symm
  let ν' : D'.ntw.Tw → Fin D'.R.m → Bool → ℂ := fun i' j' b => Z.ν (cast h.Tw_eq.symm i') (Fin.cast hm j') b
  have hν : ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : Fin D.R.m) b, ν' i' (h.cm j) b = Z.ν i j b := by
    intro i i' hi j b
    have e1 : cast h.Tw_eq.symm i' = i := eq_of_heq ((cast_heq _ _).trans hi.symm)
    have e2 : Fin.cast hm (h.cm j) = j := Fin.ext rfl
    change Z.ν (cast h.Tw_eq.symm i') (Fin.cast hm (h.cm j)) b = _
    rw [e1, e2]
  have back : ∀ (i' : D'.ntw.Tw) (j' : Fin D'.R.m), ∃ i : D.ntw.Tw, ∃ j : Fin D.R.m, HEq i i' ∧ h.cm j = j' :=
    fun i' j' => ⟨cast h.Tw_eq.symm i', Fin.cast hm j', cast_heq _ _, Fin.ext rfl⟩
  have hrdZ : RdRel h (fun i j b => realRd YS X.geo.v₀ Z.good i j b (Z.ν i j b))
      (fun i j b => realRd (Forms.tie h m YS hsup) X'.geo.v₀ hg i j b (ν' i j b)) := by
    intro i i' hi j b f
    have := hrd (Z.ν i j b) i i' hi j b f
    change HEq (realRd (Forms.tie h m YS hsup) X'.geo.v₀ hg i' (h.cm j) b (ν' i' (h.cm j) b) _) _
    rw [hν i i' hi j b]
    exact this
  obtain ⟨T', hT'⟩ := TieUp.tie_move h hs Z.good hg _ _ hrdZ Z.tie
  have hv := isExtremalVector_of_realSideBaseChange h m Z.vec
  have hsc : ∀ i' j' b, IsScalar (Forms.tie h m YS hsup) X'.geo.v₀ hg i' j' b (ν' i' j' b) := by
    intro i' j' b
    obtain ⟨i, j, hi, rfl⟩ := back i' j'
    rw [hν i i' hi j b]
    exact scalar_move h m hs Z.good hg Z.pin hp Z.vec hv hrd i i' hi j b _ (Z.scalar i j b)
  have hhk : ∀ i' j' b, HeckeTie (realRd (Forms.tie h m YS hsup) X'.geo.v₀ hg i' j' b (ν' i' j' b)) := by
    intro i' j' b
    obtain ⟨i, j, hi, rfl⟩ := back i' j'
    exact heckeTie_move h hs _ _ hrdZ i i' hi j b (Z.hecke i j b)
  exact ⟨ExportTie.mk ρ' hg hp hv ν' hsc T' hhk (GlobalTheory.UnivCharCopy.isUnivChar_copy h Z.univ), hs,
    fun i i' hi j b => ⟨hν i i' hi j b, hT' i i' hi j b⟩⟩

theorem serAt_move (h : CopyAll D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {S : NX.RatDat D.ntw}
    (YS : NX.NExpRealS X.R X.cG S) {Xe : NExpTied D} {Xe' : NExpTied D'} (hX : ExpMove Xe Xe')
    {PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV} {PV' : ∀ i : Fin D'.R.m, principalLevelFrame.RowPsi (Vc D' i) D'.R.nV}
    (hp : KeepsMat fun i => (PV i).ψ) (hp' : KeepsMat fun i => (PV' i).ψ) {cf : CharFrame D} {cf' : CharFrame D'}
    (hcf : SameFrame cf cf') {Pq Pq'} (hPq : HEq Pq Pq') (Z : SerAt YS X.geo.v₀ Xe PV cf Pq) :
    Nonempty (SerAt (Forms.tie h.cp m YS Z.sup) X'.geo.v₀ Xe' PV' cf' Pq') := by
  obtain ⟨Z', hs, hr⟩ := exportTie_move h.cp m YS Z.sup Z.ex
  obtain ⟨lam, l1, l2, l3, l4, l5⟩ := LamCopy.lam_copy h hcf ⟨Z.lam, Z.lam_ok, Z.lam_teich, Z.lam_C, Z.lam_q, Z.lam_tie⟩
  refine ⟨{ ex := Z'
            bad := (low_copy h.cp).2.1 _ _ hs.bad Z.bad
            ch := (pq_copy h.cp Pq Pq' hPq).1 _ _ hs.ch Z.ch
            join := fun i' j' b k Q' ψ' hA' hT' => ?_
            sup := sup_move h.cp m YS Z.sup
            off := (low_copy h.cp).2.2 Z.off
            lam := lam
            lam_ok := l1
            lam_teich := l2
            lam_C := l3
            lam_q := l4
            lam_tie := l5 }⟩
  obtain ⟨j, rfl⟩ : ∃ j, h.cp.cm j = j' := ⟨⟨j', lt_m h.cp j'.2⟩, rfl⟩
  obtain ⟨i, Q, ψ, hi, hQ, hψ, hT, e1, e2, e3, e4⟩ := join_copy h.cp i' j (h.cp.cm j) rfl b k Q' ψ' hT'
  obtain ⟨e5, e6⟩ := e4 _ _ hs.ek
  obtain ⟨hA, -, -, hR⟩ := hX i i' hi ((j : ℕ) + 1) b k Q Q' hQ ψ ψ' hψ (Nat.le_add_left _ _) j.2 (h.cp.cm j).2 hA'
  exact hR _ _ e5 _ _ e1 e2 e3 _ _ (e6 _ _ (hr i i' hi j b).2 _ _ (keepsMat_heq h.cp _ _ hp hp' j (h.cp.cm j) rfl))
    (Z.join i j b k Q ψ hA hT)

theorem series_move (h : CopyAll D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι)
    (g₀ : GlobalTheory.RealGeo.GeoHalf X.core X.R.toRealDat fun _ => 1) (g₁ : GlobalTheory.RealGeo.GeoHalf X'.core X'.R.toRealDat fun _ => 1)
    {kKs hk} (kKs' hk') (YS : NX.NExpRealS X.R X.cG (NX.ratDatR X.R X.cG kKs hk)) (hfi : ∀ i x, HEq ((YS.fi i).e x) x)
    (hl : LowIn D) {Sb Sb'} (hSb : OverSet D Sb (lowAll D)) (hSb' : OverSet D' Sb' (lowAll D'))
    {hL hL'} (H : HkAd X Sb hL) (H' : HkAd X' Sb' hL') {hs c} (hs') {c'} (hc : SameUnits c c') (L : HkLaw D _ YS.eF hL hs c)
    {cf : CharFrame D} {cf' : CharFrame D'} (hcf : SameFrame cf cf') (s : CharSide D cf) (s' : CharSide D' cf')
    {PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV} {PV' : ∀ i : Fin D'.R.m, principalLevelFrame.RowPsi (Vc D' i) D'.R.nV}
    (hp : KeepsMat fun i => (PV i).ψ) (hp' : KeepsMat fun i => (PV' i).ψ) {Pq Pq'} (hPq : HEq Pq Pq')
    {Xe : NExpTied D} (hq : PqLaw Xe Pq) (hτ : TauTrue Xe) (Z : SerAt YS g₀.v₀ Xe PV cf Pq) :
    ∃ (YS' : NX.NExpRealS X'.R X'.cG (NX.ratDatR X'.R X'.cG kKs' hk')) (Xe' : NExpTied D'), PqLaw Xe' Pq' ∧
      HkLaw D' (NX.ratDatR X'.R X'.cG kKs' hk') YS'.eF hL' hs' c' ∧ (∀ i x, HEq ((YS'.fi i).e x) x) ∧
      Nonempty (SerAt YS' g₁.v₀ Xe' PV' cf' Pq') ∧ TauTrue Xe' := by
  obtain rfl : kKs' = m.kKsOf (e := e) YS (NX.idxOf D 0) :=
    RingHom.ext fun x => Subtype.ext ((hk' x).trans (m.kKsOf_spec h.cp YS _ x).symm)
  obtain ⟨Xe', ht, hX⟩ := GlobalTheory.HeightCounting.ExpCopy.expTied_copy h hcf s s' Xe
  obtain ⟨Z₁⟩ := GlobalTheory.SerVec.serAt_vec X g₀ X.geo YS _ _ _ _ Z
  obtain ⟨Z₂⟩ := serAt_move h m YS hX hp hp' hcf hPq Z₁
  exact ⟨Forms.tie h.cp m YS Z₁.sup, Xe', pqLaw_move h.cp hX hPq hq,
    hkLaw_move h.cp m YS hfi hl ((low_copy h.cp).1 hl) hSb hSb' H H' Z₁.sup hs' hc L, fun i x => fiOfEq_heq X' _ x,
    GlobalTheory.SerVec.serAt_vec X' X'.geo g₁ _ _ _ _ _ Z₂, ht hτ⟩

end GlobalTheory.HeightCounting.SerCarry

end
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace GlobalTheory.HeightCounting.SerCarry

open GlobalTheory.HeightCounting.SerMove GlobalTheory.Mem.R3.Tr

theorem sideB_facts {D : D7} {cf Rw Pq} {S : RatDat D.ntw} {hL eig θ} (B : SideB D cf Rw (lowAll D) Pq S hL eig θ) {eF}
    (h : eF = B.eF) : HkLaw D S eF hL B.hs B.cHk ∧ LowIn D ∧ PqLaw B.exp Pq := by
  subst h
  refine ⟨B.hkEq, fun i p hp P hP => ?_, B.pq⟩
  rw [B.tw.ringSpec_excludedPlaces_eq i]
  exact Or.inr (B.tw.concreteTwistFrame_extraExcluded_over_smallPrimes i p hp hP)

end GlobalTheory.HeightCounting.SerCarry

end
