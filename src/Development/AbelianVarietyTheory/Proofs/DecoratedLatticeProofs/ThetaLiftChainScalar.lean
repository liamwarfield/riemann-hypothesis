module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeFormOfDoubling
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsAtAndSeedFacts
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFamilyProperty

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainScalar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.LiftVol

theorem thetaKO_sum_translates {D : D7} {S T : HSp D} {ι : Type} (s : Finset ι) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (g : GA D S) (h : GA D T) (c : ι → ℂ) (κ : ι → GA D S) (f : WO S T → ℂ) :
    thetaKO om g h (∑ p ∈ s, c p • om (κ p, 1) f) = ∑ p ∈ s, c p * thetaKO om (g * κ p) h f := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [thetaKO, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]



end GlobalTheory.Fam.LiftVol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RankOneGramRelation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FamChars

open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)

variable {D : D7}

theorem cu_mul {χ χ' : (AE D)ˣ →* Circle} {x : HeightOneSpectrum (𝓞 D.host.F)} (h : CharUnramAt D χ x)
    (h' : CharUnramAt D χ' x) : CharUnramAt D (χ * χ') x := fun y h1 h2 h3 h4 => by
  rw [MonoidHom.mul_apply, h y h1 h2 h3 h4, h' y h1 h2 h3 h4, one_mul]

theorem cu_inv {χ : (AE D)ˣ →* Circle} {x : HeightOneSpectrum (𝓞 D.host.F)} (h : CharUnramAt D χ x) :
    CharUnramAt D χ⁻¹ x := fun y h1 h2 h3 h4 => by
  rw [MonoidHom.inv_apply, h y h1 h2 h3 h4, inv_one]

theorem mem_under (PP : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ) :
    ((n : ℕ) : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal ↔ ((n : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((n : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal ↔ _
  rw [map_natCast]

theorem not_both (PP : HeightOneSpectrum (𝓞 D.host.E)) {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : ((a : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (hb : ((b : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : False := by
  haveI : PP.asIdeal.IsPrime := PP.isPrime
  have ha' : ((a : ℕ) : (𝓞 D.host.E) ⧸ PP.asIdeal) = 0 := by
    simpa using (Ideal.Quotient.eq_zero_iff_mem (I := PP.asIdeal)).2 ha
  have hb' : ((b : ℕ) : (𝓞 D.host.E) ⧸ PP.asIdeal) = 0 := by
    simpa using (Ideal.Quotient.eq_zero_iff_mem (I := PP.asIdeal)).2 hb
  exact CharP.ringChar_ne_one (Nat.eq_one_of_dvd_coprimes hab (ringChar.dvd ha') (ringChar.dvd hb'))

end GlobalTheory.FamChars

namespace GlobalTheory.FamChars

open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)

theorem weil_rec {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {T : HSp D} {a b : (AE D)ˣ →* Circle}
    (ω : Om (Yc D (D.R.m - 1)) T) (hω : IsWeilDatumO ψ _ _ a b ω) :
    ∀ n (e : D.R.m - 1 = n), IsWeilDatumO ψ (Yc D n) T a b (Eq.rec (motive := fun n _ => Om (Yc D n) T) ω e) := by
  rintro n rfl
  exact hω

end GlobalTheory.FamChars
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainStepThetaLift
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.BaseChain.thetaKO_sum_smul_act {D : D7} {S T : HSp D} {ι : Type} (s : Finset ι) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (g : GA D S) (h : GA D T) (c : ι → ℂ) (κ : ι → GA D S) (f : WO S T → ℂ) :
    thetaKO om g h (∑ p ∈ s, c p • om (κ p, 1) f) = ∑ p ∈ s, c p * thetaKO om (g * κ p) h f := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [thetaKO, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTypePlacesOfLevCh
section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsStage
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def comL (L : LevCh D Unit) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (P : LevelP L.Pg D.R.r ℂ) : Com D :=
  ⟨θ, ψ, L.mu (), L.eta, L.Pg, P, L.chi⟩

theorem mem_S {L : LevCh D Unit} (hL : L.Is ()) (θ ψ P) (k : Fin 2) (Q : Pl D.host.E)
    (hk : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal) : Q.under (𝓞 D.host.F) ∈ (comL L θ ψ P).S := by
  classical
  unfold Com.S
  rw [Finset.mem_image]
  rcases GlobalTheory.ConjOverQuad.div_or_conj_div D L.C.P k Q hk with h1 | ⟨Q', h1, hc⟩
  · exact ⟨Q, (hL.Pg Q).2 ⟨k, h1⟩, rfl⟩
  · refine ⟨Q', (hL.Pg Q').2 ⟨k, h1⟩, ?_⟩
    ext x
    show algebraMap _ _ x ∈ Q'.asIdeal ↔ algebraMap _ _ x ∈ Q.asIdeal
    rw [hc, Formalism.L2.Col.mem_conjIdeal]
    have : Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = algebraMap _ _ x := by
      apply RingOfIntegers.ext
      exact (D.sp.cm.fixed _).2 ⟨x, rfl⟩
    rw [this]

end GlobalTheory.ChainOnto.Model

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.ComCols

variable {D : D7}

theorem isTypePlaces_of_levCh {L : LevCh D Unit} (hL : L.Is ()) : GlobalTheory.Core.Mi.IsTypePlaces L.Pg := by
  classical
  refine ⟨fun PP hPP => ?_, fun v hv => ?_⟩
  · obtain ⟨k, hk⟩ := (hL.Pg PP).1 hPP
    have h1 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := L.C.P.overP hk
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ h1
    · exact Ideal.mul_mem_left _ _ h1
  · have := v.isMaximal
    obtain ⟨Q, hQ, hQ'⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    let W : Formalism.L2.DIV.Pl D.host.E := ⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
    have hW : W.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hQ'.over.symm
    have hk : ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ W.asIdeal := by
      rw [← hW] at hv
      have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ W.asIdeal := hv
      rw [map_natCast, Nat.cast_mul] at h2
      exact (W.isPrime.mem_or_mem h2).elim (fun h => ⟨0, h⟩) fun h => ⟨1, h⟩
    obtain ⟨k, hk⟩ := hk
    have hS := GlobalTheory.ChainOnto.Model.mem_S hL (GlobalTheory.Member.exists_isInfFam_family D).choose 1 L.triv k W hk
    unfold GlobalTheory.ChainOnto.Com.S at hS
    obtain ⟨P, hP, e⟩ := Finset.mem_image.1 hS
    refine ⟨P, ⟨hP, e.trans hW⟩, ?_⟩
    rintro P' ⟨hP', e'⟩
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq (e'.trans (e.trans hW).symm) with h | h
    · exact h
    · exact absurd (GlobalTheory.GoodPrimes.isConjPl_iff.2 h) (GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hL () (Or.inl hP) (Or.inl hP'))

theorem com_is_of_levCh {L : LevCh D Unit} (hL : L.Is ()) (c : GlobalTheory.ChainOnto.Com D) (hθ : IsInfFam c.θ) (hψ : IsStdChar D c.ψ (-1))
    (hP : c.Pg = L.Pg) (hμ : ∀ j : Fin D.R.m, ChrEq (c.μ ((j : ℕ) + 1)) (L.C.mu0 j)) (hη : ChrEq c.η L.C.eta)
    (hχ : ∀ j : Fin D.R.m, ∀ PP ∈ c.Pg, IsRes (L.C.mu0 j) PP (c.chi ((j : ℕ) + 1) PP)⁻¹) : c.Is := by
  have hres := GlobalTheory.Mem.EtaTilde.isEta_res D c.η L.C.eta hη L.C.isEta
  have hS : ∀ (k : Fin 2) (Q : Formalism.L2.DIV.Pl D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal →
      Q.under (𝓞 D.host.F) ∈ c.S := fun k Q hk => by
    have := GlobalTheory.ChainOnto.Model.mem_S hL c.θ c.ψ L.triv k Q hk
    unfold GlobalTheory.ChainOnto.Com.S at this ⊢
    rw [hP]
    exact this
  refine ⟨hθ, hψ, ⟨hη.1, GlobalTheory.Mem.TupChar.unramEverywhere hη L.C.isEta.unr, ⟨⟨_, hres⟩, fun η h a => ?_⟩, fun τ => ?_,
    fun j hj => ?_⟩, fun j τ => ?_, fun j w hw => ?_, fun j => ⟨_, hμ j, hχ j⟩, ?_⟩
  · rw [(GlobalTheory.IdeleNormChar.existsUnique_isEta D).unique h hres, pow_one, MonoidHom.comp_apply]
  · exact GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hη
      (GlobalTheory.InnerSteps.hasInfQ_tauE (a := fun _ => 1 / 2) ⟨fun _ => 1, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  · obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hi : i < D.R.m := by omega
    refine ⟨(hμ ⟨i, hi⟩).1, ⟨_, hres⟩, fun η _ a => ?_⟩
    show c.μ (i + 1) (idF D a) = _
    rw [pow_zero]
    exact GlobalTheory.GridWeil.triv_base (hμ ⟨i, hi⟩) (L.C.isMu0 ⟨i, hi⟩).triv a
  · have h1 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hμ j) (GlobalTheory.InnerSteps.hasInfQ_tauE (L.C.isMu0 j).inf) τ
    simp only [Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at h1
    exact h1
  · exact (GlobalTheory.LFun.unrAt_iff_of_chrEq (hμ j) w).2 ((L.C.isMu0 j).unr w fun k hk => hw (hS k w hk))
  · rw [hP]
    exact GlobalTheory.CentralShift.exists_idemSum _ fun Q hQ Q' hQ' => GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hL () (Or.inl hQ) (Or.inl hQ')

end GlobalTheory.SeeSaw.ComCols
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryExistsKernel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

namespace GlobalTheory.Fam.KomExist

theorem even_rankX {D : D7} (j : ℕ) (hj : j ≤ D.R.m) : Even (D.sp.X j).rank := by
  rw [Formalism.L2.Forms.rankN D j hj]
  show Even (D.R.k + j * (D.R.t + 1))
  obtain ⟨c, hc⟩ := D.R.t_odd
  exact D.R.k_even.add (Even.mul_left ⟨c + 1, by omega⟩ j)

end GlobalTheory.Fam.KomExist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesUnderInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesUnderInjective
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.PlaceInj

theorem under_injective : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → Function.Injective (fun i : {PP // PP ∈ (pk W).Pg ∨ QAll W PP} => HeightOneSpectrum.under (𝓞 D.host.F) i.1) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW
  have lev : (pk W).toLevCh.Is W.P.A3.A.μ0 := hW.bot.hyp.2.2.2.1.lev
  rintro ⟨P, hP⟩ ⟨P', hP'⟩ h
  simp only at h
  apply Subtype.ext
  show P = P'

  have key : ∀ A B : Formalism.L2.DIV.Pl D.host.E, A ∈ (pk W).Pg → (B ∈ (pk W).Pg ∨ QAll W B) →
      A.under (𝓞 D.host.F) = B.under (𝓞 D.host.F) → A = B := by
    intro A B hA hB hAB
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hAB.symm with e | e
    · exact e.symm
    · exfalso
      have hc : Formalism.IndefR.Lev.IsConjPl A B := GlobalTheory.GoodPrimes.isConjPl_iff.2 e
      rcases hB with hB | ⟨t, hB⟩
      · exact (GlobalTheory.ChainEquiv.places_sep _ _ lev W.P.A3.A.μ0).1 A hA B (Or.inl hB) hc
      · exact (GlobalTheory.ChainEquiv.places_sep _ _ lev t).1 A hA B (Or.inr hB) hc
  rcases hP with hP | hP
  · exact key P P' hP hP' h
  · rcases hP' with hP' | hP'
    · exact (key P' P hP' (Or.inr hP) h.symm).symm
    · exact hW.sel P P' hP hP' h

end GlobalTheory.Fam.PlaceInj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesUnderInjectiveStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_places_under_injective : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → Function.Injective (fun i : {PP // PP ∈ (pk W).Pg ∨ QAll W PP} => HeightOneSpectrum.under (𝓞 D.host.F) i.1) := by
  first | exact @GlobalTheory.Fam.PlaceInj.under_injective | exact GlobalTheory.Fam.PlaceInj.under_injective | (intros; apply GlobalTheory.Fam.PlaceInj.under_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowStepValue
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.PenLevOff

section Cut

open GlobalTheory.FinPl GlobalTheory.FinPl.SetCut

set_option synthInstance.maxHeartbeats 200000

variable {D : D7}

theorem prV_comm (v : GlobalTheory.FinPl.Pl D) (z : Af ↥D.host.F ⊗[↥D.host.F] D.host.E) :
    Formalism.UG.prV (E := D.host.E) v ((Algebra.TensorProduct.comm (↥D.host.F) (Af ↥D.host.F) D.host.E) z) =
      (Algebra.TensorProduct.comm _ _ _) (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul a e =>
    rw [Algebra.TensorProduct.comm_tmul]
    simp only [Formalism.UG.prV, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.comm_tmul]
    rfl
  | add a b ha hb =>
    simp only [map_add (f := _)]
    exact congrArg₂ (· + ·) ha hb

theorem prV_toEAf_congr (v : GlobalTheory.FinPl.Pl D) {y y' : AE D} (h : GlobalTheory.FinPl.compAt D v y = GlobalTheory.FinPl.compAt D v y') :
    Formalism.UG.prV (E := D.host.E) v (toEAf D y) = Formalism.UG.prV (E := D.host.E) v (toEAf D y') := by
  unfold GlobalTheory.FinPl.compAt at h
  unfold toEAf
  simp only [RingHom.comp_apply] at h ⊢
  generalize finPart D y = z at h ⊢
  generalize finPart D y' = z' at h ⊢
  refine (prV_comm v z).trans (Eq.trans ?_ (prV_comm v z').symm)
  rw [h]

theorem bc_congr (V : HSp D) {n : ℕ} (hn : V.rank = n) (v : GlobalTheory.FinPl.Pl D) {g h : GA D V} {x y : GL (Fin n) (EF D)}
    (hx : x.1 = finM V hn g) (hy : y.1 = finM V hn h)
    (e : ∀ i j, GlobalTheory.FinPl.compAt D v (Formalism.L2.Theta.mt V g i j) = GlobalTheory.FinPl.compAt D v (Formalism.L2.Theta.mt V h i j)) :
    Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x = Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) y := by
  apply Units.ext
  ext i j
  change Formalism.UG.prV (E := D.host.E) v (x.1 i j) = Formalism.UG.prV (E := D.host.E) v (y.1 i j)
  rw [hx, hy]
  simp only [GlobalTheory.AdForm.finM, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
  exact prV_toEAf_congr v (e _ _)

theorem bc_eq_one (V : HSp D) {n : ℕ} (hn : V.rank = n) {P : GlobalTheory.FinPl.Pl D → Prop} {v : GlobalTheory.FinPl.Pl D} (hv : ¬ P v) {g : GA D V}
    (hg : g ∈ grpAt V P) {x : GL (Fin n) (EF D)} (hx : x.1 = finM V hn g) :
    Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x = 1 := by
  have h1 : (1 : GL (Fin n) (EF D)).1 = finM V hn 1 := by
    subst hn
    rw [GlobalTheory.AdForm.CongAtIdem.finM_rfl, GlobalTheory.SplitCut.mt_one, Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  rw [bc_congr V hn v hx h1 fun i j => ?_, map_one]
  have := ((mem_grpAt_iff_parts V P g).1 hg i j).2 v hv
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at this
  rw [this, GlobalTheory.SplitCut.mt_one]

abbrev cutAt (V : HSp D) (v : GlobalTheory.FinPl.Pl D) : GA D V →* GA D V := cutG V _ (idemQ_mul_self {v})

theorem cutAt_mem (V : HSp D) (v : GlobalTheory.FinPl.Pl D) (g : GA D V) : cutAt V v g ∈ grpAt V (· ∈ ({v} : Finset (GlobalTheory.FinPl.Pl D))) :=
  cutG_mem_Q V {v} g

theorem compAt_cutAt (V : HSp D) (v : GlobalTheory.FinPl.Pl D) (g : GA D V) (i j) :
    GlobalTheory.FinPl.compAt D v (Formalism.L2.Theta.mt V (cutAt V v g) i j) = GlobalTheory.FinPl.compAt D v (Formalism.L2.Theta.mt V g i j) := by
  rw [mt_cutG, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, RingHom.map_add (f := _), RingHom.map_mul,
    RingHom.map_mul, RingHom.map_sub, RingHom.map_one, (parts_idemQ {v}).2 v, if_pos (Finset.mem_singleton_self v), sub_self,
    zero_mul, one_mul, add_zero]

theorem grpAt_mono (V : HSp D) {P Q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ v, P v → Q v) : grpAt V P ≤ grpAt V Q := fun g hg =>
  (mem_grpAt_iff_parts V Q g).2 fun i j =>
    ⟨((mem_grpAt_iff_parts V P g).1 hg i j).1, fun w hw => ((mem_grpAt_iff_parts V P g).1 hg i j).2 w fun h' => hw (h w h')⟩

theorem cutAt_eq_one (V : HSp D) {P : GlobalTheory.FinPl.Pl D → Prop} {v : GlobalTheory.FinPl.Pl D} (hv : ¬ P v) {g : GA D V} (hg : g ∈ grpAt V P) :
    cutAt V v g = 1 := by
  have h := cutG_left V {v} (one_mem _) (grpAt_mono V (Q := (· ∉ ({v} : Finset (GlobalTheory.FinPl.Pl D))))
    (fun w hw hm => hv (Finset.mem_singleton.1 hm ▸ hw)) hg)
  rwa [one_mul] at h

end Cut

section Level

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
  {Ch : ℕ → Type} {A : TwDat I l Z u a Ch}


set_option maxHeartbeats 1000000 in
theorem mem_U_iff (hA : A.Is) (j : ℕ) (hj : j ≤ B.R.m) (β : Ch j) (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :
    g ∈ A.U j β ↔ g ∈ GfC _ ∧ ∀ v, cutAt _ v g ∈ A.U j β := by
  have ex := GlobalTheory.AdForm.RdVal.finM_mem ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj) (gramN (I.rec7 l Z) j hj) rfl
  constructor
  · intro hg
    obtain ⟨hC, κ, hκ⟩ := (hA.U j hj β g).1 hg
    refine ⟨hC, fun v => (hA.U j hj β _).2 ⟨GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ (cutAt_mem _ v g), ?_⟩⟩
    obtain ⟨x, hx⟩ := ex (cutAt _ v g)
    refine ⟨⟨x.1, ((A.K j hj β).lev.U_eq _).2 ⟨x.2, fun w => ?_⟩⟩, hx⟩
    by_cases hw : w = v
    · subst hw
      rw [bc_congr _ _ w hx hκ (compAt_cutAt _ w g)]
      exact (((A.K j hj β).lev.U_eq _).1 κ.2).2 w
    · rw [bc_eq_one _ _ (P := (· ∈ ({v} : Finset _))) (fun h => hw (Finset.mem_singleton.1 h)) (cutAt_mem _ v g) hx]
      exact one_mem _
  · rintro ⟨hC, h⟩
    refine (hA.U j hj β _).2 ⟨hC, ?_⟩
    obtain ⟨x, hx⟩ := ex g
    refine ⟨⟨x.1, ((A.K j hj β).lev.U_eq _).2 ⟨x.2, fun w => ?_⟩⟩, hx⟩
    obtain ⟨-, κ, hκ⟩ := (hA.U j hj β _).1 (h w)
    rw [← bc_congr _ _ w hκ hx (compAt_cutAt _ w g)]
    exact (((A.K j hj β).lev.U_eq _).1 κ.2).2 w


set_option maxHeartbeats 1000000 in
theorem mem_of_uloc_le {a' : I.ι} {Ch' : ℕ → Type} {A' : TwDat I l Z u a' Ch'} (hA : A.Is) (hA' : A'.Is) (j : ℕ) (hj : j ≤ B.R.m) (β : Ch j)
    (β' : Ch' j) (v : GlobalTheory.FinPl.Pl (I.rec7 l Z)) (hle : (A.K j hj β).lev.Uloc v ≤ (A'.K j hj β').lev.Uloc v)
    {g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)} (hv : g ∈ GlobalTheory.FinPl.grpAt _ (· ∈ ({v} : Finset _))) (hg : g ∈ A.U j β) :
    g ∈ A'.U j β' := by
  obtain ⟨hC, κ, hκ⟩ := (hA.U j hj β g).1 hg
  refine (hA'.U j hj β' g).2 ⟨hC, ⟨κ.1, ((A'.K j hj β').lev.U_eq _).2 ⟨(((A.K j hj β).lev.U_eq _).1 κ.2).1, fun w => ?_⟩⟩, hκ⟩
  by_cases hw : w = v
  · subst hw
    exact hle ((((A.K j hj β).lev.U_eq _).1 κ.2).2 w)
  · rw [bc_eq_one _ _ (P := (· ∈ ({v} : Finset _))) (fun h => hw (Finset.mem_singleton.1 h)) hv hκ]
    exact one_mem _

end Level

end GlobalTheory.PenLevOff
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowFamilyValue
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PenultimateDatumUnchangedFramesCongruentOneStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PenultimateDatumUnchangedFramesCongruentOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.PenPsiInv

open GlobalTheory.CongLevel

section Ext

variable {E : Type} [Field E]

theorem resX_extE {n : ℕ} (c : ℕ) (κ : (Fin n → E) ≃ₗ[E] (Fin n → E)) (v : Fin (n + c) → E) :
    resX c (extE c κ v) = κ (resX c v) := by
  rw [extE_apply, map_add (f := _), resX_inX]
  abel

theorem atNL_inX {n : ℕ} (c : ℕ) (w : Fin n → E) : atNL E (n + c) n (Loc.inX E n c w) = 0 := by
  unfold atNL
  split_ifs with h
  · rw [LinearMap.proj_apply, inX_apply, dite_eq_right (lt_irrefl n)]
  · rfl

theorem atNL_extE {n : ℕ} (c : ℕ) (κ : (Fin n → E) ≃ₗ[E] (Fin n → E)) (v : Fin (n + c) → E) :
    atNL E (n + c) n (extE c κ v) = atNL E (n + c) n v := by
  rw [extE_apply, map_add (f := _), atNL_inX, add_zero]

theorem joinCol_inFr {n' c' n c : ℕ} (f : Sp E n' ≃ₗ[E] Sp E n') (f' : Sp E n ≃ₗ[E] Sp E n) (x : HomE E n' n)
    (y : Sp E n) :
    joinCol (c' := c') (c := c) (inFr f f' x) (f'.symm y) =
      (extE c f'.symm).toLinearMap ∘ₗ joinCol (c' := c') (c := c) x y ∘ₗ (extE c' f).toLinearMap := by
  apply LinearMap.ext
  intro v
  simp only [joinCol, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.add_apply, LinearMap.smulRight_apply]
  rw [extE_inX]
  congr 1
  have h1 : LinearMap.funLeft E E (Fin.castAdd c') (extE c' f v) = f (LinearMap.funLeft E E (Fin.castAdd c') v) :=
    resX_extE c' f v
  rw [h1, atNL_extE, map_add (f := _), map_smul]
  rfl

end Ext

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu)

theorem extE_mem_Jat (sharp : Bool) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.E)) (hw : w ∈ Pr.vGs)
    (hd : ∀ a : X.E, IntAt w a → redP w a = 0 → IntAt w (a / (qOf w : X.E)))
    (κ : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (hκ : κ ∈ GLint X.E (R.N j) w)
    (hr : ∀ x ∈ stdAt X.E (R.N j) w, redV w (κ x) = redV w x) :
    extE (cOf R j) κ ∈ Jat (Pr := Pr) sharp j w := by
  have h := (Subgroup.mem_inf.1
    (GlobalTheory.Mem.Col2.LevMod.extE_mem_Cbe (Pr := Pr) sharp j w hw hd 1 (one_mem _) κ hκ hr)).2
  rw [Subgroup.mem_comap, inv_one, map_one] at h
  exact h

theorem lamRow_extE (sharp : Bool) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.E)) (hw : w ∈ Pr.vGs)
    (hd : ∀ a : X.E, IntAt w a → redP w a = 0 → IntAt w (a / (qOf w : X.E)))
    (κ : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (hκ : κ ∈ GLint X.E (R.N j) w)
    (hr : ∀ x ∈ stdAt X.E (R.N j) w, redV w (κ x) = redV w x) :
    lamRow Ch mu sharp j w (extE (cOf R j) κ).toLinearMap = 1 := by
  have hq : ((qOf w : ℕ) : X.E) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have e : (extE (cOf R j) κ).toLinearMap = LinearMap.id + ((qOf w : ℕ) : X.E) •
      (((qOf w : ℕ) : X.E)⁻¹ • ((extE (cOf R j) κ).toLinearMap - LinearMap.id)) := by
    rw [smul_inv_smul₀ hq, add_sub_cancel]
  rw [e]
  refine GlobalTheory.LamRowCong.lamRow_one_add_q Ch mu sharp j w hw _ fun v hv => ?_
  unfold lamYat at hv ⊢
  rw [if_pos hw] at hv ⊢
  exact extE_cong w (qOf w) (cOf R j) (fun i => i + 1) hd κ hκ hr v hv

theorem muAt_det_extE (i : ℕ) {n : ℕ} (c : ℕ)
    (hd : ∀ a : X.E, IntAt P.1 a → redP P.1 a = 0 → IntAt P.1 (a / (qOf P.1 : X.E)))
    (κ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (hκ : κ ∈ GLint X.E n P.1)
    (hr : ∀ x ∈ stdAt X.E n P.1, redV P.1 (κ x) = redV P.1 x) :
    muAt Ch sel mu cst i P ((LinearEquiv.det (extE c κ) : X.Eˣ) : X.E) = 1 := by
  refine GlobalTheory.TwU.MidIndep.muAt_det_cong Ch sel mu cst i P (n + c) 1 le_rfl _ fun v hv => ?_
  rw [pow_one]
  rw [GlobalTheory.DatumLaw.stdAt_eq] at hv ⊢
  exact extE_cong P.1 (qOf P.1) c 0 hd κ hκ hr v hv

end Main

theorem psiAt_one_inFr : ∀ {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Formalism.BasicNotions.Ranks} (Ch : Formalism.L2.Col.Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ} (mu : Formalism.L2.DIV.Tup X.F X.E X.K S₀) (cst : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu)) (s : ℕ) (P : Formalism.L2.Col.rowSG Pr sel mu), P.1 ∈ Pr.vGs → R.m = s + 2 → (∀ a : X.E, Formalism.L2.Col.IntAt P.1 a → Formalism.L2.Col.redP P.1 a = 0 → Formalism.L2.Col.IntAt P.1 (a / (Formalism.L2.Col.qOf P.1 : X.E))) → ∀ (f : Formalism.L2.Col.Sp X.E (R.N s) ≃ₗ[X.E] Formalism.L2.Col.Sp X.E (R.N s)) (f' : Formalism.L2.Col.Sp X.E (R.N (s + 1)) ≃ₗ[X.E] Formalism.L2.Col.Sp X.E (R.N (s + 1))), f ∈ Formalism.L2.Col.GLint X.E (R.N s) P.1 → (∀ x ∈ Formalism.L2.Col.stdAt X.E (R.N s) P.1, Formalism.L2.Col.redV P.1 (f x) = Formalism.L2.Col.redV P.1 x) → f' ∈ Formalism.L2.Col.GLint X.E (R.N (s + 1)) P.1 → (∀ x ∈ Formalism.L2.Col.stdAt X.E (R.N (s + 1)) P.1, Formalism.L2.Col.redV P.1 (f' x) = Formalism.L2.Col.redV P.1 x) → ∀ (x : Formalism.L2.Col.HomE X.E (R.N s) (R.N (s + 1))) (y : Formalism.L2.Col.Sp X.E (R.N (s + 1))), Formalism.L2.Col.PsiAt Ch sel mu cst s P 1 (Formalism.L2.Col.inFr f f' x) (f'.symm y) = Formalism.L2.Col.PsiAt Ch sel mu cst s P 1 x y := by
  intro X Pr R Ch sel S₀ mu cst s P hP hm hd f f' hf hr hf' hr' x y
  have hi : s + 2 ≤ R.m := hm.ge
  have hg : f'.symm ∈ GLint X.E (R.N (s + 1)) P.1 := inv_mem hf'
  have hgr : ∀ v ∈ stdAt X.E (R.N (s + 1)) P.1, redV P.1 (f'.symm v) = redV P.1 v := fun v hv => by
    have h := hr' _ ((hg v).2 hv)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have h1 := GlobalTheory.DatumLaw.phiAt_target Ch sel mu cst cst.sharp hi P (extE_mem_Jat cst.sharp (s + 1) P.1 hP hd _ hg hgr)
    (joinCol x y ∘ₗ (extE (cOf R s) f).toLinearMap)
  have h2 := GlobalTheory.DatumLaw.phiAt_source Ch sel mu cst cst.sharp hi P (extE_mem_Jat cst.sharp s P.1 hP hd _ hf hr) (joinCol x y)
  rw [muAt_det_extE Ch sel mu cst P s _ hd _ hg hgr, lamRow_extE Ch mu cst.sharp (s + 1) P.1 hP hd _ hg hgr, mul_one, one_mul] at h1
  rw [muAt_det_extE Ch sel mu cst P s _ hd _ hf hr, lamRow_extE Ch mu cst.sharp s P.1 hP hd _ hf hr, mul_one, one_mul] at h2
  unfold PsiAt
  rw [GlobalTheory.SymBridge.PsiStep.omPhi_one_one, GlobalTheory.SymBridge.PsiStep.omPhi_one_one, joinCol_inFr, h1, h2]

end GlobalTheory.PenPsiInv
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.penultimateDatum_unchanged_frames_congruent_one : ∀ {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Formalism.BasicNotions.Ranks} (Ch : Formalism.L2.Col.Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ} (mu : Formalism.L2.DIV.Tup X.F X.E X.K S₀) (cst : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu)) (s : ℕ) (P : Formalism.L2.Col.rowSG Pr sel mu), P.1 ∈ Pr.vGs → R.m = s + 2 → (∀ a : X.E, Formalism.L2.Col.IntAt P.1 a → Formalism.L2.Col.redP P.1 a = 0 → Formalism.L2.Col.IntAt P.1 (a / (Formalism.L2.Col.qOf P.1 : X.E))) → ∀ (f : Formalism.L2.Col.Sp X.E (R.N s) ≃ₗ[X.E] Formalism.L2.Col.Sp X.E (R.N s)) (f' : Formalism.L2.Col.Sp X.E (R.N (s + 1)) ≃ₗ[X.E] Formalism.L2.Col.Sp X.E (R.N (s + 1))), f ∈ Formalism.L2.Col.GLint X.E (R.N s) P.1 → (∀ x ∈ Formalism.L2.Col.stdAt X.E (R.N s) P.1, Formalism.L2.Col.redV P.1 (f x) = Formalism.L2.Col.redV P.1 x) → f' ∈ Formalism.L2.Col.GLint X.E (R.N (s + 1)) P.1 → (∀ x ∈ Formalism.L2.Col.stdAt X.E (R.N (s + 1)) P.1, Formalism.L2.Col.redV P.1 (f' x) = Formalism.L2.Col.redV P.1 x) → ∀ (x : Formalism.L2.Col.HomE X.E (R.N s) (R.N (s + 1))) (y : Formalism.L2.Col.Sp X.E (R.N (s + 1))), Formalism.L2.Col.PsiAt Ch sel mu cst s P 1 (Formalism.L2.Col.inFr f f' x) (f'.symm y) = Formalism.L2.Col.PsiAt Ch sel mu cst s P 1 x y := by
  intro X Pr R Ch sel S₀ mu cst s P hP hm hd f f' hf hr hf' hr' x y
  exact GlobalTheory.PenPsiInv.psiAt_one_inFr Ch sel mu cst s P hP hm hd f f' hf hr hf' hr' x y
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel
set_option maxHeartbeats 1000000

noncomputable section
namespace GlobalTheory.Fam.PenLoc

theorem psiAt_one_eq {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Formalism.BasicNotions.Ranks} (Ch : Formalism.L2.Col.Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ S₁ : Set ℕ} (mu : Formalism.L2.DIV.Tup X.F X.E X.K S₀)
    (mu' : Formalism.L2.DIV.Tup X.F X.E X.K S₁) (cst : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu))
    (cst' : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu')) (s : ℕ) (P : Formalism.L2.Col.rowSG Pr sel mu)
    (P' : Formalism.L2.Col.rowSG Pr sel mu') (hPP : P.1 = P'.1) (hmem : P.1 ∈ Pr.vGs) (hsh : cst.sharp = cst'.sharp)
    (x : Formalism.L2.Col.HomE X.E (R.N s) (R.N (s + 1))) (y : Formalism.L2.Col.Sp X.E (R.N (s + 1))) :
    Formalism.L2.Col.PsiAt Ch sel mu cst s P 1 x y = Formalism.L2.Col.PsiAt Ch sel mu' cst' s P' 1 x y := by
  have hmem' : P'.1 ∈ Pr.vGs := hPP ▸ hmem
  unfold Formalism.L2.Col.PsiAt
  rw [GlobalTheory.SymBridge.PsiStep.omPhi_one_one, GlobalTheory.SymBridge.PsiStep.omPhi_one_one]
  unfold Formalism.L2.Col.PhiAt
  rw [if_pos hmem, if_pos hmem', hsh, hPP]

theorem lastStepPoints_sub_integral_of_uniformiser_inv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s κ : ℕ}
    (S S' : GlobalTheory.SymChain.SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
    (h : valuation k (((S'.ϖ⁻¹ : kˣ) : k) - ((S.ϖ⁻¹ : kˣ) : k)) ≤ 1) (r : GlobalTheory.StepData.XIx (Fin κ) t (s + 1)) :
    S.y0 t r - S'.y0 t r ∈ 𝒪[k] := by
  unfold GlobalTheory.SymChain.SymData.y0
  by_cases hr : r = Sum.inl (Sum.inr 0)
  · subst hr
    simp only [Pi.single_eq_same]
    have h3 := neg_mem (show ((S'.ϖ⁻¹ : kˣ) : k) - ((S.ϖ⁻¹ : kˣ) : k) ∈ 𝒪[k] from h)
    rwa [neg_sub] at h3
  · simp [Pi.single_eq_of_ne hr]

end GlobalTheory.Fam.PenLoc
end
end
