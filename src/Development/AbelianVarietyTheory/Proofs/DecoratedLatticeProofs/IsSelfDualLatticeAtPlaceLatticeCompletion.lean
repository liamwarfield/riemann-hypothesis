module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmEulerProductDiscrUnramified
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContAutRapidDecBoundedIntegrable
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixSchwartzMajorantMeasurableRationalSh
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupActionFourierBesselBasePoint
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapVacuumAtGoodPlace
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.FiniteAdeleRingNontrivial

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open NumberField GlobalTheory.FinPl.FrameLat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.IwaPlace.LocSD

variable {D : D7}

theorem exists_idem (v : Pl D) :
    ∃ ε : AE D, cA D ε = ε ∧ ε ∈ intAt D (· = v) ∧ ∀ a, a ∈ idAt D (· = v) → ε * a = a := by
  have hs := GlobalTheory.LatAlmostStd.intSupp_single_mul v (α := 1) (fun w => by rw [map_one]; exact one_mem _)
  rw [mul_one] at hs
  have hp : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ⟨_, rfl, GlobalTheory.LatAlmostStd.evalV_single_same v 1, fun w hw => GlobalTheory.LatAlmostStd.evalV_single_ne v 1 hw⟩
  refine ⟨pairA D.host.F 0 (singleV D.host.F v 1) ⊗ₜ[D.host.F] (1 : D.host.E), ?_,
    ⟨GlobalTheory.FinPl.LatMem.tmul_mem_idAt hs.2 _, AddSubgroup.subset_closure ⟨_, hs.1, 1, rfl⟩⟩,
    fun a ha => ((placeIdem_acts D v _ hp).1 a).1 ha⟩
  change pairA D.host.F 0 (singleV D.host.F v 1) ⊗ₜ[D.host.F] (D.sp.cm.sig (1 : D.host.E)) = _
  rw [map_one]

variable {S : HSp D}

theorem hermAt_mul_inc (y : Fin S.rank → AE D) (a : AE D) (s : Fin S.rank → D.host.E) :
    hermAt S y (fun i => a * incA D (s i)) = cA D a * pairing S s y := by
  unfold hermAt pairing FrameLat.row
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.map_mul, RingHom.map_mul, cA_incA, show gA S i j = incA D (S.gram i j) from rfl]
  ring

theorem hermAt_sum_right {m : ℕ} (y : Fin S.rank → AE D) (x : Fin m → Fin S.rank → AE D) :
    hermAt S y (fun i => ∑ l, x l i) = ∑ l, hermAt S y (x l) := by
  unfold hermAt
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := Finset.univ (α := Fin m))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

theorem hermAt_mem_idAt {P : Pl D → Prop} {y : Fin S.rank → AE D} (hy : ∀ i, y i ∈ idAt D P)
    (x : Fin S.rank → AE D) : hermAt S y x ∈ idAt D P :=
  Ideal.sum_mem _ fun _ _ => Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

variable {L : Lat S}

theorem exists_mul_mem (hL : IsSelfDualC S L) (v : Pl D) :
    ∃ m : ℕ, 0 < m ∧ ∀ y : Fin S.rank → AE D, (∀ i, y i ∈ intAt D (· = v)) → (m : AE D) • y ∈ latV S L (· = v) := by
  have hfull : Submodule.IsFullLattice D.host.E L := by
    haveI : Submodule.IsLattice D.host.E L := hL.1
    refine ⟨?_⟩
    obtain ⟨m, s, s', hs, _, hd⟩ := GlobalTheory.FinPl.LatMem.exists_dualBasis S hL
    apply eq_top_iff.mpr
    intro y _
    have hy : y = ∑ l, (∑ b, (∑ k, star (s' l k) * S.gram k b) * y b) • s l := by
      funext a
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have heq : (∑ l, (∑ b, (∑ k, star (s' l k) * S.gram k b) * y b) * s l a) =
          ∑ b, ∑ l, (∑ k, star (s' l k) * S.gram k b) * y b * s l a := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun l _ => Finset.sum_mul ..
      rw [heq]
      have hterm : ∀ b, (∑ l, (∑ k, star (s' l k) * S.gram k b) * y b * s l a) =
          (if a = b then 1 else 0) * y b := by
        intro b
        calc
          _ = ∑ l, (s l a * ∑ k, star (s' l k) * S.gram k b) * y b := by
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
          _ = _ := by rw [← Finset.sum_mul, hd]
      simp_rw [hterm]
      simp
    rw [hy]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span (hs l))
  obtain ⟨N, hN, -, h⟩ := GlobalTheory.LatAlmostStd.exists_commensurable L hfull
  refine ⟨N.natAbs, Int.natAbs_pos.2 hN, fun y hy => ?_⟩
  have h1 : (N : AE D) • y ∈ latV S L (· = v) := by
    have e : (N : AE D) • y = ∑ i, fun k => y i * incA D ((Pi.single i (N • ((1 : 𝓞 D.host.E) : D.host.E)) :
        Fin S.rank → D.host.E) k) := by
      funext k
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · rw [Pi.single_eq_same, map_zsmul, show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, RingHom.map_one,
          zsmul_one, Pi.smul_apply, smul_eq_mul, mul_comm]
      · intro i _ hi
        rw [Pi.single_eq_of_ne' hi, RingHom.map_zero, mul_zero]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    rw [e]
    exact sum_mem fun i _ => int_mul_mem (hy i) (h i 1)
  rcases Int.natAbs_eq N with e | e
  · rw [← Int.cast_natCast, ← e]; exact h1
  · have e' : ((N.natAbs : ℕ) : ℤ) = -N := by omega
    rw [← Int.cast_natCast, e', Int.cast_neg, neg_smul]; exact neg_mem h1

theorem isSDAt_latV : ∀ (D : D7) (S : HSp D) (L : Lat S) (v : Pl D), IsSelfDualC S L → IsSDAt S v (latV S L (· = v)) := by
  intro D S L v hL
  refine ⟨fun y hy i => latV_supp hy i, exists_mul_mem hL v, fun y hy => ⟨fun hyL x hx => ?_, fun h => ?_⟩⟩
  · refine ⟨hermAt_mem_idAt hy x, ?_⟩
    obtain ⟨m, s, s', hs, hs', hd⟩ := exists_expansion hL
    have e : x = fun i => ∑ l, (fun l i => pairing S (s' l) x * incA D (s l i)) l i := funext fun i => hd x i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, hermAt_sum_right, map_sum]
    refine sum_mem fun l _ => ?_
    rw [hermAt_mul_inc, RingHom.map_mul]
    exact mul_mem_intAE ((cA_int_iff _).2 (pairing_int hL (hs' l) hx)) (pairing_int hL (hs l) hyL)
  · obtain ⟨ε, hc, hε, hact⟩ := exists_idem v
    refine mem_of_pairing hL hy fun s hs => ?_
    have h1 := (h _ (int_mul_mem hε hs)).2
    rwa [hermAt_mul_inc, hc, hact (pairing S s y) (Ideal.sum_mem _ fun b _ => Ideal.mul_mem_left _ _ (hy b))] at h1

end GlobalTheory.IwaPlace.LocSD

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSelfDualLatticeAtPlace_latticeCompletion : ∀ (D : D7) (S : HSp D) (L : Lat S) (v : Pl D), IsSelfDualC S L → IsSDAt S v (latV S L (· = v)) := by
  first | exact @GlobalTheory.IwaPlace.LocSD.isSDAt_latV | exact GlobalTheory.IwaPlace.LocSD.isSDAt_latV | (intros; apply GlobalTheory.IwaPlace.LocSD.isSDAt_latV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAll
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAll
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open NumberField IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.TamePlaces

theorem extUnramAt (D : D7) (v : Pl D) : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.ExtUnramAt D v := by
  intro P hP _
  refine not_dvd_differentIdeal_iff.1 ?_
  rw [GlobalTheory.DensityEuler.differentIdeal_eq_top D.sp.cm]
  intro hd
  exact hP.ne_top (top_le_iff.1 (Ideal.dvd_iff_le.1 hd))

theorem split_over_two (D : D7) (v : Pl D) (h2 : (2 : 𝓞 D.host.F) ∈ v.asIdeal) :
    ∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε := by
  obtain ⟨e, he, hc, hs, -⟩ := GlobalTheory.SplitIdem.exists_split_idempotent D v h2
  have hε : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ⟨singleV D.host.F v 1, rfl, GlobalTheory.SplitIdem.evalV_singleV_same D.host.F v 1,
      fun v' hv' => GlobalTheory.SplitIdem.evalV_singleV_ne D.host.F v 1 hv'⟩
  exact ⟨e, _, ⟨he, hc, v, _, hε, hs⟩, hε, hs⟩

theorem tame : ∀ (D : D7) (v : Pl D), Tame D v := by
  intro D v
  refine ⟨extUnramAt D v, ?_⟩
  by_cases h2 : (2 : 𝓞 D.host.F) ∈ v.asIdeal
  · exact Or.inr (split_over_two D v h2)
  · exact Or.inl h2

end GlobalTheory.FinPl.TamePlaces
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAllStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTameFinitePlaceHermitian_all : ∀ (D : D7) (v : Pl D), Tame D v := by
  first | exact @GlobalTheory.FinPl.TamePlaces.tame | exact GlobalTheory.FinPl.TamePlaces.tame | (intros; apply GlobalTheory.FinPl.TamePlaces.tame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsWeilDatumConjNegHermitianSpaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsWeilDatumConjNegHermitianSpaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.ConjWeil

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.ChiGrid

variable {D : D7}

theorem cj_id_cj_id {X : Type} (f : X → ℂ) : cj id (cj id f) = f := cj_cj id id (fun _ => rfl) f

theorem cj_id_apply {X : Type} (f : X → ℂ) (x : X) : cj id f x = starRingEnd ℂ (f x) := rfl

theorem hecke_inv {χ : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) : IsHeckeChar D χ⁻¹ :=
  ⟨(h.1.inv : Continuous fun x => (χ x)⁻¹), fun x => by rw [MonoidHom.inv_apply, h.2 x, inv_one]⟩

theorem enorm_conj (z : ℂ) : ‖starRingEnd ℂ z‖ₑ = ‖z‖ₑ := by
  simp [enorm]

theorem mt_negGA_symm (V : HSp D) (g : GA D (negSp V)) : mt V ((negGA V).symm g) = mt (negSp V) g := by
  rw [← mt_negGA, MulEquiv.apply_symm_apply]

theorem continuous_negGA_symm (V : HSp D) : Continuous (negGA V).symm :=
  Continuous.subtype_mk continuous_subtype_val _

theorem UJ_neg {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A) (J : Matrix n n A) :
    Formalism.UG.UJ σ (-J) = Formalism.UG.UJ σ J := by
  ext g
  show Formalism.UG.cT σ (g : Matrix n n A) * (-J) * (g : Matrix n n A) = -J ↔
    Formalism.UG.cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J
  rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem negGA_symm_mem_GQ (V : HSp D) (γ : GA D (negSp V)) (h : γ ∈ GQ (negSp V)) : (negGA V).symm γ ∈ GQ V := by
  unfold GQ HFinIn HFin at *
  erw [Subgroup.mem_subgroupOf] at h ⊢
  convert h using 2 <;> first | rfl | exact (UJ_neg _ _).symm

theorem splitFacO_inv (χS χT : (AE D)ˣ →* Circle) (x y : (AE D)ˣ) :
    ((splitFacO χS⁻¹ χT⁻¹ x y : Circle) : ℂ) = starRingEnd ℂ (splitFacO χS χT x y) := by
  rw [← Circle.coe_inv_eq_conj]
  congr 1
  simp only [splitFacO, MonoidHom.inv_apply, inv_inv, _root_.mul_inv_rev]
  exact mul_comm _ _

theorem conjTarget_apply {S T : HSp D} (om : Om S T) (p : GA D S × GA D (negSp T)) (f : WO S T → ℂ) :
    conjTarget om p f = cj id (om (p.1, (negGA T).symm p.2) (cj id f)) := rfl

theorem conjSource_apply {S T : HSp D} (om : Om S T) (p : GA D (negSp S) × GA D T) (f : WO S T → ℂ) :
    conjSource om p f = cj id (om ((negGA S).symm p.1, p.2) (cj id f)) := rfl

theorem actO_negT (S T : HSp D) (g : GA D S) (h : GA D (negSp T)) (w : WO S T) :
    actO S (negSp T) g h w = actO S T g ((negGA T).symm h) w := by
  unfold actO; rw [mt_negGA_symm]

theorem actO_negS (S T : HSp D) (g : GA D (negSp S)) (h : GA D T) (w : WO S T) :
    actO (negSp S) T g h w = actO S T ((negGA S).symm g) h w := by
  unfold actO; rw [← map_inv (negGA S).symm g, mt_negGA_symm]

theorem weil_conjTarget (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : Om S T) (hw : IsWeilDatumO ψ S T χS χT om) :
    IsWeilDatumO ψ S (negSp T) χS⁻¹ χT⁻¹ (conjTarget om) := by
  have I := GlobalTheory.CjNeg.theta_heis_neg D ψ hw.std S T
  have thT : ∀ f : WO S (negSp T) → ℂ, IsThetaFunO ψ S (negSp T) f ↔ IsThetaFunO ψ S T (cj id f) := fun f => by
    have := (I.1 (cj id f)).1
    rwa [cj_id_cj_id] at this
  have hzT : ∀ (w : WO S T) (f : WO S (negSp T) → ℂ),
      heisO ψ S (negSp T) w f = cj id (heisO ψ S T w (cj id f)) := fun w f => by
    have := (I.2 w (cj id f)).1
    rwa [cj_id_cj_id] at this
  refine
    { std := hw.std
      hecS := hecke_inv hw.hecS
      hecT := hecke_inv hw.hecT
      resS := resEta_inv hw.resS
      resT := resEta_inv hw.resT
      om_pres := ?_
      om_heis := ?_
      om_aut := ?_
      om_cont := ?_
      om_unit := ?_
      om_split := ?_ }
  · intro p f hf
    rw [conjTarget_apply, thT, cj_id_cj_id]
    exact hw.om_pres _ _ ((thT f).1 hf)
  · intro g h w₀ f hf
    rw [conjTarget_apply, conjTarget_apply, hzT w₀ f, cj_id_cj_id, hw.om_heis _ _ _ _ ((thT f).1 hf),
      hzT _ (cj id _), cj_id_cj_id, actO_negT]
  · intro γ hγ γ' hγ' f hf
    rw [conjTarget_apply]
    show starRingEnd ℂ (om (γ, (negGA T).symm γ') (cj id f) 0) = f 0
    rw [hw.om_aut γ hγ _ (negGA_symm_mem_GQ T γ' hγ') _ ((thT f).1 hf)]
    show starRingEnd ℂ (starRingEnd ℂ (f 0)) = f 0
    simp
  · intro f hf w
    have hc := hw.om_cont _ ((thT f).1 hf) w
    simp only [conjTarget_apply]
    exact Complex.continuous_conj.comp
      (hc.comp (continuous_fst.prodMk ((continuous_negGA_symm T).comp continuous_snd)))
  · intro μ 𝓕 hμ hF p f hf
    have hu := hw.om_unit μ 𝓕 hμ hF (p.1, (negGA T).symm p.2) (cj id f) ((thT f).1 hf)
    simp only [conjTarget_apply, cj_id_apply, enorm_conj] at hu ⊢
    exact hu
  · intro e he g h hg hh x y hx hy
    obtain ⟨r, hr, H⟩ := hw.om_split e he g ((negGA T).symm h) hg
      (by unfold SuppAt; rw [mt_negGA_symm]; exact hh) x y hx (by unfold IsDetAt; rw [mt_negGA_symm]; exact hy)
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    let ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun f => starRingEnd ℂ (ℓ (cj id f))
        map_add' := fun a b => by
          have : cj id (a + b) = cj id a + cj id b := by funext z; simp [cj_id_apply]
          rw [this, map_add (f := _), map_add (f := _)]
        map_smul' := fun c a => by
          have : cj id (c • a) = starRingEnd ℂ c • cj id a := by funext z; simp [cj_id_apply]
          rw [this, map_smul, smul_eq_mul, map_mul, Complex.conj_conj]; rfl }
    have h1 : starRingEnd ℂ (ℓ (cj id (om (g, (negGA T).symm h) (cj id f)))) =
        (r : ℂ) * (splitFacO χS χT x y : ℂ) * starRingEnd ℂ (ℓ (cj id (cj id f))) :=
      H ℓ' (fun u hu f' hf' => by
        show starRingEnd ℂ (ℓ (cj id (heisO ψ S T u f'))) = starRingEnd ℂ (ℓ (cj id f'))
        rw [← (I.2 u f').1, hℓ u hu (cj id f') ((I.1 f').1.2 hf')]) (cj id f) ((thT f).1 hf)
    rw [cj_id_cj_id, ← conjTarget_apply om (g, h) f] at h1
    rw [splitFacO_inv]
    have h2 := congrArg (starRingEnd ℂ) h1
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal] at h2
    exact h2

theorem weil_conjSource (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : Om S T) (hw : IsWeilDatumO ψ S T χS χT om) :
    IsWeilDatumO ψ (negSp S) T χS⁻¹ χT⁻¹ (conjSource om) := by
  have I := GlobalTheory.CjNeg.theta_heis_neg D ψ hw.std S T
  have thS : ∀ f : WO (negSp S) T → ℂ, IsThetaFunO ψ (negSp S) T f ↔ IsThetaFunO ψ S T (cj id f) := fun f => by
    have := (I.1 (cj id f)).2
    rwa [cj_id_cj_id] at this
  have hzS : ∀ (w : WO S T) (f : WO (negSp S) T → ℂ),
      heisO ψ (negSp S) T w f = cj id (heisO ψ S T w (cj id f)) := fun w f => by
    have := (I.2 w (cj id f)).2
    rwa [cj_id_cj_id] at this
  refine
    { std := hw.std
      hecS := hecke_inv hw.hecS
      hecT := hecke_inv hw.hecT
      resS := resEta_inv hw.resS
      resT := resEta_inv hw.resT
      om_pres := ?_
      om_heis := ?_
      om_aut := ?_
      om_cont := ?_
      om_unit := ?_
      om_split := ?_ }
  · intro p f hf
    rw [conjSource_apply, thS, cj_id_cj_id]
    exact hw.om_pres _ _ ((thS f).1 hf)
  · intro g h w₀ f hf
    rw [conjSource_apply, conjSource_apply, hzS w₀ f, cj_id_cj_id, hw.om_heis _ _ _ _ ((thS f).1 hf),
      hzS _ (cj id _), cj_id_cj_id, actO_negS]
  · intro γ hγ γ' hγ' f hf
    rw [conjSource_apply]
    show starRingEnd ℂ (om ((negGA S).symm γ, γ') (cj id f) 0) = f 0
    rw [hw.om_aut _ (negGA_symm_mem_GQ S γ hγ) γ' hγ' _ ((thS f).1 hf)]
    show starRingEnd ℂ (starRingEnd ℂ (f 0)) = f 0
    simp
  · intro f hf w
    have hc := hw.om_cont _ ((thS f).1 hf) w
    simp only [conjSource_apply]
    exact Complex.continuous_conj.comp
      (hc.comp (((continuous_negGA_symm S).comp continuous_fst).prodMk continuous_snd))
  · intro μ 𝓕 hμ hF p f hf
    have hu := hw.om_unit μ 𝓕 hμ hF ((negGA S).symm p.1, p.2) (cj id f) ((thS f).1 hf)
    simp only [conjSource_apply, cj_id_apply, enorm_conj] at hu ⊢
    exact hu
  · intro e he g h hg hh x y hx hy
    obtain ⟨r, hr, H⟩ := hw.om_split e he ((negGA S).symm g) h
      (by unfold SuppAt; rw [mt_negGA_symm]; exact hg) hh x y (by unfold IsDetAt; rw [mt_negGA_symm]; exact hx) hy
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    let ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun f => starRingEnd ℂ (ℓ (cj id f))
        map_add' := fun a b => by
          have : cj id (a + b) = cj id a + cj id b := by funext z; simp [cj_id_apply]
          rw [this, map_add (f := _), map_add (f := _)]
        map_smul' := fun c a => by
          have : cj id (c • a) = starRingEnd ℂ c • cj id a := by funext z; simp [cj_id_apply]
          rw [this, map_smul, smul_eq_mul, map_mul, Complex.conj_conj]; rfl }
    have h1 : starRingEnd ℂ (ℓ (cj id (om ((negGA S).symm g, h) (cj id f)))) =
        (r : ℂ) * (splitFacO χS χT x y : ℂ) * starRingEnd ℂ (ℓ (cj id (cj id f))) :=
      H ℓ' (fun u hu f' hf' => by
        show starRingEnd ℂ (ℓ (cj id (heisO ψ S T u f'))) = starRingEnd ℂ (ℓ (cj id f'))
        rw [← (I.2 u f').2, hℓ u hu (cj id f') ((I.1 f').2.2 hf')]) (cj id f) ((thS f).1 hf)
    rw [cj_id_cj_id, ← conjSource_apply om (g, h) f] at h1
    rw [splitFacO_inv]
    have h2 := congrArg (starRingEnd ℂ) h1
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal] at h2
    exact h2

theorem conj_isWeilDatumO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : Om S T), IsWeilDatumO ψ S T χS χT om →
      IsWeilDatumO ψ S (GlobalTheory.ChiGrid.negSp T) χS⁻¹ χT⁻¹ (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjTarget om) ∧
      IsWeilDatumO ψ (GlobalTheory.ChiGrid.negSp S) T χS⁻¹ χT⁻¹ (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjSource om) :=
  fun D ψ S T χS χT om hw => ⟨weil_conjTarget D ψ S T χS χT om hw, weil_conjSource D ψ S T χS χT om hw⟩

end GlobalTheory.ConjWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsWeilDatumConjNegHermitianSpacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isWeilDatum_conj_negHermitianSpaces : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S (GlobalTheory.ChiGrid.negSp T) χS⁻¹ χT⁻¹ (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjTarget om) ∧ IsWeilDatumO ψ (GlobalTheory.ChiGrid.negSp S) T χS⁻¹ χT⁻¹ (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjSource om) := by
  first | exact @GlobalTheory.ConjWeil.conj_isWeilDatumO | exact GlobalTheory.ConjWeil.conj_isWeilDatumO | (intros; apply GlobalTheory.ConjWeil.conj_isWeilDatumO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiHandOffAutomorphic
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiHandOffAutomorphic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory

theorem handFBLaw : ∀ D : D7, HandFBLaw D := by
  intro D
  unfold HandFBLaw
  intro ψ σ J B s vL Y Ξ hY hΞ

  obtain ⟨hc, hl, hr⟩ := GlobalTheory.T.pairedThetaKernel_continuous_and_rationally_invariant D ψ σ J B s vL Y Ξ hY hΞ
  refine ⟨fun γ hγ g => ?_, ?_⟩
  ·
    simp only [handFB, hr γ hγ]
  ·
    exact (GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D J.W₀ J.cpt J.v0 (GA D B.A) (pairKer s vL Y Ξ) hc hl).2.1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiHandOffAutomorphicStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiHandOff_automorphic : ∀ D : D7, HandFBLaw D := by
  first | exact @GlobalTheory.handFBLaw | exact GlobalTheory.handFBLaw | (intros; apply GlobalTheory.handFBLaw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiUnipotentTrivialOnLevel
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl GlobalTheory.FinPlLoc Filter Topology
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.PsiUnit

variable {D : D7}


open Formalism.IndefR.Fin.LevelGroupLemmas in
theorem char_eq_one_of_local (ψ : AddChar (AF D.host.F) ℂ) (hψ : Continuous ψ) (t : AF D.host.F)
    (ht : fstA D.host.F t = 0) (h : ∀ v : Pl D, ψ (pairA D.host.F 0 (ePl D (· = v)) * t) = 1) : ψ t = 1 := by
  classical
  have h1 : ∀ A : Finset (Pl D), ψ (idemS A * t) = 1 := by
    intro A
    induction A using Finset.induction_on with
    | empty => rw [idemS_empty, zero_mul, AddChar.map_zero_eq_one]
    | insert v A hv ih =>
      have e : idemS (insert v A) = idemS A + pairA D.host.F 0 (ePl D (· = v)) := by
        unfold idemS
        rw [← pairA_add]
        congr 1
        refine RestrictedProduct.ext _ _ fun w => ?_
        change evalV D.host.F w (sglS (insert v A)) = evalV D.host.F w (sglS A + ePl D (· = v))
        rw [map_add (f := _), evalV_sglS, evalV_sglS, evalV_ePl]
        by_cases hw : w = v
        · subst hw; simp [hv]
        · simp [hw]
      rw [e, add_mul, AddChar.map_add_eq_mul, ih, h, one_mul]
  have h2 := (hψ.tendsto 0).comp (tendsto_AF t ht)
  rw [AddChar.map_zero_eq_one] at h2
  refine tendsto_nhds_unique tendsto_const_nhds (h2.congr fun A => ?_)
  have e : t = idemS A * t + (1 - idemS A) * t := by ring
  change ψ ((1 - idemS A) * t) = ψ t
  conv_rhs => rw [e, AddChar.map_add_eq_mul, h1, one_mul]

theorem trace_idem (Q : Pl D → Prop) (s : AE D) : Algebra.trace (AF D.host.F) (AE D) (idem D Q * s) =
    pairA D.host.F 0 (ePl D Q) * Algebra.trace (AF D.host.F) (AE D) s := by
  rw [← smul_eq_mul (pairA D.host.F 0 (ePl D Q)), ← map_smul, Algebra.smul_def]
  rfl

theorem psiE_eq_one_of_local (ψ : AddChar (AF D.host.F) ℂ) (hψ : Continuous ψ) {P : Pl D → Prop} {s : AE D}
    (hs : s ∈ idAt D P) (h : ∀ v, P v → psiE ψ (idem D (· = v) * s) = 1) : psiE ψ s = 1 := by
  refine char_eq_one_of_local ψ hψ _ ?_ fun v => ?_
  · rw [← (mem_idAt_iff P s).1 hs, trace_idem, map_mul]
    exact zero_mul _
  · rw [← trace_idem]
    by_cases hv : P v
    · exact h v hv
    · have h0 : idem D (· = v) * s = 0 := by
        refine (mem_idOff_iff _ s).1 ((Submodule.mem_iInf _).2 fun w => RingHom.mem_ker.2 ?_)
        exact compAt_of_idAt hs (by rw [w.2]; exact hv)
      rw [h0]
      exact psiE_zero ψ

theorem latV_mono {S : HSp D} {L : Lat S} {P : Pl D → Prop} {v : Pl D} (hv : P v) : latV S L (· = v) ≤ latV S L P := by
  refine AddSubgroup.closure_mono ?_
  rintro y ⟨α, h1, h2, h3⟩
  exact ⟨α, h1, fun w hw => h2 w fun e => hw (e ▸ hv), h3⟩

theorem mulVec_colMul {l m n : ℕ} (A : Mx D l m) (x : Mx D m n) (i : Fin n) (a : AE D) :
    A *ᵥ colMul x i a = colMul (A ⬝ x) i a := by
  funext k
  simp only [Matrix.mulVec, dotProduct, colMul, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.FinPl.PsiUnit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselBasePointIsUnfoldingBasePointSpec
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselBasePointIsUnfoldingBasePointSpec
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB

variable {D : D7} {σ : ℕ}

def eLast (D : D7) (ρ : ℕ) : Fin ρ → D.host.E := fun i => if i.1 + 1 = ρ then 1 else 0

theorem ratV_eLast (ρ : ℕ) : ratV (eLast D ρ) = ell D ρ := by
  funext i
  simp only [ratV, eLast, ell]
  split_ifs <;> simp

def zlQ (B : BesLev D σ) : Matrix (Fin B.L.rank) (Fin (σ + 1)) D.host.E := vecMulVec B.ζ (eLast D (σ + 1))

theorem rat_zlQ (B : BesLev D σ) : (rat (zlQ B) : Mx D B.L.rank (σ + 1)) = zl B := by
  rw [zl, zEll, ← ratV_eLast]
  funext i j
  simp [rat, zlQ, vecMulVec_apply, ratV]

theorem rat_gramQ (W : HSp D) {ρ : ℕ} (x : Matrix (Fin W.rank) (Fin ρ) D.host.E) :
    (rat (gramQ W x) : Mx D ρ ρ) = adj (rat x) ⬝ (gA W ⬝ rat x) := by
  rw [gramQ, rat_mul, rat_mul, rat_conjTranspose]; rfl

theorem gramQ_eq_of_gramSkew {W W' : HSp D} {ρ : ℕ} (x : Matrix (Fin W.rank) (Fin ρ) D.host.E)
    (x' : Matrix (Fin W'.rank) (Fin ρ) D.host.E)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew W (rat x : Mx D W.rank ρ) = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew W' (rat x')) :
    gramQ W x = gramQ W' x' := by
  have hu : IsUnit (-incA D D.host.xi0) :=
    ((isUnit_iff_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)).map (incA D)).neg
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew at h
  rw [hu.smul_left_cancel, Matrix.transpose_inj] at h
  apply rat_injective
  rw [rat_gramQ, rat_gramQ, h]

theorem pairS_mul (T : HSp D) {ρ : ℕ} (x : Mx D T.rank ρ) (c : Mx D ρ ρ) :
    pairS T x (x ⬝ c) = (adj c ⬝ (adj x ⬝ (gA T ⬝ x))).trace := by
  rw [pairS, adj_mul, Matrix.mul_assoc]

theorem gramQ_zlQ_mulVec_last (B : BesLev D σ) (a : Fin (σ + 1) → D.host.E) :
    (gramQ B.L (zlQ B) *ᵥ a) (Fin.last σ) = (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ) * a (Fin.last σ) := by
  simp only [gramQ, zlQ, Matrix.mulVec, dotProduct, Matrix.mul_apply, conjTranspose_apply, vecMulVec_apply, eLast,
    Pi.star_apply, Fin.val_last]
  simp only [if_true, mul_one, star_one]
  rw [Finset.sum_eq_single (Fin.last σ)]
  · simp only [Fin.val_last, if_true, mul_one]
  · intro b _ hb
    have hb' : ¬ (b.1 + 1 = σ + 1) := fun h => hb (Fin.ext (by simp only [Fin.val_last]; omega))
    simp only [hb', if_false, mul_zero, Finset.sum_const_zero, zero_mul]
  · simp

theorem basePoint_spec : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), ∃ x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E,
    (rat x₀ : Mx D B.V.rank (σ + 1)) = x0 B ∧ IsBase B.V x₀ ∧
    Rgrp B.V (rat x₀ : Mx D B.V.rank (σ + 1)) = besGrp B.d B.o ∧
    (∀ a : Fin (σ + 1) → D.host.E, gramQ B.V x₀ *ᵥ a = 0 → a (Fin.last σ) = 0) ∧
    ∀ (S S₀ : HSp D) (d : HypDec S S₀ (σ + 1)) (c : skewA D (σ + 1)), d.qS B.V c (x0 B) = d.qS B.L c (zl B) := by
  intro D σ B
  obtain ⟨x, ⟨hli, hg⟩, hx⟩ := GlobalTheory.T.exists_mem_orb_rat_eq_x0 D σ B
  rw [← rat_zlQ] at hg
  have hG : gramQ B.V x = gramQ B.L (zlQ B) := gramQ_eq_of_gramSkew x (zlQ B) hg
  have hA : adj (x0 B) ⬝ (gA B.V ⬝ x0 B) = adj (zl B) ⬝ (gA B.L ⬝ zl B) := by
    rw [← hx, ← rat_zlQ, ← rat_gramQ, ← rat_gramQ, hG]
  refine ⟨x, hx, ⟨hli, fun u hu => ?_⟩, ?_, fun a ha => ?_, fun S S₀ d c => ?_⟩
  · rw [rat_gramQ, hx, hA, ]
    have hz : zl B ⬝ u.1 = zl B := zEll_mul B.L B.ζ hu
    calc adj u.1 ⬝ (adj (zl B) ⬝ (gA B.L ⬝ zl B) ⬝ u.1) = adj (zl B ⬝ u.1) ⬝ (gA B.L ⬝ (zl B ⬝ u.1)) := by
          rw [adj_mul]; simp only [Matrix.mul_assoc]
      _ = adj (zl B) ⬝ (gA B.L ⬝ zl B) := by rw [hz]
  · ext g
    rw [hx]
    exact ((GlobalTheory.T.mem_besGrp_iff_mt_mul_x0_eq_x0_mul D σ B).1 g).symm
  · have h1 := congrFun ha (Fin.last σ)
    rw [hG, gramQ_zlQ_mulVec_last, Pi.zero_apply] at h1
    exact (mul_eq_zero.1 h1).resolve_left B.line.2
  · rw [HypDec.qS, HypDec.qS, HypDec.symplOH_extX_extY, HypDec.symplOH_extX_extY, pairS_mul, pairS_mul, hA]

end GlobalTheory.Unf.FB
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselBasePointIsUnfoldingBasePointSpecStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierBesselBasePoint_isUnfoldingBasePoint_spec : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), ∃ x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E, (rat x₀ : Mx D B.V.rank (σ + 1)) = x0 B ∧ IsBase B.V x₀ ∧ Rgrp B.V (rat x₀ : Mx D B.V.rank (σ + 1)) = besGrp B.d B.o ∧ (∀ a : Fin (σ + 1) → D.host.E, gramQ B.V x₀ *ᵥ a = 0 → a (Fin.last σ) = 0) ∧ ∀ (S S₀ : HSp D) (d : HypDec S S₀ (σ + 1)) (c : skewA D (σ + 1)), d.qS B.V c (x0 B) = d.qS B.L c (zl B) := by
  exact GlobalTheory.Unf.FB.basePoint_spec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtZeroIncZeroMemLattice
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZeroAt

variable {D : D7}

theorem mulVec_idAt {m n : ℕ} (M : Mx D m n) {P : Pl D → Prop} {y : Fin n → AE D} (hy : ∀ i, y i ∈ idAt D P) :
    ∀ i, (M *ᵥ y) i ∈ idAt D P := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem wittProjectionZero_mem_latticeCompletion_of_splits {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {P : Pl D → Prop}
    (hL₀ : Submodule.IsLattice D.host.E L₀) (hm : ∀ v, P v → MonoAt d L L₀ v) {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L P) : d.p0 *ᵥ y ∈ latV S₀ L₀ P := by
  refine (GlobalTheory.FinPlLoc.part_lat P S₀ L₀ _ hL₀).2 ⟨mulVec_idAt _ (GlobalTheory.FinPlLoc.latV_idAt hy), fun v hv e he => ?_⟩
  rw [← Matrix.mulVec_smul]
  exact ((hm v hv _).1 (GlobalTheory.FinPlLoc.smul_latV v he hy)).2.2

theorem wittCoreInclusion_mem_latticeCompletionAtPlace {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) {L : Lat T} {L₀ : Lat T₀} {P : Pl D → Prop}
    (hL : Submodule.IsLattice D.host.E L) (hm : ∀ v, P v → MonoAt d L L₀ v) {u : Fin T₀.rank → AE D}
    (hu : u ∈ latV T₀ L₀ P) : d.j0 *ᵥ u ∈ latV T L P := by
  refine (GlobalTheory.FinPlLoc.part_lat P T L _ hL).2 ⟨mulVec_idAt _ (GlobalTheory.FinPlLoc.latV_idAt hu), fun v hv e he => ?_⟩
  rw [← Matrix.mulVec_smul]
  exact GlobalTheory.FinPl.VacFlat.wittCoreInclusion_mem_latticeCompletionAtPlace d (hm v hv) (GlobalTheory.FinPlLoc.smul_latV v he hu)

end GlobalTheory.FinPl.ExtZeroAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicTrivialAtPlacesSubgroupAntitone
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicTrivialAtPlacesSubgroupAntitone
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

namespace GlobalTheory.FinPl

theorem OffAnti.idOff_le (D : D7) {P Q : Pl D → Prop} (h : ∀ v, Q v → P v) : idOff D P ≤ idOff D Q := by
  unfold idOff
  exact le_iInf fun w => iInf_le_of_le ⟨w.1, h w.1 w.2⟩ le_rfl

theorem OffAnti.congGrp_le {D : D7} (V : HSp D) {I J : Ideal (AE D)} (hIJ : I ≤ J) : congGrp V I ≤ congGrp V J := by
  intro g hg
  simp only [congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply] at hg ⊢
  have key : Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk J) (matHom V g) =
      Matrix.GeneralLinearGroup.map (Ideal.Quotient.factor hIJ)
        (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) (matHom V g)) := by
    ext i j
    simp [Ideal.Quotient.factor_mk]
  rw [key, hg, map_one]

theorem grpOff_anti : ∀ (D : D7) (S : HSp D) (P Q : Pl D → Prop), (∀ v, Q v → P v) → grpOff S P ≤ grpOff S Q :=
  fun D S _ _ h => OffAnti.congGrp_le S (OffAnti.idOff_le D h)

end GlobalTheory.FinPl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicTrivialAtPlacesSubgroupAntitoneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicTrivialAtPlacesSubgroup_antitone : ∀ (D : D7) (S : HSp D) (P Q : Pl D → Prop), (∀ v, Q v → P v) → grpOff S P ≤ grpOff S Q := by
  first | exact @GlobalTheory.FinPl.grpOff_anti | exact GlobalTheory.FinPl.grpOff_anti | (intros; apply GlobalTheory.FinPl.grpOff_anti <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceFrameLatticeOfMovedLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceFrameLatticeOfMovedLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.FinPl

theorem SplitPt.sec_mem_idAt {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : SplitPt D k) (a : k) : p.sec a ∈ idAt D (· = p.v) := by
  obtain ⟨ε, hε, hsum⟩ := p.above
  have he : p.sec a = p.e * p.sec a := by
    have := p.sec_pr (p.sec a)
    rwa [p.pr_sec] at this
  rw [(placeIdem_acts D p.v ε hε).1, ← hsum, he, ← mul_assoc, add_mul, p.split.1,
    mul_comm (cA D p.e) p.e, p.split.2.1, add_zero]

theorem mt_mul_mt_inv {D : D7} (S : HSp D) (γ : GA D S) : Formalism.L2.Theta.mt S γ * Formalism.L2.Theta.mt S γ⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem Frame.isLat_of_isLatMoved : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n]
    (β : Frame p S n) (γ : GA D S) (L M : Lat S) (Λ : Submodule 𝒪[k] (n → k)),
    Moves S γ L M (· = p.v) → β.IsLatMoved γ L Λ → β.IsLat M Λ := by
  intro D k _ _ _ _ p S n _ _ β γ L M Λ hM hL x
  have hsupp : ∀ i, (Formalism.L2.Theta.mt S γ⁻¹ *ᵥ fun i => p.sec ((β.b *ᵥ x) i)) i ∈ idAt D (· = p.v) := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (p.sec_mem_idAt _)
  rw [hL x, hM _ hsupp, Matrix.mulVec_mulVec, mt_mul_mt_inv, Matrix.one_mulVec]

end GlobalTheory.FinPl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceFrameLatticeOfMovedLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceFrameLattice_of_movedLattice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (γ : GA D S) (L M : Lat S) (Λ : Submodule 𝒪[k] (n → k)), Moves S γ L M (· = p.v) → β.IsLatMoved γ L Λ → β.IsLat M Λ := by
  first | exact @GlobalTheory.FinPl.Frame.isLat_of_isLatMoved | exact GlobalTheory.FinPl.Frame.isLat_of_isLatMoved | (intros; apply GlobalTheory.FinPl.Frame.isLat_of_isLatMoved <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPointOfDecoratedLatticeUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPointOfDecoratedLatticeUnique
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Mem.Col2.PtUniq

open Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2

theorem mem_iff_hatL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    {n : ℕ} {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N) (v : Sp E n) :
    v ∈ N ↔ (fun i => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (v i)) ∈ Formalism.L2.Herm.hatL (F := F) N := by
  exact ⟨Formalism.L2.GlobalTheoryTheory.Br.latS_of_mem (F := F) N v,
    Formalism.L2.GlobalTheoryTheory.Br.latLocGlob_main (F := F) N (Module.Finite.iff_fg.2 hN.fg) v⟩

theorem isPtOf_unique : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} (g : GL (Fin n) (Formalism.L2.DIV.AfE F E))
    (p p' : Formalism.L2.Col.DecoF E n ST SG Q), GlobalTheory.Mem.Col2.IsPtOf hc g p → GlobalTheory.Mem.Col2.IsPtOf hc g p' → p = p' := by
  intro F E _ _ _ _ _ _ hc n ST SG Q g p p' h h'
  have hN : p.deco.1.N = p'.deco.1.N := by
    ext v
    rw [mem_iff_hatL (F := F) p.deco.2.lat, mem_iff_hatL (F := F) p'.deco.2.lat, h.lat, h'.lat]
  have hd : p.deco = p'.deco := by
    apply Subtype.ext
    refine Deco.Ok.ext_on p.deco.2 p'.deco.2 hN (fun P x hx => ?_) (fun w x hx => ?_)
    · rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        have hx0 : x = 0 := Subsingleton.elim _ _
        subst hx0
        have a := p.deco.2.f_smul P 0 0 (zero_mem _)
        have b := p'.deco.2.f_smul P 0 0 (zero_mem _)
        rw [zero_smul, map_zero, zero_mul] at a b
        rw [a, b]
      · exact HasRes.unique (h.f P x hx ⟨n - 1, by omega⟩ (by simp; omega))
          (h'.f P x (hN ▸ hx) ⟨n - 1, by omega⟩ (by simp; omega))
    · funext i
      exact HasRes.unique (h.be w x hx i) (h'.be w x (hN ▸ hx) i)
  have hfr : ∀ P : Q, p.fr P = p'.fr P := by
    intro P
    refine LinearEquiv.toLinearMap_injective (Module.Basis.ext (Pi.basisFun E (Fin n)) fun j => ?_)
    funext i
    have e := (h.fr P i j).symm.trans (h'.fr P i j)
    simpa using (algebraMap E (P.1.adicCompletion E)).injective e
  apply Subtype.ext
  exact Prod.ext hd (funext hfr)

end GlobalTheory.Mem.Col2.PtUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPointOfDecoratedLatticeUniqueStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPointOfDecoratedLattice_unique : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} (g : GL (Fin n) (Formalism.L2.DIV.AfE F E)) (p p' : Formalism.L2.Col.DecoF E n ST SG Q), GlobalTheory.Mem.Col2.IsPtOf hc g p → GlobalTheory.Mem.Col2.IsPtOf hc g p' → p = p' := by
  first | exact @GlobalTheory.Mem.Col2.PtUniq.isPtOf_unique | exact GlobalTheory.Mem.Col2.PtUniq.isPtOf_unique | (intros; apply GlobalTheory.Mem.Col2.PtUniq.isPtOf_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.XZeroColumnLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.ColSplitA

variable {D : D7}

theorem mulVec_mem_latA {S T : HSp D} {L : Lat S} {L' : Lat T} {P : Pl D → Prop} (M : Mx D T.rank S.rank)
    (hM : ∀ y ∈ latV S L P, M *ᵥ y ∈ latV T L' P) {z : Fin S.rank → AE D} (hz : z ∈ latA S L P) :
    M *ᵥ z ∈ latA T L' P := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    set u : Fin S.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hu
    have hu' : u ∈ latV S L P := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have heq : M *ᵥ (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) =
        fun k => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (M *ᵥ u) k := by
      funext k
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, hu]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i) =
          ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
      rw [h1]; ring
    rw [heq]
    exact VacFlat.smul_mem_latA ha (hM u hu')
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

end GlobalTheory.FinPl.ColSplitA

end
end
