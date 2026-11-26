module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalEqOfMemDpcris
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NullPowerSeriesOfNullAinfMul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceNondegenerateOfIsSSRep

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedFamilyPotentiallyCrystallineFrobStable
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRTwO
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Classical

noncomputable section

namespace GlobalTheory.TwistPotCrys

section

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem loc_rTwO (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    Br.loc D.nbr i w hw (rTwO D.nd i r x) =
      twistM (Br.loc D.nbr i w hw (rO D.nd i r x)) (Br.locChi D.nbr i w hw (D.nd.chi i 1))⁻¹ := by
  refine MonoidHom.ext fun g => Matrix.ext fun a b => ?_
  show (D.nbr i w hw).toLL ((((chiU D.nd i 1)⁻¹ (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i) *
      rO D.nd i r x (decS D.nd w (Br.iota D.nbr i w hw g)) a b) = _
  rw [map_mul]
  rfl

theorem matRep_loc_rO (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    matRep (Br.loc D.nbr i w hw (rO D.nd i r x)) = (D.nbr i w hw).rep ((r x).comp (decS D.nd w)) := rfl

theorem isTwistRep_loc (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    IsTwistRep (Br.locChi D.nbr i w hw (D.nd.chi i 1))⁻¹ (matRep (Br.loc D.nbr i w hw (rO D.nd i r x)))
      (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x))) := by
  refine ⟨LinearEquiv.refl _ _, fun g v => ?_⟩
  rw [loc_rTwO]
  change ((((Br.locChi D.nbr i w hw (D.nd.chi i 1))⁻¹ g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) •
      Br.loc D.nbr i w hw (rO D.nd i r x) g).mulVec v = _
  exact Matrix.smul_mulVec _ _ _

theorem continuous_rTwO (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i)
    (hc : Continuous (fun g => ((r x g : GL (Fin D.R.nV) (D.nd.O i)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)))) :
    Continuous fun g => rTwO D.nd i r x g := by
  have h1 : Continuous fun g : GE D.nd => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) :=
    (D.nd.chi_cont i 1).comp continuous_inv
  refine (h1.smul hc).congr fun g => ?_
  simp [rTwO, twistM, rO]

end


set_option maxHeartbeats 1600000 in
theorem twist_potCrys : ∀ (D : D7), PcrisTensorL D.loc → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) (K' : FinExt (D.nd.l i))
    (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) =
        algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c')
    (Sig0 : Finset ((pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ))
    (c : (pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ),
    Continuous (fun g => ((r x g : GL (Fin D.R.nV) (D.nd.O i)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i))) →
    (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep ((r x).comp (decS D.nd w))) →
    (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough ((D.nbr i w hw).rep ((r x).comp (decS D.nd w))) Sig0 →
    (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys (WeaklyAdmissibleFiltrations.charRep (Br.locChi D.nbr i w hw (D.nd.chi i 1))) →
    (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough (WeaklyAdmissibleFiltrations.charRep (Br.locChi D.nbr i w hw (D.nd.chi i 1))) {c} →
    (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x))) ∧
      (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x)))
        (Sig0.image (fun a => a * c⁻¹)) := by
  intro D hT i w hw r x K' h hN hF hS Sig0 c hcont hpot hit hχpot hχit
  have hcO : Continuous fun g => rO D.nd i r x g := hcont
  have hcT := continuous_rTwO D i r x hcont
  rw [← matRep_loc_rO] at hpot hit
  exact (hT (D.nd.l i) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hF hS
      (GlobalTheory.PotDual.bundle _ _ (Br.loc D.nbr i w hw (rO D.nd i r x)) (GlobalTheory.PotDual.continuous_loc D i w hw _ hcO))
      (GlobalTheory.PotDual.bundle _ _ (Br.loc D.nbr i w hw (rTwO D.nd i r x)) (GlobalTheory.PotDual.continuous_loc D i w hw _ hcT))
      Sig0 (Sig0.image (fun a => a * c⁻¹)) hpot hit).1 _ c (isTwistRep_loc D i w hw r x) hχpot hχit
      (fun b => by
        rw [Finset.mem_image]
        exact ⟨fun ⟨a, ha, e⟩ => ⟨a, ha, e.symm⟩, fun ⟨a, ha, e⟩ => ⟨a, ha, e.symm⟩⟩)

end GlobalTheory.TwistPotCrys

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedFamilyPotentiallyCrystallineFrobStable
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Polynomial
open Classical

noncomputable section

namespace GlobalTheory.PotTwist

theorem frob : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal)
    (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c'),
    finrank ℚ_[l] ↥K.1 = 1 → ∃ F : ↥(GK K), (pc P h hN hF hS).IsFrob F := by
  intro l _ P K K' h hN hF hS hK
  have hbot : K.1 = ⊥ := IntermediateField.finrank_eq_one_iff.1 hK
  obtain ⟨g, hg⟩ : ∃ g : GQ l, ∀ x : ↥(Loc.K0 K'), g x = (((P.PD K').σ x : ↥(Loc.K0 K')) : Om l) := by
    let τ : ↥(Loc.K0 K') →ₐ[ℚ_[l]] Om l := (Loc.K0 K').val.comp (P.PD K').σ
    exact ⟨AlgEquiv.ofBijective (τ.liftNormal (Om l)) (Algebra.IsAlgebraic.algHom_bijective _),
      fun x => τ.liftNormal_commutes (Om l) x⟩
  have hmem : g ∈ GK K := by
    rw [GK, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [hbot] at hx
    obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.1 hx
    exact g.commutes a
  refine ⟨⟨g, hmem⟩, fun c => ?_⟩
  change (P.PD K).actB _ _ = algebraMap _ _ ((P.PD K').σ c)
  rw [P.PD_actB]
  exact P.actQ_Kur g (IntermediateField.inclusion (inf_le_right : Loc.K0 K' ≤ MaximalUnramifiedExtension l) c)
    (IntermediateField.inclusion (inf_le_right : Loc.K0 K' ≤ MaximalUnramifiedExtension l) ((P.PD K').σ c)) (hg c)

theorem main : ∀ (D : D7), PcrisTensorL D.loc → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)), finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 →
  ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) =
        algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c')
    (Sig0 : Finset ((pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ)) (c : (pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ) (n : ℕ),
  c ∈ Sig0 → Sig0.card ≤ n →
  (∀ x ∈ Xs, Continuous (fun g => ((r x g : GL (Fin D.R.nV) (D.nd.O i)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)))) →
  (∀ x ∈ Xs, (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep ((r x).comp (decS D.nd w))) ∧
    (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough ((D.nbr i w hw).rep ((r x).comp (decS D.nd w))) Sig0) →
  (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep ((chiGL i).comp (decS D.nd w))) →
  (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough ((D.nbr i w hw).rep ((chiGL i).comp (decS D.nd w))) {c} →
  PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n := by
  intro D hT i w hw hdeg r Xs K' h hN hF hS Sig0 c n hc hcard hcont hx hχ1 hχ2

  have hequiv : ∀ (g : Br.G D.nbr i w hw) (v : Br.LL D.nbr i w hw),
      (LinearEquiv.funUnique (Fin 1) (Br.LL D.nbr i w hw) (Br.LL D.nbr i w hw)).symm
        (WeaklyAdmissibleFiltrations.charRep (Br.locChi D.nbr i w hw (D.nd.chi i 1)) g v) =
      (D.nbr i w hw).rep ((chiGL i).comp (decS D.nd w)) g
        ((LinearEquiv.funUnique (Fin 1) (Br.LL D.nbr i w hw) (Br.LL D.nbr i w hw)).symm v) := by
    intro g v
    funext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [WeaklyAdmissibleFiltrations.charRep, LocBridge.rep, Br.locChi, Br.chiG, chiGL, Br.ι, Matrix.mulVec, dotProduct, Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply, mul_comm]
  obtain ⟨tr1, tr2⟩ := GlobalTheory.HTW.Rec.potCrysData_transport (pc (D.loc (D.nd.l i)) h hN hF hS) _ _ _ hequiv
  have htw : ∀ x : ↥Xs, (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x))) ∧
      (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x)))
        (Sig0.image (fun a => a * c⁻¹)) := fun x =>
    GlobalTheory.TwistPotCrys.twist_potCrys D hT i w hw r x K' h hN hF hS Sig0 c (hcont x x.2) (hx x x.2).1 (hx x x.2).2 (tr1 hχ1) (tr2 _ hχ2)
  obtain ⟨Fr, hFr⟩ := frob (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' h hN hF hS hdeg
  have h1 : (1 : (pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ) ∈ Sig0.image (fun a => a * c⁻¹) :=
    Finset.mem_image.2 ⟨c, hc, mul_inv_cancel c⟩
  obtain ⟨Sig, hsub, h1', hst, hit⟩ := GlobalTheory.frobStable_inertial_subset (pc (D.loc (D.nd.l i)) h hN hF hS)
    (fun x : ↥Xs => matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x))) (Fr : Br.G D.nbr i w hw) _ h1 (fun x => (htw x).2)
  exact ⟨K', h, hN, hF, hS, Sig, Fr, hFr, hst, h1',
    le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le hcard), fun x => ⟨(htw x).1, hit x⟩⟩

end GlobalTheory.PotTwist

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedFamilyPotentiallyCrystallineFrobStableStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Polynomial
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedFamily_potentiallyCrystalline_frobStable : ∀ (D : D7), PcrisTensorL D.loc → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)), finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 →
  ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) =
        algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c')
    (Sig0 : Finset ((pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ)) (c : (pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ) (n : ℕ),
  c ∈ Sig0 → Sig0.card ≤ n →
  (∀ x ∈ Xs, Continuous (fun g => ((r x g : GL (Fin D.R.nV) (D.nd.O i)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)))) →
  (∀ x ∈ Xs, (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep ((r x).comp (decS D.nd w))) ∧
    (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough ((D.nbr i w hw).rep ((r x).comp (decS D.nd w))) Sig0) →
  (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep ((chiGL i).comp (decS D.nd w))) →
  (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough ((D.nbr i w hw).rep ((chiGL i).comp (decS D.nd w))) {c} →
  PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n := by
  first | exact @GlobalTheory.PotTwist.main | exact GlobalTheory.PotTwist.main | (intros; apply GlobalTheory.PotTwist.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxUnramifiedSubfieldStableOfNormal
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Polynomial
open Classical

noncomputable section

namespace GlobalTheory.PotExt

variable {l : ℕ} [Fact l.Prime]

section Bridge

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)

theorem exists_finExt_of_open (U : Subgroup (Ω ≃ₐ[E] Ω)) (hU : IsOpen (U : Set (Ω ≃ₐ[E] Ω))) :
    ∃ L : FinExt l, ∀ g : ↥(GK Bw.Kw), (g : GQ l) ∈ GK L → ((Bw.e.symm g : Gw) : Ω ≃ₐ[E] Ω) ∈ U := by
  have hc : Continuous fun g : ↥(GK Bw.Kw) => ((Bw.e.symm g : Gw) : Ω ≃ₐ[E] Ω) :=
    continuous_subtype_val.comp Bw.e_symm_cont
  obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.1 (hU.preimage hc)
  have h1 : (1 : GQ l) ∈ t := by
    have : (1 : ↥(GK Bw.Kw)) ∈ Subtype.val ⁻¹' t := by
      rw [hts]
      simp [U.one_mem]
    exact this
  obtain ⟨L, hL, hLt⟩ := (krullTopology_mem_nhds_one_iff ℚ_[l] (Om l) t).1 (ht.mem_nhds h1)
  refine ⟨⟨L, hL⟩, fun g hg => ?_⟩
  have : g ∈ Subtype.val ⁻¹' t := hLt hg
  rw [hts] at this
  exact this

theorem rep_apply {m : ℕ} (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) O) (g : ↥(GK Bw.Kw))
    (x : Fin m → ↥Bw.LL.1) :
    Bw.rep r g x = (((r (Bw.e.symm g) : Matrix.GeneralLinearGroup (Fin m) O) : Matrix (Fin m) (Fin m) O).map Bw.toLL).mulVec x := rfl

end Bridge

end GlobalTheory.PotExt

namespace GlobalTheory.PotExt

variable {l : ℕ} [Fact l.Prime]

section Lat

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)

theorem toLL_mem (a : O) : Bw.toLL a ∈ OL Bw.LL := (Bw.eO a).2

theorem mem_stdG_OL {LL : FinExt l} {k : ℕ} (x : Fin k → ↥LL.1) :
    x ∈ stdG ↥(OL LL) ↥LL.1 k ↔ ∀ j, x j ∈ OL LL := by
  constructor
  · rintro ⟨u, rfl⟩ j
    exact (u j).2
  · intro h
    exact ⟨fun j => ⟨x j, h j⟩, rfl⟩


set_option synthInstance.maxHeartbeats 400000 in
def bridgeLat {m : ℕ} (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) O)
    (hr : Continuous fun g => ((r g : Matrix.GeneralLinearGroup (Fin m) O) : Matrix (Fin m) (Fin m) O))
    {K : FinExt l} (h : Bw.Kw.1 ≤ K.1) : LocLat ↥(GK K) ℚ_[l] ↥Bw.LL.1 ↥(OL Bw.LL) where
  V := Fin m → ↥Bw.LL.1
  ρ := (Bw.rep r).comp (Subgroup.inclusion (GK_le h))
  cont := fun x => by
    have h1 : Continuous fun g : ↥(GK K) =>
        ((r (Bw.e.symm (Subgroup.inclusion (GK_le h) g)) : Matrix.GeneralLinearGroup (Fin m) O) :
          Matrix (Fin m) (Fin m) O) :=
      hr.comp (Bw.e_symm_cont.comp (continuous_subtype_val.subtype_mk _))
    have h2 : Continuous (Bw.toLL) := continuous_subtype_val.comp Bw.eO_cont
    exact (h1.matrix_map h2).matrix_mulVec continuous_const
  L :=
    { T := stdG ↥(OL Bw.LL) ↥Bw.LL.1 m
      stable := fun g x hx => by
        rw [mem_stdG_OL] at hx ⊢
        intro j
        simp only [MonoidHom.comp_apply, GlobalTheory.PotExt.rep_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
        exact Subalgebra.sum_mem _ fun b _ => Subalgebra.mul_mem _ (toLL_mem Bw _) (hx b)
      fg := by
        rw [stdG, LinearMap.range_eq_map]
        exact (Module.Finite.fg_top).map _
      free := Module.Free.of_equiv (LinearEquiv.ofInjective _ (stdG_inj Subtype.val_injective m))
      span := by
        rw [eq_top_iff, ← (Pi.basisFun ↥Bw.LL.1 (Fin m)).span_eq]
        apply Submodule.span_mono
        rintro _ ⟨j, rfl⟩
        refine ⟨Pi.single j 1, ?_⟩
        funext j'
        simp [Pi.single_apply] }

theorem isCrys_up (LT : LocTheory) (hres : ElementDenominator.CrystallineRestrictionToExtension LT) {m : ℕ}
    (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) O)
    (hr : Continuous fun g => ((r g : Matrix.GeneralLinearGroup (Fin m) O) : Matrix (Fin m) (Fin m) O))
    {K₁ K₂ : FinExt l} (h₁ : Bw.Kw.1 ≤ K₁.1) (h₁₂ : K₁.1 ≤ K₂.1)
    (hc : IsCrys ((LT l).PD K₁) ((Bw.rep r).comp (Subgroup.inclusion (GK_le h₁)))) :
    IsCrys ((LT l).PD K₂) ((Bw.rep r).comp (Subgroup.inclusion (GK_le (h₁.trans h₁₂)))) :=
  (hres l K₂ K₁ h₁₂ (GK_le h₁₂) Bw.LL (bridgeLat Bw r hr h₁) hc).1

end Lat

end GlobalTheory.PotExt

namespace GlobalTheory.PotExt

variable {l : ℕ} [Fact l.Prime]

theorem Kur_stable (σ : GQ l) {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) : σ x ∈ MaximalUnramifiedExtension l := by
  have h : (MaximalUnramifiedExtension l).map (σ : Om l →ₐ[ℚ_[l]] Om l) ≤ MaximalUnramifiedExtension l := by
    unfold MaximalUnramifiedExtension
    rw [IntermediateField.adjoin_map]
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, ⟨m, hm, hlm, hy⟩, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, by rw [← map_pow, hy, map_one]⟩
  exact h ((IntermediateField.mem_map _).2 ⟨x, hx, rfl⟩)

theorem mem_of_normal {K' : FinExt l} (hn : Normal ℚ_[l] K'.1) (σ : GQ l) {x : Om l} (hx : x ∈ K'.1) :
    σ x ∈ K'.1 :=
  IntermediateField.normal_iff_forall_map_le'.1 hn σ ((IntermediateField.mem_map _).2 ⟨x, hx, rfl⟩)

theorem GKin_normal {K K' : FinExt l} (h : K.1 ≤ K'.1) (hn : Normal ℚ_[l] K'.1) : (GKin h).Normal := by
  haveI : IsGalois ℚ_[l] K'.1 := IsGalois.mk
  haveI : (GK K').Normal := (InfiniteGalois.normal_iff_isGalois K'.1).2 inferInstance
  unfold GKin
  infer_instance

theorem GKin_finiteIndex {K K' : FinExt l} (h : K.1 ≤ K'.1) : (GKin h).FiniteIndex := by
  haveI : Finite (GQ l ⧸ GK K') := Subgroup.quotient_finite_of_isOpen _ (@IntermediateField.fixingSubgroup_isOpen _ _ _ _ _ K'.1 K'.2)
  haveI : (GK K').FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  unfold GKin
  infer_instance

theorem maxUnramifiedSubfield_stable_of_normal (P : LocPrime l) {K K' : FinExt l} (hn : Normal ℚ_[l] K'.1) (g : ↥(GK K)) (c : ↥(K0 K')) :
    ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c' := by
  have hc1 : ((c : Om l)) ∈ K'.1 := c.2.1
  have hc2 : ((c : Om l)) ∈ MaximalUnramifiedExtension l := c.2.2
  refine ⟨⟨(g : GQ l) c, mem_of_normal hn _ hc1, Kur_stable _ hc2⟩, ?_⟩
  rw [P.PD_actB]
  exact P.actQ_Kur (g : GQ l) ⟨c, hc2⟩ ⟨(g : GQ l) c, Kur_stable _ hc2⟩ rfl

end GlobalTheory.PotExt

namespace GlobalTheory.PotExt

theorem main : ∀ (D : D7) (P : Pend D), ElementDenominator.adm12 D → ∀ (i : D.nd.Loc) (k : Fin 2)
  (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
  (Y : Finset (Fb (D.host.g k) (D.host.g_prime k))), (∀ y ∈ Y, y ≠ 0) →
  ∀ (ι : Type) [Finite ι] (n : ℕ) (R : ι → (GE D.nd →* GL (Fin n) (D.nd.O i))) (n₀ : ℕ)
    (R₀ : GE D.nd →* GL (Fin n₀) (D.nd.O i)),
  (∀ j, Continuous fun g => ((R j g : GL (Fin n) (D.nd.O i)) : Matrix (Fin n) (Fin n) (D.nd.O i))) →
  (Continuous fun g => ((R₀ g : GL (Fin n₀) (D.nd.O i)) : Matrix (Fin n₀) (Fin n₀) (D.nd.O i))) →
  (∀ j, Br.IsPotCrysW D.loc D.nbr i w hw (R j)) → Br.IsPotCrysW D.loc D.nbr i w hw R₀ →
  ∃ (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
      (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
        ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) =
          algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c'),
    (∀ j, (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep ((R j).comp (decS D.nd w)))) ∧
    (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep (R₀.comp (decS D.nd w))) ∧
    ∀ y ∈ Y, ∀ g ∈ GKin h,
      (((D.nbr i w hw).e.symm g : Gw D.nd w) : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) →
        P.om k w y (((D.nbr i w hw).e.symm g : Gw D.nd w) : GE D.nd) = 1 := by
  intro D P hadm i k w hw Y hY ι _ n R n₀ R₀ hRc hR₀c hRp hR₀p
  unfold Br.IsPotCrysW LocBridge.IsPotCrysW at hRp hR₀p
  choose Kj hj hcj using hRp
  obtain ⟨K₀', h₀, hc₀⟩ := hR₀p
  have hLy : ∀ y : ↥Y, ∃ L : FinExt (D.nd.l i), ∀ g : ↥(GK (D.nbr i w hw).Kw), (g : GQ (D.nd.l i)) ∈ GK L →
      (((D.nbr i w hw).e.symm g : Gw D.nd w) : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) →
      P.om k w y (((D.nbr i w hw).e.symm g : Gw D.nd w) : GE D.nd) = 1 := by
    intro y
    obtain ⟨U, hU, hUo⟩ := P.om_open k w y (hY y y.2)
    obtain ⟨L, hL⟩ := exists_finExt_of_open (D.nbr i w hw) U hU
    exact ⟨L, fun g hg hI => hUo _ (hL g hg) hI⟩
  choose Ly hLy using hLy
  haveI : ∀ j, FiniteDimensional ℚ_[D.nd.l i] (Kj j).1 := fun j => (Kj j).2
  haveI : ∀ y, FiniteDimensional ℚ_[D.nd.l i] (Ly y).1 := fun y => (Ly y).2
  haveI := (D.nbr i w hw).Kw.2
  haveI := K₀'.2
  let M : IntermediateField ℚ_[D.nd.l i] (Om (D.nd.l i)) :=
    (D.nbr i w hw).Kw.1 ⊔ K₀'.1 ⊔ (⨆ j, (Kj j).1) ⊔ (⨆ y, (Ly y).1)
  haveI : FiniteDimensional ℚ_[D.nd.l i] M := by infer_instance
  let K' : FinExt (D.nd.l i) := ⟨IntermediateField.normalClosure ℚ_[D.nd.l i] M (Om (D.nd.l i)), inferInstance⟩
  have hMK : M ≤ K'.1 := IntermediateField.le_normalClosure M
  have hn : Normal ℚ_[D.nd.l i] K'.1 := normalClosure.normal _ _ _
  have h : (D.nbr i w hw).Kw.1 ≤ K'.1 := le_trans (le_sup_left.trans (le_sup_left.trans le_sup_left)) hMK
  have h0K : K₀'.1 ≤ K'.1 := le_trans (le_sup_right.trans (le_sup_left.trans le_sup_left)) hMK
  refine ⟨K', h, GKin_normal h hn, GKin_finiteIndex h, maxUnramifiedSubfield_stable_of_normal _ hn, fun j => ?_, ?_, ?_⟩
  · have hjK : (Kj j).1 ≤ K'.1 :=
      le_trans ((le_iSup (fun j => (Kj j).1) j).trans (le_sup_right.trans le_sup_left)) hMK
    refine (GlobalTheory.PcRes.main _ _ _ _ _ h _ _ _ _ _).2.2 ?_
    exact isCrys_up (D.nbr i w hw) D.loc hadm _ ((hRc j).comp continuous_subtype_val) (hj j) hjK (hcj j)
  · refine (GlobalTheory.PcRes.main _ _ _ _ _ h _ _ _ _ _).2.2 ?_
    exact isCrys_up (D.nbr i w hw) D.loc hadm _ (hR₀c.comp continuous_subtype_val) h₀ h0K hc₀
  · intro y hy g hg hI
    have hyK : (Ly ⟨y, hy⟩).1 ≤ K'.1 :=
      le_trans ((le_iSup (fun y => (Ly y).1) ⟨y, hy⟩).trans le_sup_right) hMK
    exact hLy ⟨y, hy⟩ g (GK_le hyK (Subgroup.mem_subgroupOf.1 hg)) hI

end GlobalTheory.PotExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyZeroOfDeRhamCharacter
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Polynomial
open Classical

noncomputable section

namespace GlobalTheory.TypeInertia

variable {D : D7}

theorem cont_iotaOQ (hPH : tiePH (D := D)) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) : Continuous (iotaOQ D.nd D.naut i) := by
  have h : (iotaOQ D.nd D.naut i : D.nd.O i → Qbar (D.nd.l i)) =
      fun x => (((D.nbr i w hw).toLL x : ↥(D.nbr i w hw).LL.1) : Loc.Om (D.nd.l i)) :=
    funext (hPH i w hw).1
  rw [h]
  exact continuous_subtype_val.comp (continuous_subtype_val.comp (D.nbr i w hw).eO_cont)

theorem cont_mapRep (hPH : tiePH (D := D)) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) {a : ℕ} (ρ : GE D.nd →* GL (Fin a) (D.nd.O i))
    (hc : Continuous fun g => ((ρ g : GL (Fin a) (D.nd.O i)) : Matrix (Fin a) (Fin a) (D.nd.O i))) :
    Continuous fun g => ((mapRep (iotaOQ D.nd D.naut i) ρ g : GL (Fin a) (Qbar (D.nd.l i))) :
      Matrix (Fin a) (Fin a) (Qbar (D.nd.l i))) :=
  hc.matrix_map (cont_iotaOQ hPH i w hw)

theorem potCrys_of (h0 : SumRepresentations.tie0 D) (hPH : tiePH (D := D)) (i : D.nd.Loc)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) {a : ℕ}
    (ρ : GE D.nd →* GL (Fin a) (D.nd.O i))
    (hc : Continuous fun g => ((ρ g : GL (Fin a) (D.nd.O i)) : Matrix (Fin a) (Fin a) (D.nd.O i)))
    (hdR : D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) ρ) w)
    (hm : D.naut.mono0 (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) ρ) w)) :
    Br.IsPotCrysW D.loc D.nbr i w hw ρ := by
  have hQ := (h0.2.2.2.1 i a _ w hw (cont_mapRep hPH i w hw ρ hc)).2 ⟨hdR, hm⟩
  exact ((hPH i w hw).2.1 a ρ hc).2.2.1.1 hQ

theorem cont_chiGL (i : D.nd.Loc) :
    Continuous fun g => ((chiGL i g : GL (Fin 1) (D.nd.O i)) : Matrix (Fin 1) (Fin 1) (D.nd.O i)) := by
  have h := D.nd.chi_cont i 1
  have e : (fun g => ((chiGL i g : GL (Fin 1) (D.nd.O i)) : Matrix (Fin 1) (Fin 1) (D.nd.O i))) =
      fun g => Matrix.scalar (Fin 1) ((D.nd.chi i 1 g : (D.nd.O i)ˣ) : D.nd.O i) := by
    funext g; rfl
  rw [e]
  exact Continuous.matrix_diagonal (continuous_pi fun _ => h)

theorem twGL_one_chi {k : Type} [Field k] {Γ : Type} [Group Γ] (χ : Γ →* GL (Fin 1) k) :
    SumRepresentations.At.twGL (1 : Γ →* GL (Fin 1) k) (Matrix.GeneralLinearGroup.det.comp χ) = χ := by
  ext g a b
  fin_cases a; fin_cases b
  simp [SumRepresentations.At.twGL, Matrix.det_unique, Matrix.algebraMap_matrix_apply]

theorem mapRep_one {A B : Type} [CommRing A] [CommRing B] {Γ : Type} [Group Γ] {a : ℕ} (f : A →+* B) :
    mapRep f (1 : Γ →* GL (Fin a) A) = 1 := by
  ext g x y
  simp [mapRep]

theorem crys_one (hPH : tiePH (D := D)) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    D.naut.IsCrysW i (1 : GE D.nd →* GL (Fin 1) (Qbar (D.nd.l i))) w := by
  have hc : Continuous fun g => (((1 : GE D.nd →* GL (Fin 1) (D.nd.O i)) g : GL (Fin 1) (D.nd.O i)) :
      Matrix (Fin 1) (Fin 1) (D.nd.O i)) := by simpa using continuous_const
  have h := ((hPH i w hw).2.1 1 (1 : GE D.nd →* GL (Fin 1) (D.nd.O i)) hc).1.2
  rw [mapRep_one] at h
  apply h
  haveI := (D.nbr i w hw).LL.2
  show IsCrys _ _
  exact GlobalTheory.TrivCrys.isCrys_of_trivial _ _ (fun g x => by simp [LocBridge.rep])

theorem monodromy_zero_of_deRham_character (h0 : SumRepresentations.tie0 D) (hPH : tiePH (D := D)) (i : D.nd.Loc)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (χ : GE D.nd →* GL (Fin 1) (Qbar (D.nd.l i)))
    (hc : Continuous fun g => ((χ g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))))
    (hdR : D.naut.IsdRW i χ w) : D.naut.mono0 (D.naut.wdOf i χ w) := by
  have h1c : SumRepresentations.At.ContQ D.nd i (1 : GE D.nd →* GL (Fin 1) (Qbar (D.nd.l i))) := by
    unfold SumRepresentations.At.ContQ; simpa using continuous_const
  have hcr := (h0.2.2.1 i 1 1 w hw h1c).1 (crys_one hPH i w hw)
  have hm1 : D.naut.mono0 (D.naut.wdOf i (1 : GE D.nd →* GL (Fin 1) (Qbar (D.nd.l i))) w) :=
    D.naut.unr_mono0 _ hcr.2
  have htw := ((h0.2.2.2.2.2 i).2.2.2 1 1 χ h1c hc).2.1 w (Or.inr hcr.1) (Or.inr hdR)
  rw [twGL_one_chi] at htw
  rw [htw, D.naut.monomial_char_iff _ _ (D.naut.wdOf_dim i χ w)]
  exact hm1

section Alg

variable {g : ℕ} [hg : Fact g.Prime]

theorem sub_one_dvd_card_GL {r a : ℕ} (ha : 1 ≤ a) (har : a ≤ r) :
    g ^ a - 1 ∣ Nat.card (GL (Fin r) (ZMod g)) := by
  rw [Matrix.card_GL_field, ZMod.card]
  have hmem : (⟨r - a, by omega⟩ : Fin r) ∈ (Finset.univ : Finset (Fin r)) := Finset.mem_univ _
  refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ hmem)
  refine ⟨g ^ (r - a), ?_⟩
  simp only
  have e : g ^ r = g ^ a * g ^ (r - a) := by rw [← pow_add]; congr 1; omega
  rw [e, Nat.sub_mul, one_mul, mul_comm]

theorem pow_card_GL_eq_one {r : ℕ} (hr : 1 ≤ r) {y : Formalism.CyclotomicNorms.Fbar g} (hy : y ≠ 0) {p : (ZMod g)[X]}
    (hp : p ≠ 0) (hd : p.natDegree ≤ r) (hroot : aeval y p = 0) :
    y ^ Nat.card (GL (Fin r) (ZMod g)) = 1 := by
  set K := IntermediateField.adjoin (ZMod g) ({y} : Set (Formalism.CyclotomicNorms.Fbar g))
  have hint : IsIntegral (ZMod g) y := Algebra.IsIntegral.isIntegral y
  haveI : FiniteDimensional (ZMod g) K := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  letI : Fintype K := Fintype.ofFinite K
  set a := Module.finrank (ZMod g) K
  have ha : a = (minpoly (ZMod g) y).natDegree := IntermediateField.adjoin.finrank hint
  have hda : a ≤ r := by
    rw [ha]
    have := Polynomial.natDegree_le_natDegree (minpoly.degree_le_of_ne_zero (ZMod g) y hp hroot)
    omega
  have ha1 : 1 ≤ a := Module.finrank_pos
  have hcard : Fintype.card K = g ^ a := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card]
  let y' : K := ⟨y, IntermediateField.mem_adjoin_simple_self _ _⟩
  have hy' : y' ≠ 0 := fun h => hy (congrArg Subtype.val h)
  have h1 : y' ^ (g ^ a - 1) = 1 := by
    rw [← hcard]; exact FiniteField.pow_card_sub_one_eq_one y' hy'
  obtain ⟨m, hm⟩ := sub_one_dvd_card_GL (g := g) ha1 hda
  rw [hm, pow_mul]
  have : y ^ (g ^ a - 1) = 1 := congrArg Subtype.val h1
  rw [this, one_pow]

def ySet (S : (ZMod g)[X]) (c : (ZMod g)ˣ) : Finset (Formalism.CyclotomicNorms.Fbar g) :=
  (Formalism.CyclotomicNorms.rootsBar S).toFinset ∪
    {algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (c : ZMod g), algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) ((c⁻¹ : (ZMod g)ˣ) : ZMod g)}

theorem mem_rootsBar {S : (ZMod g)[X]} (hS : S ≠ 0) {y : Formalism.CyclotomicNorms.Fbar g} :
    y ∈ Formalism.CyclotomicNorms.rootsBar S ↔ aeval y S = 0 := by
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.mem_roots', Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap]
  exact ⟨fun h => h.2, fun h => ⟨(Polynomial.map_ne_zero_iff (algebraMap (ZMod g) _).injective).2 hS, h⟩⟩

theorem alg_spec {r N : ℕ} (hr : 1 ≤ r) (hN : Nat.card (GL (Fin r) (ZMod g)) ∣ N) (x : ZMod g) (hx : x ≠ 0) :
    algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) x ≠ 0 ∧ (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) x) ^ N = 1 := by
  have h0 : algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) x ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap (ZMod g) _).injective]; exact hx
  refine ⟨h0, ?_⟩
  obtain ⟨m, rfl⟩ := hN
  rw [pow_mul, pow_card_GL_eq_one hr h0 (X_sub_C_ne_zero x) (by rw [natDegree_X_sub_C]; exact hr)
    (by rw [map_sub, aeval_X, aeval_C, sub_self]), one_pow]

theorem ySet_spec {r N : ℕ} (hr : 1 ≤ r) (hN : Nat.card (GL (Fin r) (ZMod g)) ∣ N) {S : (ZMod g)[X]}
    (hS : S ≠ 0) (hS0 : S.coeff 0 ≠ 0) (hSd : S.natDegree ≤ r) (c : (ZMod g)ˣ) :
    ∀ y ∈ ySet S c, y ≠ 0 ∧ y ^ N = 1 := by
  intro y hy
  rw [ySet, Finset.mem_union, Multiset.mem_toFinset, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with hy | rfl | rfl
  · rw [mem_rootsBar hS] at hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [← Polynomial.coeff_zero_eq_aeval_zero', map_eq_zero_iff _ (algebraMap (ZMod g) _).injective] at hy
      exact hS0 hy
    refine ⟨hy0, ?_⟩
    obtain ⟨m, rfl⟩ := hN
    rw [pow_mul, pow_card_GL_eq_one hr hy0 hS hSd hy, one_pow]
  · exact alg_spec hr hN _ c.ne_zero
  · exact alg_spec hr hN _ (c⁻¹).ne_zero

theorem ySet_card {r : ℕ} {S : (ZMod g)[X]} (hSd : S.natDegree ≤ r) (c : (ZMod g)ˣ) :
    (ySet S c).card ≤ r + 2 := by
  unfold ySet
  refine (Finset.card_union_le _ _).trans (add_le_add ?_ ?_)
  · refine (Multiset.toFinset_card_le _).trans ?_
    unfold Formalism.CyclotomicNorms.rootsBar
    refine (Polynomial.card_roots' _).trans ?_
    rw [Polynomial.natDegree_map]; exact hSd
  · exact (Finset.card_insert_le _ _).trans (by rw [Finset.card_singleton])

theorem alg_mem_ySet (S : (ZMod g)[X]) {c u : (ZMod g)ˣ} (hu : u = c ∨ u = c⁻¹) :
    algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (u : ZMod g) ∈ ySet S c := by
  unfold ySet
  refine Finset.mem_union_right _ ?_
  rcases hu with rfl | rfl
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

theorem root_mem_ySet {S : (ZMod g)[X]} (hS : S ≠ 0) {c u : (ZMod g)ˣ} (hu : u = c ∨ u = c⁻¹) (t : ℕ)
    {y : Formalism.CyclotomicNorms.Fbar g} (hy : y ∈ Formalism.CyclotomicNorms.rootsBar (S * (X - C (u : ZMod g)) ^ t)) : y ∈ ySet S c := by
  have hne : S * (X - C (u : ZMod g)) ^ t ≠ 0 := mul_ne_zero hS (pow_ne_zero _ (X_sub_C_ne_zero _))
  rw [mem_rootsBar hne, map_mul, map_pow, mul_eq_zero] at hy
  rcases hy with hy | hy
  · unfold ySet
    exact Finset.mem_union_left _ (Multiset.mem_toFinset.2 ((mem_rootsBar hS).2 hy))
  · have h1 : aeval y (X - C (u : ZMod g)) = 0 := by
      by_contra hne; exact pow_ne_zero t hne hy
    rw [map_sub, aeval_X, aeval_C, sub_eq_zero] at h1
    rw [h1]; exact alg_mem_ySet S hu

theorem inv_mem_image {Y : Finset (Formalism.CyclotomicNorms.Fbar g)} {y : Formalism.CyclotomicNorms.Fbar g} (hy : y ∈ Y) :
    y⁻¹ ∈ Y.image (·⁻¹) := Finset.mem_image_of_mem _ hy

theorem image_spec {Y : Finset (Formalism.CyclotomicNorms.Fbar g)} {N : ℕ} (h : ∀ y ∈ Y, y ≠ 0 ∧ y ^ N = 1) :
    ∀ y ∈ Y.image (·⁻¹), y ≠ 0 ∧ y ^ N = 1 := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
  obtain ⟨h1, h2⟩ := h z hz
  exact ⟨inv_ne_zero h1, by rw [inv_pow, h2, inv_one]⟩

end Alg

theorem rootsBar_X_sub_C {g : ℕ} [Fact g.Prime] (a : ZMod g) :
    Formalism.CyclotomicNorms.rootsBar (X - C a) = {algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) a} := by
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.roots_X_sub_C]

theorem inePol_char (P : Pend D) (k : Fin 2) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hwk : w ∈ placesOver D.host.E (D.host.g k)) (L : D.naut.LP w) (a : ZMod (D.host.g k))
    (hlab : D.naut.items₂ k w L = X - C a) (hdim : D.naut.lpDim L = 1) :
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
      D.naut.inePol L σ = X - C (P.om k w (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) a) σ) := by
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  intro σ hσ
  have h := P.inertiaCharpoly_eigenvalues k w hwk L (by rw [hlab, natDegree_X_sub_C, hdim]) σ hσ
  rw [h, hlab, rootsBar_X_sub_C, Multiset.map_singleton, Multiset.prod_singleton]

theorem inertial_chars : ∀ (D : D7) (P : Pend D), TypeLGC P → SumRepresentations.tie0 D → tiePH (D := D) → tieChi (D := D) →
  ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k →
  ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
  ∀ Xs : Set (D.nd.X i), TypeLocus P i k Xs →
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
  ∃ (Y : Finset (Fb (D.host.g k) (D.host.g_prime k))) (u : Fb (D.host.g k) (D.host.g_prime k)),
    u ∈ Y ∧ (∀ y ∈ Y, y ≠ 0 ∧ y ^ D.what₂.restRowsFiniteGroupCard = 1) ∧ Y.card ≤ D.R.nV + 1 ∧
    (∀ x ∈ Xs, Br.IsPotCrysW D.loc D.nbr i w hw (r x) ∧
      ∃ M : Multiset (Fb (D.host.g k) (D.host.g_prime k)), (∀ y ∈ M, y ∈ Y) ∧
        ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
          D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w) σ =
            (M.map fun y => X - C (P.om k w y σ)).prod) ∧
    Br.IsPotCrysW D.loc D.nbr i w hw (chiGL i) ∧
      ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
        D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (chiGL i)) w) σ = X - C (P.om k w u σ) := by
  intro D P hLGC h0 hPH hChi i k hik r hr Xs hXs w hw
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hwk : w ∈ placesOver D.host.E (D.host.g k) := hik ▸ hw
  obtain ⟨v, hv⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hwk
  obtain ⟨s, hs, hx⟩ := hXs
  obtain ⟨S, hS0, hSc, hSd, hSx⟩ : ∃ S : (ZMod (D.host.g k))[X], S ≠ 0 ∧ S.coeff 0 ≠ 0 ∧
      S.natDegree ≤ D.R.r ∧ ∀ x ∈ Xs, S = s v := by
    by_cases hne : Xs.Nonempty
    · obtain ⟨x0, hx0⟩ := hne
      obtain ⟨PI, -, hτ⟩ := hx x0 hx0
      obtain ⟨τ, -, hl⟩ := hτ v
      obtain ⟨hm, hd, hc⟩ := (P.lz k).lab_spec τ
      rw [hl] at hm hd hc
      exact ⟨s v, hm.ne_zero, hc, hd.le, fun _ _ => rfl⟩
    · exact ⟨1, one_ne_zero, by rw [AddMonoidAlgebra.coeff_one_zero]; exact one_ne_zero,
        by rw [natDegree_one]; exact Nat.zero_le _, fun x hx => absurd ⟨x, hx⟩ hne⟩
  have hr1 : 1 ≤ D.R.r := by have := D.R.two_le_m; unfold Ranks.r; omega
  have hN : Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) ∣ D.what₂.restRowsFiniteGroupCard := by
    rw [D.nd.restN_card_levelGroup_eq]
    exact (dvd_pow_self _ (by have := D.R.two_le_m; have := D.R.m_le_f; unfold Ranks.f Ranks.n; omega)).trans
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ k))
  have hcard : D.R.r + 2 ≤ D.R.nV + 1 := by
    have := D.R.rank_add_five_le; unfold Ranks.nV; unfold Ranks.r at *; omega
  have hY := GlobalTheory.TypeInertia.ySet_spec hr1 hN hS0 hSc hSd (PairedCharacterCondition.chiJ D i k v)
  have hYc := GlobalTheory.TypeInertia.ySet_card hSd (PairedCharacterCondition.chiJ D i k v)
  obtain ⟨u, hu, hχ⟩ := hChi i k hik v
  have hcχ := GlobalTheory.TypeInertia.cont_chiGL (D := D) i
  have hpt : ∀ x ∈ Xs, ∃ ux : (ZMod (D.host.g k))ˣ, (ux = PairedCharacterCondition.chiJ D i k v ∨ ux = (PairedCharacterCondition.chiJ D i k v)⁻¹) ∧
      ∀ M : Multiset (Formalism.CyclotomicNorms.Fbar (D.host.g k)),
        ((w = D.naut.plGw k v ∧ M = Formalism.CyclotomicNorms.rootsBar (S * (X - C (ux : ZMod (D.host.g k))) ^ D.R.t)) ∨
          (IsConjPl D.host (D.naut.plGw k v) w ∧
            M = (Formalism.CyclotomicNorms.rootsBar (S * (X - C (ux : ZMod (D.host.g k))) ^ D.R.t)).map (·⁻¹))) →
        Br.IsPotCrysW D.loc D.nbr i w hw (r x) ∧
        ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
          D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w) σ =
            (M.map fun y => X - C (P.om k w y σ)).prod := by
    intro x hxX
    obtain ⟨PI, hPI, hτ⟩ := hx x hxX
    obtain ⟨τ, hτk, hl⟩ := hτ v
    have hSv := hSx x hxX
    obtain ⟨ux, hux, hM⟩ := hLGC i k hik r hr x PI hPI v τ hτk (by rw [hl]; exact (hs v).1)
      (by rw [hl]; exact (hs v).2)
    refine ⟨ux, hux, fun M hMc => ?_⟩
    obtain ⟨hdR, hm0, hine⟩ := hM w M (by rw [hl, ← hSv]; exact hMc)
    exact ⟨GlobalTheory.TypeInertia.potCrys_of h0 hPH i w hw (r x) (hr x).1 hdR hm0, hine⟩
  have hchiQ : ∀ a : ZMod (D.host.g k), Br.IsdRW D.loc D.nbr i w hw (chiGL i) →
      D.naut.items₂ k w (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (chiGL i)) w) = X - C a →
      Br.IsPotCrysW D.loc D.nbr i w hw (chiGL i) ∧
      ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
        D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (chiGL i)) w) σ =
          X - C (P.om k w (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) a) σ) := by
    intro a hdR hlab
    have hdRQ := ((hPH i w hw).2.1 1 (chiGL i) hcχ).2.1.2 hdR
    refine ⟨GlobalTheory.TypeInertia.potCrys_of h0 hPH i w hw _ hcχ hdRQ
      (GlobalTheory.TypeInertia.monodromy_zero_of_deRham_character h0 hPH i w hw _ (GlobalTheory.TypeInertia.cont_mapRep hPH i w hw _ hcχ) hdRQ), ?_⟩
    exact GlobalTheory.TypeInertia.inePol_char P k w hwk _ a hlab (D.naut.wdOf_dim i _ w)
  rcases hv with hfix | hconj
  · obtain ⟨hdR, hlab⟩ := (hχ w hw).1 hfix
    refine ⟨GlobalTheory.TypeInertia.ySet S (PairedCharacterCondition.chiJ D i k v), algebraMap _ _ (u : ZMod (D.host.g k)),
      GlobalTheory.TypeInertia.alg_mem_ySet S hu, hY, hYc.trans hcard, ?_, hchiQ _ hdR hlab⟩
    intro x hxX
    obtain ⟨ux, hux, hpx⟩ := hpt x hxX
    exact ⟨(hpx _ (Or.inl ⟨hfix, rfl⟩)).1, _, fun y hy => GlobalTheory.TypeInertia.root_mem_ySet hS0 hux _ hy,
      (hpx _ (Or.inl ⟨hfix, rfl⟩)).2⟩
  · obtain ⟨hdR, hlab⟩ := (hχ w hw).2 hconj
    refine ⟨(GlobalTheory.TypeInertia.ySet S (PairedCharacterCondition.chiJ D i k v)).image (·⁻¹),
      algebraMap _ _ ((u⁻¹ : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)), ?_,
      GlobalTheory.TypeInertia.image_spec hY, Finset.card_image_le.trans (hYc.trans hcard), ?_, hchiQ _ hdR hlab⟩
    · rw [Units.val_inv_eq_inv_val, map_inv₀]
      exact GlobalTheory.TypeInertia.inv_mem_image (GlobalTheory.TypeInertia.alg_mem_ySet S hu)
    · intro x hxX
      obtain ⟨ux, hux, hpx⟩ := hpt x hxX
      refine ⟨(hpx _ (Or.inr ⟨hconj, rfl⟩)).1, _, fun y hy => ?_, (hpx _ (Or.inr ⟨hconj, rfl⟩)).2⟩
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
      exact GlobalTheory.TypeInertia.inv_mem_image (GlobalTheory.TypeInertia.root_mem_ySet hS0 hux _ hz)

end GlobalTheory.TypeInertia
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeFamilyPotentiallyCrystallineCommonTameExtens
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Polynomial
open Classical

namespace GlobalTheory.PotDirect

theorem main : StepPotDirect := by
  intro D P hT hFo h0 hBr hPH hChi hIE h12 hTen hTP i k hl r ρ hr π hπ hdec Xs hπX hTL w hw
  obtain ⟨Y, u, hu, hY, hYc, hX, hχ, hχσ⟩ := GlobalTheory.TypeInertia.inertial_chars D P hT h0 hPH hChi i k hl r hr Xs hTL w hw
  have hχc : Continuous fun g => ((chiGL i g : GL (Fin 1) (D.nd.O i)) : Matrix (Fin 1) (Fin 1) (D.nd.O i)) := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    have hab : a = b := Subsingleton.elim a b
    subst hab
    simpa [chiGL, Matrix.scalar] using D.nd.chi_cont i 1
  obtain ⟨K', h, hN, hF', hS, hpc, hpc0, hker⟩ := GlobalTheory.PotExt.main D P h12 i k w hw Y (fun y hy => (hY y hy).1) (↥Xs) D.R.nV
    (fun x => r x) 1 (chiGL i) (fun x => (hr x).1) hχc (fun x => (hX x x.2).1) hχ
  obtain ⟨ch, hch⟩ := GlobalTheory.InertiaChars.main D P hTP hIE i k hl w hw Y hY K' h hN hF' hS hker
  have hdeg := (GlobalTheory.TypeDegOne.degree_one D i k hl).2 w hw
  refine GlobalTheory.T.twistedFamily_potentiallyCrystalline_frobStable D hTen i w hw hdeg r Xs K' h hN hF' hS (Y.image ch) (ch u) (D.R.nV + 1)
    (Finset.mem_image_of_mem _ hu) (Finset.card_image_le.trans hYc) (fun x _ => (hr x).1) ?_ hpc0 ?_
  · intro x hx
    obtain ⟨M, hM, hσ⟩ := (hX x hx).2
    exact ⟨hpc ⟨x, hx⟩, hch Y subset_rfl _ (r x) (hr x).1 (hpc ⟨x, hx⟩) M hM hσ⟩
  · have := hch {u} (by simpa using hu) 1 (chiGL i) hχc hpc0 {u} (by simp) (fun σ hσ => by simpa using hχσ σ hσ)
    simpa using this

end GlobalTheory.PotDirect
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeFamilyPotentiallyCrystallineCommonTameExtensStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typeFamily_potentiallyCrystalline_common_tame_extension : StepPotDirect := by
  first | exact @GlobalTheory.PotDirect.main | exact GlobalTheory.PotDirect.main | (intros; apply GlobalTheory.PotDirect.main <;> assumption)
end
