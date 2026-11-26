module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealLieOperatorThetaQuotientLine
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyFinOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesStdMatched

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContragredientIsIrreducibleFiniteDimensional
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContragredientIsIrreducibleFiniteDimensional
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem contragredient_isIrreducible : ∀ (k : Type) [Field k] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V), ρ.IsIrreducible → ρ.dual.IsIrreducible := by
  intro k _ G _ V _ _ _ ρ hρ
  haveI : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    exact (bot_ne_top (α := Subrepresentation ρ))
      (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  have hdualNT : Nontrivial (Module.Dual k V) := inferInstance
  refine { toNontrivial := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · have h' := congrArg Subrepresentation.toSubmodule h
    obtain ⟨x, y, hxy⟩ := hdualNT
    have hx : x ∈ (⊤ : Subrepresentation ρ.dual).toSubmodule := Submodule.mem_top
    have hy : y ∈ (⊤ : Subrepresentation ρ.dual).toSubmodule := Submodule.mem_top
    rw [← h'] at hx hy
    exact hxy (((Submodule.mem_bot k).1 hx).trans ((Submodule.mem_bot k).1 hy).symm)
  · let T : Subrepresentation ρ := ⟨S.toSubmodule.dualCoannihilator, fun g v hv => by
      rw [Submodule.mem_dualCoannihilator] at hv ⊢
      intro φ hφ
      have h1 := hv _ (S.apply_mem_toSubmodule g⁻¹ hφ)
      simpa [Representation.dual_apply, Module.Dual.transpose_apply] using h1⟩
    have hST : S.toSubmodule = T.toSubmodule.dualAnnihilator :=
      (Subspace.dualCoannihilator_dualAnnihilator_eq (W := S.toSubmodule)).symm
    rcases hρ.eq_bot_or_eq_top T with hT | hT
    · right
      apply Subrepresentation.toSubmodule_injective
      rw [hST, hT]
      exact Submodule.dualAnnihilator_bot
    · left
      apply Subrepresentation.toSubmodule_injective
      rw [hST, hT]
      exact Submodule.dualAnnihilator_top

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContragredientIsIrreducibleFiniteDimensionalStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contragredient_isIrreducible_finiteDimensional : ∀ (k : Type) [Field k] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V), ρ.IsIrreducible → ρ.dual.IsIrreducible := by
  first | exact @GlobalTheory.contragredient_isIrreducible | exact GlobalTheory.contragredient_isIrreducible | (intros; apply GlobalTheory.contragredient_isIrreducible <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmTypeEmbeddingAtSideDistinctNonconjugate
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmTypeEmbeddingAtSideDistinctNonconjugate
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.FormsStep

theorem complexConj_eq_hostConj (D : D7) (x : D.host.E) : IsCMField.complexConj D.host.E x = D.host.conj x := by
  apply D.host.φ₀.injective
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem kEmbT_cmDist : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (b : Bool), GlobalTheory.AlgWtF.CMDist (kEmbT D T i b) := by
  intro D T i b
  have hR : Function.Injective ((readT D T i b).comp (Formalism.L2.NX.embEL0 D)) := RingHom.injective _
  have hS : ∀ g h : D.R.GG, (∀ x : D.host.E, D.host.sigmaOf g x = D.host.sigmaOf h x) → g = h := by
    intro g h e
    exact Formalism.MainNotions.Gaps.LevGap.sigmaOf_injective D.host (AlgEquiv.ext e)
  have hk : ∀ t x, kEmbT D T i b t x =
      ((readT D T i b).comp (Formalism.L2.NX.embEL0 D)) (D.host.sigmaOf ((D.eTau t : D.R.Psi) : D.R.GG) x) :=
    fun _ _ => rfl
  refine ⟨?_, ?_⟩
  · intro t t' e
    apply D.eTau.injective
    apply Subtype.ext
    apply hS
    intro x
    apply hR
    rw [← hk, ← hk, e]
  · intro t t' e
    have h1 : ((D.eTau t : D.R.Psi) : D.R.GG) =
        ((D.eTau t' : D.R.Psi) : D.R.GG) * D.R.cc := by
      apply hS
      intro x
      apply hR
      rw [← hk, Formalism.MainNotions.Gaps.LevGap.sigmaOf_mul, AlgEquiv.mul_apply, ← Formalism.MainNotions.Gaps.LevGap.conj_eq_sigmaOf,
        ← complexConj_eq_hostConj D x]
      exact DFunLike.congr_fun e x
    have ht : ((D.eTau t : D.R.Psi) : D.R.GG).1.2 = 1 := (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau t).2
    have ht' : ((D.eTau t' : D.R.Psi) : D.R.GG).1.2 = 1 := (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau t').2
    have h2 : ((D.eTau t : D.R.Psi) : D.R.GG).1.2 =
        ((D.eTau t' : D.R.Psi) : D.R.GG).1.2 * (-1) := by rw [h1]; rfl
    rw [ht, ht'] at h2
    exact absurd h2 (by decide)

end GlobalTheory.HeightCounting.FormsStep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmTypeEmbeddingAtSideDistinctNonconjugateStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmTypeEmbeddingAtSide_distinct_nonconjugate : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (b : Bool), GlobalTheory.AlgWtF.CMDist (kEmbT D T i b) := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.kEmbT_cmDist | exact GlobalTheory.HeightCounting.FormsStep.kEmbT_cmDist | (intros; apply GlobalTheory.HeightCounting.FormsStep.kEmbT_cmDist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumFixesLatticeVacuaAtInertPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumFixesLatticeVacuaAtInertPlaces
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertAll

theorem nonSplitAt_of_forall (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F) (hε : IsPlaceIdem D v ε)
    (hns : ∀ e, IsSplitIdem D e → e * algebraMap (AF D.host.F) (AE D) ε = 0) : GlobalTheory.WeilParts.NonSplitAt D v ε := by
  refine ⟨hε, fun ⟨e, he, heq⟩ => ?_⟩
  have k := hns e he
  have e0 : e = 0 := by
    rw [← heq, mul_add, he.1, he.2.1, add_zero] at k
    exact k
  rw [e0, map_zero, zero_add] at heq
  obtain ⟨α, rfl, h1, -⟩ := hε
  have hinj : Function.Injective (algebraMap (AF D.host.F) (AE D)) :=
    Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective
  have : pairA D.host.F 0 α = 0 := hinj (by rw [map_zero]; exact heq.symm)
  have : α = 0 := congrArg Prod.snd this
  rw [this, map_zero] at h1
  exact zero_ne_one h1

theorem unramAt_of_unrAtV (D : D7) (ε : AF D.host.F) (χ : (AE D)ˣ →* Circle) (hχ : Formalism.IndefR.WeilFull.UnrAtV ε χ) : GlobalTheory.WeilParts.UnramAt ε χ :=
  fun x hx i1 i2 => hχ x (by linear_combination (-1 : AE D) * hx) i1 i2

theorem inertAllO_of_eta (D : D7) (hη : ∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) : Formalism.IndefR.WeilFull.InertAllO D := by
  intro ψ S T χS χT om H _ _ ΛS ΛT hS hT βS βT hβS hβT v ε hε _ hns uS uT g h sg sh hg hh f hf hvac
  have hv : GlobalTheory.WeilParts.NonSplitAt D v ε := nonSplitAt_of_forall D v ε hε hns
  have hst : ∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun w => w = v) ↔
      actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun w => w = v) :=
    fun u => GlobalTheory.LatStab.mem_latO_iff_actO_mem D S T ΛS ΛT βS βT hS.1 hT.1 hβS hβT g h hg hh _ u
  have hfix : ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun w => w = v),
      heisO ψ S T u f = f := by
    intro u hu
    obtain ⟨a, ha, ha2⟩ := GlobalTheory.FinWeilO.exists_half_of_nonSplit hv
    have h1 : 2 • (a • u) = u := by
      rw [two_nsmul, ← add_smul, ← two_mul, ha2, GlobalTheory.VecInvInert.idem_smul_eq hε hu]
    have h2 := hvac.1 (a • u) (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha u hu)
    rwa [h1] at h2
  exact GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified D ψ H.std S T ΛS ΛT hS hT χS χT om hη H v ε hv (unramAt_of_unrAtV D ε χS uS) (unramAt_of_unrAtV D ε χT uT) g h sg sh hst f hf hfix

theorem inertAllO : ∀ D : D7, Formalism.IndefR.WeilFull.InertAllO D :=
  fun D => inertAllO_of_eta D (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D)

end GlobalTheory.InertAll
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumFixesLatticeVacuaAtInertPlacesStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_datum_fixes_lattice_vacua_at_inert_places : ∀ D : D7, Formalism.IndefR.WeilFull.InertAllO D := by
  first | exact @GlobalTheory.InertAll.inertAllO | exact GlobalTheory.InertAll.inertAllO | (intros; apply GlobalTheory.InertAll.inertAllO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisRepOfCuspidal
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisRepOfCuspidal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.TwistAny

open Formalism.L2.NR

theorem exists_isRepOf_tw : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE), GalEx D → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : D.naut.CG D.R.r), D.naut.csd π → D.naut.ralg π → ∃ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (Qbar l), IsRepOf D l ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) ρ := by
  intro hGA D cf jE A hGal l _ ι π hc hr
  obtain ⟨ρ₁, c1, ss1, f1⟩ := hGal l ι D.R.r (Formalism.L2.NR.one_le_r D) π hc hr
  obtain ⟨n, hn⟩ := (GlobalTheory.Mem.CharAlg.isAlg_even_odd D.R D.host).2 cf.eta cf.isEta.inf D.R.t D.R.t_odd
  obtain ⟨art, ha⟩ := hGA D.host.E D.nd.Om
  obtain ⟨μ, hμc, hμ⟩ := ha.exists_isLAdicOf ι (GlobalTheory.HeckeGal.isAlgPos_of_isAlg hn)
  refine ⟨Formalism.MainNotions.SumRepresentations.At.twGL ρ₁ μ, ?_, GlobalTheory.TwistLG.isSSRep_twGL _ _ ss1, ?_⟩
  · simp only [GlobalTheory.TwistLG.twGL_val]
    exact (Units.continuous_val.comp hμc).smul c1
  have hfin := placesOver_finite D.host.E l (Fact.out : l.Prime).ne_zero
  filter_upwards [f1, D.naut.locG_unr_ae π, hfin.compl_mem_cofinite] with w hw1 hu hwl
  intro B σ hB hσ
  have hwl' : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := hwl
  have hue : D.naut.unr (D.naut.locG D.naut.etaTinv w) := (D.naut.etaTinv_def w).1
  have hU := (A.chr.unr_iff _ w).1 hue
  have hf := A.chr.frob _ w hU
  rw [A.chr.etaTinv] at hf hU
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow D.host.E (-(D.R.t : ℝ) / 2)
  have hψu : (cf.eta⁻¹ * GlobalTheory.HeckeGal.Model.absPow D.host.E (-(D.R.t : ℝ) / 2)).UnrAt w := by
    intro x hx
    change (cf.eta⁻¹).loc w x * (GlobalTheory.HeckeGal.Model.absPow D.host.E
      (-(D.R.t : ℝ) / 2)).loc w x = 1
    rw [hU x hx, hν.1 w x hx, one_mul]
  have hμv := hμ.frob_unr ha (Or.inl hwl') hψu hB hσ
  set u : ℂ := (((cf.eta⁻¹ * GlobalTheory.HeckeGal.Model.absPow D.host.E (-(D.R.t : ℝ) / 2)).val w : ℂˣ) : ℂ)⁻¹ with hu_def
  have hu1 : D.naut.frobEig (D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(D.R.t : ℝ) / 2)) = {u} := by
    rw [D.naut.frobEig_tw _ _ hue, hf, Multiset.map_singleton]
    congr 1
    rw [hu_def, HChar.val_mul, HChar.val_inv, Units.val_mul, hν.2.1 w]
    have hn' : (Ideal.absNorm w.asIdeal : ℕ) = normV w := by
      simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [hn', mul_inv, Units.val_inv_eq_inv_val, Complex.cpow_neg, inv_inv]
  have hχu : ι ((μ σ : (Qbar l)ˣ) : Qbar l) = u := by
    rw [hμv, map_inv₀, ι.apply_symm_apply]
  have h1 := hw1 B σ hB hσ
  rw [GlobalTheory.TwistLG.twGL_val, ← Matrix.charpoly_map, GlobalTheory.ParamRep.map_smul_matrix,
    GlobalTheory.ParamRep.galPol_twist D.nd D.naut π hu u hu1]
  have h2 : ((((ρ₁ σ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).map ι.toRingHom)).charpoly =
      ((D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2))).map fun α => X - C α).prod := by
    rw [Matrix.charpoly_map]; exact h1
  have h3 := GlobalTheory.ParamRep.charpoly_smul_of_prod _ u _ h2
  have hχu' : ι.toRingHom ((μ σ : (Qbar l)ˣ) : Qbar l) = u := hχu
  rw [hχu']
  exact h3

end GlobalTheory.HeightCounting.TwistAny
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisRepOfCuspidalStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_rep_of_cuspidal : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE), GalEx D → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : D.naut.CG D.R.r), D.naut.csd π → D.naut.ralg π → ∃ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (Qbar l), IsRepOf D l ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) ρ := by
  first | exact @GlobalTheory.HeightCounting.TwistAny.exists_isRepOf_tw | exact GlobalTheory.HeightCounting.TwistAny.exists_isRepOf_tw | (intros; apply GlobalTheory.HeightCounting.TwistAny.exists_isRepOf_tw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePlaceLevelPlacesDistinctUnderlying
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePlaceLevelPlacesDistinctUnderlying
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelTypePlace

theorem not_two_primes {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hne : p ≠ q) (h1 : (p : R) ∈ P) (h2 : (q : R) ∈ P) : False := by
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hne)
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom R)
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact P.add_mem (P.mul_mem_left _ h1) (P.mul_mem_left _ h2)

theorem natCast_mem_of_card {E : Type} [Field E] [NumberField E] (PP : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    {q : ℕ} (hc : Nat.card (𝓞 E ⧸ PP.asIdeal) = q) (hq0 : q ≠ 0) : (q : 𝓞 E) ∈ PP.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hc, ← nsmul_one]
  exact card_nsmul_eq_zero'

theorem offPlace : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) → ∀ (t : T) (s : ReciprocityTheory.Aut.SplitPlace D.host.E), s.w ∈ L.Pg → (∀ PP ∈ L.Pg, PP ≠ s.w → ¬ NG.OverPl PP s.v) ∧ (∀ PP ∈ L.Q t, ¬ NG.OverPl PP s.v) ∧ s.w ∉ L.Q t ∧ (L.xiH t).UnrAt s.w := by
  intro D T L μ0 hL hPg t s hs

  have hA : ∀ PP : Pl D.host.E, NG.OverPl PP s.v → ∀ p : ℕ, (p : 𝓞 D.host.E) ∈ s.w.asIdeal →
      (p : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP hov p hp
    have h1 : (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal := by
      rw [← s.w_under, Ideal.mem_comap, map_natCast]; exact hp
    rw [← hov, Ideal.mem_comap, map_natCast] at h1; exact h1
  have hgne : ∀ k k' : Fin 2, k ≠ k' → D.host.g k ≠ D.host.g k' := by
    intro k k' h
    fin_cases k <;> fin_cases k' <;> first | exact absurd rfl h | exact D.host.g_ne | exact D.host.g_ne.symm
  obtain ⟨k, v, hkv⟩ := (hPg s.w).1 hs
  have hgk : (D.host.g k : 𝓞 D.host.E) ∈ s.w.asIdeal := by rw [hkv]; exact D.naut.plGw_over k v

  have hQ : ∀ PP ∈ L.Q t, (D.host.g k : 𝓞 D.host.E) ∈ PP.asIdeal → False := by
    intro PP hP hg
    obtain ⟨q, hq, hcard, -, hqg⟩ := (hL.Q_pl t PP hP).1
    exact not_two_primes PP.asIdeal (D.host.g_prime k) hq (hqg k).symm hg
      (natCast_mem_of_card PP hcard hq.ne_zero)
  have h3 : s.w ∉ L.Q t := fun h => hQ s.w h hgk
  refine ⟨?_, fun PP hP hov => hQ PP hP (hA PP hov _ hgk), h3, ?_⟩
  · intro PP hP hne hov
    rcases GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s PP hov with e | hc
    · exact hne e.symm
    obtain ⟨k', v', hkv'⟩ := (hPg PP).1 hP
    have hk : k' = k := by
      by_contra hk
      have h1 : (D.host.g k' : 𝓞 D.host.E) ∈ PP.asIdeal := by rw [hkv']; exact D.naut.plGw_over k' v'
      exact not_two_primes PP.asIdeal (D.host.g_prime k') (D.host.g_prime k) (hgne k' k hk) h1
        (hA PP hov _ hgk)
    subst hk
    rw [hkv, hkv'] at hc
    exact D.naut.plGw_nconj k' v' v hc
  · by_contra hn
    rcases (hL.Q_ram t s.w).1 hn with h | ⟨PP', hP', hc⟩
    · exact h3 h
    obtain ⟨q, hq, hcard, -, hqg⟩ := (hL.Q_pl t PP' hP').1
    obtain ⟨c', hc', hcq⟩ := hc _ (natCast_mem_of_card PP' hcard hq.ne_zero)
    have hq' : (q : 𝓞 D.host.E) = c' := by
      apply RingOfIntegers.ext
      rw [hcq]; simp
    exact not_two_primes s.w.asIdeal (D.host.g_prime k) hq (hqg k).symm hgk (hq' ▸ hc')

end GlobalTheory.LevelTypePlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePlaceLevelPlacesDistinctUnderlyingStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePlace_levelPlaces_distinct_underlying : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) → ∀ (t : T) (s : ReciprocityTheory.Aut.SplitPlace D.host.E), s.w ∈ L.Pg → (∀ PP ∈ L.Pg, PP ≠ s.w → ¬ NG.OverPl PP s.v) ∧ (∀ PP ∈ L.Q t, ¬ NG.OverPl PP s.v) ∧ s.w ∉ L.Q t ∧ (L.xiH t).UnrAt s.w := by
  first | exact @GlobalTheory.LevelTypePlace.offPlace | exact GlobalTheory.LevelTypePlace.offPlace | (intros; apply GlobalTheory.LevelTypePlace.offPlace <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneSubEwMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar.Resid

open GlobalTheory.Mem.SymFrame

variable {D : D7}

theorem rank_eq (D : D7) : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
  unfold Ranks.r Ranks.rS
  obtain ⟨t, ht⟩ := D.R.m_even
  have := D.R.two_le_m
  omega

def posE (D : D7) (a : Fin D.R.rS) : Fin D.R.r := ⟨a.1, by have := rank_eq D; omega⟩

def posB (D : D7) (i : Fin D.R.k) : Fin D.R.r := ⟨D.R.rS + i.1, by have := rank_eq D; omega⟩

def posN (D : D7) (a : Fin D.R.rS) : Fin D.R.r :=
  ⟨if a.1 + 1 < D.R.rS then a.1 + 1 else D.R.rS + D.R.k, by have := rank_eq D; split_ifs <;> omega⟩

theorem symVec_posN (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (a : Fin D.R.rS) :
    symVec X w (posN D a) = nxt X.e0 X.z0 a := by
  unfold symVec GlobalTheory.SeeConjRead.flagV posN nxt
  by_cases h : a.1 + 1 < D.R.rS
  · simp [h]
  · have h2 : ¬ (D.R.rS + D.R.k < D.R.rS) := by omega
    simp [h]

theorem symVec_posB (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : EwAt X w) (i : Fin D.R.k) :
    symVec X w (posB D i) = X.bw i := by
  unfold symVec GlobalTheory.SeeConjRead.flagV posB epsW
  have h1 : ¬ (D.R.rS + i.1 < D.R.rS) := by omega
  have h2 : D.R.rS + i.1 < D.R.rS + D.R.k := by omega
  simp [h1, h2, hw]

theorem dual_row (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {g : ℕ} {u : Fin D.R.r → VA X.B.I}
    {x : X.B.I.Gf} {N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod g)} (hN : IsMatIn X w u x N)
    {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) (i₀ : Fin D.R.r)
    (hd : ∀ j, hA X.B.I y (u j) - (if j = i₀ then 1 else 0) ∈ wInt X w) (i : Fin D.R.r) :
    hA X.B.I y (X.B.I.fmat x *ᵥ u i) - (((N i₀ i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈
      wInt X w := by
  have h := hA_isMatIn X w hN hy i
  have hs : (∑ j, (((N j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) *
      (hA X.B.I y (u j) - (if j = i₀ then 1 else 0))) ∈ wInt X w := by
    refine Submodule.sum_mem _ fun j _ => ?_
    exact (wInt X w).smul_mem
      (⟨_, natCast_mem _ (N j i).val⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) (hd j)
  have e : (∑ j, (((N j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) *
      (hA X.B.I y (u j) - (if j = i₀ then 1 else 0))) =
      (∑ j, (((N j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * hA X.B.I y (u j)) -
        (((N i₀ i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) := by
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  rw [e] at hs
  have := add_mem h hs
  convert this using 1
  abel

theorem natCast_g_mem (X : HidaSetting D) {w : HeightOneSpectrum (𝓞 D.host.E)} (k : Fin 2)
    (hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) :
    ((D.host.g k : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w := by
  refine Submodule.subset_span ⟨(D.host.g k : 𝓞 X.B.I.E), ⟨_, hg, ?_⟩, ?_⟩
  · simp
  · simp

theorem one_sub_ew_mem (X : HidaSetting D) {w : HeightOneSpectrum (𝓞 D.host.E)} (k : Fin 2)
    (hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) (hw : EwAt X w) : 1 - X.ew ∈ wInt X w := by
  have hz : X.z0 ∈ X.B.I.Lf := X.vectorsInLattice.2.1
  have h1 := hA_mem_wInt X w hz (hw X.z0 hz)
  rw [hA_smul_right'] at h1
  have h2 := wInt_of_zmod X k hg X.formsAtZero.1
  have hint : 1 - X.ew ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E := sub_mem (one_mem _) X.ew_int
  have h3 : (1 - X.ew) * (hA X.B.I X.z0 X.z0 + 1) ∈ wInt X w :=
    (wInt X w).smul_mem (⟨_, hint⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) h2
  have := sub_mem h3 h1
  convert this using 1
  ring

end GlobalTheory.Mem.SymChar.Resid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryGroupsEquivUnitFormGramOne
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryGroupsEquivUnitFormGramOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.StdGroups

theorem castGL_bc {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {m n : ℕ} (h : m = n) (x : GL (Fin m) A) :
    castGL h (Formalism.UG.bc f x) = Formalism.UG.bc f (castGL h x) := by
  subst h
  ext i j
  simp [castGL, Formalism.UG.bc, Matrix.reindexAlgEquiv_apply]

theorem castGL_symm_castGL' {A : Type} [CommRing A] {m n : ℕ} (h : m = n) (x : GL (Fin m) A) :
    castGL h.symm (castGL h x) = x := by
  subst h
  ext i j
  simp [castGL, Matrix.reindexAlgEquiv_apply]

theorem castGL_mem_UJ_one {A : Type} [CommRing A] (σ : A →+* A) {m n : ℕ} (h : m = n) (x : GL (Fin m) A)
    (hx : x ∈ Formalism.UG.UJ σ (1 : Matrix (Fin m) (Fin m) A)) : castGL h x ∈ Formalism.UG.UJ σ (1 : Matrix (Fin n) (Fin n) A) := by
  subst h
  have e : castGL (rfl : m = m) x = x := by
    ext i j
    simp [castGL, Matrix.reindexAlgEquiv_apply]
  rwa [e]

theorem bc_injective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f) {m : ℕ} :
    Function.Injective (Formalism.UG.bc (n := Fin m) f) := by
  intro x y hxy
  ext i j
  exact hf (congrArg (fun z : GL (Fin m) B => (z : Matrix (Fin m) (Fin m) B) i j) hxy)

def phiG (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) :
    Bridge.Gf (Vc X.toD7 i) →* Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV where
  toFun g := ⟨castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) g.1), by
    obtain ⟨k, hk⟩ := g.2
    have h1 : Formalism.UG.bc (swapAE X.toD7) g.1 ∈ Formalism.L2.DIV.UA X.toD7.sp.cm (Vc X.toD7 i).gram := by
      rw [← hk]
      exact GlobalTheory.LevSplit.finE_mem_UA _ k
    rw [hg] at h1
    exact castGL_mem_UA_std _ _ _ h1⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

theorem phiG_val (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) (g : Bridge.Gf (Vc X.toD7 i)) :
    (phiG X i hg g : GL (Fin X.B.R.nV) (LiftBrg.EA X)) = castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) g.1) := rfl

theorem phiG_injective (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) :
    Function.Injective (phiG X i hg) := by
  intro a b hab
  have h1 := congrArg (fun z : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV => (z : GL (Fin X.B.R.nV) (LiftBrg.EA X))) hab
  simp only [phiG_val] at h1
  have h2 := (castGL (rkEq X i).symm).injective h1
  exact Subtype.ext (bc_injective _ (Algebra.TensorProduct.comm _ _ _).injective h2)

theorem phiG_surjective (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) :
    Function.Surjective (phiG X i hg) := by
  intro x
  have hy : castGL (rkEq X i) (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)) ∈ Formalism.L2.DIV.UA X.toD7.sp.cm (Vc X.toD7 i).gram := by
    rw [hg]
    exact castGL_mem_UA_std _ _ _ x.2
  refine ⟨⟨finHom (Vc X.toD7 i) (GlobalTheory.StdFrameExist.liftF (Vc X.toD7 i) _ hy), _, rfl⟩, Subtype.ext ?_⟩
  rw [phiG_val]
  have e := GlobalTheory.StdFrameExist.finE_liftF (Vc X.toD7 i) _ hy
  change castGL (rkEq X i).symm (finE (Vc X.toD7 i) (GlobalTheory.StdFrameExist.liftF (Vc X.toD7 i) _ hy)) = _
  rw [e, castGL_symm_castGL']

end GlobalTheory.Mem.R3.LiftBrg.StdGroups

namespace GlobalTheory.Mem.R3.LiftBrg.StdGroups

theorem bc_inclR_mem_HR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (γ : GL (Fin m) E) (hγ : γ ∈ Formalism.UG.UJ (σ : E →+* E) J) :
    Formalism.UG.bc (inclR (F := F) R) γ ∈ HR R σ J := by
  have h : Formalism.UG.cT (σ : E →+* E) (γ : Matrix (Fin m) (Fin m) E) * J * γ = J := hγ
  show Formalism.UG.cT (sigR R σ) ((γ : Matrix (Fin m) (Fin m) E).map (inclR R)) * J.map (inclR R) *
    (γ : Matrix (Fin m) (Fin m) E).map (inclR R) = J.map (inclR R)
  have h2 : Formalism.UG.cT (sigR R σ) ((γ : Matrix (Fin m) (Fin m) E).map (inclR R)) =
      (Formalism.UG.cT (σ : E →+* E) (γ : Matrix (Fin m) (Fin m) E)).map (inclR (F := F) R) := by
    ext i j
    simp [Formalism.UG.cT, sigR, inclR]
  rw [h2, ← Matrix.map_mul, ← Matrix.map_mul, h]

def psiQ (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) :
    Formalism.L2.Col.URat X.toD7.sp.cm X.B.R.nV →* GQ (Vc X.toD7 i) where
  toFun γ :=
    have hm : castGL (rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E) ∈
        Formalism.UG.UJ (X.toD7.sp.cm.sig : X.toD7.host.E →+* X.toD7.host.E) (Vc X.toD7 i).gram := by
      rw [hg]
      exact castGL_mem_UJ_one _ _ _ γ.2
    ⟨(show GA X.toD7 (Vc X.toD7 i) from
        (⟨Formalism.UG.bc (inclR (F := X.toD7.host.F) (AF X.toD7.host.F)) (castGL (rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E)),
          bc_inclR_mem_HR _ _ _ _ hm⟩ : HR (AF X.toD7.host.F) X.toD7.sp.cm.sig (Vc X.toD7 i).gram)),
      Subgroup.mem_subgroupOf.2 ⟨_, hm, rfl⟩⟩
  map_one' := Subtype.ext (Subtype.ext (by first | rfl | (simp only [map_one]; rfl) | (simp <;> rfl)))
  map_mul' a b := Subtype.ext (Subtype.ext (by first | rfl | (simp only [map_mul]; rfl) | (simp <;> rfl)))

theorem psiQ_mat (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) (γ : Formalism.L2.Col.URat X.toD7.sp.cm X.B.R.nV) :
    matHom (Vc X.toD7 i) (psiQ X i hg γ : GA X.toD7 (Vc X.toD7 i)) =
      Formalism.UG.bc (incA X.toD7) (castGL (rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E)) := rfl

theorem phiG_ratF_psiQ (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) (γ : Formalism.L2.Col.URat X.toD7.sp.cm X.B.R.nV) :
    phiG X i hg (Bridge.ratF (Vc X.toD7 i) (psiQ X i hg γ)) = Formalism.L2.Col.ratIn X.toD7.sp.cm X.B.R.nV γ := by
  apply Subtype.ext
  rw [phiG_val, Formalism.L2.Col.ratIn_val]
  have e1 : ((Bridge.ratF (Vc X.toD7 i) (psiQ X i hg γ)) : GL (Fin (Vc X.toD7 i).rank) _) =
      Formalism.UG.bc (inclR (F := X.toD7.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F)) (castGL (rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E)) := by
    change finHom (Vc X.toD7 i) _ = _
    rw [finHom, MonoidHom.comp_apply, Subgroup.coe_subtype, psiQ_mat]
    exact GlobalTheory.HLatMove.bc_map_bc_inclR _ _
  rw [e1]
  have e2 : Formalism.UG.bc (swapAE X.toD7) (Formalism.UG.bc (inclR (F := X.toD7.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F))
      (castGL (rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E))) =
      Formalism.UG.bc (Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E) (castGL (rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E)) := by
    ext a b
    simp [Formalism.UG.bc, swapAE, inclR, Formalism.UG.inclE]
  rw [e2, ← castGL_bc, castGL_symm_castGL']

theorem psiQ_injective (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) :
    Function.Injective (psiQ X i hg) := by
  intro a b hab
  have h1 : Formalism.L2.Col.ratIn X.toD7.sp.cm X.B.R.nV a = Formalism.L2.Col.ratIn X.toD7.sp.cm X.B.R.nV b := by
    rw [← phiG_ratF_psiQ X i hg a, ← phiG_ratF_psiQ X i hg b, hab]
  have h2 := congrArg (fun z : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV => (z : GL (Fin X.B.R.nV) (LiftBrg.EA X))) h1
  simp only [Formalism.L2.Col.ratIn_val] at h2
  exact Subtype.ext (Formalism.L2.DIV.incl_inj _ _ _ h2)

theorem psiQ_surjective (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) :
    Function.Surjective (psiQ X i hg) := by
  intro δ
  obtain ⟨γE, hγE, e⟩ := Subgroup.mem_subgroupOf.1 δ.2
  have hγ : castGL (rkEq X i).symm γE ∈ Formalism.L2.Col.URat X.toD7.sp.cm X.B.R.nV := by
    rw [hg] at hγE
    exact castGL_mem_UJ_one _ _ _ hγE
  refine ⟨⟨_, hγ⟩, Subtype.ext (Subtype.ext ?_)⟩
  change Formalism.UG.bc (inclR (F := X.toD7.host.F) (AF X.toD7.host.F)) (castGL (rkEq X i) (castGL (rkEq X i).symm γE)) = _
  rw [castGL_symm_castGL' (rkEq X i).symm γE]
  exact e

theorem stdGroups_equiv : ∀ (X : Stages) (i : Fin X.toD7.R.m), (Vc X.toD7 i).gram = 1 →
    ∃ (eG : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i))
      (eΓ : Formalism.L2.Col.URat X.toD7.sp.cm X.B.R.nV ≃* GQ (Vc X.toD7 i)),
      (∀ x, LiftBrg.castGL (LiftBrg.rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7)
          ((eG x : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F ⊗[X.toD7.host.F] X.toD7.host.E))) =
        (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))) ∧
      (∀ γ, Bridge.ratF (Vc X.toD7 i) (eΓ γ) = eG (Formalism.L2.Col.ratIn X.toD7.sp.cm X.B.R.nV γ)) ∧
      (∀ γ, Bridge.IsRatMat (Vc X.toD7 i) (eΓ γ) (LiftBrg.castGL (LiftBrg.rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E))) := by
  intro X i hg
  let eG0 := MulEquiv.ofBijective (phiG X i hg) ⟨phiG_injective X i hg, phiG_surjective X i hg⟩
  let eQ := MulEquiv.ofBijective (psiQ X i hg) ⟨psiQ_injective X i hg, psiQ_surjective X i hg⟩
  refine ⟨eG0.symm, eQ, fun x => ?_, fun γ => ?_, fun γ => ?_⟩
  · have h := eG0.apply_symm_apply x
    exact congrArg (fun z : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV => (z : GL (Fin X.B.R.nV) (LiftBrg.EA X))) h
  · rw [MulEquiv.eq_symm_apply]
    exact phiG_ratF_psiQ X i hg γ
  · exact psiQ_mat X i hg γ

end GlobalTheory.Mem.R3.LiftBrg.StdGroups
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryGroupsEquivUnitFormGramOneStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryGroups_equiv_unitForm_gram_one : ∀ (X : Stages) (i : Fin X.toD7.R.m), (Vc X.toD7 i).gram = 1 →
    ∃ (eG : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i))
      (eΓ : Formalism.L2.Col.URat X.toD7.sp.cm X.B.R.nV ≃* GQ (Vc X.toD7 i)),
      (∀ x, LiftBrg.castGL (LiftBrg.rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7)
          ((eG x : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F ⊗[X.toD7.host.F] X.toD7.host.E))) =
        (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))) ∧
      (∀ γ, Bridge.ratF (Vc X.toD7 i) (eΓ γ) = eG (Formalism.L2.Col.ratIn X.toD7.sp.cm X.B.R.nV γ)) ∧
      (∀ γ, Bridge.IsRatMat (Vc X.toD7 i) (eΓ γ) (LiftBrg.castGL (LiftBrg.rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E))) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.StdGroups.stdGroups_equiv | exact GlobalTheory.Mem.R3.LiftBrg.StdGroups.stdGroups_equiv | (intros; apply GlobalTheory.Mem.R3.LiftBrg.StdGroups.stdGroups_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTwistSideFormsLeSpanGoodLiftForms
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTwistSideFormsLeSpanGoodLiftForms
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsSpan

variable (D : D7) (S : RatDat D.ntw)

def actLHom (j : ℕ) : G0g D.nd →* Module.End D.what₂.LL (S.WL j) where
  toFun := actL D S j
  map_one' := by
    simp only [actL, map_one, Units.val_one, inv_one, one_smul]
  map_mul' g h := by
    simp only [actL, map_mul, Units.val_mul, mul_inv]
    exact (smul_mul_smul_comm _ _ _ _).symm

def finiteLevelGroupFintype : Fintype (G0g D.nd) := Fintype.ofFinite _

attribute [local instance] finiteLevelGroupFintype

def opL (j : ℕ) : MonoidAlgebra ↥D.LL0 (G0g D.nd) →+* Module.End D.what₂.LL (S.WL j) :=
  (MonoidAlgebra.lift D.what₂.LL (Module.End D.what₂.LL (S.WL j)) (G0g D.nd) (actLHom D S j)).toRingHom.comp
    (MonoidAlgebra.mapRingHom (G0g D.nd) (algebraMap ↥D.LL0 D.what₂.LL))

theorem opL_of (j : ℕ) (g : G0g D.nd) : opL D S j (MonoidAlgebra.of _ _ g) = actL D S j g := by
  simp [opL, MonoidAlgebra.of_apply, actLHom]

theorem opL_eL (j : ℕ) : opL D S j (eL D) = ∑ᶠ g : G0g D.nd, ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) • actL D S j g := by
  rw [finsum_eq_sum_of_fintype]
  simp [opL, eL, MonoidAlgebra.lift_apply, actLHom, Finsupp.sum_fintype]

variable {D S}

theorem actL_mul (j : ℕ) (g h : G0g D.nd) : actL D S j (g * h) = actL D S j g * actL D S j h :=
  (actLHom D S j).map_mul g h

theorem eLop_idem (he : EIdem D) (j : ℕ) (x : S.WL j) :
    opL D S j (eL D) (opL D S j (eL D) x) = opL D S j (eL D) x := by
  rw [← Module.End.mul_apply, ← map_mul, he.1]

theorem eLop_comm (he : EIdem D) (j : ℕ) (g : G0g D.nd) (x : S.WL j) :
    opL D S j (eL D) (actL D S j g x) = actL D S j g (opL D S j (eL D) x) := by
  rw [← opL_of D S j g, ← Module.End.mul_apply, ← map_mul, he.2 g, map_mul, Module.End.mul_apply]

def fintypeU : Fintype ↥(Formalism.IndefR.NX.U D.nd) := Fintype.ofFinite _

attribute [local instance] fintypeU


variable (D) in
def cU (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (u : ↥(Formalism.IndefR.NX.U D.nd)) : ↥D.LL0 :=
  (Fintype.card ↥(Formalism.IndefR.NX.U D.nd) : ↥D.LL0)⁻¹ * ((psiUOf D.nd (NX.xiRed D) θ u⁻¹ : (↥D.LL0)ˣ) : ↥D.LL0)

theorem cU_mul (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (u' u : ↥(Formalism.IndefR.NX.U D.nd)) :
    ((psiUOf D.nd (NX.xiRed D) θ u' : (↥D.LL0)ˣ) : ↥D.LL0) * cU D θ (u' * u) = cU D θ u := by
  unfold cU
  rw [mul_inv_rev, map_mul, Units.val_mul, map_inv (psiUOf D.nd (NX.xiRed D) θ) u', Units.val_inv_eq_inv_val]
  have h0 : ((psiUOf D.nd (NX.xiRed D) θ u' : (↥D.LL0)ˣ) : ↥D.LL0) ≠ 0 := Units.ne_zero _
  field_simp

def projL (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (j : ℕ) : Module.End D.what₂.LL (S.WL j) :=
  ∑ u : ↥(Formalism.IndefR.NX.U D.nd), ((cU D θ u : ↥D.LL0) : D.what₂.LL) • actL D S j u

theorem projL_isot (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (j : ℕ)
    (u' : ↥(Formalism.IndefR.NX.U D.nd)) (w : S.WL j) :
    actL D S j u' (projL (S := S) θ j w) =
      (((psiUOf D.nd (NX.xiRed D) θ u' : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) • projL (S := S) θ j w := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [projL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
  refine Fintype.sum_equiv (Equiv.mulLeft u') _ _ fun u => ?_
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, actL_mul, Module.End.mul_apply]
  congr 1
  rw [← cU_mul θ u' u]
  push_cast
  ring

theorem goodL_of (he : EIdem D) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (j : ℕ) (w : S.WL j) :
    opL D S j (eL D) (projL (S := S) θ j w) ∈ goodL D S θ j := by
  unfold goodL
  rw [← opL_eL, Submodule.mem_inf, Submodule.mem_iInf]
  refine ⟨?_, fun u => ?_⟩
  · rw [Module.End.mem_eigenspace_iff, one_smul, eLop_idem he]
  · rw [Module.End.mem_eigenspace_iff, ← eLop_comm he, projL_isot, map_smul]

section KSide

variable (T : TwR D.LL0 D.nd)

def projT (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) : Module.End (FractionRing (T.O i)) (FmT D T S i j b) :=
  ∑ u : ↥(Formalism.IndefR.NX.U D.nd), readT D T i b (cU D In.θ u) • (actGT D T S In.rho In.chi i j b u).toLinearMap

theorem card_ne (i : T.Tw) (b : Bool) :
    readT D T i b (Fintype.card ↥(Formalism.IndefR.NX.U D.nd) : ↥D.LL0) ≠ 0 := by
  refine (map_ne_zero (readT D T i b)).mpr fun h => ?_
  have h' := congrArg (fun x : ↥D.LL0 => (x : D.what₂.LL)) h
  exact Fintype.card_ne_zero (by exact_mod_cast h')

theorem projT_fix (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) (z : FmT D T S i j b)
    (hz : z ∈ Fm0T D T S In.rho In.chi In.θ i j b) : projT T In i j b z = z := by
  have hu : ∀ u : ↥(Formalism.IndefR.NX.U D.nd), actGT D T S In.rho In.chi i j b u z =
      readT D T i b ((psiUOf D.nd (NX.xiRed D) In.θ u : (↥D.LL0)ˣ) : ↥D.LL0) • z := by
    intro u
    have h := (Submodule.mem_iInf _).mp hz u
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
    exact h
  simp only [projT, LinearMap.sum_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, hu, smul_smul, ← map_mul]
  have hc : ∀ u : ↥(Formalism.IndefR.NX.U D.nd), cU D In.θ u * ((psiUOf D.nd (NX.xiRed D) In.θ u : (↥D.LL0)ˣ) : ↥D.LL0) =
      (Fintype.card ↥(Formalism.IndefR.NX.U D.nd) : ↥D.LL0)⁻¹ := by
    intro u
    unfold cU
    rw [map_inv, Units.val_inv_eq_inv_val]
    have h0 : ((psiUOf D.nd (NX.xiRed D) In.θ u : (↥D.LL0)ˣ) : ↥D.LL0) ≠ 0 := Units.ne_zero _
    field_simp
  simp only [hc, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul (FractionRing (T.O i)), smul_smul]
  have h1 : ((Fintype.card ↥(Formalism.IndefR.NX.U D.nd) : ℕ) : FractionRing (T.O i)) *
      readT D T i b (Fintype.card ↥(Formalism.IndefR.NX.U D.nd) : ↥D.LL0)⁻¹ = 1 := by
    rw [map_inv₀, ← map_natCast (readT D T i b)]
    exact mul_inv_cancel₀ (card_ne T i b)
  rw [h1, one_smul]

end KSide

theorem projT_phi (T : TwR D.LL0 D.nd) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) (Φ : S.WL j →+ FmT D T S i j b)
    (hsl : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (hact : ∀ (g : G0g D.nd) (x : S.WL j), Φ (actL D S j g x) = actGT D T S In.rho In.chi i j b g (Φ x))
    (w : S.WL j) : projT T In i j b (Φ w) = Φ (projL (S := S) In.θ j w) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [projT, projL, LinearMap.sum_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, map_sum, hsl, hact]

theorem span_one_tmul {R A M : Type} [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M] [Module R M] :
    Submodule.span A (Set.range fun m : M => (1 : A) ⊗ₜ[R] m) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a m =>
    have h : a ⊗ₜ[R] m = a • ((1 : A) ⊗ₜ[R] m) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
  | add x y hx hy => exact Submodule.add_mem _ hx hy


variable (S) in
def oneT (T : TwR D.LL0 D.nd) (i : T.Tw) (j : ℕ) (b : Bool) (w : ↥(WKr D S j)) : FmT D T S i j b :=
  (1 : KT D T i b) ⊗ₜ[S.Ks] w

theorem FmT_span (T : TwR D.LL0 D.nd) (i : T.Tw) (j : ℕ) (b : Bool) :
    Submodule.span (FractionRing (T.O i)) (Set.range (oneT S T i j b)) = ⊤ :=
  span_one_tmul (R := S.Ks) (A := KT D T i b) (M := ↥(WKr D S j))

end GlobalTheory.HeightCounting.FormsSpan


open GlobalTheory.HeightCounting.FormsSpan in
theorem GlobalTheory.HeightCounting.FormsStep.goodTwistSideForms_le_span_goodLiftForms : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd) (i : T.Tw) (j : ℕ) (b : Bool),
    1 ≤ j → j ≤ D.R.m → EIdem D → ∀ (Φ : S.WL j →+ FmT D T S i j b),
    (∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x) →
    (∀ (g : G0g D.nd) (x : S.WL j), Φ (actL D S j g x) = actGT D T S In.rho In.chi i j b g (Φ x)) →
    (∀ x : S.WL j, Φ ((∑ᶠ g : G0g D.nd, ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) • actL D S j g) x) =
      eGT D T S In.rho In.chi i j b (Φ x)) →
    (∀ w : ↥(WKr D S j), Φ (w : S.WL j) = (1 : KT D T i b) ⊗ₜ[S.Ks] w) →
    V0T D T S In.rho In.chi In.θ i j b ≤
      Submodule.span (FractionRing (T.O i)) (Φ '' (goodL D S In.θ j : Set (S.WL j))) := by
  intro D S In T i j b _ _ he Φ hsl hact hE h1 y hy
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
  rw [← projT_fix T In i j b z hz]
  have key : Submodule.span (FractionRing (T.O i))
      (Set.range (oneT S T i j b)) ≤
      (Submodule.span (FractionRing (T.O i)) (Φ '' (goodL D S In.θ j : Set (S.WL j)))).comap
        (eGT D T S In.rho In.chi i j b ∘ₗ projT T In i j b) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨w, rfl⟩
    change eGT D T S In.rho In.chi i j b (projT T In i j b (oneT S T i j b w)) ∈
      Submodule.span (FractionRing (T.O i)) (Φ '' (goodL D S In.θ j : Set (S.WL j)))
    rw [show oneT S T i j b w = Φ (w : S.WL j) from (h1 w).symm, projT_phi T In i j b Φ hsl hact, ← hE, ← opL_eL]
    exact Submodule.subset_span ⟨_, goodL_of he In.θ j (w : S.WL j), rfl⟩
  exact key (Submodule.eq_top_iff'.mp (FmT_span (S := S) T i j b) z)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTwistSideFormsLeSpanGoodLiftFormsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.V0T_le_span_image_goodL : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd) (i : T.Tw) (j : ℕ) (b : Bool),
    1 ≤ j → j ≤ D.R.m → EIdem D → ∀ (Φ : S.WL j →+ FmT D T S i j b),
    (∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x) →
    (∀ (g : G0g D.nd) (x : S.WL j), Φ (actL D S j g x) = actGT D T S In.rho In.chi i j b g (Φ x)) →
    (∀ x : S.WL j, Φ ((∑ᶠ g : G0g D.nd, ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) • actL D S j g) x) =
      eGT D T S In.rho In.chi i j b (Φ x)) →
    (∀ w : ↥(WKr D S j), Φ (w : S.WL j) = (1 : KT D T i b) ⊗ₜ[S.Ks] w) →
    V0T D T S In.rho In.chi In.θ i j b ≤
      Submodule.span (FractionRing (T.O i)) (Φ '' (goodL D S In.θ j : Set (S.WL j))) := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.goodTwistSideForms_le_span_goodLiftForms | exact GlobalTheory.HeightCounting.FormsStep.goodTwistSideForms_le_span_goodLiftForms | (intros; apply GlobalTheory.HeightCounting.FormsStep.goodTwistSideForms_le_span_goodLiftForms <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianZ0SymmetricFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianZ0SymmetricFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf

namespace GlobalTheory.Mem.SymChar.ZPair
open GlobalTheory.Mem.SymFrame

theorem rank_eq' (D : D7) : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
  unfold Ranks.r Ranks.rS
  obtain ⟨t, ht⟩ := D.R.m_even
  have := D.R.two_le_m
  omega

theorem zmod_hA_z0_symVec (D : D7) (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (j : Fin D.R.r) :
    ZMod' X.B.I X.B.g (hA X.B.I X.z0 (symVec X w j) - (if j.val = D.R.rS + D.R.k then -1 else 0)) := by
  have hr := rank_eq' D
  have hj := j.2
  unfold symVec GlobalTheory.SeeConjRead.flagV epsW
  split_ifs
  · exfalso; omega
  · rw [sub_zero, unitaryCongruence.hA_symm]; exact unitaryCongruence.Z_sig _ _ (X.formsAtZero.2 _).1
  · exfalso; omega
  · rw [sub_zero]; exact (X.weightVectorsIntegral _).1
  · exfalso; omega
  · rw [sub_zero]; exact (X.weightVectorsIntegral _).2.1
  · rw [sub_neg_eq_add]; exact X.formsAtZero.1
  · rw [sub_zero, unitaryCongruence.hA_symm]; exact unitaryCongruence.Z_sig _ _ (X.formsAtZero.2 _).2
  · exfalso; omega

theorem hA_z0_symVec : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (j : Fin D.R.r), hA X.B.I X.z0 (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) j) - (if j.val = D.R.rS + D.R.k then -1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  intro D X kv hg j
  exact GlobalTheory.Mem.SymChar.wInt_of_zmod X kv.1 hg (zmod_hA_z0_symVec D X _ j)

end GlobalTheory.Mem.SymChar.ZPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianZ0SymmetricFrameStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_z0_symmetric_frame : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (j : Fin D.R.r), hA X.B.I X.z0 (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) j) - (if j.val = D.R.rS + D.R.k then -1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  first | exact @GlobalTheory.Mem.SymChar.ZPair.hA_z0_symVec | exact GlobalTheory.Mem.SymChar.ZPair.hA_z0_symVec | (intros; apply GlobalTheory.Mem.SymChar.ZPair.hA_z0_symVec <;> assumption)
end
end
