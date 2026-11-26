module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisLogTeichmullerUniqueGaloisFrobeniusBdR
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsBdRPlusSectionOfTheta
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.Tuples
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineTIsUnitBcrisAndUniformizerBdRPlus
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineTIsUnitBcrisAndUniformizerBdRPlus
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.TFil

variable {l : ℕ} [Fact l.Prime]

theorem alg_factor (a : Per.Ainf l) :
    algebraMap (Per.Ainf l) (Per.Acris l) a =
      algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) a) :=
  GlobalTheory.RingIface.tower l a

theorem j_alg {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) (a : Per.Ainf l) :
    j (algebraMap (Per.Ainf l) (Per.Acris l) a) = aDp l a := by
  rw [alg_factor, hj.on0]
  rfl

theorem mu_eq (e : Per.Fl l) :
    mu e = xi e * (Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e) - 1) := by
  rw [xi, geom_sum_mul, ← map_pow, mu]
  congr 2
  rw [← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]

theorem isUnit_mu {e : Per.Fl l} (he : IsEps e) :
    IsUnit (algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Per.Ainf l) (Per.Acris l) (mu e))) := by
  have h1 : e ≠ 1 := by
    rintro rfl
    exact he.2 (by rw [map_one, map_one])
  exact GlobalTheory.CrisLoc.unit_of_root l e he.1 h1

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem isUnit_l {e : Per.Fl l} (he : IsEps e) : IsUnit (l : Per.Bcris l) := by
  obtain ⟨w, hw, -⟩ := GlobalTheory.T.exists_teichmullerTiltMinusOne_pow_div_envelope l e he.1
  have h0 : (l : Per.Acris0 l) * w = algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e) ^ (l - 1) := by
    apply Subtype.ext
    simpa using hw
  have h1 := congrArg (fun x => algebraMap (Per.Acris l) (Per.Bcris l)
    (algebraMap (Per.Acris0 l) (Per.Acris l) x)) h0
  simp only [map_mul, map_natCast, map_pow, ← alg_factor] at h1
  have h2 := (isUnit_mu he).pow (l - 1)
  rw [← h1] at h2
  exact isUnit_of_mul_isUnit_left h2

theorem isUnit_cofactor {e : Per.Fl l} (he : IsEps e) :
    IsUnit (aDp l (Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e) - 1)) := by
  obtain ⟨-, -, hu, hθ, -⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
  apply hu
  rw [hθ, map_sub, map_one, WittVector.fontaineTheta_teichmuller]
  intro h
  apply he.2
  rw [← sub_eq_zero]
  exact Subtype.ext h

theorem fil_of_eq {e : Per.Fl l} (he : IsEps e) (y v : Per.BdRp l) (hv : IsUnit v)
    (hy : y = aDp l (xi e) * v) : y ∈ Per.FilP l 1 ∧ y ∉ Per.FilP l 2 := by
  obtain ⟨hF, hr, -, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l e he
  obtain ⟨-, hk, -, -, -⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
  refine ⟨(hF 1 y).2 ⟨v, by rw [hy, pow_one]⟩, fun h => ?_⟩
  obtain ⟨c, hc⟩ := (hF 2 y).1 h
  have h1 : v - aDp l (xi e) * c = 0 := by
    apply hr
    rw [mul_sub, ← hy, hc]
    ring
  have h2 : v ∈ Per.FilP l 1 := (hF 1 v).2 ⟨c, by rw [pow_one]; exact sub_eq_zero.1 h1⟩
  exact (hv.map (Per.θD l)).ne_zero ((hk v).2 h2)

end GlobalTheory.MemLoc.TFil

namespace GlobalTheory.MemLoc
open TFil

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem core_t_unit_fil : ∀ (l : ℕ) [Fact l.Prime], ∀ C : Core l,
    IsUnit (algebraMap (Per.Acris l) (Per.Bcris l) C.t) ∧ C.j C.t ∈ Per.FilP l 1 ∧
      C.j C.t ∉ Per.FilP l 2 ∧ IsUnit (l : Per.Bcris l) := by
  intro l _ C
  have he := GlobalTheory.T.isPrimitiveTiltedRootOfUnity_localPeriodRingsData l C
  obtain ⟨t, u, ht, hu, htu⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l C.ε he.1
  have h1 : t = C.t := (GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l C.ε C.t he.1 C.t_log).1 t ht
  rw [h1] at htu
  have h2 : C.j C.t = aDp l (xi C.ε) *
      (aDp l (Per.tm ((frobeniusEquiv (Per.Fl l) l).symm C.ε) - 1) * C.j u) := by
    rw [htu, map_mul, j_alg C.j_cris, mu_eq, map_mul, mul_assoc]
  have h3 := fil_of_eq he _ _ ((isUnit_cofactor he).mul (hu.map C.j)) h2
  refine ⟨?_, h3.1, h3.2, isUnit_l he⟩
  rw [htu, map_mul]
  exact (isUnit_mu he).mul (hu.map _)

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineTIsUnitBcrisAndUniformizerBdRPlusStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fontaine_t_isUnit_bcris_and_uniformizer_bdRPlus : ∀ (l : ℕ) [Fact l.Prime], ∀ C : Core l, IsUnit (algebraMap (Per.Acris l) (Per.Bcris l) C.t) ∧ C.j C.t ∈ Per.FilP l 1 ∧ C.j C.t ∉ Per.FilP l 2 ∧ IsUnit (l : Per.Bcris l) := by
  first | exact @GlobalTheory.MemLoc.core_t_unit_fil | exact GlobalTheory.MemLoc.core_t_unit_fil | (intros; apply GlobalTheory.MemLoc.core_t_unit_fil <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
noncomputable section
namespace GlobalTheory.MemLoc.ActLaws
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

section
variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T]

theorem mem_map_of_evalₐ_eq_zero_pt (I : Ideal R) (hI : I.FG) (n : ℕ) (z : AdicCompletion I R)
    (hz : AdicCompletion.evalₐ I n z = 0) : z ∈ (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
  have h5 : z ∈ (I ^ n • ⊤ : Submodule R (AdicCompletion I R)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker]
    induction z using AdicCompletion.induction_on with
    | _ z =>
      rw [AdicCompletion.evalₐ_mk, Ideal.Quotient.eq_zero_iff_mem] at hz
      change Submodule.Quotient.mk (z.1 n) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      simpa using hz
  rw [Ideal.smul_top_eq_map] at h5
  exact h5

theorem evalₐ_alg_pt (I : Ideal R) (n : ℕ) (y : R) :
    AdicCompletion.evalₐ I n (algebraMap R (AdicCompletion I R) y) = Ideal.Quotient.mk (I ^ n) y :=
  (AdicCompletion.evalₐ I n).commutes y

theorem evalₐ_hom_pt (I : Ideal R) (hI : I.FG) (K : Ideal S) (f : R →+* S) (hf : I ≤ K.comap f)
    (φ : AdicCompletion I R →+* AdicCompletion K S)
    (hφ : ∀ r, φ (algebraMap R (AdicCompletion I R) r) = algebraMap S (AdicCompletion K S) (f r))
    (n : ℕ) (x : AdicCompletion I R) (y : R) (hy : AdicCompletion.evalₐ I n x = Ideal.Quotient.mk (I ^ n) y) :
    AdicCompletion.evalₐ K n (φ x) = Ideal.Quotient.mk (K ^ n) (f y) := by
  have h1 : x - algebraMap R (AdicCompletion I R) y ∈ (I ^ n).map (algebraMap R (AdicCompletion I R)) :=
    mem_map_of_evalₐ_eq_zero_pt I hI n _ (by rw [map_sub, hy, evalₐ_alg_pt, sub_self])
  have h2 : (I ^ n).map (algebraMap R (AdicCompletion I R)) ≤
      RingHom.ker ((AdicCompletion.evalₐ K n).toRingHom.comp φ) := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    have h3 : f r ∈ K ^ n := Ideal.le_comap_pow f n (Ideal.pow_right_mono hf n hr)
    rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply, hφ]
    exact (evalₐ_alg_pt K n (f r)).trans (Ideal.Quotient.eq_zero_iff_mem.2 h3)
  have h4 : AdicCompletion.evalₐ K n (φ (x - algebraMap R (AdicCompletion I R) y)) = 0 := h2 h1
  rw [map_sub, map_sub, hφ, evalₐ_alg_pt, sub_eq_zero] at h4
  exact h4

theorem hom_ext_pt (I : Ideal R) (hI : I.FG) (K : Ideal S) (f : R →+* S) (hf : I ≤ K.comap f)
    (φ ψ : AdicCompletion I R →+* AdicCompletion K S)
    (hφ : ∀ r, φ (algebraMap R (AdicCompletion I R) r) = algebraMap S (AdicCompletion K S) (f r))
    (hψ : ∀ r, ψ (algebraMap R (AdicCompletion I R) r) = algebraMap S (AdicCompletion K S) (f r))
    (x : AdicCompletion I R) : φ x = ψ x := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [evalₐ_hom_pt I hI K f hf φ hφ n x y hy.symm, evalₐ_hom_pt I hI K f hf ψ hψ n x y hy.symm]

theorem endo_ext_pt {A : Type} [CommRing A] (I : Ideal R) (hI : I.FG) (i : R →+* A) (e : A ≃+* AdicCompletion I R)
    (he : ∀ r, e (i r) = algebraMap R (AdicCompletion I R) r) (f : R →+* R) (hf : I ≤ I.comap f)
    (φ ψ : A →+* A) (hφ : ∀ r, φ (i r) = i (f r)) (hψ : ∀ r, ψ (i r) = i (f r)) (x : A) : φ x = ψ x := by
  have hs : ∀ r, e.symm (algebraMap R (AdicCompletion I R) r) = i r := fun r => by
    rw [← he, RingEquiv.symm_apply_apply]
  have h := hom_ext_pt I hI I f hf (e.toRingHom.comp (φ.comp e.symm.toRingHom))
    (e.toRingHom.comp (ψ.comp e.symm.toRingHom))
    (fun r => by
      change e (φ (e.symm _)) = _
      rw [hs, hφ, he])
    (fun r => by
      change e (ψ (e.symm _)) = _
      rw [hs, hψ, he]) (e x)
  change e (φ (e.symm (e x))) = e (ψ (e.symm (e x))) at h
  rw [RingEquiv.symm_apply_apply] at h
  exact e.injective h

theorem span_le_comap_pt (p : ℕ) (f : R →+* S) : Ideal.span {(p : R)} ≤ (Ideal.span {(p : S)}).comap f := by
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
  exact Ideal.mem_span_singleton_self _

end

variable {l : ℕ} [Fact l.Prime]

theorem awayMap_comp₂ (f g k : Per.Ainf l →+* Per.Ainf l) (e : ∀ x, k x = g (f x)) (x : Per.AinfP l) :
    Per.extP k x = Per.extP g (Per.extP f x) := by
  refine RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers (l : Per.Ainf l))
    (j := Per.extP k) (k := (Per.extP g).comp (Per.extP f)) (RingHom.ext fun y => ?_)) x
  simp only [RingHom.comp_apply, GlobalTheory.RingBasics.awayMap_algebraMap₂, e]

theorem awayMap_id₂ (f : Per.Ainf l →+* Per.Ainf l) (e : ∀ x, f x = x) (x : Per.AinfP l) :
    Per.extP f x = x := by
  refine RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers (l : Per.Ainf l))
    (j := Per.extP f) (k := RingHom.id _) (RingHom.ext fun y => ?_)) x
  simp only [RingHom.comp_apply, GlobalTheory.RingBasics.awayMap_algebraMap₂, e, RingHom.id_apply]

theorem acris_ext_pt (f : Per.Acris0 l →+* Per.Acris0 l) (φ ψ : Per.Acris l →+* Per.Acris l)
    (hφ : ∀ r, φ (algebraMap (Per.Acris0 l) (Per.Acris l) r) = algebraMap (Per.Acris0 l) (Per.Acris l) (f r))
    (hψ : ∀ r, ψ (algebraMap (Per.Acris0 l) (Per.Acris l) r) = algebraMap (Per.Acris0 l) (Per.Acris l) (f r))
    (x : Per.Acris l) : φ x = ψ x := by
  obtain ⟨e, he⟩ := GlobalTheory.AdicMaps.exists_acris_completion l
  exact endo_ext_pt _ (Submodule.fg_span_singleton _) (algebraMap (Per.Acris0 l) (Per.Acris l)) e he f
    (span_le_comap_pt l f) φ ψ hφ hψ x

theorem bdRp_ext_pt (f : Per.AinfP l →+* Per.AinfP l) (hf : Per.kerP l ≤ (Per.kerP l).comap f)
    (φ ψ : Per.BdRp l →+* Per.BdRp l)
    (hφ : ∀ r, φ (algebraMap (Per.AinfP l) (Per.BdRp l) r) = algebraMap (Per.AinfP l) (Per.BdRp l) (f r))
    (hψ : ∀ r, ψ (algebraMap (Per.AinfP l) (Per.BdRp l) r) = algebraMap (Per.AinfP l) (Per.BdRp l) (f r))
    (x : Per.BdRp l) : φ x = ψ x := by
  obtain ⟨e, he, -⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
  have hfg : (Per.kerP l).FG := by
    obtain ⟨ε, hε⟩ := GlobalTheory.MemLoc.Model.exists_isEps l
    rw [(GlobalTheory.MemLoc.thetaP_facts l).2.2.2.2.2.2 ε hε]
    exact Submodule.fg_span_singleton _
  exact endo_ext_pt _ hfg (algebraMap (Per.AinfP l) (Per.BdRp l)) e he f hf φ ψ hφ hψ x

theorem extends_comp {f g k : Per.Ainf l →+* Per.Ainf l} {F G K : Per.Acris l →+* Per.Acris l}
    (hf : GlobalTheory.CrisMaps.Extends f F) (hg : GlobalTheory.CrisMaps.Extends g G) (hk : GlobalTheory.CrisMaps.Extends k K)
    (e : ∀ x, k x = g (f x)) (x : Per.Acris l) : K x = G (F x) :=
  acris_ext_pt ((Per.extP k).restrict _ _ hk.mem) K (G.comp F)
    (fun r => hk.env r)
    (fun r => by
      rw [RingHom.comp_apply, hf.env, hg.env]
      exact congrArg _ (Subtype.ext (awayMap_comp₂ f g k e r).symm)) x

theorem extends_id {f : Per.Ainf l →+* Per.Ainf l} {F : Per.Acris l →+* Per.Acris l}
    (hf : GlobalTheory.CrisMaps.Extends f F) (e : ∀ x, f x = x) (x : Per.Acris l) : F x = x :=
  acris_ext_pt (RingHom.id _) F (RingHom.id _)
    (fun r => (hf.env r).trans (congrArg _ (Subtype.ext (awayMap_id₂ f e r))))
    (fun _ => rfl) x

theorem sigA_mul (g h : Per.Gq l) (x : Per.Acris l) : sigA (g * h) x = sigA g (sigA h x) :=
  extends_comp (GlobalTheory.CrisMaps.sigA_extends h) (GlobalTheory.CrisMaps.sigA_extends g) (GlobalTheory.CrisMaps.sigA_extends (g * h))
    (GlobalTheory.RingBasics.σA_mul g h) x

theorem sigA_one (x : Per.Acris l) : sigA 1 x = x :=
  extends_id (GlobalTheory.CrisMaps.sigA_extends 1) GlobalTheory.RingBasics.σA_one x

theorem σD_alg (g : Per.Gq l) (y : Per.BdRp l) :
    Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) y) = algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g y) :=
  GlobalTheory.RingIface.sigD_alg l g y

theorem σDp_mul (g h : Per.Gq l) (x : Per.BdRp l) : Per.σDp (g * h) x = Per.σDp g (Per.σDp h x) :=
  bdRp_ext_pt (Per.extP (Per.σA (g * h))) (GlobalTheory.RingBasics.ker_σ (g * h)) (Per.σDp (g * h)) ((Per.σDp g).comp (Per.σDp h))
    (GlobalTheory.RingIface.sigDp_alg l (g * h))
    (fun r => by
      rw [RingHom.comp_apply, GlobalTheory.RingIface.sigDp_alg, GlobalTheory.RingIface.sigDp_alg,
        awayMap_comp₂ _ _ _ (GlobalTheory.RingBasics.σA_mul g h)]) x

theorem σDp_one (x : Per.BdRp l) : Per.σDp 1 x = x :=
  bdRp_ext_pt (Per.extP (Per.σA (1 : Per.Gq l))) (GlobalTheory.RingBasics.ker_σ 1) (Per.σDp 1) (RingHom.id _)
    (GlobalTheory.RingIface.sigDp_alg l 1)
    (fun r => by rw [RingHom.id_apply, awayMap_id₂ _ GlobalTheory.RingBasics.σA_one]) x

theorem σDp_alg (g : Per.Gq l) (a : Per.AinfP l) :
    Per.σDp g (algebraMap (Per.AinfP l) (Per.BdRp l) a) =
      algebraMap (Per.AinfP l) (Per.BdRp l) (Per.extP (Per.σA g) a) :=
  GlobalTheory.RingIface.sigDp_alg l g a

theorem σDp_aDp (g : Per.Gq l) (a : Per.Ainf l) : Per.σDp g (aDp l a) = aDp l (Per.σA g a) := by
  simp only [aDp, RingHom.comp_apply, σDp_alg, GlobalTheory.RingBasics.awayMap_algebraMap₂]

theorem σD_mul (g h : Per.Gq l) (x : Per.BdR l) : Per.σD (g * h) x = Per.σD g (Per.σD h x) := by
  refine RingHom.congr_fun (GlobalTheory.CrisLoc.bdR_hom_ext l
    (f := Per.σD (g * h)) (g := (Per.σD g).comp (Per.σD h)) fun y => ?_) x
  simp only [RingHom.comp_apply, σD_alg, σDp_mul]

theorem σD_one (x : Per.BdR l) : Per.σD 1 x = x := by
  refine RingHom.congr_fun (GlobalTheory.CrisLoc.bdR_hom_ext l
    (f := Per.σD 1) (g := RingHom.id _) fun y => ?_) x
  simp only [RingHom.comp_apply, σD_alg, σDp_one, RingHom.id_apply]

theorem endo_zA_pt (F : Per.Ainf l →+* Per.Ainf l) (z : ℤ_[l]) : F (Per.zA l z) = Per.zA l z := by
  rw [← sub_eq_zero]
  refine WittVector.ext fun m => ?_
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec (m + 1) z)
  have hz : z = (z.appr (m + 1) : ℤ_[l]) + w * (l : ℤ_[l]) ^ (m + 1) := by rw [hw]; ring
  have h : F (Per.zA l z) - Per.zA l z ∈ Ideal.span {((l : ℕ) : Per.Ainf l) ^ (m + 1)} := by
    refine Ideal.mem_span_singleton'.2 ⟨F (Per.zA l w) - Per.zA l w, ?_⟩
    generalize z.appr (m + 1) = a at hz
    rw [hz]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  rw [(WittVector.mem_span_p_pow_iff_le_coeff_eq_zero _ _).1 h m (Nat.lt_succ_self m), WittVector.zero_coeff]

theorem φA_σA (g : Per.Gq l) (a : Per.Ainf l) : Per.φA l (Per.σA g a) = Per.σA g (Per.φA l a) := by
  refine WittVector.ext fun n => ?_
  rw [GlobalTheory.RingIface.phiA_coeff, GlobalTheory.RingIface.sigA_coeff, GlobalTheory.RingIface.sigA_coeff, GlobalTheory.RingIface.phiA_coeff,
    map_pow]

theorem φB_σB (g : Per.Gq l) (x : Per.Bcris l) : Per.φB l (Per.σB g x) = Per.σB g (Per.φB l x) := by
  refine RingHom.congr_fun (GlobalTheory.CrisLoc.bcris_hom_ext l
    (f := (Per.φB l).comp (Per.σB g)) (g := (Per.σB g).comp (Per.φB l)) fun y => ?_) x
  simp only [RingHom.comp_apply, GlobalTheory.CrisMaps.φB_phiA, GlobalTheory.CrisMaps.σB_sigA, GlobalTheory.CrisMaps.phiA_sigA]

theorem σB_mul (g h : Per.Gq l) (x : Per.Bcris l) : Per.σB (g * h) x = Per.σB g (Per.σB h x) := by
  refine RingHom.congr_fun (GlobalTheory.CrisLoc.bcris_hom_ext l
    (f := Per.σB (g * h)) (g := (Per.σB g).comp (Per.σB h)) fun y => ?_) x
  simp only [RingHom.comp_apply, GlobalTheory.CrisMaps.σB_sigA, sigA_mul]

theorem σB_one (x : Per.Bcris l) : Per.σB 1 x = x := by
  refine RingHom.congr_fun (GlobalTheory.CrisLoc.bcris_hom_ext l
    (f := Per.σB 1) (g := RingHom.id _) fun y => ?_) x
  simp only [GlobalTheory.CrisMaps.σB_sigA, sigA_one, RingHom.id_apply]

theorem σB_aB (g : Per.Gq l) (a : Per.Ainf l) : Per.σB g (Per.aB l a) = Per.aB l (Per.σA g a) := by
  rw [GlobalTheory.RingIface.aB_eq_alg, GlobalTheory.RingIface.aB_eq_alg, GlobalTheory.CrisMaps.σB_sigA, (GlobalTheory.CrisMaps.sigA_extends g).alg]

theorem φB_aB (a : Per.Ainf l) : Per.φB l (Per.aB l a) = Per.aB l (Per.φA l a) := by
  rw [GlobalTheory.RingIface.aB_eq_alg, GlobalTheory.RingIface.aB_eq_alg, GlobalTheory.CrisMaps.φB_phiA, (GlobalTheory.CrisMaps.phiA_extends l).alg]

theorem act_laws : ∀ (l : ℕ) [Fact l.Prime], (∀ (g h : Per.Gq l) (x : Per.Bcris l), Per.σB (g * h) x = Per.σB g (Per.σB h x)) ∧
    (∀ x : Per.Bcris l, Per.σB 1 x = x) ∧
    (∀ (g h : Per.Gq l) (x : Per.BdR l), Per.σD (g * h) x = Per.σD g (Per.σD h x)) ∧
    (∀ x : Per.BdR l, Per.σD 1 x = x) ∧
    (∀ (g : Per.Gq l) (x : Per.Bcris l), Per.φB l (Per.σB g x) = Per.σB g (Per.φB l x)) ∧
    (∀ (g : Per.Gq l) (a : Per.Ainf l), Per.σB g (Per.aB l a) = Per.aB l (Per.σA g a)) ∧
    (∀ a : Per.Ainf l, Per.φB l (Per.aB l a) = Per.aB l (Per.φA l a)) ∧
    (∀ (g : Per.Gq l) (z : ℤ_[l]), Per.σA g (Per.zA l z) = Per.zA l z) ∧
    (∀ z : ℤ_[l], Per.φA l (Per.zA l z) = Per.zA l z) ∧
    (∀ (g : Per.Gq l) (y : Per.BdRp l), Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) y) = algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g y)) ∧
    (∀ (g : Per.Gq l) (a : Per.Ainf l), Per.σDp g (aDp l a) = aDp l (Per.σA g a)) ∧
    (∀ (g : Per.Gq l) (x : Per.Acris l), Per.σB g (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.Acris l) (Per.Bcris l) (sigA g x)) ∧
    ∀ x : Per.Acris l, Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.Acris l) (Per.Bcris l) (phiA l x) :=
  fun l _ => ⟨σB_mul, σB_one, σD_mul, σD_one, φB_σB, σB_aB, φB_aB,
    fun g => endo_zA_pt (Per.σA g), endo_zA_pt (Per.φA l),
    σD_alg, σDp_aDp, GlobalTheory.CrisMaps.σB_sigA, GlobalTheory.CrisMaps.φB_phiA l⟩

end GlobalTheory.MemLoc.ActLaws
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusCommStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodRings_galoisAction_laws_frobenius_comm : ∀ (l : ℕ) [Fact l.Prime], (∀ (g h : Per.Gq l) (x : Per.Bcris l), Per.σB (g * h) x = Per.σB g (Per.σB h x)) ∧ (∀ x : Per.Bcris l, Per.σB 1 x = x) ∧ (∀ (g h : Per.Gq l) (x : Per.BdR l), Per.σD (g * h) x = Per.σD g (Per.σD h x)) ∧ (∀ x : Per.BdR l, Per.σD 1 x = x) ∧ (∀ (g : Per.Gq l) (x : Per.Bcris l), Per.φB l (Per.σB g x) = Per.σB g (Per.φB l x)) ∧ (∀ (g : Per.Gq l) (a : Per.Ainf l), Per.σB g (Per.aB l a) = Per.aB l (Per.σA g a)) ∧ (∀ a : Per.Ainf l, Per.φB l (Per.aB l a) = Per.aB l (Per.φA l a)) ∧ (∀ (g : Per.Gq l) (z : ℤ_[l]), Per.σA g (Per.zA l z) = Per.zA l z) ∧ (∀ z : ℤ_[l], Per.φA l (Per.zA l z) = Per.zA l z) ∧ (∀ (g : Per.Gq l) (y : Per.BdRp l), Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) y) = algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g y)) ∧ (∀ (g : Per.Gq l) (a : Per.Ainf l), Per.σDp g (aDp l a) = aDp l (Per.σA g a)) ∧ (∀ (g : Per.Gq l) (x : Per.Acris l), Per.σB g (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.Acris l) (Per.Bcris l) (sigA g x)) ∧ ∀ x : Per.Acris l, Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.Acris l) (Per.Bcris l) (phiA l x) := by
  first | exact @GlobalTheory.MemLoc.ActLaws.act_laws | exact GlobalTheory.MemLoc.ActLaws.act_laws | (intros; apply GlobalTheory.MemLoc.ActLaws.act_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMaxUnramifiedEmbeddingIntoBcris
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMaxUnramifiedEmbeddingIntoBcris
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem exists_factor_of_range {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* D) (ι : B →+* D)
    (hι : Function.Injective ι) (h : ∀ x, f x ∈ ι.range) : ∃ u : A →+* B, ∀ x, ι (u x) = f x := by
  let e : B ≃+* ι.range := RingEquiv.ofBijective ι.rangeRestrict
    ⟨fun a b hab => hι (congrArg Subtype.val hab), ι.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (f.codRestrict ι.range h), fun x => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply (f.codRestrict ι.range h x))

theorem padic_mem_range {l : ℕ} [Fact l.Prime] {B D : Type} [CommRing B] [CommRing D] (g : ℚ_[l] →+* D)
    (ι : B →+* D) (hz : ∀ z : ℤ_[l], g z ∈ ι.range) (hl : IsUnit (l : B)) (q : ℚ_[l]) : g q ∈ ι.range := by
  obtain ⟨w, hw⟩ := hl.exists_right_inv
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have h1 : g (l : ℚ_[l])⁻¹ = ι w := by
    have a : (l : D) * ι w = 1 := by simpa using congrArg ι hw
    have b : g (l : ℚ_[l])⁻¹ * (l : D) = 1 := by
      rw [← map_natCast g, ← map_mul, inv_mul_cancel₀ hl0, map_one]
    calc g (l : ℚ_[l])⁻¹ = g (l : ℚ_[l])⁻¹ * ((l : D) * ι w) := by rw [a, mul_one]
      _ = ι w := by rw [← mul_assoc, b, one_mul]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖(l : ℚ_[l]) ^ n * q‖ ≤ 1 := by
    have hp : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hp).mul_const ‖q‖
    rw [zero_mul] at ht
    obtain ⟨n, hn⟩ := (ht.eventually (ge_mem_nhds one_pos)).exists
    exact ⟨n, by rwa [norm_mul, norm_pow]⟩
  have e : q = ((l : ℚ_[l])⁻¹) ^ n * ((⟨_, hn⟩ : ℤ_[l]) : ℚ_[l]) := by
    change q = _ * ((l : ℚ_[l]) ^ n * q)
    rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hl0, one_pow, one_mul]
  rw [e, map_mul, map_pow, h1]
  exact mul_mem (pow_mem (ι.mem_range_self w) n) (hz _)

theorem exists_unram_to_cris : ∀ (l : ℕ) [Fact l.Prime], ∀ (o : Om l →+* Per.BdRp l) (ι : Per.Bcris l →+* Per.BdR l), IsSec o → Function.Injective ι → (∀ a : Per.Ainf l, ι (Per.aB l a) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a)) → IsUnit (l : Per.Bcris l) → ∃ u : ↥(MaximalUnramifiedExtension l) →+* Per.Bcris l, ∀ c : ↥(MaximalUnramifiedExtension l), ι (u c) = algebraMap (Per.BdRp l) (Per.BdR l) (o (c : Om l)) := by
  intro l _ o ι ho hι ha hl
  let f : Om l →+* Per.BdR l := (algebraMap (Per.BdRp l) (Per.BdR l)).comp o
  have hq : ∀ q : ℚ_[l], f (algebraMap ℚ_[l] (Om l) q) ∈ ι.range :=
    padic_mem_range (f.comp (algebraMap ℚ_[l] (Om l))) ι
      (fun z => ⟨Per.aB l (Per.zA l z), (ha _).trans (by
        rw [← ho.z]; rfl)⟩) hl
  let S : Subalgebra ℚ_[l] (Om l) :=
    { (ι.range.comap f).toSubsemiring with algebraMap_mem' := hq }
  have key : ∀ x ∈ MaximalUnramifiedExtension l, f x ∈ ι.range := by
    intro x hx
    unfold MaximalUnramifiedExtension at hx
    rw [← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      (fun y _ => Algebra.IsAlgebraic.isAlgebraic y)] at hx
    refine (Algebra.adjoin_le (S := S) ?_) hx
    rintro c ⟨m, h0, h1, h2⟩
    obtain ⟨⟨xb, hxb⟩, h⟩ := GlobalTheory.T.rootOfUnity_prime_to_teichmuller_lift l o ho c m h0 h1 h2
    refine ⟨Per.aB l (Per.tm xb), ?_⟩
    exact (ha _).trans (by rw [(h xb hxb).2.2]; rfl)
  exact exists_factor_of_range (f.comp (MaximalUnramifiedExtension l).val.toRingHom) ι hι (fun x => key x x.2)

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMaxUnramifiedEmbeddingIntoBcrisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maxUnramified_embedding_into_Bcris : ∀ (l : ℕ) [Fact l.Prime], ∀ (o : Om l →+* Per.BdRp l) (ι : Per.Bcris l →+* Per.BdR l), IsSec o → Function.Injective ι → (∀ a : Per.Ainf l, ι (Per.aB l a) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a)) → IsUnit (l : Per.Bcris l) → ∃ u : ↥(MaximalUnramifiedExtension l) →+* Per.Bcris l, ∀ c : ↥(MaximalUnramifiedExtension l), ι (u c) = algebraMap (Per.BdRp l) (Per.BdR l) (o (c : Om l)) := by
  first | exact @GlobalTheory.MemLoc.exists_unram_to_cris | exact GlobalTheory.MemLoc.exists_unram_to_cris | (intros; apply GlobalTheory.MemLoc.exists_unram_to_cris <;> assumption)
end
end

namespace GlobalTheory.MemLoc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem coreEx_alg_tower {l : ℕ} [Fact l.Prime] (a : Per.Ainf l) :
    algebraMap (Per.Ainf l) (Per.Acris l) a =
      algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) a) :=
  GlobalTheory.RingIface.tower l a

section
set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem coreEx_isUnit_l {l : ℕ} [Fact l.Prime] (e : Per.Fl l) (h1 : e.untilt = 1) (h2 : e ≠ 1)
    (w : Per.Acris0 l)
    (hw : (l : Per.AinfP l) * (w : Per.AinfP l) = algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ (l - 1)) :
    IsUnit (l : Per.Bcris l) := by
  have h0 : (l : Per.Acris0 l) * w = algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e) ^ (l - 1) :=
    Subtype.ext (by simpa using hw)
  have hu : IsUnit (algebraMap (Per.Acris l) (Per.Bcris l)
      (algebraMap (Per.Ainf l) (Per.Acris l) (mu e))) := by
    exact GlobalTheory.CrisLoc.unit_of_root l e h1 h2
  have h3 := congrArg ((algebraMap (Per.Acris l) (Per.Bcris l)).comp
    (algebraMap (Per.Acris0 l) (Per.Acris l))) h0
  rw [map_mul, map_natCast, map_pow] at h3
  have h4 : (algebraMap (Per.Acris l) (Per.Bcris l)).comp (algebraMap (Per.Acris0 l) (Per.Acris l))
      (algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e)) =
      algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Per.Ainf l) (Per.Acris l) (mu e)) := by
    rw [coreEx_alg_tower, RingHom.comp_apply]
  rw [h4] at h3
  exact isUnit_of_mul_isUnit_left (h3 ▸ hu.pow (l - 1))

theorem nonempty_core : ∀ (l : ℕ) [Fact l.Prime], Nonempty (Core l) := by
  intro l _
  obtain ⟨ζ, ε, z0, zs, z1, hr⟩ := GlobalTheory.T.exists_compatible_rootsOfUnity_and_tilt_padic l
  obtain ⟨o, ho⟩ := GlobalTheory.T.exists_isBdRPlusSectionOfTheta l
  obtain ⟨j, hj⟩ := GlobalTheory.T.exists_canonical_acris_to_bdRPlus l
  obtain ⟨ι, hι, hinj⟩ := GlobalTheory.T.exists_injective_bcris_to_bdR l j hj
  have h1 : ε.untilt = 1 := by
    have h := hr 0
    rw [z0, map_one] at h
    exact Subtype.ext h
  have h2 : ε ≠ 1 := by
    intro h
    have h' := hr 1
    rw [h] at h'
    simp only [rootT, Function.iterate_one, map_one] at h'
    apply z1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← h', map_one]
    rfl
  obtain ⟨w, hw, -⟩ := GlobalTheory.T.exists_teichmullerTiltMinusOne_pow_div_envelope l ε h1
  have hA : ∀ a : Per.Ainf l, ι (Per.aB l a) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a) := by
    intro a
    have h := hι (algebraMap (Per.Ainf l) (Per.Acris l) a)
    have h' : j (algebraMap (Per.Ainf l) (Per.Acris l) a) = aDp l a := by
      rw [coreEx_alg_tower, hj.on0]; rfl
    rw [h'] at h
    rw [GlobalTheory.RingIface.aB_apply]
    exact h
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_maxUnramified_embedding_into_Bcris l o ι ho hinj hA (coreEx_isUnit_l ε h1 h2 w hw)
  obtain ⟨t, -, ht, -⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l ε h1
  obtain ⟨σ, hσ⟩ := exists_frobenius_Kur l
  obtain ⟨χ, hχ⟩ := exists_cyclotomicChar l
  exact ⟨⟨ζ, z0, zs, z1, ε, hr, o, ho, j, hj, ι, hι, u, hu, t, ht, σ, hσ, χ, hχ⟩⟩

end

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusFontaineTEqMul
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusFontaineTEqMul
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.TPhi

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem untilt_pow_eq_one (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (he : e.untilt = 1) (n : ℕ) :
    (e ^ n).untilt = 1 := by
  rw [map_pow, he, one_pow]

theorem log_pow (l : ℕ) [Fact l.Prime] (j : Per.Acris l →+* Per.BdRp l) (hj : IsCrisP j)
    (e : Per.Fl l) (he : e.untilt = 1) (x : Per.BdRp l) (hx : Per.IsLog l e x) (n : ℕ) :
    ∀ y : Per.BdRp l, Per.IsLog l (e ^ n) y → y = (n : Per.BdRp l) * x := by
  induction n with
  | zero =>
    intro y hy
    have h0 := untilt_pow_eq_one l e he 0
    have h := LogAdd.log_add l (e ^ 0) (e ^ 0) y y y h0 h0 hy hy (by rwa [← pow_add])
    rw [Nat.cast_zero, zero_mul]
    exact left_eq_add.mp h
  | succ n ih =>
    intro y hy
    have hn := untilt_pow_eq_one l e he n
    obtain ⟨s, _, hs, -, -⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l (e ^ n) hn
    have hs' := (GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l (e ^ n) s hn hs).2.2.2 j hj
    have h := LogAdd.log_add l (e ^ n) e (j s) x y hn he hs' hx (by rwa [← pow_succ])
    rw [h, ih _ hs', Nat.cast_succ, add_mul, one_mul]

theorem t_phi : ∀ (l : ℕ) [Fact l.Prime], ∀ C : Core l,
    phiA l C.t = (l : Per.Acris l) * C.t := by
  intro l _ C
  have he : C.ε.untilt = 1 := (core_isEps l C).1
  obtain ⟨-, -, h3, h4⟩ := GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l C.ε C.t he C.t_log
  have h5 := (GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l (C.ε ^ l) _ (untilt_pow_eq_one l _ he l) h3).2.2.2 C.j C.j_cris
  apply GlobalTheory.T.acrisToBdRPlus_injective l C.j C.j_cris
  rw [map_mul, map_natCast]
  exact log_pow l C.j C.j_cris C.ε he _ (h4 C.j C.j_cris) l _ h5

end GlobalTheory.MemLoc.TPhi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusFontaineTEqMulStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acrisFrobenius_fontaine_t_eq_mul : ∀ (l : ℕ) [Fact l.Prime], ∀ C : Core l, phiA l C.t = (l : Per.Acris l) * C.t := by
  first | exact @GlobalTheory.MemLoc.TPhi.t_phi | exact GlobalTheory.MemLoc.TPhi.t_phi | (intros; apply GlobalTheory.MemLoc.TPhi.t_phi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisGaloisActionFontaineTEqCyclotomic
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisGaloisActionFontaineTEqCyclotomic
noncomputable section
namespace GlobalTheory.MemLoc.TAct
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

variable {l : ℕ} [Fact l.Prime]

theorem logA_mul {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) {e e' : Per.Fl l} {y y' : Per.Acris l}
    (he : e.untilt = 1) (he' : e'.untilt = 1) (hy : IsLogA e y) (hy' : IsLogA e' y') :
    IsLogA (e * e') (y + y') := by
  have hee : (e * e').untilt = 1 := by rw [map_mul, he, he', one_mul]
  obtain ⟨z, _, hz, -, -⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l (e * e') hee
  have h := GlobalTheory.MemLoc.LogAdd.log_add l e e' (j y) (j y') (j z) he he'
    ((GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l e y he hy).2.2.2 j hj) ((GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l e' y' he' hy').2.2.2 j hj)
    ((GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l _ z hee hz).2.2.2 j hj)
  rw [← map_add (f := _)] at h
  rw [← GlobalTheory.T.acrisToBdRPlus_injective l j hj h]
  exact hz

theorem logA_pow {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) {e : Per.Fl l} {y : Per.Acris l}
    (he : e.untilt = 1) (hy : IsLogA e y) (n : ℕ) : IsLogA (e ^ n) ((n : Per.Acris l) * y) := by
  induction n with
  | zero =>
    have h1 : (1 : Per.Fl l).untilt = 1 := map_one _
    obtain ⟨z, _, hz, -, -⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l 1 h1
    have h2 := logA_mul hj h1 h1 hz hz
    rw [one_mul] at h2
    have h3 := (GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l 1 z h1 hz).1 _ h2
    have h4 : z = 0 := by simpa using h3
    rw [pow_zero, Nat.cast_zero, zero_mul, ← h4]
    exact hz
  | succ n ih =>
    have := logA_mul hj (by rw [map_pow, he, one_pow]) he ih hy
    rw [pow_succ, Nat.cast_succ, add_mul, one_mul]
    exact this

theorem iter_pow (e : Per.Fl l) (m : ℕ) :
    (((frobeniusEquiv (Per.Fl l) l).symm)^[m] e) ^ (l ^ m) = e := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', pow_succ', pow_mul]
    have : ∀ x : Per.Fl l, ((frobeniusEquiv (Per.Fl l) l).symm x) ^ l = x := fun x => by
      rw [← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
    rw [this, ih]

theorem eps_untilt (C : Core l) : C.ε.untilt = 1 := by
  have h := C.ε_root 0
  rw [C.ζ_zero, map_one] at h
  exact Subtype.ext h

theorem zeta_pow (C : Core l) (m : ℕ) : C.ζ m ^ (l ^ m) = 1 := by
  induction m with
  | zero => simp [C.ζ_zero]
  | succ m ih => rw [pow_succ', pow_mul, C.ζ_succ, ih]

theorem cong (C : Core l) (g : GQ l) (m : ℕ) : ∃ w : Per.Acris l,
    sigA g C.t - ((PadicInt.toZModPow m (C.χ g : ℤ_[l])).val : Per.Acris l) * C.t = (l : Per.Acris l) ^ m * w := by
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  set a := (PadicInt.toZModPow m (C.χ g : ℤ_[l])).val with ha
  obtain ⟨b, hb⟩ : ∃ b, a + b = l ^ m := Nat.exists_eq_add_of_le (ZMod.val_lt _).le |>.imp fun _ h => h.symm
  set em := ((frobeniusEquiv (Per.Fl l) l).symm)^[m] C.ε with hem
  have hε := eps_untilt C
  have hr : ((em.untilt : Per.OC l) : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (C.ζ m) := C.ε_root m
  have he : (Per.σF g em * em ^ b).untilt = 1 := by
    rw [map_mul, map_pow, GlobalTheory.RingBasics.untilt_σF]
    apply Subtype.ext
    have h1 : ((Per.σO g em.untilt : Per.OC l) : ℂ_[l]) = Per.σC g (em.untilt : ℂ_[l]) :=
      GlobalTheory.RingIface.sigO_coe l g _
    have h2 : Per.σC g (algebraMap (Om l) ℂ_[l] (C.ζ m)) = algebraMap (Om l) ℂ_[l] (g (C.ζ m)) :=
      GlobalTheory.RingBasics.σC_coe g _
    push_cast
    rw [h1, hr, h2, C.χ_cyc g m _ (zeta_pow C m), ← ha, ← map_pow, ← map_mul, ← pow_add, hb, zeta_pow, map_one]
  obtain ⟨z, _, hz, -, -⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l _ he
  have h1 := logA_pow C.j_cris he hz (l ^ m)
  have hgε : (Per.σF g C.ε).untilt = 1 := by rw [GlobalTheory.RingBasics.untilt_σF, hε, map_one]
  have h2 := logA_mul C.j_cris hgε (by rw [map_pow, hε, one_pow])
    ((GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l _ _ hε C.t_log).2.1 g) (logA_pow C.j_cris hε C.t_log b)
  have h3 : (Per.σF g em * em ^ b) ^ (l ^ m) = Per.σF g C.ε * C.ε ^ b := by
    rw [mul_pow, ← map_pow, ← pow_mul, mul_comm b, pow_mul, hem, iter_pow]
  rw [h3] at h1
  have h4 := (GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l _ _ (by rw [map_mul, hgε, map_pow, hε, one_pow, one_mul]) h1).1 _ h2
  refine ⟨z - C.t, ?_⟩
  have h5 : (a : Per.Acris l) + b = (l : Per.Acris l) ^ m := by exact_mod_cast congrArg (Nat.cast : ℕ → Per.Acris l) hb
  push_cast at h4
  linear_combination h4 - C.t * h5

theorem t_act : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (g : GQ l),
    sigA g C.t = algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l (C.χ g : ℤ_[l])) * C.t := by
  intro l _ C g
  haveI := (acris_basic l).1
  rw [IsHausdorff.eq_iff_smodEq (I := Ideal.span {(l : Per.Acris l)})]
  intro m
  obtain ⟨w, hw⟩ := cong C g m
  set x : ℤ_[l] := (C.χ g : ℤ_[l])
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hk : x - ((PadicInt.toZModPow m x).val : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow m : ℤ_[l] →+* ZMod (l ^ m)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at hk
  obtain ⟨c, hc⟩ := hk
  have hc' := congrArg ((algebraMap (Per.Ainf l) (Per.Acris l)).comp (Per.zA l)) hc
  rw [map_mul, map_sub, map_pow, map_natCast, map_natCast, RingHom.comp_apply, RingHom.comp_apply] at hc'
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  refine ⟨w - algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l c) * C.t, ?_⟩
  linear_combination - hw - C.t * hc'

end GlobalTheory.MemLoc.TAct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisGaloisActionFontaineTEqCyclotomicStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acrisGaloisAction_fontaine_t_eq_cyclotomic : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (g : GQ l), sigA g C.t = algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l (C.χ g : ℤ_[l])) * C.t := by
  first | exact @GlobalTheory.MemLoc.TAct.t_act | exact GlobalTheory.MemLoc.TAct.t_act | (intros; apply GlobalTheory.MemLoc.TAct.t_act <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryLatticeStabilizerDetRoot
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsIntegralDetOfIsIntegral
open Polynomial in
private theorem UpperTheory.Reformulated.B.Ybf4.isIntegral_det_of_isIntegral {R E : Type} [CommRing R] [Field E]
    [Algebra R E] {N : ℕ} (γ : Matrix (Fin N) (Fin N) E) (h : IsIntegral R γ) :
    IsIntegral R γ.det := by
  let K := AlgebraicClosure E
  let φ : Matrix (Fin N) (Fin N) E →ₐ[R] Matrix (Fin N) (Fin N) K :=
    (IsScalarTower.toAlgHom R E K).mapMatrix
  have hφ : IsIntegral R (φ γ) := h.map φ
  have hdet : algebraMap E K γ.det = (φ γ).det := RingHom.map_det (algebraMap E K) γ
  rw [← isIntegral_algebraMap_iff (B := K) , hdet,
    Matrix.det_eq_prod_roots_charpoly]
  refine IsIntegral.multiset_prod fun μ hμ => ?_
  have hspec : μ ∈ spectrum K (φ γ) :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.2 (isRoot_of_mem_roots hμ)
  obtain ⟨p, hp, hp0⟩ := hφ
  refine ⟨p, hp, ?_⟩
  have h1 := spectrum.subset_polynomial_aeval (φ γ) (p.map (algebraMap R K)) ⟨μ, hspec, rfl⟩
  rw [aeval_map_algebraMap, aeval_def, hp0] at h1
  simp only [eval_map] at h1
  by_contra hne
  apply h1
  rw [spectrum.mem_resolventSet_iff, sub_zero]
  exact (IsUnit.mk0 _ hne).map _

open Polynomial in
theorem UpperTheory.Reformulated.B.Ybf4.isIntegral_det :
    ∀ {E : Type} [inst : Field E] [NumberField E] {N : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin N → E)),
      L.FG →
        Submodule.span E (↑L : Set (Fin N → E)) = ⊤ →
          ∀ (γ : Matrix (Fin N) (Fin N) E), (∀ v ∈ L, γ.mulVec v ∈ L) → IsIntegral ℤ γ.det := by
  intro E _ _ N L hfg hspan γ hγ
  refine isIntegral_trans (A := NumberField.RingOfIntegers E) _
    (UpperTheory.Reformulated.B.Ybf4.isIntegral_det_of_isIntegral γ ?_)
  haveI : Module.Finite (NumberField.RingOfIntegers E) L := Module.Finite.iff_fg.2 hfg
  let g : (Fin N → E) →ₗ[NumberField.RingOfIntegers E] (Fin N → E) :=
    (Matrix.mulVecLin γ).restrictScalars _
  let f : Module.End (NumberField.RingOfIntegers E) L := g.restrict (p := L) (q := L) hγ
  obtain ⟨p, hp, hp0⟩ := LinearMap.exists_monic_and_aeval_eq_zero (NumberField.RingOfIntegers E) f
  refine ⟨p, hp, ?_⟩
  have hpow : ∀ (n : ℕ) (v : L), ((f ^ n) v : Fin N → E) = (γ ^ n).mulVec v := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, pow_succ, Module.End.mul_apply, ih, ← Matrix.mulVec_mulVec]
      rfl
  have key : ∀ (q : (NumberField.RingOfIntegers E)[X]) (v : L),
      ((aeval f q) v : Fin N → E) = (aeval γ q).mulVec v := by
    intro q v
    induction q using Polynomial.induction_on' with
    | add a b ha hb => simp [ha, hb, Matrix.add_mulVec]
    | monomial n a =>
      rw [aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def,
        LinearMap.smul_apply, Submodule.coe_smul, hpow]
      ext i
      change a • (∑ j, (γ ^ n) i j * (v : Fin N → E) j) = ∑ j, (a • (γ ^ n) i j) * (v : Fin N → E) j
      simp only [Algebra.smul_def, mul_assoc, Finset.mul_sum]
  have hz : Matrix.mulVecLin (aeval γ p) = 0 := by
    refine LinearMap.ext_on hspan fun v hv => ?_
    have := key p ⟨v, hv⟩
    rw [hp0] at this
    simpa using this.symm
  rw [← aeval_def]
  apply Matrix.toLin'.injective
  rw [map_zero]
  exact hz
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.L2.DIV

namespace GlobalTheory.Mem.StabDet

theorem isIntegral_det {E : Type} [Field E] [NumberField E] {N : ℕ} (L : Submodule (𝓞 E) (Fin N → E))
    (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin N → E)) = ⊤) (γ : Matrix (Fin N) (Fin N) E)
    (hγ : ∀ v ∈ L, γ.mulVec v ∈ L) : IsIntegral ℤ γ.det :=
  _root_.UpperTheory.Reformulated.B.Ybf4.isIntegral_det L hfg hsp γ hγ

theorem eq_pm_one_of_unitary {R : Ranks} (H : Formalism.BasicNotions.Host R) :
    letI := H.cmStar; ∀ z : H.E, z ∈ unitary H.E → IsIntegral ℤ z → ∃ m : ℕ, 0 < m ∧ z ^ m = 1 := by
  letI := H.cmStar
  intro z hu hz
  have := H.isCMField_hostE
  obtain ⟨n, hn, hp⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one H.E ℂ hz (fun φ => by
    have h1 : star z * z = 1 := hu.1
    have h2 : φ (star z) = starRingEnd ℂ (φ z) := IsCMField.complexEmbedding_complexConj H.E φ z
    have h3 := congrArg φ h1
    rw [map_mul, h2, map_one, Complex.conj_mul'] at h3
    have h4 : ‖φ z‖ ^ 2 = 1 := by exact_mod_cast h3
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4)
  exact ⟨n, hn, hp⟩

end GlobalTheory.Mem.StabDet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTiltRootOfUnity
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem exists_tilt_root_of_unity : ∀ (l : ℕ) [Fact l.Prime] (x : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → x ^ m = 1 → ∃ e : Per.Fl l, e ^ m = 1 ∧ (e.untilt : ℂ_[l]) = (x : ℂ_[l]) := by
  intro l hl x m hm hlm hx
  obtain ⟨h1, h2, h3⟩ := tilt_facts l
  have hxC : (x : ℂ_[l]) ^ m = 1 := by
    have := congrArg (algebraMap (Om l) ℂ_[l]) hx
    rw [map_pow, map_one] at this
    exact this
  have hn : ‖(x : ℂ_[l])‖ ≤ 1 := by
    have h := congrArg norm hxC
    rw [norm_pow, norm_one] at h
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 h).le
  obtain ⟨y, hyx⟩ : ∃ y : Per.OC l, (y : ℂ_[l]) = (x : ℂ_[l]) := ⟨⟨_, (GlobalTheory.RingBasics.mem_OC _).2 hn⟩, rfl⟩
  have hy : y ^ m = 1 := Subtype.ext (by push_cast; rw [hyx, hxC])
  have hc : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl.out).2 hlm
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a * l ≡ 1 [MOD m] := by
    refine ⟨l ^ (m.totient - 1), ?_⟩
    rw [← pow_succ, Nat.sub_add_cancel (Nat.totient_pos.2 hm)]
    exact Nat.ModEq.pow_totient hc
  have hstep : ∀ z : Per.OC l, z ^ m = 1 → (z ^ a) ^ l = z := fun z hz => by
    rw [← pow_mul]
    simpa using pow_eq_pow_of_modEq ha hz
  have hpm : ∀ n : ℕ, (y ^ a ^ n) ^ m = 1 := fun n => by
    rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]
  obtain ⟨e, he⟩ := h1 (fun n => y ^ a ^ n) (fun n => by
    show (y ^ a ^ (n + 1)) ^ l = y ^ a ^ n
    rw [pow_succ, pow_mul]
    exact hstep _ (hpm n))
  refine ⟨e, h2 _ fun n => by rw [h3, he, hpm], ?_⟩
  have h0 := he 0
  rw [pow_zero, pow_one] at h0
  rw [← hyx, ← h0]
  rfl

end GlobalTheory.MemLoc
end
