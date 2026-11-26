module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineTIsUnitBcrisAndUniformizerBdRPlus
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarUpqHasOmegaDensity
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfTateTwistInvariantFiniteExtension
public import Formalism.LocalToGlobal.LocalInduction.BridgeInd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalPeriodRingsDataUnramifiedLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalPeriodRingsDataUnramifiedLaws
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.ULaws

variable {l : ℕ} [Fact l.Prime]

theorem alg_acris (a : Per.Ainf l) : algebraMap (Per.Ainf l) (Per.Acris l) a =
    algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) a) :=
  GlobalTheory.RingIface.tower l a

theorem ringHom_ext_Kur {R : Type} [CommRing R] (f g : ↥(MaximalUnramifiedExtension l) →+* R)
    (hz : ∀ z : ℤ_[l], f (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])) =
      g (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])))
    (hr : ∀ (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → f c = g c) (c : ↥(MaximalUnramifiedExtension l)) :
    f c = g c := by
  have hq : f.comp (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) = g.comp (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) :=
    IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) (RingHom.ext hz)
  obtain ⟨x, hx⟩ := c
  unfold MaximalUnramifiedExtension at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, hm, hlm, hxm⟩ := hx
    exact hr _ m hm hlm (Subtype.ext hxm)
  | algebraMap q => exact RingHom.congr_fun hq q
  | add x y hx hy a b =>
    exact (map_add f ⟨x, hx⟩ ⟨y, hy⟩).trans ((congrArg₂ (· + ·) a b).trans (map_add g ⟨x, hx⟩ ⟨y, hy⟩).symm)
  | inv x hx a => exact eq_on_inv₀ f g (a := ⟨x, hx⟩) a
  | mul x y hx hy a b =>
    exact (map_mul f ⟨x, hx⟩ ⟨y, hy⟩).trans ((congrArg₂ (· * ·) a b).trans (map_mul g ⟨x, hx⟩ ⟨y, hy⟩).symm)

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem iota_injective (C : Core l) : Function.Injective C.ι := by
  obtain ⟨ι, h1, h2⟩ := GlobalTheory.T.exists_injective_bcris_to_bdR l C.j C.j_cris
  have e : C.ι = ι := GlobalTheory.RingIface.bcris_ext l fun x => (C.ι_j x).trans (h1 x).symm
  rw [e]
  exact h2

theorem iota_aB (C : Core l) (a : Per.Ainf l) :
    C.ι (Per.aB l a) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a) := by
  have e : Per.aB l a = algebraMap (Per.Acris l) (Per.Bcris l)
      (algebraMap (Per.Ainf l) (Per.Acris l) a) := GlobalTheory.RingIface.aB_eq_alg l a
  rw [e, C.ι_j, alg_acris, C.j_cris.on0, Subalgebra.coe_algebraMap, aDp, RingHom.comp_apply]

theorem iota_sigma (C : Core l) (g : GQ l) (b : Per.Bcris l) :
    C.ι (Per.σB g b) = Per.σD g (C.ι b) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hD, -, hB, -⟩ := ActLaws.act_laws l
  have e : C.ι.comp (Per.σB g) = (Per.σD g).comp C.ι := by
    refine GlobalTheory.RingIface.bcris_ext l fun x => ?_
    simp only [RingHom.comp_apply]
    rw [hB, C.ι_j, C.ι_j, hD, (GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx l C.j C.j_cris).2.1]
  exact RingHom.congr_fun e b

theorem iota_isCrisDR (C : Core l) : Per.IsCrisDR l C.ι := by
  obtain ⟨ι, hι⟩ := GlobalTheory.CrisIncl.exists_incl l
  obtain ⟨j, h1, h2, h3⟩ := GlobalTheory.CrisIncl.exists_restrict l ι hι
  have e : j = C.j := (GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx l C.j C.j_cris).1 j ⟨h2, h3⟩
  have e' : C.ι = ι := GlobalTheory.RingIface.bcris_ext l fun x => by rw [C.ι_j, h1, e]
  rwa [e']

theorem u_padicInt (C : Core l) (z : ℤ_[l]) :
    C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])) = Per.zB l z := by
  apply iota_injective C
  have e : Per.zB l z = Per.aB l (Per.zA l z) := GlobalTheory.RingIface.zB_eq_aB_zA l z
  rw [e, iota_aB, C.ι_u, ← C.o_sec.z]
  rfl

theorem sigma_u (C : Core l) (g : GQ l) (c c' : ↥(MaximalUnramifiedExtension l)) (h : g (c : Om l) = (c' : Om l)) :
    Per.σB g (C.u c) = C.u c' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hD, -⟩ := ActLaws.act_laws l
  apply iota_injective C
  rw [iota_sigma, C.ι_u, C.ι_u, hD, (GlobalTheory.T.bdRPlus_simple_roots_section_unique_equivariant l C.o C.o_sec).2.2, h]

theorem phi_u (C : Core l) (c : ↥(MaximalUnramifiedExtension l)) : Per.φB l (C.u c) = C.u (C.σ c) := by
  obtain ⟨-, -, -, -, -, -, hφ, -, hz, -⟩ := ActLaws.act_laws l
  refine ringHom_ext_Kur ((Per.φB l).comp C.u) (C.u.comp (C.σ : ↥(MaximalUnramifiedExtension l) →+* ↥(MaximalUnramifiedExtension l)))
    (fun z => ?_) (fun c m hm hlm hc => ?_) c
  · have e : Per.zB l z = Per.aB l (Per.zA l z) := GlobalTheory.RingIface.zB_eq_aB_zA l z
    simp only [RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes]
    rw [u_padicInt, e, hφ, hz]
  · obtain ⟨⟨xb, hxb⟩, h2⟩ := GlobalTheory.T.rootOfUnity_prime_to_teichmuller_lift l C.o C.o_sec (c : Om l) m hm hlm
      (congrArg Subtype.val hc)
    have hu : C.u c = Per.aB l (Per.tm xb) := by
      apply iota_injective C
      rw [iota_aB, C.ι_u, (h2 xb hxb).2.2]
    have h1 : Per.φA l (Per.tm xb) = Per.tm xb ^ l := by
      rw [GlobalTheory.RingBasics.φA_apply, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller,
        frobenius_def, map_pow]
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    rw [C.σ_root c m hm hlm hc, map_pow, hu, hφ, h1, map_pow]

theorem u_laws (l : ℕ) [Fact l.Prime] (C : Core l) :
    (∀ c : ↥(MaximalUnramifiedExtension l), Per.φB l (C.u c) = C.u (C.σ c)) ∧
    (∀ (g : GQ l) (c c' : ↥(MaximalUnramifiedExtension l)), g (c : Om l) = (c' : Om l) → Per.σB g (C.u c) = C.u c') ∧
    (∀ z : ℤ_[l], C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])) = Per.zB l z) ∧
    Function.Injective C.ι ∧
    (∀ (g : GQ l) (b : Per.Bcris l), C.ι (Per.σB g b) = Per.σD g (C.ι b)) ∧
    Per.IsCrisDR l C.ι :=
  ⟨phi_u C, sigma_u C, u_padicInt C, iota_injective C, iota_sigma C, iota_isCrisDR C⟩

end GlobalTheory.MemLoc.ULaws
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalPeriodRingsDataUnramifiedLawsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localPeriodRingsData_unramified_laws : ∀ (l : ℕ) [Fact l.Prime], ∀ C : Core l, (∀ c : ↥(MaximalUnramifiedExtension l), Per.φB l (C.u c) = C.u (C.σ c)) ∧ (∀ (g : GQ l) (c c' : ↥(MaximalUnramifiedExtension l)), g (c : Om l) = (c' : Om l) → Per.σB g (C.u c) = C.u c') ∧ (∀ z : ℤ_[l], C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])) = Per.zB l z) ∧ Function.Injective C.ι ∧ (∀ (g : GQ l) (b : Per.Bcris l), C.ι (Per.σB g b) = Per.σD g (C.ι b)) ∧ Per.IsCrisDR l C.ι := by
  first | exact @GlobalTheory.MemLoc.ULaws.u_laws | exact GlobalTheory.MemLoc.ULaws.u_laws | (intros; apply GlobalTheory.MemLoc.ULaws.u_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyEqOfEqOnDense
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyEqOfEqOnDense
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory

theorem charpoly_eq_of_eqOn_dense : ∀ {X A : Type} [TopologicalSpace X] [Field A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] [Infinite A] {n : ℕ} (M N : X → Matrix (Fin n) (Fin n) A), Continuous M → Continuous N → ∀ U : Set X, Dense U → (∀ x ∈ U, (M x).charpoly = (N x).charpoly) → ∀ x, (M x).charpoly = (N x).charpoly := by
  intro X A _ _ _ _ _ _ n M N hM hN U hU hEq x
  apply Polynomial.funext
  intro c
  have hcM : Continuous fun y => (M y).charpoly.eval c := by
    simp_rw [Matrix.eval_charpoly]
    exact (continuous_const.sub hM).matrix_det
  have hcN : Continuous fun y => (N y).charpoly.eval c := by
    simp_rw [Matrix.eval_charpoly]
    exact (continuous_const.sub hN).matrix_det
  have h : (fun y => (M y).charpoly.eval c) = fun y => (N y).charpoly.eval c :=
    Continuous.ext_on hU hcM hcN (fun y hy => by simp only [hEq y hy])
  exact congrFun h x

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyEqOfEqOnDenseStatement
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_eq_of_continuous_of_eq_on_dense : ∀ {X A : Type} [TopologicalSpace X] [Field A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] [Infinite A] {n : ℕ} (M N : X → Matrix (Fin n) (Fin n) A), Continuous M → Continuous N → ∀ U : Set X, Dense U → (∀ x ∈ U, (M x).charpoly = (N x).charpoly) → ∀ x, (M x).charpoly = (N x).charpoly := by
  first | exact @GlobalTheory.charpoly_eq_of_eqOn_dense | exact GlobalTheory.charpoly_eq_of_eqOn_dense | (intros; apply GlobalTheory.charpoly_eq_of_eqOn_dense <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG

namespace GlobalTheory.Mem.Col2

def FunKilled {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (π : 𝓞 E) : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    (t t' : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))),
    t'.1 = inclE (F := F) (v.adicCompletion F) (π : E) • t.1 → S.fT v hv t' = 0

end GlobalTheory.Mem.Col2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelLocalGroupEqOfAgreeOffPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelLocalGroupEqOfAgreeOffPlaces
noncomputable section

namespace GlobalTheory

open NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ}

theorem stepLevel_uloc_le_of_agree {bad bad' : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (S' : StepLevel F E σ J T f bad') (Q : Set (HeightOneSpectrum (𝓞 F)))
    (hQ : ∀ x, (∀ v ∈ Q, bc (prV (E := E) v) x = 1) → x ∈ S.U → x ∈ S'.U)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ Q) : S.Uloc v ≤ S'.Uloc v := by
  intro h hh
  have hx1 : bc (prV (E := E) v) (Formalism.UG.P.afsplitU v h 1) = h := Formalism.UG.P.afsplit_right1 v h 1
  have hxw : ∀ w, w ≠ v → bc (prV (E := E) w) (Formalism.UG.P.afsplitU v h 1) = 1 := by
    intro w hw
    apply Units.ext
    rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw,
      Units.val_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hxU : Formalism.UG.P.afsplitU v h 1 ∈ S.U := by
    rw [S.U_eq]
    refine ⟨Formalism.UG.P.afsplitU_mem v σ J h 1 (S.Uloc_le v hh) (one_mem _), fun w => ?_⟩
    by_cases hw : w = v
    · rw [hw, hx1]; exact hh
    · rw [hxw w hw]; exact one_mem _
  have hxQ : ∀ w ∈ Q, bc (prV (E := E) w) (Formalism.UG.P.afsplitU v h 1) = 1 :=
    fun w hw => hxw w (fun he => hv (he ▸ hw))
  have h2 := ((S'.U_eq _).mp (hQ _ hxQ hxU)).2 v
  rwa [hx1] at h2

end

theorem stepLevel_uloc_eq_of_agree : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad bad' : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (S' : StepLevel F E σ J T f bad') (Q : Set (HeightOneSpectrum (𝓞 F))),
    (∀ x, (∀ v ∈ Q, bc (prV (E := E) v) x = 1) → (x ∈ S.U ↔ x ∈ S'.U)) → ∀ v, v ∉ Q → S.Uloc v = S'.Uloc v := by
  intro F E _ _ _ _ _ σ n J T f bad bad' S S' Q hQ v hv
  exact le_antisymm (stepLevel_uloc_le_of_agree S S' Q (fun x hx => (hQ x hx).mp) v hv)
    (stepLevel_uloc_le_of_agree S' S Q (fun x hx => (hQ x hx).mpr) v hv)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelLocalGroupEqOfAgreeOffPlacesStatement
open NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepLevel_localGroup_eq_of_agree_off_places : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad bad' : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (S' : StepLevel F E σ J T f bad') (Q : Set (HeightOneSpectrum (𝓞 F))), (∀ x, (∀ v ∈ Q, bc (prV (E := E) v) x = 1) → (x ∈ S.U ↔ x ∈ S'.U)) → ∀ v, v ∉ Q → S.Uloc v = S'.Uloc v := by
  first | exact @GlobalTheory.stepLevel_uloc_eq_of_agree | exact GlobalTheory.stepLevel_uloc_eq_of_agree | (intros; apply GlobalTheory.stepLevel_uloc_eq_of_agree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRGaloisInvariantsEqFinExt
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRGaloisInvariantsEqFinExt
namespace GlobalTheory.MemLoc.InvDR
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

section Abstract
variable {R F G : Type} [CommRing R] [IsDomain R] [Field F]

theorem inv_ker_eq_zero (θ : R →+* F) (σ : G → R →+* R) (τ : G → F →+* F) (c : G → R) (t : R) (ht : t ≠ 0)
    (hker : ∀ y, θ y = 0 → t ∣ y) (hsep : ∀ y, (∀ n : ℕ, t ^ n ∣ y) → y = 0)
    (hθ : ∀ g y, θ (σ g y) = τ g (θ y)) (hσt : ∀ g, σ g t = c g * t)
    (tate : ∀ (i : ℤ) (x : F), i ≠ 0 → (∀ g, τ g x * θ (c g) ^ i = x) → x = 0)
    (z : R) (hz : θ z = 0) (hinv : ∀ g, σ g z = z) : z = 0 := by
  have key : ∀ m : ℕ, t ^ (m + 1) ∣ z := by
    intro m
    induction m with
    | zero => simpa using hker z hz
    | succ m ih =>
      obtain ⟨w, hw⟩ := ih
      have h1 : ∀ g, σ g w * c g ^ (m + 1) = w := by
        intro g
        have h := hinv g
        rw [hw, map_mul, map_pow, hσt] at h
        apply mul_left_cancel₀ (pow_ne_zero (m + 1) ht)
        rw [← h]
        ring
      have h2 : θ w = 0 := by
        refine tate ((m + 1 : ℕ) : ℤ) _ (by omega) fun g => ?_
        rw [zpow_natCast, ← hθ, ← map_pow, ← map_mul, h1]
      obtain ⟨v, hv⟩ := hker w h2
      exact ⟨v, by rw [hw, hv]; ring⟩
  exact hsep z fun n => (pow_dvd_pow t (Nat.le_succ n)).trans (key n)

theorem eigen_eq (θ : R →+* F) (σ : G → R →+* R) (τ : G → F →+* F) (c : G → R) (t : R) (ht : t ≠ 0)
    (hker : ∀ y, θ y = 0 → t ∣ y) (hc : ∀ g, θ (c g) ≠ 0)
    (hθ : ∀ g y, θ (σ g y) = τ g (θ y)) (hσt : ∀ g, σ g t = c g * t)
    (tate : ∀ (i : ℤ) (x : F), i ≠ 0 → (∀ g, τ g x * θ (c g) ^ i = x) → x = 0)
    (n : ℕ) : ∀ y : R, (∀ g, σ g y = c g ^ n * y) → ∃ w, y = t ^ n * w ∧ ∀ g, σ g w = w := by
  induction n with
  | zero => intro y hy; exact ⟨y, by simp, fun g => by simpa using hy g⟩
  | succ n ih =>
    intro y hy
    have h2 : θ y = 0 := by
      refine tate (-((n + 1 : ℕ) : ℤ)) _ (by omega) fun g => ?_
      rw [zpow_neg, zpow_natCast, ← hθ, hy, map_mul, map_pow]
      have := pow_ne_zero (n + 1) (hc g)
      field_simp
    obtain ⟨v, hv⟩ := hker y h2
    obtain ⟨w, hw, hw'⟩ := ih v fun g => by
      have h := hy g
      rw [hv, map_mul, hσt] at h
      have hc0 : c g ≠ 0 := fun h0 => hc g (by rw [h0, map_zero])
      apply mul_left_cancel₀ (mul_ne_zero hc0 ht)
      rw [h]
      ring
    exact ⟨w, by rw [hv, hw]; ring, hw'⟩

end Abstract

variable {l : ℕ} [Fact l.Prime]

theorem j_alg (C : Core l) (a : Per.Ainf l) :
    C.j (algebraMap (Per.Ainf l) (Per.Acris l) a) = aDp l a := by
  rw [GlobalTheory.RingIface.tower, C.j_cris.on0, aDp, RingHom.comp_apply, SubalgebraClass.coe_algebraMap]

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem invariants_BdR (l : ℕ) [Fact l.Prime] (C : Core l) (K : FinExt l) (b : Per.BdR l)
    (hb : ∀ g ∈ GK K, Per.σD g b = b) :
    ∃ y ∈ K.1, algebraMap (Per.BdRp l) (Per.BdR l) (C.o y) = b := by
  have he := GlobalTheory.MemLoc.core_isEps l C
  obtain ⟨hdom, hinj, -, hfrac⟩ := GlobalTheory.T.bdRPlus_isDomain_bdR_isField l
  obtain ⟨hfil, hreg, hcompl, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l C.ε he
  obtain ⟨-, hker, hunit, -, hθ⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
  obtain ⟨-, ht1, ht2, -⟩ := GlobalTheory.T.fontaine_t_isUnit_bcris_and_uniformizer_bdRPlus l C
  obtain ⟨-, -, hoσ⟩ := GlobalTheory.T.bdRPlus_simple_roots_section_unique_equivariant l C.o C.o_sec
  obtain ⟨-, hjσ, -⟩ := GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx l C.j C.j_cris
  have hσD := (GlobalTheory.MemLoc.ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.1
  have hact := GlobalTheory.T.acrisGaloisAction_fontaine_t_eq_cyclotomic l C
  have htate := GlobalTheory.T.eq_zero_of_tateTwist_invariant_finiteExtension l C K
  have hast := GlobalTheory.T.cLTate_invariants_finiteExtension_mem l K
  generalize hx : aDp l (xi C.ε) = x at *
  obtain ⟨n, y0, hy0⟩ := hfrac C.ε he b
  rw [hx] at hy0
  generalize htt : C.j C.t = t at *
  obtain ⟨u, hu⟩ := (hfil 1 t).1 ht1
  rw [pow_one] at hu
  have huu : IsUnit u := by
    refine hunit u fun h0 => ht2 ?_
    obtain ⟨v, hv⟩ := (hfil 1 u).1 ((hker u).1 h0)
    exact (hfil 2 t).2 ⟨v, by rw [hu, hv]; ring⟩
  have ht0 : t ≠ 0 := fun h0 => ht2 (h0 ▸ zero_mem _)
  have htx : t ∣ x := by rw [hu]; exact huu.mul_right_dvd.2 dvd_rfl
  have hxt : x ∣ t := ⟨u, hu⟩
  let c : ↥(GK K) → Per.BdRp l := fun g => C.o (algebraMap ℚ_[l] (Om l) ((C.χ g.1 : ℤ_[l]) : ℚ_[l]))
  have hθc : ∀ g, Per.θD l (c g) = algebraMap ℚ_[l] ℂ_[l] ((C.χ g.1 : ℤ_[l]) : ℚ_[l]) := fun g =>
    (C.o_sec.th _).trans rfl
  have hc : ∀ g, Per.θD l (c g) ≠ 0 := fun g => by
    rw [hθc, map_ne_zero]
    exact fun h => (C.χ g.1).ne_zero (PadicInt.coe_eq_zero.1 h)
  have hσt : ∀ g : ↥(GK K), Per.σDp g.1 t = c g * t := fun g => by
    rw [← htt, ← hjσ, hact, map_mul, j_alg, ← C.o_sec.z]
  have hker' : ∀ y, Per.θD l y = 0 → t ∣ y := fun y hy =>
    htx.trans (by simpa using (hfil 1 y).1 ((hker y).1 hy))
  have hsep : ∀ y : Per.BdRp l, (∀ n : ℕ, t ^ n ∣ y) → y = 0 := fun y hy => by
    refine hcompl.toIsHausdorff.haus y fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact (pow_dvd_pow_of_dvd hxt n).trans (hy n)
  have tate : ∀ (i : ℤ) (x : ℂ_[l]), i ≠ 0 →
      (∀ g : ↥(GK K), Per.σC g.1 x * Per.θD l (c g) ^ i = x) → x = 0 := fun i x hi h =>
    htate i x hi fun g hg => by simpa only [hθc] using h ⟨g, hg⟩
  have hy : b * algebraMap (Per.BdRp l) (Per.BdR l) t ^ n =
      algebraMap (Per.BdRp l) (Per.BdR l) (y0 * u ^ n) := by
    rw [hu, map_mul, map_mul, map_pow, ← hy0]
    ring
  generalize y0 * u ^ n = y at hy
  have hyσ : ∀ g : ↥(GK K), Per.σDp g.1 y = c g ^ n * y := fun g => by
    apply hinj
    rw [← hσD, ← hy, map_mul, map_pow, hσD, hσt, hb g.1 g.2, map_mul, map_mul, map_pow, ← hy]
    ring
  obtain ⟨w, hw, hw'⟩ := eigen_eq (Per.θD l) (fun g : ↥(GK K) => Per.σDp g.1) (fun g => Per.σC g.1) c t ht0
    hker' hc (fun g y => hθ g.1 y) hσt tate n y hyσ
  obtain ⟨k, hk, hkθ⟩ := hast (Per.θD l w) fun g hg => by rw [← hθ, hw' ⟨g, hg⟩]
  have hz : w - C.o k = 0 := by
    refine inv_ker_eq_zero (Per.θD l) (fun g : ↥(GK K) => Per.σDp g.1) (fun g => Per.σC g.1) c t ht0
      hker' hsep (fun g y => hθ g.1 y) hσt tate _ ?_ fun g => ?_
    · rw [map_sub, C.o_sec.th, hkθ, sub_self]
    · have hg : g.1 k = k := g.2 ⟨k, hk⟩
      rw [map_sub, hw' g, hoσ, hg]
  refine ⟨k, hk, ?_⟩
  rw [← sub_eq_zero.1 hz]
  haveI : IsDomain (Per.BdR l) := (GlobalTheory.T.bdRPlus_isDomain_bdR_isField l).2.2.1.isDomain
  have ht' : algebraMap (Per.BdRp l) (Per.BdR l) t ^ n ≠ 0 :=
    pow_ne_zero n ((map_ne_zero_iff _ hinj).2 ht0)
  apply mul_right_cancel₀ ht'
  rw [hy, hw, map_mul, map_pow, mul_comm]

end GlobalTheory.MemLoc.InvDR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRGaloisInvariantsEqFinExtStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bdR_galois_invariants_eq_finExt : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (K : FinExt l) (b : Per.BdR l), (∀ g ∈ GK K, Per.σD g b = b) → ∃ y ∈ K.1, algebraMap (Per.BdRp l) (Per.BdR l) (C.o y) = b := by
  first | exact @GlobalTheory.MemLoc.InvDR.invariants_BdR | exact GlobalTheory.MemLoc.InvDR.invariants_BdR | (intros; apply GlobalTheory.MemLoc.InvDR.invariants_BdR <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormEqOneOfVEqZero
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.LocArith

variable {l : ℕ} [Fact l.Prime]

theorem v_nonneg_iff (P : LocPrime l) (LL : FinExt l) (y : ↥LL.1) :
    0 ≤ P.v LL y ↔ ‖((y : ↥LL.1) : Om l)‖ ≤ 1 := by
  rw [P.v_O]
  exact GlobalTheory.mem_integralClosure_padicInt_iff LL.1 y

theorem norm_natCast_prime : ‖((l : ℕ) : Om l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends, Padic.norm_p]

theorem norm_eq_one_of_v_eq_zero (P : LocPrime l) (LL : FinExt l) (y : ↥LL.1) (hy : P.v LL y = 0) :
    ‖((y : ↥LL.1) : Om l)‖ = 1 := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [AddValuation.map_zero] at hy
    exact WithTop.top_ne_zero hy
  have h1 : ‖((y : ↥LL.1) : Om l)‖ ≤ 1 := (v_nonneg_iff P LL y).1 (hy ▸ le_rfl)
  have hinv : P.v LL y⁻¹ = 0 := by
    have h := (P.v LL).map_mul y y⁻¹
    rw [mul_inv_cancel₀ hy0, AddValuation.map_one, hy, zero_add] at h
    exact h.symm
  have h2 : ‖((y⁻¹ : ↥LL.1) : Om l)‖ ≤ 1 := (v_nonneg_iff P LL _).1 (hinv ▸ le_rfl)
  have hc : ((y : ↥LL.1) : Om l) ≠ 0 := by simpa using hy0
  have hpos : 0 < ‖((y : ↥LL.1) : Om l)‖ := norm_pos_iff.2 hc
  rw [IntermediateField.coe_inv, norm_inv, inv_le_one₀ hpos] at h2
  exact le_antisymm h1 h2

theorem norm_of_v_eq (P : LocPrime l) (LL : FinExt l) (x : ↥LL.1) (r : ℚ)
    (hx : P.v LL x = ((r : ℚ) : WithTop ℚ)) :
    ‖((x : ↥LL.1) : Om l)‖ = (l : ℝ) ^ (-(r : ℝ)) := by
  set n := r.den with hn
  set a := r.num.toNat with ha
  set b := (-r.num).toNat with hb
  have hkab : (r.num : ℚ) = (a : ℚ) - (b : ℚ) := by
    have : r.num = (a : ℤ) - (b : ℤ) := by simp [ha, hb]
    exact_mod_cast this
  have hnr : (n : ℚ) * r = (a : ℚ) - b := by rw [mul_comm, hn, Rat.mul_den_eq_num, hkab]
  have hL0 : ((l : ℕ) : ↥LL.1) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  set y : ↥LL.1 := x ^ n * (l : ↥LL.1) ^ b / (l : ↥LL.1) ^ a with hy
  have hya : y * (l : ↥LL.1) ^ a = x ^ n * (l : ↥LL.1) ^ b := div_mul_cancel₀ _ (pow_ne_zero _ hL0)
  have hvy : P.v LL y = 0 := by
    have h := congrArg (P.v LL) hya
    rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_pow,
      AddValuation.map_pow, P.v_l, hx] at h
    have e1 : (n • ((r : ℚ) : WithTop ℚ)) = (((n : ℚ) * r : ℚ) : WithTop ℚ) := by
      rw [← WithTop.coe_nsmul, nsmul_eq_mul]
    have e2 : ∀ m : ℕ, m • (1 : WithTop ℚ) = (((m : ℚ) : ℚ) : WithTop ℚ) := fun m => by
      rw [← WithTop.coe_one, ← WithTop.coe_nsmul, nsmul_eq_mul, mul_one]
    rw [e1, e2, e2, hnr] at h
    by_cases ht : P.v LL y = ⊤
    · rw [ht, WithTop.top_add] at h
      exact absurd h.symm (WithTop.coe_ne_top)
    · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 ht
      rw [← hs] at h ⊢
      rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_inj] at h
      have : s = 0 := by linarith
      rw [this, WithTop.coe_zero]
  have hN := congrArg (fun z : ↥LL.1 => ‖((z : ↥LL.1) : Om l)‖) hya
  simp only [IntermediateField.coe_mul, IntermediateField.coe_pow,
    norm_mul, norm_pow] at hN
  have hc : (((l : ℕ) : ↥LL.1) : Om l) = ((l : ℕ) : Om l) := map_natCast (IntermediateField.val LL.1) l
  rw [norm_eq_one_of_v_eq_zero P LL y hvy, hc, norm_natCast_prime] at hN
  have hpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hn0 : n ≠ 0 := r.den_nz
  have hxn : ‖((x : ↥LL.1) : Om l)‖ ^ n = (l : ℝ) ^ b / (l : ℝ) ^ a := by
    rw [inv_pow, inv_pow, one_mul] at hN
    have hb0 : (0 : ℝ) < (l : ℝ) ^ b := pow_pos hpos b
    have ha0 : (0 : ℝ) < (l : ℝ) ^ a := pow_pos hpos a
    field_simp at hN ⊢
    linarith
  have hrn : ((l : ℝ) ^ (-(r : ℝ))) ^ n = (l : ℝ) ^ b / (l : ℝ) ^ a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    have : -(r : ℝ) * (n : ℝ) = (b : ℝ) - (a : ℝ) := by
      have h2 : ((n : ℚ) * r : ℚ) = (a : ℚ) - b := hnr
      have h3 : ((n : ℝ) * (r : ℝ)) = (a : ℝ) - b := by exact_mod_cast h2
      linarith
    rw [this, Real.rpow_sub hpos, Real.rpow_natCast, Real.rpow_natCast]
  rw [← hrn] at hxn
  exact (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg hpos.le _) hn0).1 hxn

theorem v_eq_iff (P : LocPrime l) (LL : FinExt l) (x : ↥LL.1) (q : ℚ) :
    P.v LL x = ((q : ℚ) : WithTop ℚ) ↔ ‖((x : ↥LL.1) : Om l)‖ = (l : ℝ) ^ (-(q : ℝ)) := by
  refine ⟨norm_of_v_eq P LL x q, fun h => ?_⟩
  have hpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hx0 : x ≠ 0 := by
    rintro rfl
    have : (0 : ℝ) < (l : ℝ) ^ (-(q : ℝ)) := Real.rpow_pos_of_pos hpos _
    simp at h
    linarith
  have ht : P.v LL x ≠ ⊤ := fun ht => hx0 ((P.v LL).top_iff.1 ht)
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 ht
  have h2 := norm_of_v_eq P LL x s hs.symm
  rw [h2] at h
  have hqs : (q : ℝ) = (s : ℝ) := by
    have := le_antisymm ((Real.rpow_le_rpow_left_iff hl1).1 h.le) ((Real.rpow_le_rpow_left_iff hl1).1 h.ge)
    linarith
  rw [← hs, show q = s by exact_mod_cast hqs]

theorem arithTied : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), Formalism.L2.ArithTied P := fun l _ P =>
  ⟨fun LL x q => v_eq_iff P LL x q⟩

end GlobalTheory.LocArith
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetTwistedConjugateIsKTypeOfReversed
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetTwistedConjugateIsKTypeOfReversed
open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ConjTwist

variable {k : ℕ}

theorem Jm_allPos (k : ℕ) : Formalism.REAL.Jm (allPos k) = 1 := by
  simp [Formalism.REAL.Jm, allPos]

theorem mem_U_iff (g : Matrix (Fin k) (Fin k) ℂ) : g ∈ UJset (allPos k) ↔ gᴴ * g = 1 := by
  show gᴴ * Formalism.REAL.Jm (allPos k) * g = Formalism.REAL.Jm (allPos k) ↔ _
  rw [Jm_allPos, Matrix.mul_one]

theorem mem_K_iff (g : Matrix (Fin k) (Fin k) ℂ) :
    g ∈ Formalism.REAL.Kset (allPos k) ↔ g ∈ UJset (allPos k) := by
  rw [mem_U_iff]
  show (g ∈ Matrix.unitaryGroup (Fin k) ℂ ∧ g * Formalism.REAL.Jm (allPos k) = Formalism.REAL.Jm (allPos k) * g) ↔ _
  rw [Jm_allPos, Matrix.mul_one, Matrix.one_mul, Matrix.mem_unitaryGroup_iff']
  simp [Matrix.star_eq_conjTranspose]

theorem map_star_mul (g h : Matrix (Fin k) (Fin k) ℂ) :
    (g * h).map star = g.map star * h.map star :=
  Matrix.map_mul (f := starRingEnd ℂ)

theorem map_star_one : (1 : Matrix (Fin k) (Fin k) ℂ).map star = 1 :=
  Matrix.map_one _ (star_zero _) (star_one _)

theorem map_star_star (g : Matrix (Fin k) (Fin k) ℂ) : (g.map star).map star = g := by
  ext a b
  simp

theorem map_star_mem {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) :
    g.map star ∈ UJset (allPos k) := by
  rw [mem_U_iff] at hg ⊢
  have h : (g.map star)ᴴ = gᴴ.map star := by
    ext a b
    simp
  rw [h, ← map_star_mul, hg, map_star_one]

theorem norm_det {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) : ‖g.det‖ = 1 := by
  rw [mem_U_iff] at hg
  have h := congrArg (fun M => ‖Matrix.det M‖) hg
  simp only [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star, Matrix.det_one,
    norm_one] at h
  nlinarith [norm_nonneg g.det]

theorem det_ne_zero {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) : g.det ≠ 0 := by
  intro h
  have := norm_det hg
  rw [h, norm_zero] at this
  exact zero_ne_one this

abbrev tor (θ : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℂ :=
  Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)

theorem tor_map_star (θ : Fin k → ℝ) : (tor θ).map star = tor (fun a => -θ a) := by
  rw [tor, Matrix.diagonal_map (star_zero _)]
  congr 1
  funext a
  show (starRingEnd ℂ) _ = _
  rw [← Complex.exp_conj]
  simp

theorem tor_mem (θ : Fin k → ℝ) : tor θ ∈ UJset (allPos k) := by
  rw [mem_U_iff, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  show (starRingEnd ℂ) _ * _ = _
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp

theorem tor_det_zpow (θ : Fin k → ℝ) (x : ℤ) :
    (tor θ).det ^ x = Complex.exp (((∑ a, (x : ℝ) * θ a : ℝ) : ℂ) * Complex.I) := by
  rw [Matrix.det_diagonal, ← Complex.exp_sum, ← Complex.exp_int_mul]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => by ring

def revMat (k : ℕ) : Matrix (Fin k) (Fin k) ℂ := Matrix.of fun a b => if Fin.rev a = b then 1 else 0

theorem revMat_mul_self : revMat k * revMat k = 1 := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev a)]
  · simp [revMat, Matrix.one_apply]
  · intro c _ hc
    simp [revMat, hc.symm]
  · simp

theorem revMat_conjTranspose : (revMat k)ᴴ = revMat k := by
  ext a b
  simp only [revMat, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases h : Fin.rev a = b
  · subst h
    simp
  · have h' : ¬ Fin.rev b = a := fun h' => h (by rw [← h', Fin.rev_rev])
    simp [h, h']

theorem revMat_mem : revMat k ∈ UJset (allPos k) := by
  rw [mem_U_iff, revMat_conjTranspose, revMat_mul_self]

theorem tor_mul_revMat (θ : Fin k → ℝ) :
    tor θ * revMat k = revMat k * tor (fun a => θ (Fin.rev a)) := by
  ext a b
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, revMat, Matrix.of_apply]
  by_cases h : Fin.rev a = b
  · subst h
    simp
  · simp [h]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)}

theorem isWtOn_rev (hσ : IsURepOn (UJset (allPos k)) σ) {μ : Fin k → ℝ} {v : H}
    (hv : IsWtOn (Formalism.REAL.Kset (allPos k)) σ μ v) :
    IsWtOn (Formalism.REAL.Kset (allPos k)) σ (fun a => μ (Fin.rev a)) (σ (revMat k) v) := by
  intro θ _
  have h1 : σ (tor θ) (σ (revMat k) v) = σ (revMat k) (σ (tor fun a => θ (Fin.rev a)) v) := by
    have h2 := hσ.1.2 _ (tor_mem θ) _ revMat_mem
    have h3 := hσ.1.2 _ revMat_mem _ (tor_mem fun a => θ (Fin.rev a))
    rw [tor_mul_revMat, h3] at h2
    exact (congrArg (fun f : H →L[ℂ] H => f v) h2).symm
  refine h1.trans ?_
  rw [hv _ ((mem_K_iff _).2 (tor_mem _)), map_smul]
  congr 4
  rw [← Equiv.sum_comp Fin.revPerm]
  simp

theorem rev_ne_zero (hσ : IsURepOn (UJset (allPos k)) σ) {v : H} (hv : v ≠ 0) :
    σ (revMat k) v ≠ 0 := by
  rw [← norm_ne_zero_iff, hσ.2.1 _ revMat_mem, norm_ne_zero_iff]
  exact hv

theorem exp_split (x : ℤ) (μ θ : Fin k → ℝ) :
    Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) =
      (tor θ).det ^ x * Complex.exp (((∑ a, ((x : ℝ) - μ a) * -θ a : ℝ) : ℂ) * Complex.I) := by
  rw [tor_det_zpow, ← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, ← Finset.sum_add_distrib]
  congr 3
  exact Finset.sum_congr rfl fun a _ => by ring

theorem isWtOn_twist_iff (x : ℤ) (μ : Fin k → ℝ) (v : H) :
    IsWtOn (Formalism.REAL.Kset (allPos k)) (fun g => g.det ^ x • σ (g.map star)) μ v ↔
      IsWtOn (Formalism.REAL.Kset (allPos k)) σ (fun a => (x : ℝ) - μ a) v := by
  constructor
  · intro h θ _
    have h1 : (tor fun a => -θ a).det ^ x • σ ((tor fun a => -θ a).map star) v = _ :=
      h (fun a => -θ a) ((mem_K_iff _).2 (tor_mem _))
    rw [exp_split x, ← smul_smul, tor_map_star] at h1
    simp only [neg_neg] at h1
    exact smul_right_injective H (zpow_ne_zero x (det_ne_zero (tor_mem _))) h1
  · intro h θ _
    show (tor θ).det ^ x • σ ((tor θ).map star) v = _
    rw [exp_split x, ← smul_smul, tor_map_star, h _ ((mem_K_iff _).2 (tor_mem _))]

theorem stable_twist_iff (x : ℤ) (S : Submodule ℂ H) :
    IsKStableOn (allPos k) (fun g => g.det ^ x • σ (g.map star)) S ↔ IsKStableOn (allPos k) σ S := by
  constructor
  · intro h g hg v hv
    have hg' := map_star_mem ((mem_K_iff g).1 hg)
    have h1 : (g.map star).det ^ x • σ ((g.map star).map star) v ∈ S :=
      h _ ((mem_K_iff _).2 hg') v hv
    rw [map_star_star] at h1
    exact (S.smul_mem_iff (zpow_ne_zero x (det_ne_zero hg'))).1 h1
  · intro h g hg v hv
    exact S.smul_mem _ (h _ ((mem_K_iff _).2 (map_star_mem ((mem_K_iff g).1 hg))) v hv)

theorem isURepOn_twist (hσ : IsURepOn (UJset (allPos k)) σ) (x : ℤ) :
    IsURepOn (UJset (allPos k)) (fun g => g.det ^ x • σ (g.map star)) := by
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg v => ?_, fun v => ?_⟩
  · simp only [Matrix.det_one, _root_.one_zpow, one_smul, map_star_one, hσ.1.1]
  · simp only [Matrix.det_mul, mul_zpow, map_star_mul]
    rw [hσ.1.2 _ (map_star_mem ha) _ (map_star_mem hb)]
    ext v
    simp [smul_smul, mul_comm]
  · simp only [ContinuousLinearMap.smul_apply, norm_smul, norm_zpow, norm_det hg, _root_.one_zpow,
      one_mul, hσ.2.1 _ (map_star_mem hg)]
  · simp only [ContinuousLinearMap.smul_apply]
    refine ContinuousOn.smul ?_ ?_
    · exact (continuous_id.matrix_det.continuousOn).zpow₀ x fun g hg => Or.inl (det_ne_zero hg)
    · exact (hσ.2.2 v).comp (continuous_id.matrix_map continuous_star).continuousOn
        fun g hg => map_star_mem hg

theorem cdom_rev (x : ℤ) (Λ μ : Fin k → ℝ)
    (h : CDom (allPos k) (fun a => (x : ℝ) - μ (Fin.rev a)) Λ) :
    CDom (allPos k) μ (fun a => (x : ℝ) - Λ (Fin.rev a)) := by
  obtain ⟨c, hc, he⟩ := h
  refine ⟨fun a b => c (Fin.rev b) (Fin.rev a), fun a b hab => ⟨?_, rfl⟩, ?_⟩
  · exact Fin.rev_lt_rev.1 (hc _ _ hab).1
  · funext i
    have h1 := congrFun he (Fin.rev i)
    simp only [Pi.sub_apply, Fin.rev_rev, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    have h2 : ∑ a, ∑ b, (c (Fin.rev b) (Fin.rev a) : ℝ) * Formalism.REAL.root a b i =
        -∑ a, ∑ b, (c a b : ℝ) * Formalism.REAL.root a b (Fin.rev i) := by
      rw [Finset.sum_comm, ← Equiv.sum_comp Fin.revPerm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Equiv.sum_comp Fin.revPerm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [Fin.revPerm_apply, Fin.rev_rev, Formalism.REAL.root, Pi.sub_apply, Pi.single_apply,
        Fin.rev_eq_iff]
      ring
    rw [h2, ← h1]
    ring

theorem conj_twist_isKTypeOf : ∀ (k : ℕ) (Λ : Fin k → ℝ) (x : ℤ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), IsURepOn (UJset (allPos k)) σ → IsKTypeOf (allPos k) σ Λ ⊤ → IsURepOn (UJset (allPos k)) (fun g => g.det ^ x • σ (g.map star)) ∧ IsKTypeOf (allPos k) (fun g => g.det ^ x • σ (g.map star)) (fun a => (x : ℝ) - Λ (Fin.rev a)) ⊤ := by
  intro k Λ x H _ _ _ σ hσ hK
  obtain ⟨hfd, -, hirr, ⟨v, -, hv0, hv⟩, hdom⟩ := hK
  refine ⟨isURepOn_twist hσ x, hfd, fun _ _ _ _ => trivial,
    fun S hS hst => hirr S hS ((stable_twist_iff x S).1 hst),
    ⟨σ (revMat k) v, trivial, rev_ne_zero hσ hv0, ?_⟩, fun μ w _ hw0 hw => ?_⟩
  · rw [isWtOn_twist_iff]
    simpa only [sub_sub_cancel] using isWtOn_rev hσ hv
  · rw [isWtOn_twist_iff] at hw
    exact cdom_rev x Λ μ (hdom _ _ trivial (rev_ne_zero hσ hw0) (isWtOn_rev hσ hw))

end GlobalTheory.ConjTwist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetTwistedConjugateIsKTypeOfReversedStatement
open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detTwistedConjugate_isKTypeOf_reversed : ∀ (k : ℕ) (Λ : Fin k → ℝ) (x : ℤ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), IsURepOn (UJset (allPos k)) σ → IsKTypeOf (allPos k) σ Λ ⊤ → IsURepOn (UJset (allPos k)) (fun g => g.det ^ x • σ (g.map star)) ∧ IsKTypeOf (allPos k) (fun g => g.det ^ x • σ (g.map star)) (fun a => (x : ℝ) - Λ (Fin.rev a)) ⊤ := by
  first | exact @GlobalTheory.ConjTwist.conj_twist_isKTypeOf | exact GlobalTheory.ConjTwist.conj_twist_isKTypeOf | (intros; apply GlobalTheory.ConjTwist.conj_twist_isKTypeOf <;> assumption)
end
end
