module

public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorWordActionContinuous
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuotVolumeNeZeroNeTop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFormsEqKilledByGroupAlgebra
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfDualVectorPairsIntegralFrameColumns
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfDualVectorPairsIntegralFrameColumns
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairIntegral

theorem sum_mem_intAf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (u : Fin n → E)
    (hu : ∀ y ∈ Λ, ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = ∑ k, u k * y k)
    (z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    ∑ k, (u k ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) * z k ∈ Formalism.L2.Herm.intAf F E := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨c, hc⟩ := hu y hy
    have hm : (algebraMap (𝓞 E) E c) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) ∈ Formalism.L2.Herm.intAf F E :=
      Subring.subset_closure (Or.inl ⟨⟨_, c, rfl⟩, rfl⟩)
    convert hm using 1
    rw [hc, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun k _ => ?_
    change (u k ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) * (y k ⊗ₜ[F] 1) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | zero => simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]; exact zero_mem _
  | add x y _ _ hx hy => simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]; exact add_mem hx hy
  | smul c x _ hx =>
    have := mul_mem c.2 hx
    convert this using 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change _ * (c.1 * x k) = _
    ring

theorem pair_mem_intAf : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSDFrame W β Λ 1 → ∀ v : Fin W.rank → D.host.E, finVec W v ∈ gLat W 1 → ∀ a : Fin W.rank, ∑ k, eToEAf D (∑ l, D.sp.cm.sig (v l) * W.gram l k) * β.val k a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D W β Λ hβ v hv a
  have hΛ := GlobalTheory.PrincInLevel.eq_latC hβ
  have hfr : Formalism.L2.DIV.IsFrame β Λ := by obtain ⟨c, h, -⟩ := hβ; exact h
  obtain ⟨h1, -, hfg, hsp, -, -, -, -, -, -, hsd⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D W
  have hv' : v ∈ GlobalTheory.Member.latC W := by
    obtain ⟨z, hz, e⟩ := hv
    rw [map_one, Units.val_one, Matrix.one_mulVec] at e
    subst e
    rw [h1] at hz
    exact ((GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E W.rank _ hfg hsp).1 v).1 hz
  have hcol : (fun k => β.val k a) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    refine (hfr _).2 fun i => ?_
    have e : ((β⁻¹).val *ᵥ fun k => β.val k a) i = ((β⁻¹).val * β.val) i a := rfl
    rw [e, Units.inv_mul, Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  refine sum_mem_intAf Λ (fun k => ∑ l, D.sp.cm.sig (v l) * W.gram l k) (fun y hy => ?_) _ hcol
  rw [hΛ] at hy
  obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 ((hsd y).2 hy v hv')
  refine ⟨c, hc.trans (Finset.sum_congr rfl fun k _ => ?_)⟩
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  change y k * W.gram l k * D.sp.cm.sig (v l) = _
  ring

end GlobalTheory.PairIntegral
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfDualVectorPairsIntegralFrameColumnsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_vector_pairs_integral_frame_columns : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSDFrame W β Λ 1 → ∀ v : Fin W.rank → D.host.E, finVec W v ∈ gLat W 1 → ∀ a : Fin W.rank, ∑ k, eToEAf D (∑ l, D.sp.cm.sig (v l) * W.gram l k) * β.val k a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.PairIntegral.pair_mem_intAf | exact GlobalTheory.PairIntegral.pair_mem_intAf | (intros; apply GlobalTheory.PairIntegral.pair_mem_intAf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLiftModelsOn
noncomputable section

open Formalism.IndefR.Links
open scoped InnerProductSpace

namespace GlobalTheory.HilbertModel

def Syn {X : Type} [AddCommGroup X] [Module ℂ X] (V : Submodule ℂ X) : Type := V

instance {X : Type} [AddCommGroup X] [Module ℂ X] (V : Submodule ℂ X) : AddCommGroup (Syn V) :=
  inferInstanceAs (AddCommGroup V)

instance {X : Type} [AddCommGroup X] [Module ℂ X] (V : Submodule ℂ X) : Module ℂ (Syn V) :=
  inferInstanceAs (Module ℂ V)

def Syn.incl {X : Type} [AddCommGroup X] [Module ℂ X] (V : Submodule ℂ X) : Syn V →ₗ[ℂ] X := V.subtype

theorem Syn.incl_mem {X : Type} [AddCommGroup X] [Module ℂ X] {V : Submodule ℂ X} (x : Syn V) : Syn.incl V x ∈ V :=
  (show V from x).2

theorem Syn.incl_injective {X : Type} [AddCommGroup X] [Module ℂ X] (V : Submodule ℂ X) :
    Function.Injective (Syn.incl V) := Subtype.val_injective

theorem Syn.range_incl {X : Type} [AddCommGroup X] [Module ℂ X] (V : Submodule ℂ X) :
    LinearMap.range (Syn.incl V) = V := V.range_subtype

@[reducible] def core {X : Type} [AddCommGroup X] [Module ℂ X] (V : Submodule ℂ X) (ip : X → X → ℂ)
    (h : ∀ x ∈ V, ∀ y ∈ V, ∀ z ∈ V, ∀ c : ℂ, ip x (y + c • z) = ip x y + c * ip x z ∧ ip y x = star (ip x y))
    (hp : ∀ x ∈ V, x ≠ 0 → 0 < (ip x x).re) : InnerProductSpace.Core ℂ (Syn V) :=
  have hs : ∀ x ∈ V, ∀ y ∈ V, ip y x = star (ip x y) := fun x hx y hy => (h x hx y hy 0 V.zero_mem 0).2
  have h0 : ∀ x ∈ V, ip x 0 = 0 := fun x hx => by
    have := (h x hx 0 V.zero_mem 0 V.zero_mem 1).1
    simpa using this
  { inner := fun x y => ip (Syn.incl V x) (Syn.incl V y)
    conj_inner_symm := fun x y => (hs _ (Syn.incl_mem y) _ (Syn.incl_mem x)).symm
    re_inner_nonneg := fun x => by
      show 0 ≤ (ip (Syn.incl V x) (Syn.incl V x)).re
      by_cases hx : Syn.incl V x = 0
      · rw [hx, h0 0 V.zero_mem]; simp
      · exact (hp _ (Syn.incl_mem x) hx).le
    add_left := fun x y z => by
      show ip (Syn.incl V (x + y)) (Syn.incl V z) = ip (Syn.incl V x) (Syn.incl V z) + ip (Syn.incl V y) (Syn.incl V z)
      have h1 := (h _ (Syn.incl_mem z) _ (Syn.incl_mem x) _ (Syn.incl_mem y) 1).1
      rw [one_smul, one_mul] at h1
      rw [hs _ (Syn.incl_mem z) _ (Syn.incl_mem (x + y)), map_add (f := _), h1, star_add,
        ← hs _ (Syn.incl_mem z) _ (Syn.incl_mem x), ← hs _ (Syn.incl_mem z) _ (Syn.incl_mem y)]
    smul_left := fun x y r => by
      show ip (Syn.incl V (r • x)) (Syn.incl V y) = starRingEnd ℂ r * ip (Syn.incl V x) (Syn.incl V y)
      have h1 := (h _ (Syn.incl_mem y) _ V.zero_mem _ (Syn.incl_mem x) r).1
      rw [zero_add, h0 _ (Syn.incl_mem y), zero_add] at h1
      rw [hs _ (Syn.incl_mem y) _ (Syn.incl_mem (r • x)), map_smul, h1, star_mul',
        ← hs _ (Syn.incl_mem y) _ (Syn.incl_mem x)]
      rfl
    definite := fun x hx => by
      have hx' : ip (Syn.incl V x) (Syn.incl V x) = 0 := hx
      by_contra hne
      have h1 : Syn.incl V x ≠ 0 := fun h2 => hne (Syn.incl_injective V (by rw [h2, map_zero]))
      have := hp _ (Syn.incl_mem x) h1
      rw [hx'] at this
      simp at this }

theorem exists_hmod : ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (V : Submodule ℂ X) (ip : X → X → ℂ), FiniteDimensional ℂ V → (∀ x ∈ V, ∀ y ∈ V, ∀ z ∈ V, ∀ c : ℂ, ip x (y + c • z) = ip x y + c * ip x z ∧ ip y x = star (ip x y)) → (∀ x ∈ V, x ≠ 0 → 0 < (ip x x).re) → ∃ M : HMod X, M.Is V ip := by
  intro X _ _ V ip hf h hp
  let cd : InnerProductSpace.Core ℂ (Syn V) := core V ip h hp
  let nH : NormedAddCommGroup (Syn V) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (cd := cd)
  let iH : InnerProductSpace ℂ (Syn V) := InnerProductSpace.ofCore cd.toCore
  exact ⟨@Formalism.IndefR.Links.HMod.mk X _ _ (Syn V) nH iH hf (Syn.incl V), Syn.incl_injective V, Syn.range_incl V, fun _ _ => rfl⟩

section Lift

variable {X : Type} [AddCommGroup X] [Module ℂ X] {M : HMod X} {V : Submodule ℂ X} {ip : X → X → ℂ}

def equivSub (hM : M.Is V ip) : M.H ≃ₗ[ℂ] V :=
  (LinearEquiv.ofInjective M.e hM.1).trans (LinearEquiv.ofEq _ _ hM.2.1)

@[simp] theorem coe_equivSub (hM : M.Is V ip) (x : M.H) : (equivSub hM x : X) = M.e x := rfl

@[simp] theorem e_equivSub_symm (hM : M.Is V ip) (v : V) : M.e ((equivSub hM).symm v) = v := by
  rw [← coe_equivSub hM, LinearEquiv.apply_symm_apply]

theorem exists_lift_fun {R A : Type*} [Semiring R] [AddCommMonoid A] [Module R A] (σ : R →+* ℂ) (hM : M.Is V ip)
    (f : A → X) (hadd : ∀ a b, f (a + b) = f a + f b) (hsmul : ∀ (c : R) a, f (c • a) = σ c • f a) (hf : ∀ a, f a ∈ V) :
    ∃ g : A →ₛₗ[σ] M.H, ∀ a, M.e (g a) = f a :=
  ⟨{ toFun := fun a => (equivSub hM).symm ⟨f a, hf a⟩
     map_add' := fun a b => hM.1 (by simp [hadd])
     map_smul' := fun c a => hM.1 (by simp [hsmul]) }, fun a => e_equivSub_symm hM _⟩

theorem exists_lift {R A : Type*} [Semiring R] [AddCommMonoid A] [Module R A] {σ : R →+* ℂ} (hM : M.Is V ip)
    (f : A →ₛₗ[σ] X) (hf : ∀ a, f a ∈ V) : ∃ g : A →ₛₗ[σ] M.H, ∀ a, M.e (g a) = f a :=
  exists_lift_fun σ hM f f.map_add f.map_smulₛₗ hf

variable {X' : Type} [AddCommGroup X'] [Module ℂ X'] {M' : HMod X'} {V' : Submodule ℂ X'} {ip' : X' → X' → ℂ}

end Lift

end GlobalTheory.HilbertModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNumberFieldHeckeCharacterSqrtNormValues
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNumberFieldHeckeCharacterSqrtNormValues
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.BVal

open Formalism.L2.Host
open scoped nonZeroDivisors

section General

variable {L : Type} [Field L] [NumberField L]

theorem onId_mul (χ : HChar L) {I J : FractionalIdeal (𝓞 L)⁰ L} (hI : I ≠ 0) (hJ : J ≠ 0) :
    χ.onId (I * J) = χ.onId I * χ.onId J := by
  have hf : ∀ K : FractionalIdeal (𝓞 L)⁰ L,
      (Function.mulSupport fun v : HeightOneSpectrum (𝓞 L) => χ.val v ^ FractionalIdeal.count L v K).Finite := fun K => by
    refine (FractionalIdeal.finite_factors (K := L) K).subset fun v hv h => hv ?_
    have h' : FractionalIdeal.count L v K = 0 := h
    simp [h']
  unfold HChar.onId
  rw [← finprod_mul_distrib (hf I) (hf J)]
  refine finprod_congr fun v => ?_
  rw [FractionalIdeal.count_mul L v hI hJ, _root_.zpow_add]

theorem onId_one (χ : HChar L) : χ.onId 1 = 1 := by
  unfold HChar.onId
  simp [FractionalIdeal.count_one]

theorem onId_prime (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    χ.onId (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) = χ.val v := by
  unfold HChar.onId
  rw [finprod_eq_single _ v fun w hw => by rw [FractionalIdeal.count_maximal_coprime L w hw.symm, zpow_zero],
    FractionalIdeal.count_self, zpow_one]

theorem mem_of_primes (χ : HChar L) (M : IntermediateField ℚ ℂ) (b : 𝓞 L)
    (h : ∀ v : HeightOneSpectrum (𝓞 L), b ∉ v.asIdeal →
      ((χ.val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) ∈ M)
    (cc : Ideal (𝓞 L)) (h0 : cc ≠ ⊥) (h1 : cc ⊔ Ideal.span {b} = ⊤) :
    ((χ.onId (cc : FractionalIdeal (𝓞 L)⁰ L) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm cc : ℝ) : ℝ) : ℂ) ∈ M := by
  induction cc using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl h0
  | h₂ x hx =>
    obtain rfl : x = ⊤ := Ideal.isUnit_iff.1 hx
    simp [onId_one]
  | h₃ a p ha hp ih =>
    let v : HeightOneSpectrum (𝓞 L) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    have hb : b ∉ v.asIdeal := fun hb => v.isPrime.ne_top
      (top_le_iff.1 (h1.ge.trans (sup_le Ideal.mul_le_left ((Ideal.span_singleton_le_iff_mem _).2 hb))))
    have ha1 : a ⊔ Ideal.span {b} = ⊤ := top_le_iff.1 (h1.ge.trans (sup_le_sup_right Ideal.mul_le_right _))
    have := mul_mem (h v hb) (ih ha ha1)
    rw [FractionalIdeal.coeIdeal_mul, onId_mul χ (FractionalIdeal.coeIdeal_ne_zero.2 hp.ne_zero)
      (FractionalIdeal.coeIdeal_ne_zero.2 ha), map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _),
      show χ.onId (p : FractionalIdeal (𝓞 L)⁰ L) = χ.val v from onId_prime χ v]
    convert this using 1
    push_cast
    ring

theorem val_mul_sqrt (α β γ : HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    (((α * β * γ⁻¹).val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) =
      α.valTw 0 v * β.valTw 0 v * (γ.valTw (1 / 2) v)⁻¹ := by
  have e : (α * β * γ⁻¹).val v = α.val v * β.val v * (γ.val v)⁻¹ := rfl
  have e2 : ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) = (Ideal.absNorm v.asIdeal : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast]
  rw [e, e2]
  simp only [HChar.valTw, Complex.cpow_neg, Complex.ofReal_zero, Complex.cpow_zero, inv_one, mul_one, mul_inv, inv_inv,
    Units.val_mul, Units.val_inv_eq_inv_val, mul_assoc]

end General

theorem exists_field_BIs : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (t : T0), ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ (M' : IntermediateField ℚ ℂ), M ≤ M' → ∀ bad : ℕ, D.host.g 0 * D.host.g 1 ∣ bad → (∀ PP ∈ R.Q t, ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∃ B : Ideal (𝓞 D.host.E) → M', BIs R i M'.val.toRingHom t bad B := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL i t
  obtain ⟨M₁, hM₁, -, -, hmu, heta, -⟩ := GlobalTheory.Mem.FrameVal.frame_values D.R D.host (eExp D)
    ⟨R.C.P, R.C.W, R.C.mu0, R.C.eta, R.C.chiPsi, R.C.del, R.C.del', R.C.isMu0, R.C.isEta, R.C.isChi, R.C.isDel, R.C.isDel'⟩
    fun j τ => (D.hc _).e_int j
  obtain ⟨M₂, hM₂, hxi⟩ := GlobalTheory.Mem.FrameVal.exists_of_order (hL.xi_fin t)
  refine ⟨M₁ ⊔ M₂, inferInstance, fun M' hM bad hg hQ => ?_⟩
  have key : ∀ v : HeightOneSpectrum (𝓞 D.host.E), ((bad : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal →
      (((R.C.mu0 i * R.xiH t * R.C.eta⁻¹).val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) ∈ M' := by
    intro v hv
    have u1 : (R.C.mu0 i).UnrAt v := (R.C.isMu0 i).unr v fun k hk => hv (by
      have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal := hk
      have hd : D.host.g k ∣ bad := by
        refine dvd_trans ?_ hg
        fin_cases k
        · exact dvd_mul_right _ _
        · exact dvd_mul_left _ _
      obtain ⟨c, rfl⟩ := hd
      rw [Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ hk')
    have u2 : (R.xiH t).UnrAt v := by
      by_contra h
      rcases (hL.Q_ram t v).1 h with h | ⟨P', hP', h⟩
      · exact hv (hQ v h)
      · obtain ⟨c', hc', e⟩ := h _ (hQ P' hP')
        have e' : c' = (bad : 𝓞 D.host.E) := RingOfIntegers.ext (by
          rw [e]
          change star ((bad : 𝓞 D.host.E) : D.host.E) = ((bad : 𝓞 D.host.E) : D.host.E)
          rw [show ((bad : 𝓞 D.host.E) : D.host.E) = (bad : D.host.E) from
            map_natCast (algebraMap (𝓞 D.host.E) D.host.E) bad, star_natCast])
        exact hv (e' ▸ hc')
    obtain ⟨y1, hy1⟩ := hmu i v u1
    obtain ⟨y2, hy2⟩ := hxi v u2
    obtain ⟨y3, hy3⟩ := heta v (R.C.isEta.unr v)
    rw [val_mul_sqrt, ← hy1, ← hy2, ← hy3]
    exact mul_mem (mul_mem (hM (le_sup_left (b := M₂) y1.2)) (hM (le_sup_right (a := M₁) y2.2)))
      (inv_mem (hM (le_sup_left (b := M₂) y3.2)))
  classical
  refine ⟨fun cc => if h : cc ≠ ⊥ ∧ cc ⊔ Ideal.span {((bad : ℕ) : 𝓞 D.host.E)} = ⊤ then
    ⟨_, mem_of_primes _ M' _ key cc h.1 h.2⟩ else 0, fun cc h0 h1 => ?_⟩
  simp only [dif_pos (And.intro h0 h1)]
  rfl

end GlobalTheory.Mem.BVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNumberFieldHeckeCharacterSqrtNormValuesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_numberField_heckeCharacter_sqrtNorm_values : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (t : T0), ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ (M' : IntermediateField ℚ ℂ), M ≤ M' → ∀ bad : ℕ, D.host.g 0 * D.host.g 1 ∣ bad → (∀ PP ∈ R.Q t, ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∃ B : Ideal (𝓞 D.host.E) → M', BIs R i M'.val.toRingHom t bad B := by
  first | exact @GlobalTheory.Mem.BVal.exists_field_BIs | exact GlobalTheory.Mem.BVal.exists_field_BIs | (intros; apply GlobalTheory.Mem.BVal.exists_field_BIs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InverseSelfDualFrameStandardSpaceIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InverseSelfDualFrameStandardSpaceIntegral
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdFrameInv

theorem inv_col_int {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)) (hfr : Formalism.L2.DIV.IsFrame β Λ)
    (a j : Fin n) (hmem : (Pi.single j 1 : Fin n → E) ∈ Λ) : (β⁻¹).val a j ∈ Formalism.L2.Herm.intAf F E := by
  have hhat : (fun k => (Pi.single j 1 : Fin n → E) k ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) ∈
      Formalism.L2.Herm.hatL (F := F) Λ := Submodule.subset_span ⟨_, hmem, rfl⟩
  have e : (fun k => (Pi.single j 1 : Fin n → E) k ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) = Pi.single j 1 := by
    funext k
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs
    · rfl
    · exact TensorProduct.zero_tmul _ _
  rw [e] at hhat
  have := (hfr _).1 hhat a
  rw [Matrix.mulVec_single_one] at this
  exact this

theorem isIntM_inv : ∀ (D : D7) (i : Fin D.R.m) (β : GL (Fin (Vc D i).rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)), VStd D i → IsSDFrame (Vc D i) β Λ 1 → IsIntM (β⁻¹).val := by
  intro D i β Λ hV hΛ a j
  have hfr : Formalism.L2.DIV.IsFrame β Λ := by obtain ⟨c, h, -⟩ := hΛ; exact h
  have hmem : (Pi.single j 1 : Fin (Vc D i).rank → D.host.E) ∈ Λ := by
    rw [GlobalTheory.PrincInLevel.eq_latC hΛ, ← GlobalTheory.SplitReps.hLat_one, hV.2]
    intro k _
    rw [Pi.single_apply]
    split_ifs
    · exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · exact zero_mem _
  exact inv_col_int β Λ hfr a j hmem

end GlobalTheory.StdFrameInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InverseSelfDualFrameStandardSpaceIntegralStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverse_selfDual_frame_standard_space_integral : ∀ (D : D7) (i : Fin D.R.m) (β : GL (Fin (Vc D i).rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)), VStd D i → IsSDFrame (Vc D i) β Λ 1 → IsIntM (β⁻¹).val := by
  first | exact @GlobalTheory.StdFrameInv.isIntM_inv | exact GlobalTheory.StdFrameInv.isIntM_inv | (intros; apply GlobalTheory.StdFrameInv.isIntM_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevContinuousFormGardingVector
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevContinuousFormGardingVector
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SobGarding

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {P G : Matrix (Fin n) (Fin n) ℂ}

theorem word_gard (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) (hσ : IsURepOn (UJset ε) σ)
    {φ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφ : IsTest φ) (l : List (Matrix (Fin n) (Fin n) ℂ))
    (hl : ∀ X ∈ l, X ∈ lieG G) :
    ∃ φ', IsTest φ' ∧ ∀ w, word (trRep σ P) l (gard ε σ φ w) = gard ε σ φ' w := by
  induction l with
  | nil => exact ⟨φ, hφ, fun _ => rfl⟩
  | cons X l ih =>
    obtain ⟨φ', h1, h2⟩ := ih fun Y hY => hl Y (by simp [hY])
    obtain ⟨ψ, hψ⟩ := GlobalTheory.T.gardingVector_derivative_eq_gardingVector n ε H σ P G hP h hσ φ' h1
    exact ⟨ψ X, (hψ X).1, fun w => by rw [word_cons, h2, (hψ X).2 (hl X (by simp))]⟩

theorem inner_word_gard (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) (hσ : IsURepOn (UJset ε) σ)
    {φ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφ : IsTest φ) (l : List (Matrix (Fin n) (Fin n) ℂ))
    (hl : ∀ X ∈ l, X ∈ lieG G) {w : H} (hw : w ∈ smSub G (trRep σ P)) (a : H) :
    ⟪a, word (trRep σ P) l (gard ε σ φ w)⟫_ℂ
      = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪a, word (trRep σ P) l (σ (umat g) w)⟫_ℂ ∂(Formalism.REAL.muG ε) := by
  have hc := GlobalTheory.T.smooth_vector_word_action_continuous n ε H σ P G hP h hσ l hl w hw
  have key : ∀ y : H, ⟪y, ∫ g : Formalism.REAL.UJ ε, φ (umat g) • word (trRep σ P) l (σ (umat g) w) ∂(Formalism.REAL.muG ε)⟫_ℂ
      = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪y, word (trRep σ P) l (σ (umat g) w)⟫_ℂ ∂(Formalism.REAL.muG ε) := by
    intro y
    rw [← integral_inner (hφ.integrable hc)]
    congr 1
    funext g
    rw [← Complex.coe_smul, inner_smul_right, Complex.real_smul]
  rw [← key]
  congr 1
  refine ext_inner_smooth hP h hσ fun u hu => ?_
  obtain ⟨u', -, h2⟩ := word_adjoint (gram_unit hP h) (isURepOn_trRep hP h hσ) hl hu
  rw [key, h2 _ (gard_mem hP h hσ hφ w), inner_gard hσ hφ]
  congr 1
  funext g
  rw [h2 _ (sigma_mem hP h hσ hw g.2)]

theorem sobCont_gard : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ (lieG G) (trRep σ P) ℓ → (∀ φ, IsTest φ → ∃ C : ℝ, ∀ w, ‖ℓ (gard ε σ φ w)‖ ≤ C * ‖w‖) ∧ ∀ w ∈ smSub G (trRep σ P), (Continuous fun g : Formalism.REAL.UJ ε => ℓ (σ (umat g) w)) ∧ ∀ φ, IsTest φ → ℓ (gard ε σ φ w) = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ℓ (σ (umat g) w) ∂(Formalism.REAL.muG ε) := by
  intro n ε H _ _ _ σ P G hP h hσ ℓ hℓ
  obtain ⟨m, ls, a, hls, hrep⟩ := GlobalTheory.T.sobolevContinuousForm_sum_lieWord_inner n ε H σ P G hP h hσ ℓ hℓ
  refine ⟨fun φ hφ => ?_, fun w hw => ?_⟩
  · choose ψ _ hψ using fun i => word_gard hP h hσ hφ (ls i) (hls i)
    refine ⟨∑ i, ‖a i‖ * ∫ g : Formalism.REAL.UJ ε, |ψ i (umat g)| ∂(Formalism.REAL.muG ε), fun w => ?_⟩
    rw [hrep _ (gard_mem hP h hσ hφ w), Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [hψ, mul_assoc]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (norm_gard_le hσ _ w) (norm_nonneg _))
  · have e : ∀ g : Formalism.REAL.UJ ε, ℓ (σ (umat g) w) = ∑ i, ⟪a i, word (trRep σ P) (ls i) (σ (umat g) w)⟫_ℂ :=
      fun g => hrep _ (sigma_mem hP h hσ hw g.2)
    have hc : ∀ i, Continuous fun g : Formalism.REAL.UJ ε => ⟪a i, word (trRep σ P) (ls i) (σ (umat g) w)⟫_ℂ :=
      fun i => continuous_const.inner (GlobalTheory.T.smooth_vector_word_action_continuous n ε H σ P G hP h hσ (ls i) (hls i) w hw)
    simp only [e]
    refine ⟨continuous_finsetSum _ fun i _ => hc i, fun φ hφ => ?_⟩
    rw [hrep _ (gard_mem hP h hσ hφ w)]
    simp only [Finset.smul_sum]
    rw [integral_finsetSum _ fun i _ => hφ.integrable (hc i)]
    exact Finset.sum_congr rfl fun i _ => inner_word_gard hP h hσ hφ (ls i) (hls i) hw (a i)

end GlobalTheory.SobGarding
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevContinuousFormGardingVectorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolevContinuous_form_gardingVector : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ (lieG G) (trRep σ P) ℓ → (∀ φ, IsTest φ → ∃ C : ℝ, ∀ w, ‖ℓ (gard ε σ φ w)‖ ≤ C * ‖w‖) ∧ ∀ w ∈ smSub G (trRep σ P), (Continuous fun g : Formalism.REAL.UJ ε => ℓ (σ (umat g) w)) ∧ ∀ φ, IsTest φ → ℓ (gard ε σ φ w) = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ℓ (σ (umat g) w) ∂(Formalism.REAL.muG ε) := by
  first | exact @GlobalTheory.SobGarding.sobCont_gard | exact GlobalTheory.SobGarding.sobCont_gard | (intros; apply GlobalTheory.SobGarding.sobCont_gard <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinUnitIsDetRoot
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.LatticeUnitRoot

theorem exists_finUnit_isDetRoot : ∀ (D : D7) (S : HSp D) (Λ : Lt D.host.E S.rank), IsSelfDualC S Λ → ∀ k ∈ GfC S, GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt S k) Λ Λ → ∃ x : (AE D)ˣ, FinUnit x ∧ IsDetRoot S k x := by
  intro D V Λ hΛ k hk hm
  have hu : ∀ z ∈ GlobalTheory.Ker.hatV Λ, ∃ y ∈ GlobalTheory.Ker.hatV Λ, (finHom V k).1.mulVec z - z = (1 : ℕ) • y := fun z hz =>
    ⟨_, sub_mem ((hm _).2 ⟨z, hz, rfl⟩) hz, (one_nsmul _).symm⟩
  classical
  have hfull : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
      IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
    intro V Λ hΛ
    haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
    refine ⟨?_⟩
    obtain ⟨s, hs⟩ := hΛ.1.fg
    apply eq_top_iff.mpr
    intro y _
    let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
      ∑ i, ∑ j, star (x i) * V.gram i j * y j
    obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
    have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
      exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
    let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
      carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
      zero_mem' := by refine ⟨0, ?_⟩; simp [f]
      add_mem' := by
        rintro x z ⟨b, hb⟩ ⟨c, hc⟩
        refine ⟨b + c, ?_⟩
        change (b : D.host.E) + c = _
        rw [hb, hc]
        simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
      smul_mem' := by
        rintro c x ⟨b, hb⟩
        refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
        simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change star (c : D.host.E) * _ = _
        ring }
    have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
      intro x hx
      obtain ⟨b, hb⟩ := ha x hx
      exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
    have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
      apply (hΛ.2 _).2
      intro x hx
      have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
      obtain ⟨b, hb⟩ := hxP
      refine ⟨b, ?_⟩
      rw [hb]
      dsimp only [f, Pi.smul_apply]
      simp only [smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
      Submodule.subset_span hy
    have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
      (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
    change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
      ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
    rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
    exact this
  obtain ⟨w, hw, hwe⟩ := GlobalTheory.MarkDet.det_sub_one_of_cong D.host.F Λ hΛ.1.fg (Submodule.IsFullLattice.span_eq_top (self := hfull V Λ hΛ)) 1 one_ne_zero _ hu
  rw [← GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers] at hw
  have hn := GlobalTheory.RecDict.det_finHom_norm V k
  obtain ⟨y, y', hy, hy', hyy, hroot, -⟩ := GlobalTheory.OddRoot.exists_root_odd D 1 odd_one _ w hw hwe hn
  obtain ⟨Y, hY1, hY2, hY3⟩ := GlobalTheory.DetRootCong.exists_idele D y y' hyy
  refine ⟨Y, ⟨hY1, hY2 ▸ hy, hY3 ▸ hy'⟩, ?_⟩
  have hdet : (finHom V k).1.det = finPart D (matHom V k).1.det := ((finPart D).map_det _).symm
  have hdet' : (infHom V k).1.det = infPart D (matHom V k).1.det := ((infPart D).map_det _).symm
  have hk1 : infHom V k = 1 := hk
  rw [hk1, Units.val_one, Matrix.det_one] at hdet'
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  apply e.injective
  refine Prod.ext (((he _).1.trans ?_).trans (he _).1.symm) (((he _).2.trans ?_).trans (he _).2.symm)
  · change infPart D (Y : AE D) = infPart D ((matHom V k).1.det * sigR (AF D.host.F) D.sp.cm.sig (Y : AE D))
    rw [RingHom.map_mul, ← hdet', GlobalTheory.UnitDetRoot.infPart_sigR_one D _ hY1, hY1, _root_.mul_one]
  · change finPart D (Y : AE D) = finPart D ((matHom V k).1.det * sigR (AF D.host.F) D.sp.cm.sig (Y : AE D))
    rw [RingHom.map_mul, ← hdet, GlobalTheory.DetRootCong.finPart_sigR, hY2]
    exact hroot

end GlobalTheory.LatticeUnitRoot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalNegFirstFamilyFrameCartanMove
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalNegFirstFamilyFrameCartanMove
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

noncomputable section

namespace GlobalTheory.OneMapRef.Frames

open GlobalTheory.Ker.ONBasis

variable {D : D7} {T : HSp D}

theorem negM_sq (T : HSp D) (q : ℕ) : negM T q * negM T q = 1 := by
  unfold negM
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  unfold sgn
  split_ifs <;> simp

theorem negM_herm (T : HSp D) (q : ℕ) : (negM T q)ᴴ = negM T q := by
  unfold negM
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp

theorem compAt_eq (θ : InfFam D) (ρ : D.what₂.Tau) (h : GA D T) :
    compAt θ ρ (Formalism.L2.Theta.mt T h) = infMat D.sp.cm.sig T.gram (θ ρ) h := rfl

theorem compAt_unitary' {θ : InfFam D} (hθ : IsInfFam θ) (ρ : D.what₂.Tau) (g : GA D T) :
    (compAt θ ρ (Formalism.L2.Theta.mt T g))ᴴ * gramAt D T ρ * compAt θ ρ (Formalism.L2.Theta.mt T g) = gramAt D T ρ := by
  rw [GlobalTheory.FockCompare.RealAction.gramAt_eq hθ]
  exact GlobalTheory.FockCompare.RealAction.unitary_map (cA D) ((θ ρ).comp (infPart D))
    (GlobalTheory.FockCompare.comp_cA hθ ρ) _ _ (mt_rel T g)

theorem isONeg_mvZ {θ : InfFam D} (hθ : IsInfFam θ) {q : ℕ} {Z : Fam T} (hZ : IsONeg T q Z) (g : GA D T) :
    IsONeg T q (mvZ θ g Z) := by
  intro τ
  unfold mvZ
  rw [Matrix.conjTranspose_mul, ← hZ τ]
  conv_rhs => rw [← compAt_unitary' hθ τ g]
  simp only [Matrix.mul_assoc]

theorem mvZ_mul (θ : InfFam D) (Z : Fam T) (g g' : GA D T) : mvZ θ (g' * g) Z = mvZ θ g' (mvZ θ g Z) := by
  funext τ
  unfold mvZ
  have e : Formalism.L2.Theta.mt T (g' * g) = Formalism.L2.Theta.mt T g' * Formalism.L2.Theta.mt T g := by simp [Formalism.L2.Theta.mt]
  rw [e, ← Matrix.mul_assoc]
  congr 1
  exact Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem mvZ_fin (θ : InfFam D) (Z : Fam T) {g : GA D T} (hg : g ∈ GfC T) : mvZ θ g Z = Z := by
  funext τ
  have h1 : (Formalism.L2.Theta.mt T g).map (infPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hg)
  have h2 : compAt θ τ (Formalism.L2.Theta.mt T g) = ((Formalism.L2.Theta.mt T g).map (infPart D)).map (θ τ) := rfl
  unfold mvZ
  rw [h2, h1, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem cartZ_mvZ {θ : InfFam D} (hθ : IsInfFam θ) {q : ℕ} {Z : Fam T} (hZ : IsONeg T q Z) (g : GA D T)
    (τ : D.what₂.Tau) :
    cartZ T q (mvZ θ g Z) τ * compAt θ τ (Formalism.L2.Theta.mt T g) = compAt θ τ (Formalism.L2.Theta.mt T g) * cartZ T q Z τ := by
  have hu' := isUnit_det (negM_sq T q) (isONeg_mvZ hθ hZ g τ)
  have e : (mvZ θ g Z τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt T g) = (Z τ)⁻¹ := by
    symm
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.mul_assoc]
    exact Matrix.nonsing_inv_mul _ hu'
  unfold cartZ
  rw [Matrix.mul_assoc, e]
  unfold mvZ
  simp only [Matrix.mul_assoc]

theorem fin_of_mvZ {θ : InfFam D} (hθ : IsInfFam θ) {q : ℕ} {Z : Fam T} (hZ : IsONeg T q Z) {g : GA D T}
    (h : mvZ θ g Z = Z) : g ∈ GfC T := by
  refine (GlobalTheory.SmoothForms.RealPts.glue θ hθ T).1 g fun τ => ?_
  have hu := isUnit_det (negM_sq T q) (hZ τ)
  have h1 : compAt θ τ (Formalism.L2.Theta.mt T g) * Z τ = Z τ := congrFun h τ
  rw [← compAt_eq]
  calc _ = compAt θ τ (Formalism.L2.Theta.mt T g) * Z τ * (Z τ)⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = 1 := by rw [h1, Matrix.mul_nonsing_inv _ hu]

theorem exists_move {θ : InfFam D} (hθ : IsInfFam θ) {q : ℕ} {Z Z' : Fam T} (hZ : IsONeg T q Z)
    (hZ' : IsONeg T q Z') : ∃ a ∈ GinfC T, Z' = mvZ θ a Z := by
  have hu := fun τ => isUnit_det (negM_sq T q) (hZ τ)
  obtain ⟨a, ha, h⟩ := (GlobalTheory.SmoothForms.RealPts.glue θ hθ T).2 (fun τ => Z' τ * (Z τ)⁻¹) (fun τ => by
    show (Z' τ * (Z τ)⁻¹)ᴴ * gramAt D T τ * (Z' τ * (Z τ)⁻¹) = gramAt D T τ
    have h2 := Matrix.mul_nonsing_inv _ (hu τ)
    calc _ = (Z τ)⁻¹ᴴ * ((Z' τ)ᴴ * gramAt D T τ * Z' τ) * (Z τ)⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (Z τ * (Z τ)⁻¹)ᴴ * gramAt D T τ * (Z τ * (Z τ)⁻¹) := by
          rw [hZ' τ, ← hZ τ]
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one])
  refine ⟨a, ha, funext fun τ => ?_⟩
  unfold mvZ
  rw [compAt_eq, h τ, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hu τ), Matrix.mul_one]

theorem isOrtho_frOf {X : Data D.host.E T.rank} (eT : D.what₂.Tau ≃ X.Ψ) (hM : ModelW T rfl X)
    (he : ∀ ρ, (eT ρ).1 = tauE D ρ) {Z : Fam T} (hZ : IsONeg T X.p0 Z) : X.IsOrtho (frOf rfl eT Z) := by
  intro σ
  obtain ⟨τ, rfl⟩ := eT.surjective σ
  have hm : mat (frOf rfl eT Z) (eT τ) = Z τ := by
    ext a b
    simp [mat, frOf]
  have hG : ∀ a b, tauE D τ (X.Gm a b) = -gramAt D T τ b a := fun a b => by
    rw [hM.1]
    simp [gramAt]
  rw [hm, he]
  ext a b
  have h1 := congrFun (congrFun (hZ τ) b) a
  have h2 : FD.gram (tauE D τ) X.Gm (Z τ) a b = -((Z τ)ᴴ * gramAt D T τ * Z τ) b a := by
    simp only [FD.gram, hermC, FD.col, Matrix.of_apply, hG, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Finset.sum_mul, ← Finset.sum_neg_distrib, RCLike.star_def]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h2, h1, negM]
  by_cases hab : a = b
  · subst hab
    simp
  · rw [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab), neg_zero]

theorem isUnitFr_of_isOrtho {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    {x : Frame X.Ψ r} (hx : X.IsOrtho x) : IsUnitFr X x := by
  intro τ i
  unfold dmin
  have h : FD.gram τ.1 X.Gm (mat x τ) = sgnM X := hx τ
  rw [h, GlobalTheory.SW.Slab.lminor_sgnM]
  rcases GlobalTheory.SW.Slab.psgn_sq X.p0 i with h | h <;> rw [h] <;> norm_num

end GlobalTheory.OneMapRef.Frames


open GlobalTheory.OneMapRef.Frames GlobalTheory.Ker.ONBasis in
theorem GlobalTheory.OneMapRef.oneg_frames : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hS : IsSet ψ θ S T hr X eT bas), ∀ Z : Fam T, IsONeg T X.p0 Z → frOf hr eT Z ∈ X.dom ∧ IsUnitFr X (frOf hr eT Z) ∧ X.IsOrtho (frOf hr eT Z) ∧ (∀ ρ, IsCartanInv (gramAt D T ρ) (cartZ T X.p0 Z ρ)) ∧ ∀ h : GA D T, IsONeg T X.p0 (mvZ θ h Z) ∧ (∀ ρ, cartZ T X.p0 (mvZ θ h Z) ρ * compAt θ ρ (Formalism.L2.Theta.mt T h) = compAt θ ρ (Formalism.L2.Theta.mt T h) * cartZ T X.p0 Z ρ) ∧ (∀ h', mvZ θ (h' * h) Z = mvZ θ h' (mvZ θ h Z)) ∧ (h ∈ GfC T → mvZ θ h Z = Z) ∧ (mvZ θ h Z = Z → h ∈ GfC T) ∧ ∀ Z', IsONeg T X.p0 Z' → ∃ a ∈ GinfC T, Z' = mvZ θ a Z := by
  intro D S T r g hr ψ θ X eT bas idx hS Z hZ
  subst hr
  obtain ⟨-, hθ, -, -, hM, -, he, -⟩ := hS
  have ho := isOrtho_frOf eT hM he hZ
  exact ⟨mem_dom X ho, isUnitFr_of_isOrtho X ho, ho,
    fun ρ => isCartanInv (negM_sq T _) (negM_herm T _) (hZ ρ),
    fun h => ⟨isONeg_mvZ hθ hZ h, cartZ_mvZ hθ hZ h, mvZ_mul θ Z h, mvZ_fin θ Z, fin_of_mvZ hθ hZ,
      fun _ hZ' => exists_move hθ hZ hZ'⟩⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalNegFirstFamilyFrameCartanMoveStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthonormalNegFirstFamily_frame_cartan_move : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hS : IsSet ψ θ S T hr X eT bas), ∀ Z : Fam T, IsONeg T X.p0 Z → frOf hr eT Z ∈ X.dom ∧ IsUnitFr X (frOf hr eT Z) ∧ X.IsOrtho (frOf hr eT Z) ∧ (∀ ρ, IsCartanInv (gramAt D T ρ) (cartZ T X.p0 Z ρ)) ∧ ∀ h : GA D T, IsONeg T X.p0 (mvZ θ h Z) ∧ (∀ ρ, cartZ T X.p0 (mvZ θ h Z) ρ * compAt θ ρ (Formalism.L2.Theta.mt T h) = compAt θ ρ (Formalism.L2.Theta.mt T h) * cartZ T X.p0 Z ρ) ∧ (∀ h', mvZ θ (h' * h) Z = mvZ θ h' (mvZ θ h Z)) ∧ (h ∈ GfC T → mvZ θ h Z = Z) ∧ (mvZ θ h Z = Z → h ∈ GfC T) ∧ ∀ Z', IsONeg T X.p0 Z' → ∃ a ∈ GinfC T, Z' = mvZ θ a Z := by
  first | exact @GlobalTheory.OneMapRef.oneg_frames | exact GlobalTheory.OneMapRef.oneg_frames | (intros; apply GlobalTheory.OneMapRef.oneg_frames <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevEmbeddingDiscreteSeriesHilbertSchmidt
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevEmbeddingDiscreteSeriesHilbertSchmidt
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.SobHS

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem exists_orthonormal_expansion {ι : Type} [Fintype ι] (f : ι → H) :
    ∃ (m : ℕ) (h : Fin m → H) (φ : ι → Fin m → ℂ), Orthonormal ℂ h ∧ (∀ j, f j = ∑ p, φ j p • h p) ∧
      ∀ j, ∑ p, ‖φ j p‖ ^ 2 = ‖f j‖ ^ 2 := by
  let U : Submodule ℂ H := Submodule.span ℂ (Set.range f)
  haveI : FiniteDimensional ℂ U := FiniteDimensional.span_of_finite ℂ (Set.finite_range f)
  let b := stdOrthonormalBasis ℂ U
  let u : ι → U := fun j => ⟨f j, Submodule.subset_span ⟨j, rfl⟩⟩
  refine ⟨_, fun p => (b p : H), fun j p => ⟪b p, u j⟫_ℂ, b.orthonormal.comp_linearIsometry U.subtypeₗᵢ,
    fun j => ?_, fun j => b.sum_sq_norm_inner_right (u j)⟩
  have := congrArg Subtype.val (b.sum_repr' (u j))
  simpa using this.symm

theorem integral_sq_sum {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)} {μ : Measure (UJ ε)} {d : ℝ}
    (hd : IsFdeg μ σ d) {m : ℕ} {h : Fin m → H} (hh : Orthonormal ℂ h) (y : Fin m → H) :
    Integrable (fun g : UJ ε => ‖∑ p, ⟪h p, σ (umat g) (y p)⟫_ℂ‖ ^ 2) μ ∧
      ∫ g : UJ ε, ‖∑ p, ⟪h p, σ (umat g) (y p)⟫_ℂ‖ ^ 2 ∂μ = (∑ p, ‖y p‖ ^ 2) / d := by
  have e : ∀ g : UJ ε, ((‖∑ p, ⟪h p, σ (umat g) (y p)⟫_ℂ‖ ^ 2 : ℝ) : ℂ) =
      ∑ p, ∑ q, coefOn σ (y p) (h p) g * star (coefOn σ (y q) (h q) g) := by
    intro g
    rw [← Finset.sum_mul_sum, ← star_sum, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rfl
  have i1 : ∀ p, Integrable (fun g : UJ ε => ∑ q, coefOn σ (y p) (h p) g * star (coefOn σ (y q) (h q) g)) μ :=
    fun p => integrable_finsetSum _ fun q _ => (hd.2 _ _ _ _).1
  have i2 : Integrable (fun g : UJ ε => ((‖∑ p, ⟪h p, σ (umat g) (y p)⟫_ℂ‖ ^ 2 : ℝ) : ℂ)) μ := by
    simp only [e]
    exact integrable_finsetSum _ fun p _ => i1 p
  refine ⟨by simpa only [RCLike.re_to_complex, Complex.ofReal_re] using i2.re, ?_⟩
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp only [e]
  rw [integral_finsetSum _ fun p _ => i1 p]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_finsetSum _ fun q _ => (hd.2 _ _ _ _).1]
  simp only [(hd.2 _ _ _ _).2, orthonormal_iff_ite.1 hh]
  rw [Finset.sum_eq_single p (fun q _ hq => by simp [Ne.symm hq]) (by simp)]
  simp [inner_self_eq_norm_sq_to_K]

theorem sobolev_hilbertSchmidt : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧ ∀ (ι : Type) [Fintype ι] (f x : ι → H) (A : ℝ), 0 ≤ A → (∀ j, Sm ε σ (x j)) → (∀ l ∈ S, ∀ z : ι → ℂ, ‖∑ j, z j • Dw σ l (x j)‖ ^ 2 ≤ A * ∑ j, ‖z j‖ ^ 2) → ‖∑ j, ⟪f j, x j⟫_ℂ‖ ^ 2 ≤ C * A * ∑ j, ‖f j‖ ^ 2 := by
  intro n ε H _ _ _ σ hσ
  obtain ⟨S, C, hS, hC, H1⟩ := GlobalTheory.T.sobolev_inequality_at_one_indefiniteUnitary n ε
  obtain ⟨d, hd⟩ := hσ.2.2.2.1
  have hd0 := hd.1
  refine ⟨S, C * S.length / d, hS, by positivity, fun ι _ f x A hA hx hb => ?_⟩
  obtain ⟨m, h, φ, hh, hf, hφ⟩ := exists_orthonormal_expansion f
  let F : List (Mx n) → Mx n → ℂ := fun l g => ∑ j, ⟪f j, σ g (Dw σ l (x j))⟫_ℂ
  have eF : ∀ l g, F l g = ∑ p, ⟪h p, σ g (∑ j, (starRingEnd ℂ) (φ j p) • Dw σ l (x j))⟫_ℂ := by
    intro l g
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [F, map_sum, map_smul, inner_sum, inner_smul_right]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hf j, sum_inner]
    simp only [inner_smul_left]
  have hI := fun l => integral_sq_sum hd hh fun p => ∑ j, (starRingEnd ℂ) (φ j p) • Dw σ l (x j)
  simp only [← eF] at hI
  have key := H1 F (fun l _ => continuousOn_finsetSum _ fun j _ =>
      (innerSL ℂ (f j)).continuous.comp_continuousOn (hσ.1.2.2 _)) ?_ fun l _ => (hI l).1
  · have e1 : F [] 1 = ∑ j, ⟪f j, x j⟫_ℂ := by simp only [F, sigma_one hσ.1]; rfl
    rw [e1] at key
    refine key.trans ?_
    have h2 : (S.map fun l => ∫ g : UJ ε, ‖F l (umat g)‖ ^ 2 ∂(muG ε)).sum ≤
        (S.map fun l => ∫ g : UJ ε, ‖F l (umat g)‖ ^ 2 ∂(muG ε)).length • ((A * ∑ j, ‖f j‖ ^ 2) / d) := by
      refine List.sum_le_card_nsmul _ _ fun r hr => ?_
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hr
      rw [(hI l).2]
      refine div_le_div_of_nonneg_right ?_ hd0.le
      refine (Finset.sum_le_sum fun p _ => hb l hl _).trans (le_of_eq ?_)
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [RCLike.norm_conj, hφ]
    rw [List.length_map, nsmul_eq_mul] at h2
    refine (mul_le_mul_of_nonneg_left h2 hC).trans (le_of_eq ?_)
    ring
  · intro l hl X hX g hg
    have e : ∀ t : ℝ, F l (g * NormedSpace.exp (t • X)) =
        ∑ j, ⟪f j, σ g (σ (NormedSpace.exp (t • X)) (Dw σ l (x j)))⟫_ℂ := fun t => by
      simp only [F, sigma_mul hσ.1 hg (exp_mem_UJ hX t)]
    simp only [e]
    refine HasDerivAt.fun_sum fun j _ => ?_
    have h1 := hasDerivAt_orbit hσ.1 ((hx j).word hσ.1 hl) hX 0
    rw [zero_smul, NormedSpace.exp_zero, sigma_one hσ.1] at h1
    exact (((innerSL ℂ (f j)).comp (σ g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h1

end GlobalTheory.TypeSum.SobHS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevEmbeddingDiscreteSeriesHilbertSchmidtStatement
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolev_embedding_discrete_series_hilbertSchmidt : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧ ∀ (ι : Type) [Fintype ι] (f x : ι → H) (A : ℝ), 0 ≤ A → (∀ j, Sm ε σ (x j)) → (∀ l ∈ S, ∀ z : ι → ℂ, ‖∑ j, z j • Dw σ l (x j)‖ ^ 2 ≤ A * ∑ j, ‖z j‖ ^ 2) → ‖∑ j, ⟪f j, x j⟫_ℂ‖ ^ 2 ≤ C * A * ∑ j, ‖f j‖ ^ 2 := by
  first | exact @GlobalTheory.TypeSum.SobHS.sobolev_hilbertSchmidt | exact GlobalTheory.TypeSum.SobHS.sobolev_hilbertSchmidt | (intros; apply GlobalTheory.TypeSum.SobHS.sobolev_hilbertSchmidt <;> assumption)
end
end
