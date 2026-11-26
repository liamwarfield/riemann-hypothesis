module

public import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicWeightPolyMatrixMultiplicative
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotMemSqOfDerivative
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicTowerLevelGeneratorProperties

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LocDualInt

section Pow

variable {O : Type} [CommRing O] {G : Type} [Group G] {M : Type} [AddCommGroup M] [Module O M]

def powSub (a : O) (n : ℕ) : Submodule O M := LinearMap.range ((a ^ n) • LinearMap.id : M →ₗ[O] M)

theorem mem_powSub {a : O} {n : ℕ} {x : M} : x ∈ powSub (M := M) a n ↔ ∃ y : M, a ^ n • y = x := by
  simp [powSub]

theorem smul_mem_powSub (a : O) (n : ℕ) (y : M) : a ^ n • y ∈ powSub (M := M) a n :=
  mem_powSub.2 ⟨y, rfl⟩

theorem powSub_anti (a : O) {m n : ℕ} (h : m ≤ n) : powSub (M := M) a n ≤ powSub a m := by
  intro x hx
  obtain ⟨y, rfl⟩ := mem_powSub.1 hx
  refine mem_powSub.2 ⟨a ^ (n - m) • y, ?_⟩
  rw [smul_smul, ← pow_add, Nat.add_sub_cancel' h]

theorem powSub_stable (ρ : Representation O G M) (a : O) (n : ℕ) (g : G) (x : M)
    (hx : x ∈ powSub (M := M) a n) : ρ g x ∈ powSub (M := M) a n := by
  obtain ⟨y, rfl⟩ := mem_powSub.1 hx
  exact mem_powSub.2 ⟨ρ g y, by rw [map_smul]⟩

def quotRep (ρ : Representation O G M) (a : O) (n : ℕ) :
    Representation O G (M ⧸ powSub (M := M) a n) where
  toFun g := (powSub a n).mapQ (powSub a n) (ρ g) (fun x hx => powSub_stable ρ a n g x hx)
  map_one' := by
    apply Submodule.linearMap_qext
    ext x
    simp
  map_mul' g h := by
    apply Submodule.linearMap_qext
    ext x
    simp [Module.End.mul_apply]

@[simp] theorem quotRep_mk (ρ : Representation O G M) (a : O) (n : ℕ) (g : G) (x : M) :
    quotRep ρ a n g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ρ g x) := rfl

def qlift {N : Submodule O M} (z : M ⧸ N) : M := (Submodule.Quotient.mk_surjective N z).choose

@[simp] theorem mk_qlift {N : Submodule O M} (z : M ⧸ N) : Submodule.Quotient.mk (qlift z) = z :=
  (Submodule.Quotient.mk_surjective N z).choose_spec

end Pow

section TopPow

variable {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul O M]

theorem continuous_factor (a : O) {m n : ℕ} (h : m ≤ n) :
    Continuous (Submodule.factor (powSub_anti (M := M) a h)) := by
  rw [(Submodule.isOpenQuotientMap_mkQ _).isQuotientMap.continuous_iff]
  exact continuous_quot_mk

theorem factor_mem_cocycles_pow_quot (ρ : Representation O G M) (a : O) {m n : ℕ} (h : m ≤ n)
    {z : G → M ⧸ powSub (M := M) a n} (hz : z ∈ Z1 (quotRep ρ a n)) :
    (fun g => Submodule.factor (powSub_anti (M := M) a h) (z g)) ∈ Z1 (quotRep ρ a m) := by
  refine ⟨(continuous_factor a h).comp hz.1, fun g g' => ?_⟩
  show Submodule.factor _ (z (g * g')) = Submodule.factor _ (z g) +
    quotRep ρ a m g (Submodule.factor (powSub_anti (M := M) a h) (z g'))
  rw [hz.2 g g', map_add (f := _)]
  congr 1
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (z g')
  rw [← hy]
  rfl

end TopPow

end GlobalTheory.LocDualInt

noncomputable section

namespace GlobalTheory.LocDualInt

section Lat

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {G : Type} [Group G] [TopologicalSpace G]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] (D : LatData O G VT VT')

def cupMod (c : G → VT ⧸ D.T) (a : O) (n : ℕ) (z : G → ↥D.T' ⧸ powSub (M := ↥D.T') a n) :
    G × G → KO O :=
  fun p => pairKO D.bT D.T (c p.1) (D.ρTl' p.1 (qlift (z p.2)))

theorem pairKO_eq_zero_of_mem {a : O} {r : ℕ} {x : VT ⧸ D.T} (hx : a ^ r • x = 0) {t : ↥D.T'}
    (ht : t ∈ powSub (M := ↥D.T') a r) : pairKO D.bT D.T x t = 0 := by
  obtain ⟨y, rfl⟩ := mem_powSub.1 ht
  rw [map_smul, ← LinearMap.smul_apply, ← map_smul, hx, map_zero, LinearMap.zero_apply]

theorem pairKO_eq_of_sub_mem {a : O} {r : ℕ} {x : VT ⧸ D.T} (hx : a ^ r • x = 0) {t t' : ↥D.T'}
    (ht : t - t' ∈ powSub (M := ↥D.T') a r) : pairKO D.bT D.T x t = pairKO D.bT D.T x t' := by
  rw [← sub_eq_zero, ← map_sub]
  exact pairKO_eq_zero_of_mem D hx ht

theorem cupMod_factor {c : G → VT ⧸ D.T} {a : O} {r m n : ℕ} (hc : ∀ g, a ^ r • c g = 0)
    (hrm : r ≤ m) (hmn : m ≤ n) (z : G → ↥D.T' ⧸ powSub (M := ↥D.T') a n) :
    cupMod D c a m (fun g => Submodule.factor (powSub_anti (M := ↥D.T') a hmn) (z g)) =
      cupMod D c a n z := by
  funext p
  refine pairKO_eq_of_sub_mem D (hc p.1) ?_
  rw [← map_sub]
  refine powSub_stable _ a r p.1 _ (powSub_anti a hrm ?_)
  apply (Submodule.Quotient.eq _).1
  have e : (Submodule.Quotient.mk (qlift (z p.2)) : ↥D.T' ⧸ powSub (M := ↥D.T') a m) =
      Submodule.factor (powSub_anti (M := ↥D.T') a hmn) (z p.2) := by
    conv_rhs => rw [← mk_qlift (z p.2)]
    rfl
  rw [e, mk_qlift]

end Lat

end GlobalTheory.LocDualInt
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEmbOfFixed
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL.Letters

theorem exists_emb_of_fixed {F E L : Type} [Field F] [Field E] [Field L] [Algebra F E] [Algebra F L]
    [FiniteDimensional F E] (σ : E →ₐ[F] E) (hσ : Function.Bijective σ)
    (hfix : ∀ x, σ x = x → ∃ c : F, algebraMap F E c = x) (e : E →ₐ[F] L) :
    ∃ emb : ZMod (Module.finrank F E) → (E →ₐ[F] L),
      Function.Bijective emb ∧ ∀ i, (emb (i + 1)).comp σ = emb i := by
  classical
  let g : E ≃ₐ[F] E := AlgEquiv.ofBijective σ hσ
  have hbot : IntermediateField.fixedField (Subgroup.zpowers g) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    exact IntermediateField.mem_bot.2 (hfix x (hx g (Subgroup.mem_zpowers g)))
  have hord : orderOf g = Module.finrank F E := by
    have h := IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers g)
    rw [hbot, IntermediateField.finrank_bot', Nat.card_zpowers] at h
    exact h.symm
  haveI : NeZero (Module.finrank F E) := ⟨Module.finrank_pos.ne'⟩
  let emb : ZMod (Module.finrank F E) → (E →ₐ[F] L) := fun i =>
    e.comp (g⁻¹ ^ i.val : E ≃ₐ[F] E).toAlgHom
  have hord' : orderOf g⁻¹ = Module.finrank F E := by rw [orderOf_inv, hord]
  have hinj : Function.Injective emb := by
    intro i j h
    have h1 : (g⁻¹ ^ i.val : E ≃ₐ[F] E) = g⁻¹ ^ j.val :=
      AlgEquiv.ext fun x => e.injective (DFunLike.congr_fun h x)
    rw [pow_eq_pow_iff_modEq, hord', ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val] at h1
    exact h1
  refine ⟨emb, ?_, fun i => ?_⟩
  · refine hinj.bijective_of_nat_card_le ?_
    rw [Nat.card_zmod]
    exact card_algHom_le_finrank F E L
  · have h1 : (g⁻¹ ^ (i + 1).val : E ≃ₐ[F] E) = g⁻¹ ^ (i.val + 1) := by
      rw [pow_eq_pow_iff_modEq, hord', ← ZMod.natCast_eq_natCast_iff]
      simp
    have h2 : (g⁻¹ ^ (i + 1).val : E ≃ₐ[F] E) * g = g⁻¹ ^ i.val := by
      rw [h1, pow_succ, inv_mul_cancel_right]
    exact AlgHom.ext fun x => congrArg e (DFunLike.congr_fun h2 x)

variable {l : ℕ} [Fact l.Prime]

theorem sigma_fixed (P : LocPrime l) (K : FinExt l) (x : ↥(K0 K)) (hx : (P.PD K).σ x = x) :
    ∃ c : ℚ_[l], algebraMap ℚ_[l] ↥(K0 K) c = x := by
  haveI : Nontrivial P.R.B := by
    refine ⟨⟨(P.PD K).t, 0, fun h => (P.PD K).not_mem_filtration_two ?_⟩⟩
    rw [h, map_zero]
    exact zero_mem _
  obtain ⟨c, hc⟩ := (P.PD K).fund (algebraMap ↥(K0 K) P.R.B x) (by rw [(P.PD K).φ_K₀, hx]) (by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 P.R.BdR,
      Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (P.PD K).one_mem)
  refine ⟨c, (algebraMap ↥(K0 K) P.R.B).injective ?_⟩
  rw [← IsScalarTower.algebraMap_apply, hc]

end GlobalTheory.HWL.Letters

namespace GlobalTheory.HWL

theorem exists_letters : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∃ emb : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1), Function.Bijective emb ∧ ∀ i, (emb (i + 1)).comp (P.PD K).σ = emb i := by
  intro l _ P K s LL h
  haveI := (P.PD K).finK₀
  have hle : K0 K ≤ LL.1 := fun x hx =>
    h.2.2.2 (Ks K s).val ⟨x, (le_sup_left : K0 K ≤ Ks K s) hx⟩
  exact Letters.exists_emb_of_fixed _ (P.PD K).σ_bij (Letters.sigma_fixed P K)
    (IntermediateField.inclusion hle)

end GlobalTheory.HWL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltFrobeniusIntegerPowerLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltFrobeniusIntegerPowerLaws
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer.PwLaws
variable {l : ℕ} [Fact l.Prime]
theorem pw_apply_eq (k : ℤ) (x : Fl l) :
    pw k x = ((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ k : RingAut (Fl l)) x := rfl
theorem pw_zadd (a b : ℤ) (x : Fl l) : pw (a + b) x = pw a (pw b x) := by
  simp only [pw_apply_eq, zpow_add, RingAut.mul_apply]
theorem pw_one (x : Fl l) : pw 1 x = x ^ l := by
  rw [pw_apply_eq, zpow_one]
  show frobeniusEquiv (Fl l) l x = _
  rw [frobeniusEquiv_apply, frobenius_def]
theorem pw_nat (n : ℕ) (x : Fl l) : pw (n : ℤ) x = x ^ l ^ n := by
  induction n with
  | zero => simp [pw_apply_eq]
  | succ n ih =>
    have h : ((n + 1 : ℕ) : ℤ) = 1 + (n : ℤ) := by push_cast; ring
    rw [h, pw_zadd, ih, pw_one, ← pow_mul, pow_succ]

theorem pw_zero_int (x : Fl l) : pw 0 x = x := by
  simp [pw_apply_eq]
theorem sh_pow' (x : Fl l) (m : ℕ) : sh (x ^ m) = sh x ^ m := by
  simp only [sh, map_pow, SubmonoidClass.coe_pow]
theorem norm_sh_pw_nat (n : ℕ) (x : Fl l) : ‖sh (pw (n : ℤ) x)‖ = ‖sh x‖ ^ (l ^ n) := by
  rw [pw_nat, sh_pow', norm_pow]
theorem norm_sh_pw (k : ℤ) (x : Fl l) : ‖sh (pw k x)‖ = ‖sh x‖ ^ ((l : ℝ) ^ k) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [norm_sh_pw_nat, zpow_natCast, ← Real.rpow_natCast]
    push_cast
    rfl
  · set y := pw (-(n : ℤ)) x with hy
    have hx : x = pw (n : ℤ) y := by
      rw [hy, ← pw_zadd, add_neg_cancel, pw_zero_int]
    have hne : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
    have e : ((l : ℝ) ^ (-(n : ℤ))) = (((l ^ n : ℕ) : ℝ))⁻¹ := by
      rw [zpow_neg, zpow_natCast]
      push_cast
      rfl
    conv_rhs => rw [hx, norm_sh_pw_nat, e]
    exact (Real.pow_rpow_inv_natCast (norm_nonneg _) hne).symm

theorem pw_laws : ∀ (l : ℕ) [Fact l.Prime], (∀ (k : ℤ) (x y : Fl l), pw k (x + y) = pw k x + pw k y) ∧ (∀ (k : ℤ) (x y : Fl l), pw k (x * y) = pw k x * pw k y) ∧ (∀ k : ℤ, pw k (0 : Fl l) = 0) ∧ (∀ (a b : ℤ) (x : Fl l), pw (a + b) x = pw a (pw b x)) ∧ (∀ (n : ℕ) (x : Fl l), pw n x = x ^ l ^ n) ∧ (∀ (k : ℤ) (n : ℕ) (x : Fl l), pw k (x ^ n) = pw k x ^ n) ∧ (∀ (k : ℤ) (x : Fl l), ‖sh (pw k x)‖ = ‖sh x‖ ^ ((l : ℝ) ^ k)) := by
  intro l _
  refine ⟨fun k x y => ?_, fun k x y => ?_, fun k => ?_, pw_zadd, pw_nat, fun k n x => ?_, norm_sh_pw⟩
  · simp only [pw_apply_eq, map_add (f := _)]
  · simp only [pw_apply_eq, map_mul]
  · simp only [pw_apply_eq, map_zero]
  · simp only [pw_apply_eq, map_pow]

end GlobalTheory.PSer.PwLaws
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltFrobeniusIntegerPowerLawsStatement
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tiltFrobeniusIntegerPower_laws : ∀ (l : ℕ) [Fact l.Prime], (∀ (k : ℤ) (x y : Fl l), pw k (x + y) = pw k x + pw k y) ∧ (∀ (k : ℤ) (x y : Fl l), pw k (x * y) = pw k x * pw k y) ∧ (∀ k : ℤ, pw k (0 : Fl l) = 0) ∧ (∀ (a b : ℤ) (x : Fl l), pw (a + b) x = pw a (pw b x)) ∧ (∀ (n : ℕ) (x : Fl l), pw n x = x ^ l ^ n) ∧ (∀ (k : ℤ) (n : ℕ) (x : Fl l), pw k (x ^ n) = pw k x ^ n) ∧ (∀ (k : ℤ) (x : Fl l), ‖sh (pw k x)‖ = ‖sh x‖ ^ ((l : ℝ) ^ k)) := by
  first | exact @GlobalTheory.PSer.PwLaws.pw_laws | exact GlobalTheory.PSer.PwLaws.pw_laws | (intros; apply GlobalTheory.PSer.PwLaws.pw_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneInductionPrinciple
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneInductionPrinciple
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module

namespace GlobalTheory.WeilDeligne

section Reduction

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def WDRep.resZero {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : WDRep h V) (U : Submodule ℂ V) (hU : ∀ σ, ∀ v ∈ U, a.ρ σ v ∈ U) : WDRep h U where
  ρ := { toFun := fun σ => (a.ρ σ).restrict (hU σ)
         map_one' := by ext; simp
         map_mul' := fun σ τ => by ext; simp }
  N := 0
  smooth := a.smooth.of_le fun σ hσ => by ext; simp [hσ]
  semisimple σ := End.IsSemisimple.restrict (hU σ) (a.semisimple σ)
  nilpotent := IsNilpotent.zero
  comm σ := by simp

theorem WDRep.charpoly_eq_mul_of_isCompl {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (a : WDRep h V) (U U' : Submodule ℂ V)
    (hU : ∀ σ, ∀ v ∈ U, a.ρ σ v ∈ U) (hU' : ∀ σ, ∀ v ∈ U', a.ρ σ v ∈ U') (hc : IsCompl U U')
    (σ : Weil h) :
    (a.ρ σ).charpoly = ((a.resZero U hU).ρ σ).charpoly * ((a.resZero U' hU').ρ σ).charpoly := by
  rw [← LinearMap.charpoly_prodMap, ← LinearEquiv.charpoly_conj (Submodule.prodEquivOfIsCompl U U' hc)]
  congr 1
  refine LinearMap.ext fun v => ?_
  obtain ⟨x, rfl⟩ := (Submodule.prodEquivOfIsCompl U U' hc).surjective v
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  simp [Submodule.coe_prodEquivOfIsCompl', WDRep.resZero]

theorem finite_range_of_frob_pow_eq_one {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ) {m : ℕ} (hm : 0 < m)
    (h1 : ρ (frob (h := h)) ^ m = 1) : (Set.range ρ).Finite := by
  refine (Set.Finite.image2 (· * ·) (Set.finite_range fun j : Fin m => ρ (frob (h := h)) ^ (j : ℕ))
    hρ.finite_range).subset ?_
  rintro _ ⟨σ, rfl⟩
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (h := h) deg_frob σ
  have hker : frob (h := h) ^ m ∈ ρ.ker := by rw [MonoidHom.mem_ker, map_pow, h1]
  set k := deg σ
  have hk : frob (h := h) ^ k = frob (h := h) ^ ((k % m).toNat) * (frob (h := h) ^ m) ^ (k / m) := by
    rw [← zpow_natCast (frob (h := h)) m, ← zpow_mul, ← zpow_natCast (frob (h := h)) ((k % m).toNat),
      ← zpow_add, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hm.ne')),
      add_comm, Int.mul_ediv_add_emod]
  have hlt : (k % m).toNat < m := by
    have := Int.emod_lt_of_pos k (by exact_mod_cast hm : (0 : ℤ) < m)
    omega
  refine ⟨ρ (frob (h := h)) ^ ((k % m).toNat), ⟨⟨_, hlt⟩, rfl⟩, ρ (ineIncl h τ), ⟨τ, rfl⟩, ?_⟩
  have h2 : ρ ((frob (h := h) ^ m) ^ (k / m)) = 1 := (ρ.ker.zpow_mem hker _)
  show _ = ρ σ
  rw [hτ, hk, map_mul, map_mul, h2, mul_one, map_pow]

theorem exists_of_lpSum_twist_finite (S : WD h → Prop)
    (hsum : ∀ x y, S x → S y → S (x.lpSum y))
    (hfin : ∀ (n : ℕ) (a : WDRep h (Fin n → ℂ)) (μ : Weil h →* ℂˣ) (hμ : IsSmooth μ),
      (Set.range a.ρ).Finite → S (WD.mk (a.twist μ hμ))) :
    ∀ (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
      finrank ℂ V = d → ∀ (ρ : Representation ℂ (Weil h) V), IsSmooth ρ →
      (∀ σ, End.IsSemisimple (ρ σ)) → ∃ y : WD h, S y ∧ ∀ σ, y.charPol σ = (ρ σ).charpoly := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro V _ _ _ hd ρ hρ hs
  let a0 : WDRep h V := ⟨ρ, 0, hρ, hs, IsNilpotent.zero, by simp⟩
  obtain ⟨m, hm, hcomm⟩ := exists_pow_frob_commute ρ hρ
  have hsm : ρ (frob (h := h)) ^ m = ρ (frob (h := h) ^ m) := (map_pow _ _ _).symm
  by_cases hsc : ∃ c : ℂ, c ≠ 0 ∧ ρ (frob (h := h)) ^ m = c • (1 : Module.End ℂ V)
  · obtain ⟨c, hc0, hsc⟩ := hsc
    obtain ⟨c', hc'⟩ := IsAlgClosed.exists_pow_nat_eq c hm
    have hc'0 : c' ≠ 0 := by rintro rfl; exact hc0 (by rw [← hc', zero_pow hm.ne'])
    set u : ℂˣ := Units.mk0 c' hc'0
    let b : WDRep h V := a0.twist (unrChar h u⁻¹) (isSmooth_unrChar h _)
    have hb1 : b.ρ (frob (h := h)) ^ m = 1 := by
      show ((((unrChar h u⁻¹) (frob (h := h)) : ℂˣ) : ℂ) • ρ (frob (h := h))) ^ m = 1
      rw [_root_.smul_pow, hsc, smul_smul, unrChar_apply, deg_frob, zpow_one, ← Units.val_pow_eq_pow_val,
        inv_pow]
      have : u ^ m = Units.mk0 c hc0 := Units.ext (by simp [u, hc'])
      rw [this]
      simp [hc0]
    have hfinb := finite_range_of_frob_pow_eq_one b.ρ b.smooth hm hb1
    have hfins : (Set.range (WD.std b).2.ρ).Finite :=
      (hfinb.image ((finBasis ℂ V).equivFun.conjAlgEquiv ℂ)).subset (by rintro _ ⟨σ, rfl⟩; exact ⟨_, ⟨σ, rfl⟩, rfl⟩)
    refine ⟨WD.mk ((WD.std b).2.twist (unrChar h u) (isSmooth_unrChar h _)),
      hfin _ _ _ _ hfins, fun σ => ?_⟩
    rw [← WD.sound ((WD.iso_std b).twist _ _), WD.charPol_mk]
    show ((((unrChar h u) σ : ℂˣ) : ℂ) • ((((unrChar h u⁻¹) σ : ℂˣ) : ℂ) • ρ σ)).charpoly = _
    rw [smul_smul, ← Units.val_mul, unrChar_apply, unrChar_apply, ← mul_zpow, mul_inv_cancel,
      one_zpow, Units.val_one, one_smul]
  · have hnt : Nontrivial V := by
      by_contra hn
      rw [not_nontrivial_iff_subsingleton] at hn
      exact hsc ⟨1, one_ne_zero, LinearMap.ext fun v => Subsingleton.elim _ _⟩
    set s := ρ (frob (h := h)) ^ m with hs_def
    have hss : End.IsSemisimple s := by rw [hsm]; exact hs _
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue s
    have hinv : ∀ σ α, ∀ v ∈ End.eigenspace s α, ρ σ v ∈ End.eigenspace s α := by
      intro σ α v hv
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      rw [← Module.End.mul_apply, (hcomm σ).eq, Module.End.mul_apply, hv, map_smul]
    set U := End.eigenspace s c
    set U' := ⨆ α ∈ ({c}ᶜ : Set ℂ), End.eigenspace s α
    have hU : ∀ σ, ∀ v ∈ U, ρ σ v ∈ U := fun σ => hinv σ c
    have hU' : ∀ σ, ∀ v ∈ U', ρ σ v ∈ U' := by
      intro σ v hv
      have : U' ≤ U'.comap (ρ σ) := iSup₂_le fun α hα w hw =>
        (le_iSup₂_of_le α hα le_rfl : End.eigenspace s α ≤ U') (hinv σ α w hw)
      exact this hv
    have hcompl : IsCompl U U' := by
      refine ⟨(Module.End.eigenspaces_iSupIndep s).disjoint_biSup (by simp), ?_⟩
      rw [codisjoint_iff, eq_top_iff, ← hss.iSup_eigenspace_eq_top]
      refine iSup_le fun α => ?_
      by_cases hα : α = c
      · subst hα; exact le_sup_left
      · exact le_sup_of_le_right (le_iSup₂_of_le α hα le_rfl)
    have hc0 : c ≠ 0 := by
      rintro rfl
      obtain ⟨v, hv, hv0⟩ := hc.exists_hasEigenvector
      apply hv0
      have h1 := Module.End.mem_eigenspace_iff.mp hv
      rw [zero_smul] at h1
      have h1' : ρ (frob (h := h) ^ m) v = 0 := by rw [← hsm]; exact h1
      have := congrArg (ρ (frob (h := h) ^ m)⁻¹) h1'
      rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
        map_zero] at this
    have hUb : U ≠ ⊥ := hc
    have hU'b : U' ≠ ⊥ := by
      intro hb
      apply hsc
      refine ⟨c, hc0, LinearMap.ext fun v => ?_⟩
      have hv : v ∈ U := by
        have := hcompl.sup_eq_top
        rw [hb, sup_bot_eq] at this
        rw [this]; trivial
      rw [Module.End.mem_eigenspace_iff.mp hv]
      simp
    have hrk := Submodule.finrank_add_eq_of_isCompl hcompl
    have h1 : 0 < finrank ℂ U := Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hUb)
    have h2 : 0 < finrank ℂ U' :=
      Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hU'b)
    obtain ⟨y1, hS1, hy1⟩ := ih (finrank ℂ U) (by omega) U rfl (a0.resZero U hU).ρ
      (a0.resZero U hU).smooth (a0.resZero U hU).semisimple
    obtain ⟨y2, hS2, hy2⟩ := ih (finrank ℂ U') (by omega) U' rfl (a0.resZero U' hU').ρ
      (a0.resZero U' hU').smooth (a0.resZero U' hU').semisimple
    refine ⟨y1.lpSum y2, hsum _ _ hS1 hS2, fun σ => ?_⟩
    rw [WD.charPol_lpSum, hy1, hy2]
    exact (a0.charpoly_eq_mul_of_isCompl U U' hU hU' hcompl σ).symm

end Reduction

theorem WD.induction_lpSum_twist_finite : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (S : WD h → Prop), (∀ x y, S x → S y → S (x.lpSum y)) → (∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → S x → S y) → (∀ (n : ℕ) (a : WDRep h (Fin n → ℂ)) (μ : Weil h →* ℂˣ) (hμ : IsSmooth μ), (Set.range a.ρ).Finite → S (WD.mk (a.twist μ hμ))) → ∀ x, S x := by
  intro E Ω _ _ _ _ _ A w h S hsum hchar hfin x
  induction x using WD.ind with
  | hP n a =>
  obtain ⟨y, hy, hyc⟩ := exists_of_lpSum_twist_finite S hsum hfin _ (Fin n → ℂ) rfl a.ρ a.smooth
    a.semisimple
  exact hchar y _ (fun σ => by rw [hyc, WD.charPol_mk]) hy

end GlobalTheory.WeilDeligne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneInductionPrincipleStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_deligne_induction_principle : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (S : WD h → Prop), (∀ x y, S x → S y → S (x.lpSum y)) → (∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → S x → S y) → (∀ (n : ℕ) (a : WDRep h (Fin n → ℂ)) (μ : Weil h →* ℂˣ) (hμ : IsSmooth μ), (Set.range a.ρ).Finite → S (WD.mk (a.twist μ hμ))) → ∀ x, S x := by
  first | exact @GlobalTheory.WeilDeligne.WD.induction_lpSum_twist_finite | exact GlobalTheory.WeilDeligne.WD.induction_lpSum_twist_finite | (intros; apply GlobalTheory.WeilDeligne.WD.induction_lpSum_twist_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardTorsionMulFinrank
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.TorsionCard

variable {l : ℕ} [hl : Fact l.Prime]

noncomputable def red (l : ℕ) [Fact l.Prime] : ℤ_[l]ˣ →* (ZMod l)ˣ :=
  Units.map (PadicInt.toZMod (p := l) : ℤ_[l] →+* ZMod l).toMonoidHom

theorem red_val (x : ℤ_[l]ˣ) : (red l x : ZMod l) = PadicInt.toZMod (x : ℤ_[l]) := rfl

theorem eq_one_of_red (h2 : l ≠ 2) (x : ℤ_[l]ˣ) (hx : IsOfFinOrder x) (h1 : red l x = 1) :
    x = 1 := by
  have hpos : 0 < orderOf x := hx.orderOf_pos
  have hpow : ((x : ℤ_[l])) ^ orderOf x = 1 := by
    rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  have hred : PadicInt.toZMod (x : ℤ_[l]) = 1 := by
    rw [← red_val, h1, Units.val_one]
  exact Units.ext (GlobalTheory.padicInt_eq_one_of_pow_eq_one_of_toZMod_eq_one h2 _ hpos.ne' hpow hred)

theorem exists_lift (h2 : l ≠ 2) (u : (ZMod l)ˣ) :
    ∃ x : ℤ_[l]ˣ, IsOfFinOrder x ∧ red l x = u := by
  classical
  have hl3 : 2 < l := lt_of_le_of_ne hl.out.two_le (Ne.symm h2)
  set a : ℤ_[l] := ((u : ZMod l).val : ℤ_[l]) with ha
  have hred_a : PadicInt.toZMod a = (u : ZMod l) := by
    rw [ha, map_natCast, ZMod.natCast_zmod_val]
  have norm_of : ∀ y : ℤ_[l], PadicInt.toZMod y ≠ 0 → ‖y‖ = 1 := by
    intro y hy
    by_contra hne
    have hlt : ‖y‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one y) hne
    apply hy
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton, ← PadicInt.norm_lt_one_iff_dvd]
    exact hlt
  have lt_of : ∀ y : ℤ_[l], PadicInt.toZMod y = 0 → ‖y‖ < 1 := by
    intro y hy
    rw [PadicInt.norm_lt_one_iff_dvd, ← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
      ← PadicInt.ker_toZMod, RingHom.mem_ker]
    exact hy
  let F : Polynomial ℤ_[l] := Polynomial.X ^ (l - 1) - 1
  have hF : PadicInt.toZMod (F.aeval a) = 0 := by
    simp only [F, map_sub, map_pow, Polynomial.aeval_X, map_one, hred_a]
    rw [sub_eq_zero, ← Units.val_pow_eq_pow_val, ZMod.units_pow_card_sub_one_eq_one, Units.val_one]
  have hF' : PadicInt.toZMod (F.derivative.aeval a) ≠ 0 := by
    simp [F, hred_a, Polynomial.derivative_X_pow]
    rw [ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2 := by
    rw [norm_of _ hF', one_pow]; exact lt_of _ hF
  obtain ⟨z, hz, hza, -, -⟩ := hensels_lemma hnorm
  have hz1 : z ^ (l - 1) = 1 := by
    simp only [F, map_sub, map_pow, Polynomial.aeval_X, map_one] at hz
    exact sub_eq_zero.mp hz
  have e : l - 1 = (l - 2) + 1 := by omega
  let x : ℤ_[l]ˣ := ⟨z, z ^ (l - 2), by rw [← pow_succ', ← e, hz1], by rw [← pow_succ, ← e, hz1]⟩
  refine ⟨x, ?_, ?_⟩
  · refine isOfFinOrder_iff_pow_eq_one.mpr ⟨l - 1, by omega, Units.ext ?_⟩
    rw [Units.val_pow_eq_pow_val]
    exact hz1
  · apply Units.ext
    rw [red_val, ← hred_a, ← sub_eq_zero, ← map_sub]
    by_contra hne
    have h1 := norm_of _ hne
    rw [norm_of _ hF'] at hza
    change ‖z - a‖ < 1 at hza
    linarith

theorem card_torsion (h2 : l ≠ 2) {Γ : Type} [Group Γ] (χ : Γ →* ℤ_[l]ˣ)
    (hχ : Function.Injective χ) (hk : ∀ x, red l x = 1 → x ∈ χ.range) :
    Nat.card {g : Γ // IsOfFinOrder g} = Nat.card ((red l).comp χ).range := by
  classical
  have hcomm : ∀ a b : Γ, a * b = b * a := fun a b => hχ (by rw [map_mul, map_mul, mul_comm])
  have hfin : ∀ g : Γ, IsOfFinOrder (χ g) ↔ IsOfFinOrder g := fun g => by
    rw [← orderOf_pos_iff, ← orderOf_pos_iff, orderOf_injective χ hχ g]
  let f : {g : Γ // IsOfFinOrder g} → ((red l).comp χ).range := fun g => ⟨red l (χ g.1), g.1, rfl⟩
  refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have hab' : red l (χ a) = red l (χ b) := congrArg Subtype.val hab
    have hc : Commute a b⁻¹ := hcomm a b⁻¹
    have ht : IsOfFinOrder (χ (a * b⁻¹)) := (hfin _).mpr (hc.isOfFinOrder_mul ha hb.inv)
    have h1 : red l (χ (a * b⁻¹)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_inv, hab', mul_inv_cancel]
    have h3 := eq_one_of_red h2 _ ht h1
    rw [map_mul, map_inv, mul_inv_eq_one] at h3
    exact Subtype.ext (hχ h3)
  · rintro ⟨u, g, rfl⟩
    obtain ⟨x, hx, hxu⟩ := exists_lift h2 (red l (χ g))
    have hr : red l (x⁻¹ * χ g) = 1 := by rw [map_mul, map_inv, hxu, inv_mul_cancel]
    obtain ⟨k, hk'⟩ := hk _ hr
    have hgk : χ (g * k⁻¹) = x := by
      rw [map_mul, map_inv, hk', mul_inv_rev, inv_inv, mul_inv_cancel_left]
    refine ⟨⟨g * k⁻¹, (hfin _).mp (hgk ▸ hx)⟩, Subtype.ext ?_⟩
    change red l (χ (g * k⁻¹)) = red l (χ g)
    rw [hgk, hxu]

theorem exists_chi (P : LocPrime l) :
    ∃ χ : GQ l →* ℤ_[l]ˣ, ∀ g, ((χ g : ℤ_[l]) : ℚ_[l]) = (P.χQ g : ℚ_[l]) := by
  have hn := GlobalTheory.Cyc.IsCyc.norm_eq_one P.χQ_cyc
  refine ⟨{ toFun := fun g => PadicInt.mkUnits (hn g), map_one' := ?_, map_mul' := ?_ },
    fun g => PadicInt.mkUnits_eq (hn g)⟩
  · apply Units.ext; apply PadicInt.ext
    simp
  · intro a b; apply Units.ext; apply PadicInt.ext
    simp only [Units.val_mul, PadicInt.coe_mul, PadicInt.mkUnits_eq, map_mul]

theorem finrank_eq_relIndex (K : FinExt l) :
    Module.finrank ↥(K0 K) ↥K.1 = (GK K).relIndex (K0 K).fixingSubgroup := by
  have hle : K0 K ≤ K.1 := inf_le_left
  have : FiniteDimensional ℚ_[l] K.1 := K.2
  have : FiniteDimensional ℚ_[l] (K0 K) := FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap (IntermediateField.inclusion_injective hle)
  have h1 := IntermediateField.finrank_eq_fixingSubgroup_index (E' := Om l) K.1
  have h2 := IntermediateField.finrank_eq_fixingSubgroup_index (E' := Om l) (K0 K)
  have h3 := Subgroup.relIndex_mul_index (IntermediateField.fixingSubgroup_le hle)
  have h4 := Module.finrank_mul_finrank ℚ_[l] (K0 K) K.1
  have hpos : 0 < Module.finrank ℚ_[l] (K0 K) := Module.finrank_pos
  unfold GK
  rw [← h1, ← h2] at h3
  rw [← h4, mul_comm] at h3
  exact (Nat.eq_of_mul_eq_mul_left hpos h3).symm


set_option maxHeartbeats 800000 in
theorem card_torsion_mul_finrank : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ} (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n), l ≠ 2 → K.1 ≤ Ks K 1 → W.DelF.card * Module.finrank ↥(K0 K) ↥K.1 = l - 1 := by
  intro l _ P K LL n W h2 hK
  classical
  obtain ⟨χ, hχ⟩ := exists_chi P
  have hle : K0 K ≤ K.1 := inf_le_left
  let χK : ↥(GK K) →* ℤ_[l]ˣ := χ.comp (GK K).subtype
  have hval : ∀ g : ↥(GK K), ((χK g : ℤ_[l]) : ℚ_[l]) = ((P.PD K).χ g : ℚ_[l]) := by
    intro g
    rw [P.PD_χ K g]
    exact hχ g
  have hO : Function.Injective (algebraMap (OL LL) LL.1) := Subtype.val_injective
  have hkey : ∀ g : ↥(GK K), W.resΓ g = 1 ↔ χK g = 1 := by
    intro g
    have hr := W.χΓ_res g
    constructor
    · intro h
      rw [h, map_one, Units.val_one, map_one] at hr
      have h1 : (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = 1 :=
        (algebraMap ℚ_[l] LL.1).injective (by rw [← hr, map_one])
      apply Units.ext
      apply PadicInt.ext
      rw [hval, h1]
      simp
    · intro h
      have h1 : (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = 1 := by
        rw [← hval, h]
        simp
      rw [h1, map_one] at hr
      have h3 : ((W.χΓ (W.resΓ g) : (OL LL)ˣ) : OL LL) = 1 := hO (by rw [hr, map_one])
      apply W.χΓ_inj
      rw [map_one]
      exact Units.ext h3
  let ψ : W.Gam →* ℤ_[l]ˣ :=
    W.resΓ.liftOfRightInverse (Function.surjInv W.resΓ_onto)
      (Function.rightInverse_surjInv W.resΓ_onto)
      ⟨χK, fun g hg => MonoidHom.mem_ker.mpr ((hkey g).mp (MonoidHom.mem_ker.mp hg))⟩
  have hψ : ∀ g : ↥(GK K), ψ (W.resΓ g) = χK g := fun g =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g
  have hψinj : Function.Injective ψ := by
    refine (injective_iff_map_eq_one ψ).mpr fun γ hγ => ?_
    obtain ⟨g, rfl⟩ := W.resΓ_onto γ
    rw [hψ] at hγ
    exact (hkey g).mpr hγ
  have hfix : ∀ g : GQ l, g ∈ (K0 K).fixingSubgroup → red l (χ g) = 1 → g ∈ GK K := by
    intro g hg hr
    have hz : PadicInt.toZMod ((χ g : ℤ_[l]) - 1) = 0 := by
      rw [map_sub, ← red_val, hr, Units.val_one, map_one, sub_self]
    have hd : (l : ℤ_[l]) ^ 1 ∣ (χ g : ℤ_[l]) - 1 := by
      rw [pow_one, ← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
        ← PadicInt.ker_toZMod, RingHom.mem_ker]
      exact hz
    have hnorm : ‖(P.χQ g : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-((1 : ℕ) : ℤ)) := by
      rw [← hχ g]
      have := (PadicInt.norm_le_pow_iff_mem_span_pow _ 1).mpr (Ideal.mem_span_singleton.mpr hd)
      simpa [PadicInt.norm_def] using this
    have hζ := (GlobalTheory.Cyc.IsCyc.fix_iff P.χQ_cyc g 1).mpr hnorm
    have hadj : g ∈ (IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ l ^ 1 = 1}).fixingSubgroup :=
      (GlobalTheory.Cyc.mem_fixingSubgroup_adjoin_iff _ g).mpr fun x hx => hζ x hx
    have hKs : g ∈ (Ks K 1).fixingSubgroup := by
      unfold Ks
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨hg, hadj⟩
    exact IntermediateField.fixingSubgroup_le hK hKs
  have hfd0 : FiniteDimensional ℚ_[l] (K0 K) := by
    have : FiniteDimensional ℚ_[l] K.1 := K.2
    exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  let K0' : FinExt l := ⟨K0 K, hfd0⟩
  have honto : ∀ c : ℤ_[l]ˣ, ∃ g ∈ (K0 K).fixingSubgroup, χ g = c := by
    intro c
    obtain ⟨g, hg, hgc⟩ := GlobalTheory.UnramCyc.chi_onto_of_unramified P K0' inf_le_right c
    exact ⟨g, hg, Units.ext (PadicInt.ext (by rw [hχ g, hgc]))⟩
  have hk : ∀ x : ℤ_[l]ˣ, red l x = 1 → x ∈ ψ.range := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := honto x
    exact ⟨W.resΓ ⟨g, hfix g hg hx⟩, by rw [hψ]; rfl⟩
  have hct := card_torsion h2 ψ hψinj hk
  have hdel : W.DelF.card = Nat.card {γ : W.Gam // IsOfFinOrder γ} := by
    rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun γ => by
      rw [W.DelF_def, isOfFinOrder_iff_pow_eq_one])
  let G0 := (K0 K).fixingSubgroup
  let F : ↥G0 →* (ZMod l)ˣ := (red l).comp (χ.comp G0.subtype)
  have hF : Function.Surjective F := by
    intro u
    obtain ⟨x, -, hxu⟩ := exists_lift h2 u
    obtain ⟨g, hg, hgx⟩ := honto x
    exact ⟨⟨g, hg⟩, by simp [F, hgx, hxu]⟩
  let H0 := (GK K).subgroupOf G0
  have hkerF : F.ker ≤ H0 := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    exact Subgroup.mem_subgroupOf.mpr (hfix g g.2 hg)
  have hidx : H0.index = (H0.map F).index := by
    rw [← Subgroup.index_comap_of_surjective _ hF, Subgroup.comap_map_eq_self hkerF]
  have hmap : H0.map F = ((red l).comp ψ).range := by
    ext u
    constructor
    · rintro ⟨g0, hg0, rfl⟩
      refine ⟨W.resΓ ⟨g0, Subgroup.mem_subgroupOf.mp hg0⟩, ?_⟩
      simp only [MonoidHom.comp_apply, hψ]
      rfl
    · rintro ⟨γ, rfl⟩
      obtain ⟨g, rfl⟩ := W.resΓ_onto γ
      refine ⟨⟨g, IntermediateField.fixingSubgroup_le hle g.2⟩, Subgroup.mem_subgroupOf.mpr g.2, ?_⟩
      simp only [MonoidHom.comp_apply, hψ]
      rfl
  have hcard := Subgroup.card_mul_index (H0.map F)
  rw [Nat.card_eq_fintype_card (α := (ZMod l)ˣ), ZMod.card_units] at hcard
  rw [finrank_eq_relIndex, hdel, hct, ← hmap]
  change _ * H0.index = _
  rw [hidx]
  exact hcard

end GlobalTheory.TorsionCard
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneOfFiniteImage
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneOfFiniteImage
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

theorem exists_wdRep_pull_finite_twist :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
      (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (G : Type)
      [Group G] [Finite G] (π : Weil h →* G),
      IsOpen {σ : Ine (F := E) A | π (ineIncl h σ) = 1} → ∀ (n : ℕ)
      (R : Representation ℂ G (Fin n → ℂ)) (μ : Weil h →* ℂˣ), IsSmooth μ →
      ∃ b : WDRep h (Fin n → ℂ), ∀ σ, b.ρ σ = (μ σ : ℂ) • R (π σ) := by
  intro E Ω _ _ _ _ _ A w h G _ _ π hπ n R μ hμ
  have hsm : IsSmooth (R.comp π) :=
    IsSmooth.of_le (f := π) hπ fun σ hσ => by simp [hσ]
  have hss : ∀ σ, Module.End.IsSemisimple ((R.comp π) σ) := by
    intro σ
    have hu : IsUnit ((R.comp π) σ) := ((R.comp π).toHomUnits σ).isUnit
    refine FrobSemisimple.isSemisimple_of_pow hu (m := Nat.card G) Nat.card_pos ?_
    rw [← map_pow, MonoidHom.comp_apply, map_pow, pow_card_eq_one', map_one]
    exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := Polynomial.X - Polynomial.C 1)
      (Polynomial.irreducible_X_sub_C 1).squarefree (by simp)
  let b0 : WDRep h (Fin n → ℂ) :=
    { ρ := R.comp π
      N := 0
      smooth := hsm
      semisimple := hss
      nilpotent := IsNilpotent.zero
      comm := fun σ => by simp }
  exact ⟨b0.twist μ hμ, fun σ => rfl⟩

end GlobalTheory.WeilDeligne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneOfFiniteImageStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_deligne_of_finite_image : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (G : Type) [Group G] [Finite G] (π : Weil h →* G), IsOpen {σ : Ine (F := E) A | π (ineIncl h σ) = 1} → ∀ (n : ℕ) (R : Representation ℂ G (Fin n → ℂ)) (μ : Weil h →* ℂˣ), IsSmooth μ → ∃ b : WDRep h (Fin n → ℂ), ∀ σ, b.ρ σ = (μ σ : ℂ) • R (π σ) := by
  first | exact @GlobalTheory.WeilDeligne.exists_wdRep_pull_finite_twist | exact GlobalTheory.WeilDeligne.exists_wdRep_pull_finite_twist | (intros; apply GlobalTheory.WeilDeligne.exists_wdRep_pull_finite_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH2LevelRepOneLe
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH2LevelRepOneLe
open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.ShapeNeg

theorem finite_card_dual {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [Finite V] :
    Finite (Module.Dual F V) ∧ Nat.card (Module.Dual F V) = Nat.card V := by
  haveI : Module.Finite F V := Module.Finite.of_finite
  haveI : Finite (Module.Dual F V) := DFunLike.finite (Module.Dual F V)
  refine ⟨inferInstance, ?_⟩
  rw [Module.natCard_eq_pow_finrank (K := F), Module.natCard_eq_pow_finrank (K := F) (V := V),
    Subspace.dual_finrank_eq]

theorem card_H2_level_rep_le :
    Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)},
    FiniteDimensional ℚ_[p] K → ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] {ϖ : O}, Irreducible ϖ → ∀ {M : Type} [AddCommGroup M] [Module O M],
    (M ≃ₗ[O] Formalism.NG.KO O) → ∀ (ρ : Representation O (Formalism.GaloisCohomology.GK p K) M)
    (h : ((p : O) ^ 1) ∈ Ideal.span {ϖ ^ 1}),
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p 1 h
    ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p 1 h ρ) →
    Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p 1 h ρ)) ≤ Nat.card (IsLocalRing.ResidueField O) := by
  intro hT p _ K hK O _ _ _ _ ϖ hϖ M _ _ e ρ h
  letI := GlobalTheory.ShapeNeg.levZ (M := M) p 1 h
  intro hc
  obtain ⟨hfin, hcard⟩ := GlobalTheory.T.finite_card_torsionLevel_fractionRingQuot hϖ e 1
  haveI : Finite (Lev M (ϖ ^ 1)) := hfin
  haveI : Fact (p ^ 1).Prime := ⟨by rw [pow_one]; exact Fact.out⟩
  obtain ⟨⟨eH⟩, -, -, -, hb⟩ := hT p K hK 1 (Lev M (ϖ ^ 1)) (levRepZ p 1 h ρ) one_pos hc
  set ρ' := levRepZ p 1 h ρ
  set χ := Formalism.GaloisCohomology.cycK p K 1

  let W := ↥(H0 ((twDual χ ρ').comp (MonoidHom.id _)))
  haveI : Finite (TDual (ZMod (p ^ 1)) (Lev M (ϖ ^ 1))) :=
    (finite_card_dual (F := ZMod (p ^ 1)) (V := Lev M (ϖ ^ 1))).1
  haveI : Finite W := Subtype.finite
  have hW : Nat.card W ≤ Nat.card (Lev M (ϖ ^ 1)) :=
    (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
      (finite_card_dual (F := ZMod (p ^ 1)) (V := Lev M (ϖ ^ 1))).2.le
  obtain ⟨hfd, hcd⟩ := finite_card_dual (F := ZMod (p ^ 1)) (V := W)
  let E := LinearEquiv.congrRight (M := W) eH
  haveI : Finite (W →ₗ[ZMod (p ^ 1)] H2 ((charRep χ).comp (MonoidHom.id _))) :=
    Finite.of_equiv _ E.symm.toEquiv
  have h1 : Nat.card (H2 ρ') ≤ Nat.card (W →ₗ[ZMod (p ^ 1)] H2 ((charRep χ).comp (MonoidHom.id _))) :=
    Nat.card_le_card_of_injective _ hb.1
  have h2 : Nat.card (W →ₗ[ZMod (p ^ 1)] H2 ((charRep χ).comp (MonoidHom.id _))) = Nat.card W :=
    (Nat.card_congr E.toEquiv).trans hcd
  calc Nat.card (H2 ρ') ≤ Nat.card W := h1.trans h2.le
    _ ≤ Nat.card (Lev M (ϖ ^ 1)) := hW
    _ = Nat.card (IsLocalRing.ResidueField O) := hcard.trans (pow_one _)

end GlobalTheory.ShapeNeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH2LevelRepOneLeStatement
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_H2_level_rep_one_le : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)},
    FiniteDimensional ℚ_[p] K → ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] {ϖ : O}, Irreducible ϖ → ∀ {M : Type} [AddCommGroup M] [Module O M],
    (M ≃ₗ[O] Formalism.NG.KO O) → ∀ (ρ : Representation O (Formalism.GaloisCohomology.GK p K) M)
    (h : ((p : O) ^ 1) ∈ Ideal.span {ϖ ^ 1}),
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p 1 h
    ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p 1 h ρ) →
    Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p 1 h ρ)) ≤ Nat.card (IsLocalRing.ResidueField O) := by
  first | exact @GlobalTheory.ShapeNeg.card_H2_level_rep_le | exact GlobalTheory.ShapeNeg.card_H2_level_rep_le | (intros; apply GlobalTheory.ShapeNeg.card_H2_level_rep_le <;> assumption)
end
end
