module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
public import ReciprocityTheory.DualLattices.HasLenCokerDet
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisToBdRPlusInjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisLogTeichmullerUniqueGaloisFrobeniusBdR
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisLogTeichmullerUniqueGaloisFrobeniusBdR
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.LogFun

theorem partial_eq {R : Type} [CommRing R] (u : ℕ → R) (hu : ∀ k : ℕ, ((k + 1 : ℕ) : R) * u k = 1)
    (x s : R) (n : ℕ) (hn : IsUnit ((n.factorial : ℕ) : R))
    (hs : ((n.factorial : ℕ) : R) * s =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R) * x ^ (k + 1)) :
    s = ∑ k ∈ Finset.range n, (-1) ^ k * u k * x ^ (k + 1) := by
  apply hn.mul_left_cancel
  rw [hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have h1 : n.factorial = n.factorial / (k + 1) * (k + 1) :=
    (Nat.div_mul_cancel (Nat.dvd_factorial k.succ_pos (Finset.mem_range.1 hk))).symm
  have h2 : ((n.factorial : ℕ) : R) = ((n.factorial / (k + 1) : ℕ) : R) * ((k + 1 : ℕ) : R) := by
    rw [← Nat.cast_mul, ← h1]
  generalize ((n.factorial / (k + 1) : ℕ) : R) = q at h2 ⊢
  rw [h2]
  linear_combination (-((-1) ^ k * q * x ^ (k + 1))) * hu k

theorem partial_sub_mem {R : Type} [CommRing R] (I : Ideal R) (u : ℕ → R) (x : R) (hx : x ∈ I)
    {n m : ℕ} (h : n ≤ m) :
    ∑ k ∈ Finset.range m, (-1) ^ k * u k * x ^ (k + 1) -
      ∑ k ∈ Finset.range n, (-1) ^ k * u k * x ^ (k + 1) ∈ I ^ n := by
  rw [← Finset.sum_Ico_eq_sub _ h]
  refine Ideal.sum_mem _ fun k hk => Ideal.mul_mem_left _ _ ?_
  exact Ideal.pow_le_pow_right (by have := (Finset.mem_Ico.1 hk).1; omega) (Ideal.pow_mem_pow hx (k + 1))

variable {l : ℕ} [Fact l.Prime]

theorem mu_mem {e : Per.Fl l} (he : e.untilt = 1) :
    algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ∈ Per.kerP l := by
  exact GlobalTheory.RingIface.alg_mem_kerP l (by rw [Model.theta_mu, he, sub_self])

theorem ev_alg (n : ℕ) (a : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) a) = Ideal.Quotient.mk _ a :=
  GlobalTheory.RingIface.ev_alg l n a

theorem isLog_map {e : Per.Fl l} (he : e.untilt = 1) {t : Per.Acris l} (ht : IsLogA e t)
    {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) : Per.IsLog l e (j t) := by
  refine GlobalTheory.CrisIncl.isLog_of_partial l e he _ fun n => ?_
  have hu : ∀ k : ℕ, ∃ u : Per.AinfP l, ((k + 1 : ℕ) : Per.AinfP l) * u = 1 := fun k =>
    (GlobalTheory.RingBasics.isUnit_nat l _ k.succ_ne_zero).exists_right_inv
  choose u hu using hu
  have hf : ∀ k : ℕ, IsUnit ((k.factorial : ℕ) : Per.AinfP l) := fun k =>
    GlobalTheory.RingBasics.isUnit_nat l _ k.factorial_ne_zero
  obtain ⟨d, hd⟩ := (hf n).exists_right_inv
  obtain ⟨c, hc⟩ : ∃ c : Per.AinfP l, ((n.factorial : ℕ) : Per.AinfP l) * c =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) *
        (algebraMap (Per.Ainf l) (Per.AinfP l) (mu e)) ^ (k + 1) :=
    ⟨d * _, by rw [← mul_assoc, hd, one_mul]⟩
  have key := (GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx l j hj).2.2 n t (algebraMap (Per.AinfP l) (Per.BdRp l) c) (by
    intro r
    obtain ⟨N, hN⟩ := ht r
    obtain ⟨s, hs, z, hz⟩ := hN (max N n) (le_max_left _ _)
    refine ⟨s, z, 0, by rw [← hz]; ring, ?_⟩
    rw [map_zero, mul_zero, map_zero, ← map_sub, ev_alg, Ideal.Quotient.eq_zero_iff_mem,
      partial_eq u hu _ _ _ (hf _) hs, partial_eq u hu _ _ _ (hf _) hc, ← neg_sub]
    exact neg_mem (partial_sub_mem _ u _ (mu_mem he) (le_max_right _ _)))
  exact ⟨c, hc, by rw [key, ev_alg]⟩

theorem log_fun : ∀ (l : ℕ) [Fact l.Prime], ∀ (e : Per.Fl l) (t : Per.Acris l), e.untilt = 1 → IsLogA e t → (∀ t' : Per.Acris l, IsLogA e t' → t' = t) ∧ (∀ g : Per.Gq l, IsLogA (Per.σF g e) (sigA g t)) ∧ IsLogA (e ^ l) (phiA l t) ∧ ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → Per.IsLog l e (j t) :=
  fun _ _ _ _ he ht => ⟨fun _ h => Model.isLogA_unique h ht, fun g => Model.isLogA_sigA g ht,
    Model.isLogA_phiA ht, fun _ hj => isLog_map he ht hj⟩

end GlobalTheory.MemLoc.LogFun
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisLogTeichmullerUniqueGaloisFrobeniusBdRStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR : ∀ (l : ℕ) [Fact l.Prime], ∀ (e : Per.Fl l) (t : Per.Acris l), e.untilt = 1 → IsLogA e t → (∀ t' : Per.Acris l, IsLogA e t' → t' = t) ∧ (∀ g : Per.Gq l, IsLogA (Per.σF g e) (sigA g t)) ∧ IsLogA (e ^ l) (phiA l t) ∧ ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → Per.IsLog l e (j t) := by
  first | exact @GlobalTheory.MemLoc.LogFun.log_fun | exact GlobalTheory.MemLoc.LogFun.log_fun | (intros; apply GlobalTheory.MemLoc.LogFun.log_fun <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRFiltrationLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRFiltrationLaws
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.FilLaws

theorem toNat_iff_zpow {R K : Type} [CommRing R] [CommRing K] (ι : R →+* K) (ξ : R) (u : Kˣ)
    (hu : (u : K) = ι ξ) (a : ℤ) (x : K) :
    (∃ y : R, x * ι ξ ^ (-a).toNat = ι (ξ ^ a.toNat * y)) ↔ ∃ y : R, x = ((u ^ a : Kˣ) : K) * ι y := by
  refine exists_congr fun y => ?_
  rw [map_mul, map_pow, ← hu]
  have h : u ^ a * u ^ (-a).toNat = u ^ a.toNat := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add]
    congr 1
    omega
  have h' : ((u ^ a : Kˣ) : K) * (u : K) ^ (-a).toNat = (u : K) ^ a.toNat := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul, h]
  rw [← h', mul_right_comm]
  exact (u.isUnit.pow _).mul_left_inj

theorem exists_isEps (l : ℕ) [Fact l.Prime] : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, ε, h0, -, h1, hr⟩ := GlobalTheory.T.exists_compatible_rootsOfUnity_and_tilt_padic l
  refine ⟨ε, ?_, ?_⟩
  · have := hr 0
    rw [h0, map_one] at this
    exact Subtype.ext this
  · intro h
    have := hr 1
    have e : rootT ε 1 = 1 := h
    rw [e] at this
    apply h1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← this, map_one]
    rfl

variable {l : ℕ} [Fact l.Prime]

theorem σDp_alg (g : Per.Gq l) (x : Per.AinfP l) :
    Per.σDp g (algebraMap (Per.AinfP l) (Per.BdRp l) x) =
      algebraMap (Per.AinfP l) (Per.BdRp l) (Per.extP (Per.σA g) x) :=
  GlobalTheory.RingIface.sigDp_alg l g x

theorem σD_alg (g : Per.Gq l) (y : Per.BdRp l) :
    Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) y) =
      algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g y) :=
  GlobalTheory.RingIface.sigD_alg l g y

theorem σDp_mem_FilP (g : Per.Gq l) (n : ℕ) (y : Per.BdRp l) (hy : y ∈ Per.FilP l n) :
    Per.σDp g y ∈ Per.FilP l n := by
  obtain ⟨e, he⟩ := exists_isEps l
  obtain ⟨hP, -, -, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l e he
  have hk := GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he
  have h1 : algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ∈ Per.kerP l := by
    rw [hk]; exact Ideal.mem_span_singleton_self _
  have h2 : Per.extP (Per.σA g) (algebraMap (Per.Ainf l) (Per.AinfP l) (xi e)) ∈ Per.kerP l :=
    Ideal.mem_comap.1 (GlobalTheory.RingBasics.ker_σ g h1)
  rw [hk, Ideal.mem_span_singleton] at h2
  have h3 : aDp l (xi e) ∣ Per.σDp g (aDp l (xi e)) := by
    unfold aDp
    rw [RingHom.comp_apply, σDp_alg]
    exact map_dvd _ h2
  obtain ⟨z, rfl⟩ := (hP n y).1 hy
  rw [hP, map_mul, map_pow]
  exact (pow_dvd_pow_of_dvd h3 n).mul_right _

theorem σDp_xi (e : Per.Fl l) (he : IsEps e) (g : Per.Gq l) :
    ∃ c d : Per.BdRp l, Per.σDp g (aDp l (xi e)) = aDp l (xi e) * c ∧ c * d = 1 := by
  obtain ⟨hP, hreg, -, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l e he
  have hξ : aDp l (xi e) ∈ Per.FilP l 1 := (hP 1 _).2 (by rw [pow_one])
  have hd : ∀ g : Per.Gq l, aDp l (xi e) ∣ Per.σDp g (aDp l (xi e)) := fun g => by
    have := (hP 1 _).1 (σDp_mem_FilP g 1 _ hξ)
    rwa [pow_one] at this
  obtain ⟨c, hc⟩ := hd g
  obtain ⟨c', hc'⟩ := hd g⁻¹
  have hinv : Per.σDp g (Per.σDp g⁻¹ (aDp l (xi e))) = aDp l (xi e) := by
    change Per.σDp g (Per.σDp g⁻¹ (algebraMap (Per.AinfP l) (Per.BdRp l) _)) =
      algebraMap (Per.AinfP l) (Per.BdRp l) _
    rw [σDp_alg, σDp_alg, GlobalTheory.RingBasics.extP_inv]
  refine ⟨c, Per.σDp g c', hc, ?_⟩
  rw [hc', map_mul, hc] at hinv
  have := hreg (c * Per.σDp g c' - 1) (by rw [mul_sub, mul_one, ← mul_assoc, hinv, sub_self])
  exact sub_eq_zero.1 this

theorem eq_zero_of_forall_mem_FilP (y : Per.BdRp l) (hy : ∀ n, y ∈ Per.FilP l n) : y = 0 := by
  obtain ⟨e, he⟩ := exists_isEps l
  obtain ⟨hP, -, hc, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l e he
  refine hc.toIsHausdorff.haus y fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact (hP n y).1 (hy n)

end GlobalTheory.MemLoc.FilLaws


open GlobalTheory.MemLoc.FilLaws in
theorem GlobalTheory.MemLoc.filD_laws : ∀ (l : ℕ) [Fact l.Prime], (∀ a : ℤ, Per.FilD l (a + 1) ≤ Per.FilD l a) ∧ (1 : Per.BdR l) ∈ Per.FilD l 0 ∧ (∀ (a b : ℤ) (x y : Per.BdR l), x ∈ Per.FilD l a → y ∈ Per.FilD l b → x * y ∈ Per.FilD l (a + b)) ∧ (∀ x : Per.BdR l, ∃ a, x ∈ Per.FilD l a) ∧ (∀ x : Per.BdR l, (∀ a, x ∈ Per.FilD l a) → x = 0) ∧ (∀ (g : Per.Gq l) (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a → Per.σD g x ∈ Per.FilD l a) ∧ ∀ (n : ℕ) (y : Per.BdRp l), algebraMap (Per.BdRp l) (Per.BdR l) y ∈ Per.FilD l n ↔ y ∈ Per.FilP l n := by
  intro l _
  obtain ⟨e, he⟩ := exists_isEps l
  obtain ⟨hdom, hinj, hfield, hden⟩ := GlobalTheory.T.bdRPlus_isDomain_bdR_isField l
  obtain ⟨hP, hreg, -, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l e he
  have hD := GlobalTheory.T.mem_deRhamFiltration_iff_xi_pow l e he
  have hden := hden e he
  have hσ := σDp_xi e he
  generalize aDp l (xi e) = ξ at hP hreg hD hden hσ
  have hne : algebraMap (Per.BdRp l) (Per.BdR l) ξ ≠ 0 := by
    intro h
    have h0 : ξ = 0 := hinj (by rw [h, map_zero])
    exact one_ne_zero (hreg 1 (by rw [h0, zero_mul]))
  obtain ⟨v, hv⟩ := hfield.mul_inv_cancel hne
  obtain ⟨u, hu⟩ : IsUnit (algebraMap (Per.BdRp l) (Per.BdR l) ξ) := IsUnit.of_mul_eq_one v hv
  have hZ : ∀ (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a ↔
      ∃ y, x = ((u ^ a : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) y :=
    fun a x => (hD a x).trans (toNat_iff_zpow _ ξ u hu a x)
  have hlast : ∀ (n : ℕ) (y : Per.BdRp l),
      algebraMap (Per.BdRp l) (Per.BdR l) y ∈ Per.FilD l n ↔ y ∈ Per.FilP l n := by
    intro n y
    rw [hZ, hP, zpow_natCast, Units.val_pow_eq_pow_val, hu]
    refine exists_congr fun z => ?_
    rw [← map_pow, ← map_mul]
    exact hinj.eq_iff
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hlast⟩
  · intro a x hx
    obtain ⟨y, hy⟩ := (hZ _ _).1 hx
    refine (hZ _ _).2 ⟨ξ * y, ?_⟩
    rw [hy, zpow_add_one, Units.val_mul, hu, map_mul, mul_assoc]
  · exact (hZ _ _).2 ⟨1, by rw [zpow_zero, Units.val_one, map_one, mul_one]⟩
  · intro a b x y hx hy
    obtain ⟨x', rfl⟩ := (hZ _ _).1 hx
    obtain ⟨y', rfl⟩ := (hZ _ _).1 hy
    refine (hZ _ _).2 ⟨x' * y', ?_⟩
    rw [zpow_add, Units.val_mul, map_mul, mul_mul_mul_comm]
  · intro x
    obtain ⟨n, y, hy⟩ := hden x
    refine ⟨-(n : ℤ), (hD _ _).2 ⟨y, ?_⟩⟩
    rw [neg_neg, Int.toNat_natCast, Int.toNat_neg_natCast, pow_zero, one_mul, hy]
  · intro x hx
    obtain ⟨y, hy⟩ := (hZ _ _).1 (hx 0)
    rw [zpow_zero, Units.val_one, one_mul] at hy
    subst hy
    rw [eq_zero_of_forall_mem_FilP y fun n => (hlast n y).1 (hx n), map_zero]
  · intro g a x hx
    obtain ⟨c, d, hc, hcd⟩ := hσ g
    obtain ⟨y, hy⟩ := (hD _ _).1 hx
    have h1 := congrArg (Per.σD g) hy
    rw [map_mul, map_pow, σD_alg, σD_alg, map_mul (Per.σDp g), map_pow, hc] at h1
    refine (hD _ _).2 ⟨d ^ (-a).toNat * (c ^ a.toNat * Per.σDp g y), ?_⟩
    have h2 : algebraMap (Per.BdRp l) (Per.BdR l) ξ =
        algebraMap (Per.BdRp l) (Per.BdR l) (ξ * c) * algebraMap (Per.BdRp l) (Per.BdR l) d := by
      rw [← map_mul, mul_assoc, hcd, mul_one]
    rw [h2, mul_pow, ← mul_assoc, h1, ← map_pow, ← map_mul]
    congr 1
    ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRFiltrationLawsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bdR_filtration_laws : ∀ (l : ℕ) [Fact l.Prime], (∀ a : ℤ, Per.FilD l (a + 1) ≤ Per.FilD l a) ∧ (1 : Per.BdR l) ∈ Per.FilD l 0 ∧ (∀ (a b : ℤ) (x y : Per.BdR l), x ∈ Per.FilD l a → y ∈ Per.FilD l b → x * y ∈ Per.FilD l (a + b)) ∧ (∀ x : Per.BdR l, ∃ a, x ∈ Per.FilD l a) ∧ (∀ x : Per.BdR l, (∀ a, x ∈ Per.FilD l a) → x = 0) ∧ (∀ (g : Per.Gq l) (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a → Per.σD g x ∈ Per.FilD l a) ∧ ∀ (n : ℕ) (y : Per.BdRp l), algebraMap (Per.BdRp l) (Per.BdR l) y ∈ Per.FilD l n ↔ y ∈ Per.FilP l n := by
  first | exact @GlobalTheory.MemLoc.filD_laws | exact GlobalTheory.MemLoc.filD_laws | (intros; apply GlobalTheory.MemLoc.filD_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PadicIntHomUnique
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem theta_ker_facts : ∀ (l : ℕ) [Fact l.Prime], Function.Surjective (Per.θ l) ∧ IsDomain (Per.Ainf l) ∧ ((l : ℕ) : Per.Ainf l) ≠ 0 ∧ ∀ e : Per.Fl l, IsEps e → RingHom.ker (Per.θ l) = Ideal.span {xi e} ∧ xi e ≠ 0 := by
  intro l _
  have hv := PadicComplexInt.integers l
  haveI : IsDomain (Per.Fl l) := PreTilt.isDomain _ _ _ hv l
  have hl : ((l : ℕ) : Per.Ainf l) ≠ 0 := fun h => by
    have h1 := congrArg (Per.θ l) h
    rw [map_natCast, map_zero] at h1
    exact GlobalTheory.RingBasics.p_ne_zero (p := l) (by simpa using congrArg Subtype.val h1)
  refine ⟨ReciprocityTheory.PGsh.Ainf.theta_surj l _ hv, inferInstance, hl, fun e he => ?_⟩
  have hε : IsPrimitiveRoot (((frobeniusEquiv (Per.Fl l) l).symm e).untilt) l := by
    have h1 : (((frobeniusEquiv (Per.Fl l) l).symm e).untilt) ^ l = 1 := by
      rw [← map_pow, frobeniusEquiv_symm_pow_p]; exact he.1
    have h2 := he.2
    generalize ((frobeniusEquiv (Per.Fl l) l).symm e).untilt = y at h1 h2 ⊢
    have h3 := IsPrimitiveRoot.orderOf y
    rwa [orderOf_eq_prime h1 h2] at h3
  refine ⟨ReciprocityTheory.PGsh.Ainf.ker_theta l _ hv e hε, fun h => ?_⟩
  exact one_ne_zero (ReciprocityTheory.PGsh.Ainf.xi_nzd l _ hv e hε 1 (by rw [one_mul]; exact h))

theorem tilt_facts : ∀ (l : ℕ) [Fact l.Prime], (∀ x : ℕ → Per.OC l, (∀ n, x (n + 1) ^ l = x n) → ∃ e : Per.Fl l, ∀ n, rootT e n = x n) ∧ (∀ e : Per.Fl l, (∀ n, rootT e n = 1) → e = 1) ∧ (∀ (e : Per.Fl l) (m n : ℕ), rootT (e ^ m) n = rootT e n ^ m) := by
  intro l _
  have key : ∀ (e : Per.Fl l) (n : ℕ), Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) (rootT e n) =
      PreTilt.coeff n e := by
    intro e n
    rw [rootT, PreTilt.mk_untilt_eq_coeff_zero]
    exact PreTilt.coeff_iterate_frobeniusEquiv_symm 0 n e |>.trans (by rw [zero_add])
  refine ⟨fun x hx => ?_, fun e he => ?_, fun e m n => ?_⟩
  · let e : Perfection (ModP (Per.OC l) l) l :=
      ⟨fun n => Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) (x n), fun n => by
        rw [← map_pow, hx]⟩
    have hp : ∀ n k, x (n + k) ^ l ^ k = x n := by
      intro n k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ', pow_mul, ← add_assoc, hx, ih]
    refine ⟨e, fun n => ?_⟩
    refine Perfection.teichmuller_spec (I := Ideal.span {((l : ℕ) : Per.OC l)}) fun k => ⟨x (n + k), ?_, ?_⟩
    · refine Eq.trans ?_ (PreTilt.coeff_iterate_frobeniusEquiv_symm (O := Per.OC l) k n e).symm
      rw [add_comm]; rfl
    · rw [hp]
  · refine Perfection.ext fun n => ?_
    have := key e n
    rw [he, map_one] at this
    exact this.symm.trans (map_one (PreTilt.coeff n)).symm
  · rw [rootT, rootT, ← map_pow]
    congr 1
    exact iterate_map_pow (frobeniusEquiv (Per.Fl l) l).symm.toRingHom n e m

theorem thetaP_facts : ∀ (l : ℕ) [Fact l.Prime], Function.Surjective (Per.θP l) ∧ RingHom.ker (Per.θP l) = Per.kerP l ∧ (∀ a : Per.Ainf l, Per.θP l (algebraMap (Per.Ainf l) (Per.AinfP l) a) = (Per.θ l a : ℂ_[l])) ∧ (∀ a : Per.AinfP l, Per.θD l (algebraMap (Per.AinfP l) (Per.BdRp l) a) = Per.θP l a) ∧ IsDomain (Per.AinfP l) ∧ Function.Injective (algebraMap (Per.Ainf l) (Per.AinfP l)) ∧ ∀ e : Per.Fl l, IsEps e → Per.kerP l = Ideal.span {algebraMap (Per.Ainf l) (Per.AinfP l) (xi e)} := by
  intro l _
  obtain ⟨hs, hdom, hl, hk⟩ := theta_ker_facts l
  have hle : Submonoid.powers ((l : ℕ) : Per.Ainf l) ≤ nonZeroDivisors _ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hl
  have hA : ∀ a : Per.Ainf l, Per.θP l (algebraMap (Per.Ainf l) (Per.AinfP l) a) = (Per.θ l a : ℂ_[l]) :=
    fun a => GlobalTheory.RingIface.fontaineTheta_algebraMap l a
  have hu := GlobalTheory.RingBasics.isUnit_l l
  have hsurj : ∀ y : Per.AinfP l, ∃ (n : ℕ) (a : Per.Ainf l),
      y * ((l : ℕ) : Per.AinfP l) ^ n = algebraMap (Per.Ainf l) (Per.AinfP l) a := fun y => by
    obtain ⟨n, a, h⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) y
    exact ⟨n, a, by rwa [map_natCast] at h⟩
  have hz : ∀ y : Per.AinfP l, Per.θP l y = 0 → ∃ (n : ℕ) (a : Per.Ainf l), Per.θ l a = 0 ∧
      y * ((l : ℕ) : Per.AinfP l) ^ n = algebraMap (Per.Ainf l) (Per.AinfP l) a := fun y hy => by
    obtain ⟨n, a, h⟩ := hsurj y
    refine ⟨n, a, Subtype.ext ?_, h⟩
    rw [← hA, ← h, map_mul, hy, zero_mul]
    rfl
  have hker : RingHom.ker (Per.θP l) = Per.kerP l := by
    refine le_antisymm (fun y hy => ?_) (fun y hy => GlobalTheory.RingBasics.fontaineTheta_eq_zero_of_mem_ker l y (by rwa [pow_one]))
    obtain ⟨n, a, ha, h⟩ := hz y hy
    rw [← Ideal.mul_unit_mem_iff_mem _ (hu.pow n), h]
    exact GlobalTheory.RingIface.alg_mem_kerP l ha
  refine ⟨fun x => ?_, hker, hA, fun a => ?_, IsLocalization.isDomain_of_le_nonZeroDivisors _ hle,
    IsLocalization.injective _ hle, fun e he => ?_⟩
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖x * ((l : ℕ) : ℂ_[l]) ^ n‖ ≤ 1 := by
      have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
        (GlobalTheory.RingBasics.norm_p_lt (p := l))).const_mul ‖x‖
      rw [mul_zero] at h1
      obtain ⟨n, hn⟩ := (h1.eventually (eventually_le_nhds one_pos)).exists
      exact ⟨n, by rwa [norm_mul, norm_pow]⟩
    obtain ⟨a, ha⟩ := hs ⟨_, (GlobalTheory.RingBasics.mem_OC _).2 hn⟩
    obtain ⟨d, hd⟩ := (hu.pow n).exists_right_inv
    refine ⟨algebraMap _ _ a * d, ?_⟩
    have h2 := congrArg (Per.θP l) hd
    rw [map_mul, map_pow, map_natCast, map_one] at h2
    rw [map_mul, hA, ha, mul_assoc, h2, mul_one]
  · exact GlobalTheory.RingIface.thetaD_alg l a
  · obtain ⟨h1, -⟩ := hk e he
    refine le_antisymm (fun y hy => ?_) ?_
    · rw [← hker] at hy
      obtain ⟨n, a, ha, h⟩ := hz y hy
      rw [← Ideal.mul_unit_mem_iff_mem _ (hu.pow n), h]
      have h2 : a ∈ Ideal.span {xi e} := h1 ▸ ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 h2
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · rw [Ideal.span_singleton_le_iff_mem, ← hker, RingHom.mem_ker, hA, Model.theta_xi he]
      rfl

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveBcrisToBdR
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveBcrisToBdR
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem exists_injective_lift_field {R S K : Type} [CommRing R] [CommRing S] [CommRing K] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (hK : IsField K) (g : R →+* K) (hg : Function.Injective g)
    (hM : ∀ y ∈ M, y ≠ 0) :
    ∃ ι : S →+* K, (∀ x : R, ι (algebraMap R S x) = g x) ∧ Function.Injective ι := by
  have hu : ∀ y : M, IsUnit (g y) := by
    intro y
    have h : g y ≠ 0 := fun h => hM y y.2 (hg (by rw [h, map_zero]))
    obtain ⟨b, hb⟩ := hK.mul_inv_cancel h
    exact IsUnit.of_mul_eq_one b hb
  refine ⟨IsLocalization.lift hu, fun x => IsLocalization.lift_eq hu x, ?_⟩
  rw [IsLocalization.lift_injective_iff]
  intro x y
  constructor
  · intro h
    rw [← IsLocalization.lift_eq (S := S) hu x, h, IsLocalization.lift_eq]
  · intro h
    rw [hg h]

theorem algebraMap_ainf_acris_eq {l : ℕ} [Fact l.Prime] (x : Per.Ainf l) :
    algebraMap (Per.Ainf l) (Per.Acris l) x =
      algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) x) :=
  GlobalTheory.RingIface.tower l x

theorem algebraMap_ainf_acris_ne_zero_pt {l : ℕ} [Fact l.Prime] (j : Per.Acris l →+* Per.BdRp l)
    (hj : IsCrisP j) (x : Per.Ainf l) (hx0 : x ≠ 0) : algebraMap (Per.Ainf l) (Per.Acris l) x ≠ 0 := by
  obtain ⟨hd, -, hi⟩ := GlobalTheory.T.usage l
  intro h'
  apply hx0
  have h1 := hj.on0 (algebraMap (Per.Ainf l) (Per.Acris0 l) x)
  rw [← algebraMap_ainf_acris_eq] at h1
  rw [h', map_zero] at h1
  have h2 : ((algebraMap (Per.Ainf l) (Per.Acris0 l) x : Per.Acris0 l) : Per.AinfP l) = 0 :=
    GlobalTheory.T.algebraMap_ainfInvPrime_bdRPlus_injective l (by rw [map_zero]; exact h1.symm)
  exact hi (by rw [map_zero]; exact h2)

theorem pow_root_ne_zero {l : ℕ} [Fact l.Prime] (j : Per.Acris l →+* Per.BdRp l) (hj : IsCrisP j)
    (e : Per.Fl l) (hne : e ≠ 1) (n : ℕ) :
    algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm e - 1) ^ n ≠ 0 := by
  obtain ⟨hd, -, -⟩ := GlobalTheory.T.usage l
  rw [← map_pow]
  refine algebraMap_ainf_acris_ne_zero_pt j hj _ (pow_ne_zero n fun h => ?_)
  exact GlobalTheory.CrisLoc.constantCoeff_root_ne_zero l e hne (by rw [h, map_zero])

theorem exists_iota_cris_dR : ∀ (l : ℕ) [Fact l.Prime], ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j →
    ∃ ι : Per.Bcris l →+* Per.BdR l, (∀ x : Per.Acris l, ι (algebraMap (Per.Acris l) (Per.Bcris l) x) =
      algebraMap (Per.BdRp l) (Per.BdR l) (j x)) ∧ Function.Injective ι := by
  intro l _ j hj
  obtain ⟨-, hi, hK, -⟩ := GlobalTheory.T.bdRPlus_isDomain_bdR_isField l
  obtain ⟨e, he, hne⟩ := GlobalTheory.CrisLoc.exists_root_ne_one l
  haveI := GlobalTheory.CrisLoc.bcris_away l e he hne
  refine exists_injective_lift_field
    (Submonoid.powers (algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm e - 1))) hK
    ((algebraMap (Per.BdRp l) (Per.BdR l)).comp j) (hi.comp (GlobalTheory.T.acrisToBdRPlus_injective l j hj)) ?_
  rintro _ ⟨n, rfl⟩
  exact pow_root_ne_zero j hj e hne n

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveBcrisToBdRStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_bcris_to_bdR : ∀ (l : ℕ) [Fact l.Prime], ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → ∃ ι : Per.Bcris l →+* Per.BdR l, (∀ x : Per.Acris l, ι (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.BdRp l) (Per.BdR l) (j x)) ∧ Function.Injective ι := by
  first | exact @GlobalTheory.MemLoc.exists_iota_cris_dR | exact GlobalTheory.MemLoc.exists_iota_cris_dR | (intros; apply GlobalTheory.MemLoc.exists_iota_cris_dR <;> assumption)
end
end
