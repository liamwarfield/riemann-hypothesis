module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeneralAdmissibleOfIrreducibilityStmt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdLOfGaloisSectionsBreuilKisinCoproduct
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionExponentLeOfJumpsAtEmbeddingsUnramified
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisEqMulKisinInfTameSemidirect
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerSeriesLiftOfPeriodPowSmulIntegralMatr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeGaloisTrivialModUniformizer

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemMaximalIdealIff
noncomputable section

namespace GlobalTheory.TripleAdm

open NumberField IsDedekindDomain Polynomial Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.CyclotomicNorms (Fbar rootsBar IsGood IrredOn BB primeToPart)
open GlobalTheory.TameLabels GlobalTheory.TripleResidual

section Algebra

variable {g : ℕ} [Fact g.Prime]

theorem nodup_rootsBar {f : (ZMod g)[X]} (hf : Squarefree f) : (rootsBar f).Nodup :=
  nodup_roots ((separable_map _).2 (PerfectField.separable_iff_squarefree.2 hf))

theorem exists_dvd_of_stable {K : Type} [Field K] {N : ℕ} {f : (ZMod g)[X]} (hf : Squarefree f) (a : Fbar g →* K)
    (ha : ∀ x ∈ rootsBar f, ∀ y ∈ rootsBar f, a x = a y → x = y) (T P : GL (Fin N) K) (hP : P * T * P⁻¹ = T ^ g)
    (hT : (T : Matrix (Fin N) (Fin N) K).charpoly = ((rootsBar f).map fun x => X - C (a x)).prod)
    (W : Submodule K (Fin N → K)) (hTW : ∀ x ∈ W, (T : Matrix (Fin N) (Fin N) K).mulVec x ∈ W)
    (hPW : ∀ x ∈ W, ((P⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).mulVec x ∈ W) :
    ∃ q : (ZMod g)[X], q ∣ f ∧ q.natDegree = Module.finrank K W := by
  classical
  let t : Module.End K (Fin N → K) := Matrix.toLin' (T : Matrix (Fin N) (Fin N) K)
  have ht : ∀ x ∈ W, t x ∈ W := hTW
  set p := LinearMap.charpoly (t.restrict ht) with hp
  have hT' : (T : Matrix (Fin N) (Fin N) K).charpoly = (((rootsBar f).map a).map fun x => X - C x).prod := by
    rw [hT, Multiset.map_map]; rfl
  have hdvd : p ∣ (((rootsBar f).map a).map fun x => X - C x).prod := by
    rw [← hT', ← Matrix.charpoly_toLin', GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ W t ht]
    exact dvd_mul_right _ _
  have h0 : (((rootsBar f).map a).map fun x => X - C x).prod ≠ 0 := hT' ▸ (Matrix.charpoly_monic _).ne_zero
  have hle : p.roots ≤ (rootsBar f).map a := by
    have := roots.le_of_dvd h0 hdvd
    rwa [roots_multiset_prod_X_sub_C] at this
  have hcard : p.roots.card = Module.finrank K W := by
    rw [← LinearMap.charpoly_natDegree (t.restrict ht)]
    refine (Splits.natDegree_eq_card_roots ?_).symm
    exact Splits.of_dvd (Splits.multisetProd fun x hx => by
      obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hx
      exact Splits.X_sub_C _) h0 hdvd
  have hnd := nodup_rootsBar hf
  let S := (rootsBar f).filter fun x => a x ∈ p.roots
  have hS : S.map a = p.roots := by
    have h1 : ((rootsBar f).map a).Nodup := hnd.map_on ha
    rw [Multiset.Nodup.ext (Multiset.nodup_of_le (Multiset.map_le_map (Multiset.filter_le _ _)) h1)
      (Multiset.nodup_of_le hle h1)]
    intro z
    rw [Multiset.mem_map]
    refine ⟨?_, fun hz => ?_⟩
    · rintro ⟨x, hx, rfl⟩
      exact (Multiset.mem_filter.1 hx).2
    · obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_of_le hle hz)
      exact ⟨x, Multiset.mem_filter.2 ⟨hx, hz⟩, rfl⟩
  have hroot : ∀ c, c ∈ p.roots ↔ ∃ w ∈ W, w ≠ 0 ∧ (T : Matrix (Fin N) (Fin N) K).mulVec w = c • w := fun c => by
    rw [mem_roots (LinearMap.charpoly_monic _).ne_zero, ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    refine ⟨fun h => ?_, ?_⟩
    · obtain ⟨w, hw⟩ := h.exists_hasEigenvector
      exact ⟨w.1, w.2, fun h => hw.2 (Subtype.ext h), congrArg Subtype.val hw.apply_eq_smul⟩
    · rintro ⟨w, hw, h1, h2⟩
      exact Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨w, hw⟩)
        ⟨Module.End.mem_eigenspace_iff.2 (Subtype.ext h2), fun h => h1 (congrArg Subtype.val h)⟩
  have hst : ∀ x ∈ S, x ^ g ∈ S := fun x hx => by
    obtain ⟨hx1, hx2⟩ := Multiset.mem_filter.1 hx
    refine Multiset.mem_filter.2 ⟨TameLabels.rootsBar_frob f ▸ Multiset.mem_map_of_mem _ hx1, ?_⟩
    obtain ⟨w, hw, h1, h2⟩ := (hroot _).1 hx2
    have h3 : ∀ n : ℕ, ((T ^ n : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).mulVec w = a x ^ n • w := fun n => by
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, Units.val_mul, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_smul, ih, smul_smul,
          pow_succ']
    refine (hroot _).2 ⟨_, hPW w hw, fun h => h1 ?_, ?_⟩
    · rw [← Matrix.one_mulVec w, ← Units.val_one, ← mul_inv_cancel P, Units.val_mul, ← Matrix.mulVec_mulVec, h,
        Matrix.mulVec_zero]
    · rw [Matrix.mulVec_mulVec, ← Units.val_mul, show T * P⁻¹ = P⁻¹ * T ^ g by rw [← hP]; group, Units.val_mul,
        ← Matrix.mulVec_mulVec, h3, Matrix.mulVec_smul, map_pow]
  have hSn : S.Nodup := hnd.filter _
  obtain ⟨q, hq, hqS⟩ := GlobalTheory.Compare.TeichmullerRoots.exists_monic_of_stable S (by
    refine Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset (hSn.map (frobenius (Fbar g) g).injective)).2 ?_)
      (Multiset.card_map _ _).ge
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hy
    exact hst x hx)
  refine ⟨q, ?_, by rw [← TameLabels.card_rootsBar, hqS, ← hcard, ← hS, Multiset.card_map]⟩
  rw [← map_dvd_map' (algebraMap (ZMod g) (Fbar g))]
  refine (IsAlgClosed.splits _).dvd_of_roots_le_roots (hq.map _).ne_zero ?_
  exact hqS.trans_le (Multiset.filter_le _ _)

theorem irredOn_of_labels {l N : ℕ} [Fact l.Prime] {PP Γ : Type} [Group Γ] {f : PP → (ZMod g)[X]}
    (hd : ∀ v, (f v).natDegree = N) (hf : ∀ v, Squarefree (f v))
    (h4 : ∀ a : ℕ, 1 ≤ a → 2 * a ≤ N → ∃ v, ¬ ∃ q : (ZMod g)[X], q ∣ f v ∧ q.natDegree = a)
    (a : PP → Fbar g →* Fbar l) (ha : ∀ v, ∀ x ∈ rootsBar (f v), ∀ y ∈ rootsBar (f v), a v x = a v y → x = y)
    (ρ : Γ →* GL (Fin N) (Fbar l)) (τ : PP → Γ) (hφ : ∀ v, ∃ φ, ρ (φ * τ v * φ⁻¹) = ρ (τ v) ^ g)
    (hτ : ∀ v, ((ρ (τ v) : GL (Fin N) (Fbar l)) : Matrix (Fin N) (Fin N) (Fbar l)).charpoly =
      ((rootsBar (f v)).map fun x => X - C (a v x)).prod) : IrredOn ρ ⊤ := by
  intro W hW
  have key : ∀ v, ∃ q : (ZMod g)[X], q ∣ f v ∧ q.natDegree = Module.finrank (Fbar l) W := fun v => by
    obtain ⟨φ, h⟩ := hφ v
    rw [map_mul, map_mul, map_inv] at h
    exact exists_dvd_of_stable (hf v) (a v) (ha v) _ _ h (hτ v) W (hW _ trivial)
      (by rw [← map_inv]; exact hW _ trivial)
  have hle : Module.finrank (Fbar l) W ≤ N := by simpa using W.finrank_le
  by_contra hc
  rw [not_or] at hc
  have h0 : Module.finrank (Fbar l) W ≠ 0 := fun h => hc.1 (Submodule.finrank_eq_zero.1 h)
  have h1 : Module.finrank (Fbar l) W ≠ N := fun h => hc.2 (Submodule.eq_top_of_finrank_eq (by simpa using h))
  by_cases h : 2 * Module.finrank (Fbar l) W ≤ N
  · obtain ⟨v, hv⟩ := h4 _ (by omega) h
    exact hv (key v)
  · obtain ⟨v, hv⟩ := h4 (N - Module.finrank (Fbar l) W) (by omega) (by omega)
    obtain ⟨q, ⟨q', hq⟩, hqa⟩ := key v
    have hne : q * q' ≠ 0 := hq ▸ (hf v).ne_zero
    have hdeg := hd v
    rw [hq, natDegree_mul (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne)] at hdeg
    exact hv ⟨q', Dvd.intro_left _ hq.symm, by omega⟩

theorem primeToPart_eq_of_eq {l : ℕ} [Fact l.Prime] (a : Fbar g →* Fbar l)
    (ha : ∀ x y, x ≠ 0 → y ≠ 0 → (orderOf x).Coprime l → (orderOf y).Coprime l → a x = a y → x = y)
    {x y : Fbar g} (hx : x ≠ 0) (hy : y ≠ 0) (h : a x = a y) : primeToPart l x = primeToPart l y := by
  have key : ∀ x : Fbar g, x ≠ 0 → primeToPart l x ≠ 0 ∧ (orderOf (primeToPart l x)).Coprime l := fun x hx => by
    obtain ⟨-, M, -, h1, h2, -⟩ := GlobalTheory.TameRed.part_spec (Fact.out : l.Prime) (isOfFinOrder_of_ne_zero hx)
    exact ⟨pow_ne_zero _ hx, h1.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h2)⟩
  refine ha _ _ (key x hx).1 (key y hy).1 (key x hx).2 (key y hy).2 ?_
  rw [GlobalTheory.TypeLeaf.map_primeToPart_fbar, GlobalTheory.TypeLeaf.map_primeToPart_fbar, h]

theorem charpoly_smul_congr {K : Type} [Field K] [Infinite K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K} (c : Kˣ)
    (h : A.charpoly = B.charpoly) : ((c : K) • A).charpoly = ((c : K) • B).charpoly := by
  have e : ∀ (M : Matrix (Fin n) (Fin n) K) (z : K), Matrix.scalar (Fin n) z - (c : K) • M =
      (c : K) • (Matrix.scalar (Fin n) (z / c) - M) := fun M z => by
    rw [smul_sub, Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.diagonal_smul]
    congr 2
    funext x
    simp [mul_div_cancel₀ _ c.ne_zero]
  refine Polynomial.funext fun z => ?_
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly, e, e, Matrix.det_smul, Matrix.det_smul, ← Matrix.eval_charpoly,
    ← Matrix.eval_charpoly, h]

end Algebra

open GlobalTheory.TypeLeaf (WildOne FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf IsReduction Zbar GalE toFb)
open GlobalTheory.Triple (IsParam IsResidual Reading IsChars IsTripleWith IsTripleFor IsTripleOf IsTriple muBase hframe jIdx)
open GlobalTheory.TwistDet GlobalTheory.GalChar Formalism.L2.Host

variable {D : D7}

section Row

variable {σ : D.what₂.FT} {π : D.naut.CG D.R.r} {w : D.what₂.places.Pl}

theorem root_ne_zero (hg : D.nd.goodRow σ) (k : Fin 2) (v : D.nd.PlG k) {x : Fb (D.host.g k) (D.host.g_prime k)}
    (hx : x ∈ @rootsBar _ ⟨D.host.g_prime k⟩ (D.nd.lab k σ v)) : x ≠ 0 := by
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  rintro rfl
  exact ((hg k).1.1 v).2.2 ((GlobalTheory.Compare.TeichmullerRoots.zero_mem_rootsBar ((hg k).1.1 v).1).1 hx)

theorem toFb_ne_zero (k : Fin 2) (u : (ZMod (D.host.g k))ˣ) : toFb D k u ≠ 0 :=
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  (map_ne_zero_iff _ (algebraMap (ZMod (D.host.g k)) (Fbar (D.host.g k))).injective).2 u.ne_zero

end Row

section Comparison₂

variable {Y : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : Y.Tw} {b : Bool}

theorem norm_toQ_le (ρ : Reading Y i b) (x : Y.O0 i) : ‖toQ ρ.κ x‖ ≤ 1 := by
  have h : IsIntegral ℤ_[Y.l i] x := Algebra.IsIntegral.isIntegral x
  let f : Y.O0 i →ₐ[ℤ_[Y.l i]] Qbar (Y.l i) := { toQ ρ.κ with commutes' := ρ.κ_alg }
  obtain ⟨p, hp, h0⟩ : IsIntegral ℤ_[Y.l i] (toQ ρ.κ x) := h.map f
  let v := NormedField.valuation (K := Qbar (Y.l i))
  let z : ℤ_[Y.l i] →+* v.integer := (algebraMap ℤ_[Y.l i] (Qbar (Y.l i))).codRestrict _ fun a => by
    change ‖algebraMap ℚ_[Y.l i] (Qbar (Y.l i)) (a : ℚ_[Y.l i])‖ ≤ 1
    rw [norm_algebraMap']
    exact a.2
  exact (Valuation.integer.integers v).mem_of_integral ⟨p.map z, hp.map z, by rw [eval₂_map]; exact h0⟩

def toZ (ρ : Reading Y i b) : Y.O0 i →+* Zbar (Y.l i) := (toQ ρ.κ).codRestrict _ (norm_toQ_le ρ)

theorem mem_maximalIdeal_iff (ρ : Reading Y i b) (x : Y.O0 i) :
    x ∈ IsLocalRing.maximalIdeal (Y.O0 i) ↔ ‖toQ ρ.κ x‖ < 1 := by
  obtain ⟨-, -, hint, -⟩ := GlobalTheory.CoefEmbed.embedding_closed_integral _ _ (Y.twistBaseCoefficientRing_isAdic i) ρ.κ ρ.κ_alg
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← not_le, not_iff_not]
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨u, rfl⟩
    have h1 : ‖toQ ρ.κ u‖ * ‖toQ ρ.κ (u⁻¹ : (Y.O0 i)ˣ)‖ = 1 := by
      rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
    nlinarith [norm_toQ_le ρ (u⁻¹ : (Y.O0 i)ˣ), norm_nonneg (toQ ρ.κ u)]
  · have h0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero, norm_zero] at h
      exact absurd h (by norm_num)
    obtain ⟨y, hy⟩ := hint (algebraMap (Y.O0 i) (FractionRing (Y.O0 i)) x)⁻¹ (by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ h)
    refine IsUnit.of_mul_eq_one y (IsFractionRing.injective _ (FractionRing (Y.O0 i)) ?_)
    rw [map_mul, hy, map_one, mul_inv_cancel₀ ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 h0)]

theorem exists_residue_lift (ρ : Reading Y i b) {K : Type} [Field K] (f : Y.O0 i →+* K) (hl : ((Y.l i : ℕ) : K) = 0) :
    ∃ κ : IsLocalRing.ResidueField (Y.O0 i) →+* K, ∀ x, κ (IsLocalRing.residue _ x) = f x := by
  have h0 : RingHom.ker f ≠ ⊥ := fun h => by
    have h1 : ((Y.l i : ℕ) : Y.O0 i) ∈ RingHom.ker f := by rw [RingHom.mem_ker, map_natCast, hl]
    rw [h, Ideal.mem_bot] at h1
    have h2 := congrArg (toQ ρ.κ) h1
    rw [map_natCast, map_zero] at h2
    exact (Y.lPrime i).out.ne_zero (by exact_mod_cast h2)
  have h1 := IsLocalRing.eq_maximalIdeal ((RingHom.ker_isPrime f).isMaximal h0)
  exact ⟨Ideal.Quotient.lift _ f fun x hx => by rwa [← h1] at hx, fun _ => rfl⟩

variable {C : CharFrame D} {art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om}

theorem antiHom_of_isLAdicOf (ha : GlobalTheory.HeckeGal.IsGlobalArtin art) {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ}
    {χ : HChar D.host.E} {n : (D.host.E →+* ℂ) → ℤ} {r : GalE D →* (Qbar l)ˣ} (hc : Continuous r)
    (h : GlobalTheory.HeckeGal.IsLAdicOf art ι χ n r) (ht : χ.TrivOn D.host.F) : AntiHom Y.cc r := by
  obtain ⟨c, hc1, hcm, hr, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  have h1 : ∀ x : D.host.E, Y.cc (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (c x) := fun x => by
    obtain ⟨j, hj⟩ := Y.cc_cm.1
    apply j.injective
    rw [hj, hc1]
    exact (D.host.conjE_apply (j.comp (algebraMap D.host.E D.nd.Om)) x).symm
  exact GlobalTheory.AntiLAdic.antiHom_of_trivOn D.host.F D.host.E c hcm.rank hcm.ne (fun x => by rw [hc1, hc1, conj_conj]) hr
    D.nd.Om Y.cc h1 art ha l ι χ n _ hc h ht

variable {Z : NExp D.R D.host D.what₂ D.LL0 D.nd Y}

end Comparison₂

end GlobalTheory.TripleAdm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopeFrobeniusSolutionsPowDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopeFrobeniusSolutionsPowDvd
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem envelope_dvd_lpow_aux₁ {R : Type} [CommRing R] {ι : Type} (s : Finset ι) (L a b : R) (u v : ι → R)
    (hL : L ∈ nonZeroDivisors R) (h : a * (L * b) = ∑ i ∈ s, L * u i * v i) : a * b = ∑ i ∈ s, u i * v i := by
  refine sub_eq_zero.1 ((mem_nonZeroDivisors_iff.mp hL).2 _ ?_)
  have e : ∑ i ∈ s, u i * v i * L = ∑ i ∈ s, L * u i * v i := Finset.sum_congr rfl fun i _ => by ring
  rw [sub_mul, Finset.sum_mul, e, ← h]
  ring

theorem envelope_dvd_lpow_aux₂ {R : Type} [CommRing R] (L w z : R) (k : ℕ)
    (hL : ∀ x : R, L * x = 0 → x = 0) (h : L * w = L ^ (k + 1) * z) : L ^ k ∣ w :=
  ⟨z, sub_eq_zero.1 (hL _ (by rw [mul_sub, h, pow_succ', mul_assoc, sub_self]))⟩

theorem envelope_dvd_lpow_aux₄ {R : Type} [CommRing R] (L x y : R) (k : ℕ) (hxy : x = L * y) (h : L ^ k ∣ y) :
    L ^ (k + 1) ∣ x := by
  rw [hxy, pow_succ']
  exact mul_dvd_mul_left _ h

theorem envelope_dvd_lpow_aux₃ {l : ℕ} [Fact l.Prime] {K : FinExt l} {B : Obj l ↥(OL K)} (σ : Hom B (ainfObj K))
    (x y : B.A) (k : ℕ) (hxy : x = (l : B.A) * y) (h : ((l : ℕ) : (ainfObj K).A) ^ (k + 1) ∣ σ.f x) :
    ((l : ℕ) : (ainfObj K).A) ^ k ∣ σ.f y := by
  subst hxy
  obtain ⟨z, hz⟩ := h
  rw [map_mul, map_natCast] at hz
  exact envelope_dvd_lpow_aux₂ (R := Ainf l) (l : Ainf l) (σ.f y) z k ainf_torsionFree hz

theorem envelope_dvd_lpow_of_sections : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (κ : Type) [Fintype κ] (c : κ → κ → En.Q.A) (h k : ℕ) (x : κ → En.Q.A), (∀ j, BK.hf En.inl bk.E ^ h * x j = ∑ i, En.Q.D.φ (x i) * c i j) → (∀ (g : ↥(GK K)) (σ : Hom En.Q (ainfObj K)), σ.comp En.inl = bk.ι → σ.comp En.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ^ k ∣ σ.f (x j)) → ∀ j, ((l : ℕ) : En.Q.A) ^ k ∣ x j := by
  intro l _ K bk En κ _ c h k
  have hreg : ((l : ℕ) : En.Q.A) ∈ nonZeroDivisors En.Q.A :=
    (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk En.Q.A (BK.hf En.inl) (Digits l) En.tb).2.2.1
  induction k with
  | zero => intro x _ _ j; rw [pow_zero]; exact one_dvd _
  | succ k ih =>
    intro x hx hσ j
    have h1 := GlobalTheory.T.dvd_l_of_galoisSections_breuilKisinCoproduct l K bk En κ x c h hx
      (fun g σ e1 e2 i => dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero k)) (hσ g σ e1 e2 i))
    choose y hy using h1
    have hyeq : ∀ j, BK.hf En.inl bk.E ^ h * y j = ∑ i, En.Q.D.φ (y i) * c i j := by
      intro j
      have hxj := hx j
      simp only [hy, map_mul, map_natCast] at hxj
      exact envelope_dvd_lpow_aux₁ Finset.univ _ _ _ (fun i => En.Q.D.φ (y i)) (fun i => c i j) hreg hxj
    have hσ' : ∀ (g : ↥(GK K)) (σ : Hom En.Q (ainfObj K)), σ.comp En.inl = bk.ι →
        σ.comp En.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ^ k ∣ σ.f (y j) := by
      intro g σ e1 e2 i
      exact envelope_dvd_lpow_aux₃ σ (x i) (y i) k (hy i) (hσ g σ e1 e2 i)
    exact envelope_dvd_lpow_aux₄ _ _ _ k (hy j) (ih y hyeq hσ' j)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopeFrobeniusSolutionsPowDvdStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_envelope_frobenius_solutions_pow_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (κ : Type) [Fintype κ] (c : κ → κ → En.Q.A) (h k : ℕ) (x : κ → En.Q.A), (∀ j, BK.hf En.inl bk.E ^ h * x j = ∑ i, En.Q.D.φ (x i) * c i j) → (∀ (g : ↥(GK K)) (σ : Hom En.Q (ainfObj K)), σ.comp En.inl = bk.ι → σ.comp En.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ^ k ∣ σ.f (x j)) → ∀ j, ((l : ℕ) : En.Q.A) ^ k ∣ x j := by
  first | exact @GlobalTheory.envelope_dvd_lpow_of_sections | exact GlobalTheory.envelope_dvd_lpow_of_sections | (intros; apply GlobalTheory.envelope_dvd_lpow_of_sections <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanLStable
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

noncomputable section

namespace GlobalTheory.Pass.LocDual.OneX

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

abbrev gl (g : Br.G D.nbr i w hw) : GE D.nd := ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd)

def vecL {a : ℕ} (v : Fin a → Fin D.R.nV → KK D.nd i) : Fin a → Fin D.R.nV → Br.LL D.nbr i w hw :=
  fun b j => Br.toLLK (D.nbr i w hw) (v b j)

def spanL {a : ℕ} (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) :
    Submodule (Br.LL D.nbr i w hw) (Fin a → Fin D.R.nV → Br.LL D.nbr i w hw) :=
  Submodule.span _ (vecL i w hw '' (Y : Set (Fin a → Fin D.R.nV → KK D.nd i)))

theorem loc_mulVec {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw)
    (v : Fin k → KK D.nd i) :
    (Br.loc D.nbr i w hw M g).mulVec (fun j => Br.toLLK (D.nbr i w hw) (v j)) =
      fun j => Br.toLLK (D.nbr i w hw) ((mapM (toK D.nd i) M (gl i w hw g)).mulVec v j) := by
  funext j
  rw [RingHom.map_mulVec]
  congr 1
  ext p q
  simp [Br.loc, Br.locM, Br.locO, mapM, Br.iota, Br.toLLK_alg]
  rfl

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i))

theorem contTw (hr : GoodR D.nd i r) (x : ↥Xs) (v : Fin D.R.nV → Br.LL D.nbr i w hw) :
    Continuous fun g => (Br.loc D.nbr i w hw (rTwO D.nd i r x) g).mulVec v :=
  (GlobalTheory.JumpDual.loc_cont D i w hw _ (GlobalTheory.T.twisted_dual_families_continuous D i r hr x).1).matrix_mulVec continuous_const

def sumG (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs) :
    GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
  GRep.sum (fun x : ↥Xs => Br.loc D.nbr i w hw (rTwO D.nd i r x)) (contTw i w hw r Xs hr) x

def actK {a : ℕ} (x : Fin a → ↥Xs) (γ : GE D.nd) (v : Fin a → Fin D.R.nV → KK D.nd i) :
    Fin a → Fin D.R.nV → KK D.nd i :=
  fun b => (mapM (toK D.nd i) (rTwO D.nd i r (x b)) γ).mulVec (v b)

theorem sumG_vecL (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs) (g : Br.G D.nbr i w hw)
    (v : Fin a → Fin D.R.nV → KK D.nd i) :
    (sumG i w hw r Xs hr x).ρ g (vecL i w hw v) = vecL i w hw (actK i r Xs x (gl i w hw g) v) := by
  funext b
  exact loc_mulVec i w hw _ g (v b)

theorem spanL_stable (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y) :
    ∀ g, ∀ u ∈ spanL i w hw Y, (sumG i w hw r Xs hr x).ρ g u ∈ spanL i w hw Y := by
  intro g u hu
  have h : spanL i w hw Y ≤ (spanL i w hw Y).comap ((sumG i w hw r Xs hr x).ρ g) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    show (sumG i w hw r Xs hr x).ρ g (vecL i w hw y) ∈ spanL i w hw Y
    rw [sumG_vecL]
    exact Submodule.subset_span ⟨_, hst _ y hy, rfl⟩
  exact h hu

def XG (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y) :
    GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
  (sumG i w hw r Xs hr x).sub (spanL i w hw Y) (spanL_stable i w hw r Xs hr x Y hst)

def latY {a : ℕ} (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) :
    Submodule (Br.OLL D.nbr i w hw) ↥(spanL i w hw Y) :=
  Submodule.span _ {u | (u : Fin a → Fin D.R.nV → Br.LL D.nbr i w hw) ∈ vecL i w hw '' (Y : Set _)}

def yfun {a : ℕ} (x : Fin a → ↥Xs) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (E : Fin a → Fin D.R.nV → KK D.nd i) (hE : ∀ γ : GE D.nd, actK i r Xs x γ E - E ∈ Y)
    (g : Br.G D.nbr i w hw) : ↥(spanL i w hw Y) :=
  ⟨vecL i w hw (actK i r Xs x (gl i w hw g) E - E), Submodule.subset_span ⟨_, hE _, rfl⟩⟩

end GlobalTheory.Pass.LocDual.OneX

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthModuloSpanLeOfForallFinset
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthModuloSpanLeOfForallFinset
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

namespace GlobalTheory.Pass.LocDual

theorem lenMod_eq_height_map {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (S H : Submodule O M) : BlochKatoDuality.lenMod S H = Order.height (S.map H.mkQ) := by
  show Module.length O (↥(S ⊔ H) ⧸ H.comap (S ⊔ H).subtype) = _
  have hker : LinearMap.ker (H.mkQ ∘ₗ (S ⊔ H).subtype) = H.comap (S ⊔ H).subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hrange : LinearMap.range (H.mkQ ∘ₗ (S ⊔ H).subtype) = S.map H.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype, Submodule.map_sup, Submodule.mkQ_map_self,
      sup_bot_eq]
  rw [← Module.length_submodule]
  exact ((Submodule.quotEquivOfEq _ _ hker.symm).trans
    ((H.mkQ ∘ₗ (S ⊔ H).subtype).quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))).length_eq

theorem height_map_span_le_of_finset {O M N : Type} [CommRing O] [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (f : M →ₗ[O] N) (S : Set M) (b : ℕ∞)
    (h : ∀ F : Finset M, (↑F : Set M) ⊆ S →
      Order.height ((Submodule.span O (↑F : Set M)).map f) ≤ b) :
    Order.height ((Submodule.span O S).map f) ≤ b := by
  classical
  rw [Order.height_le_iff]
  intro p hp

  have hx : ∀ i : Fin p.length, ∃ x ∈ p i.succ, x ∉ p i.castSucc :=
    fun i => SetLike.exists_of_lt (p.step i)
  choose x hxin hxout using hx

  have hfin : ∀ i : Fin p.length, ∃ F : Finset M, (↑F : Set M) ⊆ S ∧
      x i ∈ (Submodule.span O (↑F : Set M)).map f := by
    intro i
    have hxi : x i ∈ (Submodule.span O S).map f := hp (p.monotone (Fin.le_last i.succ) (hxin i))
    obtain ⟨y, hyS, hyx⟩ := Submodule.mem_map.mp hxi
    obtain ⟨T, hTS, hyT⟩ := Submodule.mem_span_finite_of_mem_span hyS
    exact ⟨T, hTS, Submodule.mem_map.mpr ⟨y, hyT, hyx⟩⟩
  choose F hFS hxF using hfin
  let G : Finset M := Finset.univ.biUnion F
  have hGS : (↑G : Set M) ⊆ S := by
    intro z hz
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hz
    exact hFS i hi
  have hFG : ∀ i, Submodule.span O (↑(F i) : Set M) ≤ Submodule.span O (↑G : Set M) := fun i =>
    Submodule.span_mono (fun z hz => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hz⟩)

  let Q := (Submodule.span O (↑G : Set M)).map f
  let q : LTSeries (Submodule O N) := LTSeries.mk p.length (fun j => p j ⊓ Q) (by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    dsimp only
    refine lt_of_le_of_ne (inf_le_inf_right _ (p.monotone (Fin.castSucc_le_succ i))) ?_
    intro heq
    have h1 : x i ∈ p i.succ ⊓ Q :=
      Submodule.mem_inf.mpr ⟨hxin i, Submodule.map_mono (hFG i) (hxF i)⟩
    rw [← heq] at h1
    exact hxout i (Submodule.mem_inf.mp h1).1)
  calc (p.length : ℕ∞) = q.length := rfl
    _ ≤ Order.height Q := Order.length_le_height inf_le_right
    _ ≤ b := h G hGS

theorem lenMod_span_le_of_finset : ∀ {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (S : Set M) (H : Submodule O M) (b : ℕ∞),
    (∀ F : Finset M, (↑F : Set M) ⊆ S → BlochKatoDuality.lenMod (Submodule.span O (↑F : Set M)) H ≤ b) →
    BlochKatoDuality.lenMod (Submodule.span O S) H ≤ b := by
  intro O M _ _ _ S H b h
  rw [lenMod_eq_height_map]
  apply height_map_span_le_of_finset H.mkQ S b
  intro F hF
  rw [← lenMod_eq_height_map]
  exact h F hF

end GlobalTheory.Pass.LocDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthModuloSpanLeOfForallFinsetStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lengthModulo_span_le_of_forall_finset : ∀ {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (S : Set M) (H : Submodule O M) (b : ℕ∞),
    (∀ F : Finset M, (↑F : Set M) ⊆ S → BlochKatoDuality.lenMod (Submodule.span O (↑F : Set M)) H ≤ b) →
    BlochKatoDuality.lenMod (Submodule.span O S) H ≤ b := by
  first | exact @GlobalTheory.Pass.LocDual.lenMod_span_le_of_finset | exact GlobalTheory.Pass.LocDual.lenMod_span_le_of_finset | (intros; apply GlobalTheory.Pass.LocDual.lenMod_span_le_of_finset <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeHomLiftsBreuilKisinDescentHom
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeHomLiftsBreuilKisinDescentHom
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.PackMap

section General

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e}
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {G : Type} [Group G] [TopologicalSpace G]

theorem latW_TWact {T T' : LocLat G ℚ_[l] K O} (f : LatHom T.L T'.L) (s : GQ l) (g : G)
    (y : TW (OW l O) T) :
    latW f (TWact (galOW O s) T g y) = TWact (galOW O s) T' g (latW f y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul w x =>
    simp only [latW, TWact, TensorProduct.map_tmul]
    congr 1
    exact Subtype.ext (f.equiv g x)
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem homW_act {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T T' : LocLat G ℚ_[l] K O}
    {I : Ident t ϖ P T} {I' : Ident t ϖ Q T'} {f : LatHom T.L T'.L} {F : BK.Hom P Q}
    (h : IsMapOf I I' f F) (s : GQ l) (g : G) (v : ι → OW l O) :
    homW t ϖ F (I.act s g v) = I'.act s g (homW t ϖ F v) :=
  I'.j.injective (by rw [h, I.j_act, latW_TWact, I'.j_act, h])

variable [TameDescentExponentData K l e a]

theorem app_act_of_cover {s : G →* GQ l} {η H η' H' : ℕ} {D₁ : BKDat O K l e a ι η H}
    {D₂ : BKDat O K l e a κ η' H'} {T₁ T₂ : LocLat G ℚ_[l] K O} (R₁ : GalDat t ϖ s D₁ T₁)
    (R₂ : GalDat t ϖ s D₂ T₂) {f : LatHom T₁.L T₂.L} {F : BK.Hom D₁.toPhiMod D₂.toPhiMod}
    (hF : IsMapOf R₁.I R₂.I f F) (hcov : ∀ γ : TameGal K l e a, ∃ g : G, Covers K t ϖ (s g) γ)
    (γ : TameGal K l e a) (v : Vec K a ι) :
    F.app (D₁.desc.act γ v) = D₂.desc.act γ (F.app v) := by
  have hb : ∀ i : ι, F.app (D₁.desc.act γ (bas i)) = D₂.desc.act γ (F.app (bas i)) := by
    intro i
    obtain ⟨g, hg⟩ := hcov γ
    have m0 : (bas i : Vec K a ι) ∈ D₁.M := PhiMod.bas_mem_M _ i
    have m1 : D₁.desc.act γ (bas i) ∈ D₁.M := D₁.desc.act_mem_M γ _ m0
    have m2 : F.app (bas i) ∈ D₂.M := F.app_mem_M m0
    have m3 : D₂.desc.act γ (F.app (bas i)) ∈ D₂.M := D₂.desc.act_mem_M γ _ m2
    have m4 : F.app (D₁.desc.act γ (bas i)) ∈ D₂.M := F.app_mem_M m1
    have e1 := R₁.desc g γ hg ⟨_, mem_ME_of_mem_M m0⟩ ⟨_, mem_ME_of_mem_M m1⟩ rfl
    have e2 := R₂.desc g γ hg ⟨_, mem_ME_of_mem_M m2⟩ ⟨_, mem_ME_of_mem_M m3⟩ rfl
    have h1 := homW_toW t ϖ F ⟨_, mem_ME_of_mem_M m1⟩
    have h2 := homW_toW t ϖ F ⟨_, mem_ME_of_mem_M m0⟩
    have key : toW t ϖ D₂.toPhiMod ⟨_, mem_ME_of_mem_M m4⟩ =
        toW t ϖ D₂.toPhiMod ⟨_, mem_ME_of_mem_M m3⟩ :=
      calc toW t ϖ D₂.toPhiMod ⟨_, mem_ME_of_mem_M m4⟩
          = homW t ϖ F (toW t ϖ D₁.toPhiMod ⟨_, mem_ME_of_mem_M m1⟩) := h1.symm
        _ = homW t ϖ F (R₁.I.act (s g) g (toW t ϖ D₁.toPhiMod ⟨_, mem_ME_of_mem_M m0⟩)) := by rw [e1]
        _ = R₂.I.act (s g) g (homW t ϖ F (toW t ϖ D₁.toPhiMod ⟨_, mem_ME_of_mem_M m0⟩)) :=
          homW_act hF _ _ _
        _ = R₂.I.act (s g) g (toW t ϖ D₂.toPhiMod ⟨_, mem_ME_of_mem_M m2⟩) := by rw [h2]
        _ = toW t ϖ D₂.toPhiMod ⟨_, mem_ME_of_mem_M m3⟩ := e2
    exact congrArg Subtype.val (toW_injective t ϖ _ key)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [eq_sum_bas v, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [D₁.desc.act_smul_tot, F.app_smul_tot, F.app_smul_tot, D₂.desc.act_smul_tot, hb]

end General

theorem main : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e]
    (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (η H : ℕ) (T₁ T₂ : QLat LL)
    (P₁ : Pack a ϖ η H T₁) (P₂ : Pack a ϖ η H T₂) (f : LatHom T₁.L T₂.L),
    ∃ F : BKHom P₁.D P₂.D, IsMapOf P₁.R.I P₂.R.I f F.toHom := by
  intro BS l _ a e _ _ ϖ LL _ _ η H T₁ T₂ P₁ P₂ f
  let f' : LatHom (resF T₁ (ϖ.field a)).L (resF T₂ (ϖ.field a)).L :=
    ⟨f.f, fun _ x => f.equiv _ x, f.cont, f.T_le⟩
  obtain ⟨F, hF⟩ := GlobalTheory.BKReal.Full.main BS l a e _ _ (thetaW a LL) ϖ _ _ P₁.D.toPhiMod P₂.D.toPhiMod
    (resF T₁ (ϖ.field a)) (resF T₂ (ϖ.field a))
    (P₁.R.I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _))
    (P₂.R.I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) P₁.isBK P₂.isBK f'
  have hF' : IsMapOf P₁.R.I P₂.R.I f F := hF
  have hcov : ∀ γ : TameGal ↥LL.1 l e a, ∃ g : Gl l, Covers ↥LL.1 (thetaW a LL) ϖ (sQ l g) γ := fun γ => by
    obtain ⟨k, -, hc⟩ := (GlobalTheory.T.galois_eq_mul_kisinInf_tameSemidirect l a e ϖ LL).2.2.1 γ
    refine ⟨⟨k, ?_⟩, hc⟩
    show k ∈ (⊥ : IntermediateField ℚ_[l] (Om l)).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_bot]
    trivial
  exact ⟨⟨F, app_act_of_cover P₁.R P₂.R hF' hcov⟩, hF'⟩

end GlobalTheory.BKGal.PackMap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeHomLiftsBreuilKisinDescentHomStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeHom_lifts_breuilKisinDescentHom : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (η H : ℕ) (T₁ T₂ : QLat LL) (P₁ : Pack a ϖ η H T₁) (P₂ : Pack a ϖ η H T₂) (f : LatHom T₁.L T₂.L), ∃ F : BKHom P₁.D P₂.D, IsMapOf P₁.R.I P₂.R.I f F.toHom := by
  first | exact @GlobalTheory.BKGal.PackMap.main | exact GlobalTheory.BKGal.PackMap.main | (intros; apply GlobalTheory.BKGal.PackMap.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantMapBreuilKisinMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantMapBreuilKisinMatrix
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.EquivKisin


set_option maxHeartbeats 1000000 in
theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N N' d d' : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') (ℤ_[l])) (F : Pre bk N d ρ) (F' : Pre bk N' d' ρ') (f : Matrix (Fin d') (Fin d) (ℤ_[l])), (∀ g, f * ρ g = ρ' g * f) → ∃ Y : Matrix (Fin d') (Fin d) (bk.S), F'.T * Y.map bk.evW = zW f * F.T := by
  intro l _ K bk τ hτ N N' d d' ρ ρ' F F' f hf
  obtain ⟨u, hu⟩ := F'.unit
  have cancel : ∀ M M' : Matrix (Fin d') (Fin d) (WCb l), F'.T * M = F'.T * M' → M = M' := by
    intro M M' h
    have h2 := congrArg (fun Z => (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l)) * Z) h
    simp only [← hu, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at h2
    exact h2
  have hzmul : ∀ {m n o : Type} [Fintype n] (A : Matrix m n ℤ_[l]) (B : Matrix n o ℤ_[l]),
      zW (A * B) = zW A * zW B := fun A B => Matrix.map_mul
  set Xm : Matrix (Fin d') (Fin d) (WCb l) := (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l)) * (zW f * F.T) with hXm
  have hX : F'.T * Xm = zW f * F.T := by
    rw [hXm, ← hu, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

  have hfix : ∀ g : ↥(GK K), bk.FixFlat g → Xm.map (galW l (g : GQ l)) = Xm := by
    intro g hg
    let G : WCb l →+* WCb l := (galW l (g : GQ l)).toRingEquiv.toRingHom
    have hzG : ∀ {m n : Type} (M : Matrix m n ℤ_[l]), (zW M).map G = zW M :=
      fun M => Matrix.ext fun i j => (galW l (g : GQ l)).commutes _
    have a1 : zW (ρ' g) * F'.T.map G = F'.T := F'.fix g hg
    have a2 : zW (ρ g) * F.T.map G = F.T := F.fix g hg
    change Xm.map G = Xm
    apply cancel
    have h1 := congrArg (fun M => M.map G) hX
    simp only [Matrix.map_mul, hzG] at h1
    calc F'.T * Xm.map G = zW (ρ' g) * (F'.T.map G * Xm.map G) := by
          rw [← Matrix.mul_assoc, a1]
      _ = zW (ρ' g * f) * F.T.map G := by rw [h1, hzmul, Matrix.mul_assoc]
      _ = zW f * (zW (ρ g) * F.T.map G) := by rw [← hf g, hzmul, Matrix.mul_assoc]
      _ = F'.T * Xm := by rw [a2, hX]

  have hφ : bk.evW bk.E ^ N • (F'.A.map bk.evW * Xm.map (frobW l)) =
      bk.evW bk.E ^ N' • (Xm * F.A.map bk.evW) := by
    let Fr : WCb l →+* WCb l := (frobW l).toRingHom
    have hzF : ∀ {m n : Type} (M : Matrix m n ℤ_[l]), (zW M).map Fr = zW M :=
      fun M => Matrix.ext fun i j => (frobW l).commutes _
    have b1 : bk.evW bk.E ^ N • F.T.map Fr = F.T * F.A.map bk.evW := F.φ
    have b2 : bk.evW bk.E ^ N' • F'.T.map Fr = F'.T * F'.A.map bk.evW := F'.φ
    change bk.evW bk.E ^ N • (F'.A.map bk.evW * Xm.map Fr) = bk.evW bk.E ^ N' • (Xm * F.A.map bk.evW)
    apply cancel
    have h1 := congrArg (fun M => M.map Fr) hX
    simp only [Matrix.map_mul, hzF] at h1
    rw [Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc, ← b2, Matrix.smul_mul, h1, smul_smul,
      ← Matrix.mul_assoc, hX, Matrix.mul_assoc, ← b1, Matrix.mul_smul, smul_smul, mul_comm]

  have hOE : ∀ i j, Xm i j ∈ bk.OE := by
    obtain ⟨w, hw, hew⟩ := (GlobalTheory.T.integral_elements_unit_factorization l K bk).2.2.1 bk.E (GlobalTheory.BSP.EquivOE.not_dvd_E bk)
    have hA : F.A.map bk.evW * F.A'.map bk.evW =
        bk.evW bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (WCb l)) := by
      rw [← Matrix.map_mul, F.A_mul]
      ext i j
      by_cases h : i = j <;> simp [h, Matrix.one_apply]
    have h1 : Xm = (w ^ (N' + 2 * N) * bk.evW bk.E ^ N) •
        (F'.A.map bk.evW * Xm.map (frobW l) * F.A'.map bk.evW) := by
      rw [mul_smul, ← Matrix.smul_mul, hφ, Matrix.smul_mul, Matrix.mul_assoc, hA, Matrix.mul_smul, Matrix.mul_one,
        smul_smul, smul_smul, mul_assoc, ← pow_add, ← mul_pow, mul_comm w, hew, one_pow, one_smul]
    intro i j
    refine GlobalTheory.T.mem_OE_of_invariant_frobenius_solution l K bk (Fin d' × Fin d) (fun p => Xm p.1 p.2)
      (fun p q => w ^ (N' + 2 * N) * bk.evW bk.E ^ N * bk.evW (F'.A q.1 p.1) * bk.evW (F.A' p.2 q.2))
      (fun p q => ?_) (fun q => ?_) (fun g h q => ?_) (i, j)
    · exact bk.OE.mul_mem (bk.OE.mul_mem (bk.OE.mul_mem (bk.OE.pow_mem hw _)
        (bk.OE.pow_mem (GlobalTheory.BSP.EquivOE.evW_mem bk _) _)) (GlobalTheory.BSP.EquivOE.evW_mem bk _))
        (GlobalTheory.BSP.EquivOE.evW_mem bk _)
    · have h2 := congrFun (congrFun h1 q.1) q.2
      rw [h2, Fintype.sum_prod_type_right]
      simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => by ring
    · exact congrFun (congrFun (hfix g h) q.1) q.2

  obtain ⟨Y₁, Y₁', hY₁, hY₁'⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N' d' ρ' F'
  obtain ⟨Y₂, Y₂', hY₂, hY₂'⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N d ρ F
  set t : WCb l := inclW l τ with ht
  have hinv : t ^ N' • Y₁'.map (inclW l) = t ^ N' • (t ^ N' • (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l))) := by
    have e1 := congrArg (fun M => M.map (inclW l)) hY₁'
    simp only [Matrix.map_mul, hY₁] at e1
    have e2 : (τ ^ (2 * N') • (1 : Matrix (Fin d') (Fin d') (Ainf l))).map (inclW l) =
        (t ^ N' * t ^ N') • (1 : Matrix (Fin d') (Fin d') (WCb l)) := by
      ext i j
      by_cases h : i = j <;> simp [h, Matrix.one_apply, ht, ← pow_add, two_mul]
    rw [e2, Matrix.smul_mul, ← hu] at e1
    have e3 := congrArg (fun Z => (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l)) * Z) e1
    simp only [Matrix.mul_smul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_one] at e3
    rw [e3, smul_smul]
  have hzf : (f.map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) = zW f := by
    exact Matrix.ext fun i j => (inclWA l).commutes (f i j)
  let x : Matrix (Fin d') (Fin d) (Ainf l) := τ ^ N' • (Y₁' * f.map (algebraMap ℤ_[l] (Ainf l)) * Y₂)
  have hx : x.map (inclW l) = inclW l τ ^ (2 * N' + N) • Xm := by
    have : x.map (inclW l) = t ^ N' • (Y₁'.map (inclW l) * zW f * (t ^ N • F.T)) := by
      have e : x.map (inclW l) = t ^ N' • ((Y₁' * f.map (algebraMap ℤ_[l] (Ainf l)) * Y₂).map (inclW l)) :=
        Matrix.ext fun i j => by simp only [x, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, ht]
      rw [e, Matrix.map_mul, Matrix.map_mul, hzf, hY₂]
    rw [this, ← Matrix.smul_mul, ← Matrix.smul_mul, hinv, hXm]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
    rw [← ht]
    congr 1
    ring
  obtain ⟨Y, hY⟩ := GlobalTheory.T.exists_powerSeries_lift_of_period_pow_smul_integral_matrix l K bk τ hτ d d' (2 * N' + N) Xm x hOE hx
  exact ⟨Y, by rw [hY, hX]⟩

end GlobalTheory.BKLim.EquivKisin

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantMapBreuilKisinMatrixStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equivariantMap_breuilKisinMatrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N N' d d' : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') (ℤ_[l])) (F : Pre bk N d ρ) (F' : Pre bk N' d' ρ') (f : Matrix (Fin d') (Fin d) (ℤ_[l])), (∀ g, f * ρ g = ρ' g * f) → ∃ Y : Matrix (Fin d') (Fin d) (bk.S), F'.T * Y.map bk.evW = zW f * F.T := by
  first | exact @GlobalTheory.BKLim.EquivKisin.main | exact GlobalTheory.BKLim.EquivKisin.main | (intros; apply GlobalTheory.BKLim.EquivKisin.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTateDualLocalGaloisRepAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTateDualLocalGaloisRepAtPlace
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section
namespace GlobalTheory.TateDualX

section Mat

variable {G : Type} [Group G] {LL : Type} [Field LL] {k : ℕ} {V : Type} [AddCommGroup V] [Module LL V]

def toMat (b : Basis (Fin k) LL V) (ρ : Representation LL G V) : G →* Matrix (Fin k) (Fin k) LL :=
  (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom.comp ρ

theorem toMat_apply (b : Basis (Fin k) LL V) (ρ : Representation LL G V) (g : G) :
    toMat b ρ g = LinearMap.toMatrix b b (ρ g) := rfl

def dualTw (c : G →* LLˣ) (M : G →* Matrix (Fin k) (Fin k) LL) : G →* Matrix (Fin k) (Fin k) LL where
  toFun g := ((c g : LLˣ) : LL) • (M g⁻¹).transpose
  map_one' := by simp
  map_mul' g h := by
    simp only [mul_inv_rev, map_mul, Units.val_mul, Matrix.transpose_mul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, mul_comm]

theorem dualTw_apply (c : G →* LLˣ) (M : G →* Matrix (Fin k) (Fin k) LL) (g : G) :
    dualTw c M g = ((c g : LLˣ) : LL) • (M g⁻¹).transpose := rfl

end Mat

section Cont

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] {k : ℕ}

theorem continuous_dualTw (c : G →* LLˣ) (M : G →* Matrix (Fin k) (Fin k) LL)
    (hc : Continuous fun g => ((c g : LLˣ) : LL)) (hM : Continuous fun g => M g) :
    Continuous fun g => dualTw c M g :=
  hc.smul (hM.comp continuous_inv).matrix_transpose

theorem continuous_toMat {V : Type} [AddCommGroup V] [Module LL V] [TopologicalSpace V]
    [IsModuleTopology LL V] (b : Basis (Fin k) LL V)
    (ρ : Representation LL G V) (hρ : ∀ x, Continuous fun g => ρ g x) :
    Continuous fun g => toMat b ρ g := by
  refine continuous_matrix fun a j => ?_
  have h : Continuous (b.coord a) := IsModuleTopology.continuous_of_linearMap _
  refine (h.comp (hρ (b j))).congr fun g => ?_
  simp [toMat_apply, LinearMap.toMatrix_apply]

end Cont

section Transport

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {k : ℕ}

theorem isDual1_basis (b : Basis (Fin k) LL V) (ρ : Representation LL G V)
    (U : G →* Matrix (Fin k) (Fin k) LL)
    (hd : IsDual1 PD (matRep (toMat b ρ)) (matRep U) (dotProductBilin LL LL)) :
    IsDual1 PD ρ (matRep U) ((dotProductBilin LL LL).comp b.equivFun.toLinearMap) := by
  have hM : ∀ g x, b.equivFun (ρ g x) = matRep (toMat b ρ) g (b.equivFun x) := by
    intro g x
    change _ = (toMat b ρ g).mulVec _
    rw [toMat_apply, Basis.equivFun_apply, Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]
  refine ⟨fun g x y => ?_, fun x hx => ?_, fun y hy => ?_, ?_⟩
  · change dotProductBilin LL LL (b.equivFun (ρ g x)) (matRep U g y) = _ * dotProductBilin LL LL (b.equivFun x) y
    rw [hM]
    exact hd.1 g (b.equivFun x) y
  · have := hd.2.1 (b.equivFun x) fun y => hx y
    exact b.equivFun.injective (by rw [this, map_zero])
  · refine hd.2.2.1 y fun v => ?_
    have h := hy (b.equivFun.symm v)
    change dotProductBilin LL LL (b.equivFun (b.equivFun.symm v)) y = 0 at h
    rwa [LinearEquiv.apply_symm_apply] at h
  · rw [Module.finrank_fin_fun, Module.finrank_eq_card_basis b, Fintype.card_fin]

end Transport

section Loc

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
  (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem continuous_cyc : Continuous fun g : Br.G D.nbr i w hw =>
    ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g : (Br.LL D.nbr i w hw)ˣ) :
      Br.LL D.nbr i w hw) := by
  rw [← GlobalTheory.CycBridge.locChi_epsU_eq_cycLL D i w hw]
  have hfc : Continuous (D.nbr i w hw).toLL :=
    continuous_subtype_val.comp (D.nbr i w hw).eO_cont
  have hι : Continuous fun g : Br.G D.nbr i w hw => ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) :=
    continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw)
  exact hfc.comp ((GlobalTheory.Pass.FamCont.epsU_cont D.nd i).comp hι)

end Loc

theorem exists_tateDual : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)),
    ∃ (X' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
      (PX : X.V →ₗ[Br.LL D.nbr i w hw] X'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw),
      IsDual1 (Br.PD D.loc D.nbr i w hw) X.ρ X'.ρ PX := by
  intro D i w hw X
  have hU : Continuous fun g => dualTw (cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw))
      (toMat (Module.finBasis (Br.LL D.nbr i w hw) X.V) X.ρ) g :=
    continuous_dualTw _ _ (continuous_cyc D i w hw) (continuous_toMat _ X.ρ X.cont)
  exact ⟨GlobalTheory.PotDual.bundle ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) _ hU, _,
    isDual1_basis (Br.PD D.loc D.nbr i w hw) (Module.finBasis (Br.LL D.nbr i w hw) X.V) X.ρ _
      (GlobalTheory.PotDual.isDual1_of_eq (Br.PD D.loc D.nbr i w hw) _ _ fun g => dualTw_apply _ _ g)⟩

end GlobalTheory.TateDualX
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTateDualLocalGaloisRepAtPlaceStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tateDual_localGaloisRep_atPlace : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)), ∃ (X' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)) (PX : X.V →ₗ[Br.LL D.nbr i w hw] X'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw), IsDual1 (Br.PD D.loc D.nbr i w hw) X.ρ X'.ρ PX := by
  first | exact @GlobalTheory.TateDualX.exists_tateDual | exact GlobalTheory.TateDualX.exists_tateDual | (intros; apply GlobalTheory.TateDualX.exists_tateDual <;> assumption)
end
end
