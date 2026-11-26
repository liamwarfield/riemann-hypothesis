module

public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.EqOffBound
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PHfGen

@[expose] public section

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.AdicBoxOpenness.CentralCharacterLocalHolds
noncomputable section
open scoped BigOperators nonZeroDivisors

namespace Formalism.L2.PairingIndexBounds.Rec

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.PairingIndexBounds.Mv Formalism.L2.Th1.H Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

theorem phi_injective_holds : PhiInj := by
  intro D cc δ N N' hδ y z h
  have : Nonempty D.what₂.Tau := by
    apply Fintype.card_pos_iff.1
    rw [FL.card_tau D]; have := D.R.ord_pos; positivity
  obtain ⟨τ⟩ := (inferInstance : Nonempty D.what₂.Tau)
  funext i j
  have h1 := congrFun (congrFun (congrFun h τ) i) j
  simp only [Phi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.smul_apply, smul_eq_mul, embV, tor0] at h1
  exact (embT D τ).injective (mul_left_cancel₀ hδ h1)

theorem good_duality_holds : GoodDual := by
  intro V _ _ H A B Λ hH hA hB hsum hsd
  have hanti : ∀ x y : V, altE H y x = -altE H x y := by
    intro x y
    simp only [altE]
    rw [hH x y]
    simp
  have hadd : ∀ w y₁ y₂ : V, altE H w (y₁ + y₂) = altE H w y₁ + altE H w y₂ := by
    intro w y₁ y₂; simp [altE, map_add (f := _)]
  constructor
  · intro a ha h
    apply hsd
    intro y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := AddSubgroup.mem_sup.1 (hsum hy)
    obtain ⟨m₁, hm₁⟩ := hA a ha y₁ (AddSubgroup.mem_inf.1 hy₁).2
    obtain ⟨m₂, hm₂⟩ := h y₂ (AddSubgroup.mem_inf.1 hy₂).2 (AddSubgroup.mem_inf.1 hy₂).1
    exact ⟨m₁ + m₂, by rw [hadd, hm₁, hm₂, Int.cast_add]⟩
  · intro b hb h
    apply hsd
    intro y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := AddSubgroup.mem_sup.1 (hsum hy)
    obtain ⟨m₁, hm₁⟩ := h y₁ (AddSubgroup.mem_inf.1 hy₁).2 (AddSubgroup.mem_inf.1 hy₁).1
    obtain ⟨m₂, hm₂⟩ := hB b hb y₂ (AddSubgroup.mem_inf.1 hy₂).2
    refine ⟨-m₁ + m₂, ?_⟩
    rw [hadd, hanti y₁ b, hm₁, hm₂, Int.cast_add, Int.cast_neg]

theorem equality_off_boundary_holds : EqOffBound := by
  intro D P π hπ N L L₀ h
  obtain ⟨m, hm⟩ := h
  refine ⟨m, ?_⟩
  have h1 := hm (π ^ m) (cO D π ^ m) (by rw [← map_pow]; rfl) (Ideal.pow_mem_pow hπ m)
  simpa only [mul_pow] using h1

theorem oSmul (D : D7) {m n : Type} (x : 𝓞 D.host.E) (A : Matrix m n D.host.E) :
    x • A = (x : D.host.E) • A := by
  ext i j
  rw [Matrix.smul_apply, Matrix.smul_apply, Algebra.smul_def, smul_eq_mul]

def kE (D : D7) (c : 𝓞 D.host.K) : 𝓞 D.host.E := ⟨((c : D.host.K) : D.host.E), FL.intK D c⟩

theorem kE_mem (D : D7) (cc : Ideal (𝓞 D.host.K)) (c : 𝓞 D.host.K) (hc : c ∈ cc) : kE D c ∈ ccE D cc :=
  Ideal.subset_span ⟨c, hc, rfl⟩

theorem multiplicity_equality_holds : MMeq := by
  intro D cc N N' L L'
  apply le_antisymm
  · rw [MM, AddSubgroup.closure_le]
    rintro y ⟨c, hc, A, hA, rfl⟩
    have : ((c : D.host.K) : D.host.E) • A = kE D c • A := by
      rw [oSmul]; rfl
    rw [this]
    exact Submodule.smul_mem_smul (kE_mem D cc c hc) hA
  · intro y hy
    change y ∈ ccE D cc • YYl D L L' at hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro x hx A hA
      induction hx using Submodule.span_induction generalizing A with
      | mem x hx =>
        obtain ⟨c, hc, hxc⟩ := hx
        apply AddSubgroup.subset_closure
        refine ⟨c, hc, A, hA, ?_⟩
        rw [oSmul, hxc]
      | zero => rw [zero_smul]; exact AddSubgroup.zero_mem _
      | add x₁ x₂ _ _ h1 h2 => rw [add_smul]; exact AddSubgroup.add_mem _ (h1 A hA) (h2 A hA)
      | smul r x _ h1 =>
        rw [smul_eq_mul, mul_comm, mul_smul]
        exact h1 _ (Submodule.smul_mem _ r hA)
    · intro a b ha hb; exact AddSubgroup.add_mem _ ha hb

theorem lattice_equality_map_holds : LaEqMap := by
  intro D cc δ N N' L L'
  rw [MM, AddMonoidHom.map_closure]
  apply le_antisymm
  · refine (IO.La_le_gen cc δ L L').trans ?_
    rw [AddSubgroup.closure_le]
    rintro z ⟨c, hc, A, hA, rfl⟩
    apply AddSubgroup.subset_closure
    refine ⟨((c : D.host.K) : D.host.E) • A, ⟨c, hc, A, hA, rfl⟩, ?_⟩
    funext τ i j
    simp only [Phi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.smul_apply, smul_eq_mul, embV, tor0,
      Matrix.smul_apply]
    rw [map_mul, FL.embT_K D τ _ (((c : D.host.K)).2)]
    ring
  · rw [AddSubgroup.closure_le]
    rintro z ⟨y, ⟨c, hc, A, hA, rfl⟩, rfl⟩
    apply AddSubgroup.subset_closure
    refine ⟨δ * D.host.φ₀ (((c : D.host.K) : D.host.E)), AddSubgroup.subset_closure ⟨c, hc, rfl⟩, A, hA, ?_⟩
    funext τ i j
    simp only [Phi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.smul_apply, smul_eq_mul, embV, tor0,
      Matrix.smul_apply]
    rw [map_mul, FL.embT_K D τ _ (((c : D.host.K)).2)]
    ring

theorem uniformizer_element_holds : UnifElt := by
  intro D P hP
  classical
  have hP0 : P.asIdeal ≠ ⊥ := P.ne_bot
  set h := Fintype.card (ClassGroup (𝓞 D.host.E))
  have hh : 0 < h := Fintype.card_pos
  have hm : P.asIdeal ^ h ∈ (Ideal (𝓞 D.host.E))⁰ := pow_mem (mem_nonZeroDivisors_of_ne_zero hP0) h
  have hprin : (P.asIdeal ^ h).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff hm]
    have : ClassGroup.mk0 (⟨P.asIdeal ^ h, hm⟩ : (Ideal (𝓞 D.host.E))⁰) =
        ClassGroup.mk0 ⟨P.asIdeal, mem_nonZeroDivisors_of_ne_zero hP0⟩ ^ h := by
      rw [← map_pow, SubmonoidClass.mk_pow]
    rw [this, pow_card_eq_one]
  obtain ⟨π, hπ⟩ := hprin
  have hspan : Ideal.span {π} = P.asIdeal ^ h := hπ.symm
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, Ideal.span_singleton_eq_bot.2 rfl] at hspan
    exact pow_ne_zero h hP0 hspan.symm
  have hπP : π ∈ P.asIdeal := by
    have : π ∈ P.asIdeal ^ h := by rw [← hspan]; exact Ideal.mem_span_singleton_self π
    exact Ideal.pow_le_self hh.ne' this
  have hprime : ∀ Q : Ideal (𝓞 D.host.E), Q.IsPrime → π ∈ Q → P.asIdeal = Q := by
    intro Q hQ hπQ
    have : P.asIdeal ^ h ≤ Q := by rw [← hspan, Ideal.span_le]; simpa using hπQ
    exact P.isMaximal.eq_of_le hQ.ne_top (hQ.le_of_pow_le this)
  refine ⟨π, hπ0, hπP, fun s hs => ?_, ?_⟩
  · rw [← Ideal.isCoprime_span_singleton_iff, Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
    have h1 : π ∈ Q := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self π))
    have h2 : s ∈ Q := hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self s))
    rw [← hprime Q hQ.isPrime h1] at h2
    exact hs h2
  · intro hc
    obtain ⟨a, b, hab, haP, hbP⟩ := hP
    have hQ : (P.asIdeal.comap (cO D)).IsPrime := Ideal.IsPrime.comap _
    have heq := hprime _ hQ (Ideal.mem_comap.2 hc)
    have ha' : a ∈ P.asIdeal.comap (cO D) := heq ▸ haP
    rw [Ideal.mem_comap] at ha'
    apply hbP
    have hb : b = cO D a := Subtype.ext (hab.trans rfl)
    rw [hb]; exact ha'

theorem ccE_ne_bot (D : D7) (cc : Ideal (𝓞 D.host.K)) (hcc : IsCurveIdeal D cc) : ccE D cc ≠ ⊥ := by
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcc.1
  intro h
  have := kE_mem D cc c hc
  rw [h, Ideal.mem_bot] at this
  apply hc0
  have h2 : ((c : D.host.K) : D.host.E) = 0 := congrArg Subtype.val this
  set_option synthInstance.maxHeartbeats 200000 in
    have h3 : (c : D.host.K) = 0 := by exact_mod_cast h2
    exact_mod_cast h3

theorem central_character_local_holds : CcLoc := by
  intro D cc hcc P
  classical
  have hI : ccE D cc ≠ ⊥ := ccE_ne_bot D cc hcc
  have hlt : ccE D cc * P.asIdeal < ccE D cc := by
    refine lt_of_le_of_ne Ideal.mul_le_left fun h => ?_
    have : ccE D cc * P.asIdeal = ccE D cc * ⊤ := by rw [h, Ideal.mul_top]
    exact P.isPrime.ne_top (mul_left_cancel₀ hI this)
  obtain ⟨γ, hγI, hγP⟩ := SetLike.exists_of_lt hlt
  have hγ0 : γ ≠ 0 := by rintro rfl; exact hγP (Submodule.zero_mem _)
  obtain ⟨J, hJ⟩ : ccE D cc ∣ Ideal.span {γ} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hγI)
  have hJP : ¬ J ≤ P.asIdeal := by
    intro hJ'
    apply hγP
    have : Ideal.span {γ} ≤ ccE D cc * P.asIdeal := by rw [hJ]; exact Ideal.mul_mono_right hJ'
    exact this (Ideal.mem_span_singleton_self γ)
  obtain ⟨t, htJ, htP⟩ := SetLike.not_le_iff_exists.1 hJP
  refine ⟨γ, hγ0, hγI, t, htP, fun c hc => ?_⟩
  have : t * c ∈ Ideal.span {γ} := by rw [hJ, mul_comm t c]; exact Ideal.mul_mem_mul hc htJ
  obtain ⟨o, ho⟩ := Ideal.mem_span_singleton'.1 this
  exact ⟨o, by rw [← ho, mul_comm]⟩

theorem mem_homL (D : D7) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (A : Matrix (Fin N') (Fin N) D.host.E) :
    A ∈ homL D L L' ↔ ∀ x ∈ L, A.mulVec x ∈ L' := by
  constructor
  · intro hA
    induction hA using Submodule.span_induction with
    | mem A hA => exact hA
    | zero => intro x _; rw [Matrix.zero_mulVec]; exact L'.zero_mem
    | add A B _ _ h1 h2 => intro x hx; rw [Matrix.add_mulVec]; exact L'.add_mem (h1 x hx) (h2 x hx)
    | smul c A _ h1 => intro x hx; rw [Matrix.smul_mulVec]; exact L'.smul_mem c (h1 x hx)
  · intro h; exact Submodule.subset_span h

theorem pairing_bound_holds : YYBound := by
  intro D w N N' L L₀ L' L₀' hL hL' y hy
  have hhom : ∀ A ∈ homL D L₀ L₀', (w * w) • A ∈ homL D L L' := by
    intro A hA
    rw [mem_homL] at hA ⊢
    intro x hx
    have : ((w * w) • A).mulVec x = w • (A.mulVec (w • x)) := by
      rw [Matrix.smul_mulVec, Matrix.mulVec_smul, mul_smul]
    rw [this]; exact hL' _ (hA _ (hL x hx))
  induction hy using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hB
    apply Submodule.subset_span
    exact ⟨a, ha, (w * w) • A, hhom A hA, smul_comm _ _ _⟩
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add _ _ _ _ h1 h2 => rw [smul_add]; exact Submodule.add_mem _ h1 h2
  | smul c B _ h1 => rw [smul_comm]; exact Submodule.smul_mem _ c h1

theorem mem_sLat (D : D7) {N : ℕ} (u : D.host.E) (hu : u ≠ 0) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (x : Fin N → D.host.E) : x ∈ sLat D u L ↔ u⁻¹ • x ∈ L := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [LinearMap.coe_restrictScalars, LinearMap.lsmul_apply]
    rwa [smul_smul, inv_mul_cancel₀ hu, one_smul]
  · intro h
    refine ⟨u⁻¹ • x, h, ?_⟩
    simp only [LinearMap.coe_restrictScalars, LinearMap.lsmul_apply]
    rw [smul_smul, mul_inv_cancel₀ hu, one_smul]

theorem unipotent_pairing_holds : UYY := by
  intro D N N' L₀ L₀' u hu
  have hhom : ∀ A, A ∈ homL D L₀ (sLat D u L₀') ↔ u⁻¹ • A ∈ homL D L₀ L₀' := by
    intro A
    rw [mem_homL, mem_homL]
    refine forall₂_congr fun x _ => ?_
    rw [mem_sLat D u hu, Matrix.smul_mulVec]
  rw [sMod, YYl, YYl, Submodule.map_span]
  congr 1
  ext B
  simp only [Set.mem_ofPred_eq, Set.mem_image, LinearMap.coe_restrictScalars, LinearMap.lsmul_apply]
  constructor
  · rintro ⟨a, ha, A, hA, rfl⟩
    refine ⟨a • (u⁻¹ • A), ⟨a, ha, u⁻¹ • A, (hhom A).1 hA, rfl⟩, ?_⟩
    rw [smul_comm u a, smul_smul u u⁻¹, mul_inv_cancel₀ hu, one_smul]
  · rintro ⟨_, ⟨a, ha, A, hA, rfl⟩, rfl⟩
    refine ⟨a, ha, u • A, (hhom _).2 (by rwa [smul_smul, inv_mul_cancel₀ hu, one_smul]), smul_comm _ _ _⟩

theorem admissible_unipotent_holds : UAdm := by
  intro D N N' L₀ L₀' u hu h
  let _ := D.host.cmStar
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have hstar : star u = u⁻¹ := by
    rw [CU.star_conj D u]; exact eq_inv_of_mul_eq_one_right hu
  obtain ⟨h1, h2, h3, ⟨hfg, hspan, hsd⟩⟩ := h
  refine ⟨h1, h2, h3, hfg.map _, ?_, ?_⟩
  · have : ((sLat D u L₀' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : Set (Fin N' → D.host.E)) =
        (LinearMap.lsmul D.host.E (Fin N' → D.host.E) u) '' (L₀' : Set (Fin N' → D.host.E)) := by
      simp [sLat]
    rw [this, Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]
    intro z
    exact ⟨u⁻¹ • z, by simp [smul_smul, inv_mul_cancel₀ hu0]⟩
  · intro y
    rw [mem_sLat D u hu0, hsd]
    constructor
    · intro hy x' hx'
      rw [mem_sLat D u hu0] at hx'
      have := hy _ hx'
      convert this using 1
      simp only [Formalism.BasicNotions.stdH, Pi.smul_apply, smul_eq_mul, star_mul', star_inv₀, hstar, inv_inv]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    · intro hy x hx
      have := hy (u • x) ((mem_sLat D u hu0 L₀' _).2 (by rwa [smul_smul, inv_mul_cancel₀ hu0, one_smul]))
      convert this using 1
      simp only [Formalism.BasicNotions.stdH, Pi.smul_apply, smul_eq_mul, star_mul', hstar]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp

end Formalism.L2.PairingIndexBounds.Rec
end
end

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.AdicBoxOpenness.SqPowMulInvDivPowEqProdPow
noncomputable section

namespace Formalism.L2.PairingIndexBounds.Rec

open IsDedekindDomain

section Gen

variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
  {m n : Type}

theorem gh_rsmul (r : R) (X : Matrix m n K) : r • X = algebraMap R K r • X := (algebraMap_smul K r X).symm

theorem gh_mem_sMod_iff (k : K) (Y : Submodule R (Matrix m n K)) (y : Matrix m n K) :
    y ∈ sMod k Y ↔ ∃ z ∈ Y, k • z = y := by
  simp [sMod]

theorem gh_map_mem {M : Type} [AddCommGroup M] [Module R M] (I : Ideal R) {Y Z : Submodule R M}
    (f : M →ₗ[R] M) (h : ∀ z ∈ Y, f z ∈ Z) {y : M} (hy : y ∈ I • Y) : f y ∈ I • Z := by
  refine Submodule.smul_induction_on hy (fun r hr z hz => ?_) (fun x y hx hy => ?_)
  · rw [map_smul]; exact Submodule.smul_mem_smul hr (h z hz)
  · rw [map_add]; exact add_mem hx hy

theorem gh_smul_mem {M : Type} [AddCommGroup M] [Module R M] (I : Ideal R) {Y Z : Submodule R M}
    (c : R) (h : ∀ z ∈ Y, c • z ∈ Z) {y : M} (hy : y ∈ I • Y) : c • y ∈ I • Z := by
  have := gh_map_mem I (LinearMap.lsmul R M c) (fun z hz => by simpa using h z hz) hy
  simpa using this

theorem gh_local_global {M : Type} [AddCommGroup M] [Module R M] (N : Submodule R M) {s B : R}
    (h : IsCoprime s B) {w : M} (hs : s • w ∈ N) (hB : B • w ∈ N) : w ∈ N := by
  obtain ⟨p, q, hpq⟩ := h
  have : w = p • (s • w) + q • (B • w) := by rw [smul_smul, smul_smul, ← add_smul, hpq, one_smul]
  rw [this]; exact add_mem (N.smul_mem p hs) (N.smul_mem q hB)

theorem gh_mem_sMod_of {k : K} {Y : Submodule R (Matrix m n K)} {r c : R} {z : Matrix m n K}
    (hz : r • z ∈ Y) (hk : k * algebraMap R K r = algebraMap R K c) : c • z ∈ sMod k Y := by
  refine (gh_mem_sMod_iff k Y _).2 ⟨r • z, hz, ?_⟩
  rw [gh_rsmul r z, gh_rsmul c z, smul_smul, hk]

theorem gh_smul_sMod_mem {k : K} {Y Z : Submodule R (Matrix m n K)} {r c : R}
    (h : ∀ z ∈ Y, r • z ∈ Z) (hk : algebraMap R K c * k = algebraMap R K r) :
    ∀ w ∈ sMod k Y, c • w ∈ Z := by
  intro w hw
  obtain ⟨z, hz, rfl⟩ := (gh_mem_sMod_iff k Y w).1 hw
  rw [gh_rsmul c, smul_smul, hk, ← gh_rsmul]
  exact h z hz

theorem gh_toHalf (I : Ideal R) {k : K} {Y Z : Submodule R (Matrix m n K)} {r c : R}
    (h : ∀ z ∈ Y, r • z ∈ Z) (hk : k * algebraMap R K r = algebraMap R K c) :
    ∀ w ∈ I • Y, c • w ∈ I • sMod k Z :=
  fun _ hw => gh_smul_mem I c (fun z hz => gh_mem_sMod_of (h z hz) hk) hw

theorem gh_fromHalf (I : Ideal R) {k : K} {Y Z : Submodule R (Matrix m n K)} {r c : R}
    (h : ∀ z ∈ Z, r • z ∈ Y) (hk : algebraMap R K c * k = algebraMap R K r) :
    ∀ w ∈ I • sMod k Z, c • w ∈ I • Y :=
  fun _ hw => gh_smul_mem I c (gh_smul_sMod_mem h hk) hw

theorem div_pow_mul_prod_pow_left {P Q X : K} (hP : P ≠ 0) (e : ℕ) : (Q / P) ^ e * (X * (P * Q) ^ e) = X * (Q ^ e * Q ^ e) := by
  rw [div_pow, mul_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero e hP)]; ring

theorem inv_div_pow_mul_prod_pow_right {P Q X : K} (hQ : Q ≠ 0) (e : ℕ) :
    ((Q / P) ^ e)⁻¹ * (X * (P * Q) ^ e) = X * (P ^ e * P ^ e) := by
  rw [← inv_pow, inv_div, div_pow, mul_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero e hQ)]; ring

theorem sq_pow_mul_div_pow_eq_prod_pow {P Q X : K} (hP : P ≠ 0) (e : ℕ) : X * (P ^ e * P ^ e) * (Q / P) ^ e = X * (P * Q) ^ e := by
  rw [div_pow, mul_pow, mul_div_assoc', div_eq_iff (pow_ne_zero e hP)]; ring

theorem sq_pow_mul_inv_div_pow_eq_prod_pow {P Q X : K} (hQ : Q ≠ 0) (e : ℕ) :
    X * (Q ^ e * Q ^ e) * ((Q / P) ^ e)⁻¹ = X * (P * Q) ^ e := by
  rw [← inv_pow, inv_div, div_pow, mul_pow, mul_div_assoc', div_eq_iff (pow_ne_zero e hQ)]; ring

theorem pow_mul_pow_mul_div_pow_eq {P Q : K} (hP : P ≠ 0) (e : ℕ) : P ^ e * P ^ e * (Q / P) ^ e = (P * Q) ^ e := by
  rw [div_pow, mul_pow, mul_div_assoc', div_eq_iff (pow_ne_zero e hP)]; ring

theorem gh_matI_add (v : HeightOneSpectrum R) (y z : Matrix m n K) : matI v (y + z) = matI v y + matI v z := by
  ext i j; simp [matI]

theorem gh_matI_zero (v : HeightOneSpectrum R) : matI v (0 : Matrix m n K) = 0 := by
  ext i j; simp [matI]

theorem gh_hatY_coe (v : HeightOneSpectrum R) (Y : Submodule R (Matrix m n K)) :
    (hatY v Y : Set (Matrix m n (v.adicCompletion K))) = closure (matI v '' (Y : Set (Matrix m n K))) := by
  rw [hatY, AddSubgroup.topologicalClosure_coe, AddSubgroup.coe_map]
  rfl

theorem gh_lowB_inf {Y₁ Y₂ : Submodule R (Matrix m n K)} {d₁ d₂ : R} (h₁ : LowB d₁ (Y₁ : Set (Matrix m n K)))
    (h₂ : LowB d₂ (Y₂ : Set (Matrix m n K))) :
    LowB (d₁ * d₂) ((Y₁ ⊓ Y₂ : Submodule R (Matrix m n K)) : Set (Matrix m n K)) := by
  intro A
  rw [SetLike.mem_coe, Submodule.mem_inf]
  constructor
  · have := Y₁.smul_mem d₂ (h₁ A)
    rw [gh_rsmul, smul_smul, ← map_mul, mul_comm d₂] at this; exact this
  · have := Y₂.smul_mem d₁ (h₂ A)
    rw [gh_rsmul, smul_smul, ← map_mul] at this; exact this

theorem gh_read_fwd (I : Ideal R) {γ t : R} (v : HeightOneSpectrum R) (hγ0 : γ ≠ 0) (ht : t ∉ v.asIdeal)
    (hto : ∀ c ∈ I, ∃ o : R, t * c = γ * o) (Y : Submodule R (Matrix m n K)) {w : Matrix m n K}
    (hw : w ∈ I • Y) : ∃ s : R, s ∉ v.asIdeal ∧ s • ((algebraMap R K γ)⁻¹ • w) ∈ Y := by
  have hγ : algebraMap R K γ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hγ0
  refine Submodule.smul_induction_on hw (fun c hc z hz => ?_) (fun w₁ w₂ h₁ h₂ => ?_)
  · obtain ⟨o, ho⟩ := hto c hc
    refine ⟨t, ht, ?_⟩
    have h' := congrArg (algebraMap R K) ho
    rw [map_mul, map_mul] at h'
    have : t • ((algebraMap R K γ)⁻¹ • (c • z)) = o • z := by
      rw [gh_rsmul t, gh_rsmul c, gh_rsmul o, smul_smul, smul_smul]
      congr 1
      rw [mul_right_comm, h', mul_comm (algebraMap R K γ), mul_assoc, mul_inv_cancel₀ hγ, mul_one]
    rw [this]; exact Y.smul_mem o hz
  · obtain ⟨s₁, hs₁, h₁⟩ := h₁
    obtain ⟨s₂, hs₂, h₂⟩ := h₂
    refine ⟨s₁ * s₂, fun h => (v.isPrime.mem_or_mem h).elim hs₁ hs₂, ?_⟩
    have e1 : (s₁ * s₂) • ((algebraMap R K γ)⁻¹ • w₁) = s₂ • (s₁ • ((algebraMap R K γ)⁻¹ • w₁)) := by
      rw [mul_comm, mul_smul]
    have e2 : (s₁ * s₂) • ((algebraMap R K γ)⁻¹ • w₂) = s₁ • (s₂ • ((algebraMap R K γ)⁻¹ • w₂)) := by
      rw [mul_smul]
    rw [smul_add, smul_add, e1, e2]
    exact add_mem (Y.smul_mem _ h₁) (Y.smul_mem _ h₂)

theorem gh_read_bwd (I : Ideal R) {γ B : R} (v : HeightOneSpectrum R) (hγ0 : γ ≠ 0) (hγI : γ ∈ I)
    (hcopB : ∀ s : R, s ∉ v.asIdeal → IsCoprime s B) (Y : Submodule R (Matrix m n K)) {w : Matrix m n K}
    (hB : B • w ∈ I • Y) {s : R} (hs : s ∉ v.asIdeal) (h : s • ((algebraMap R K γ)⁻¹ • w) ∈ Y) :
    w ∈ I • Y := by
  have hγ : algebraMap R K γ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hγ0
  refine gh_local_global _ (hcopB s hs) ?_ hB
  have : s • w = γ • (s • ((algebraMap R K γ)⁻¹ • w)) := by
    rw [gh_rsmul γ, smul_comm (algebraMap R K γ) s, smul_smul, mul_inv_cancel₀ hγ, one_smul]
  rw [this]; exact Submodule.smul_mem_smul hγI h

variable [Fintype m] [Fintype n]

theorem gh_read_iff (hC : ClosChar) (I : Ideal R) {γ t B : R} (v : HeightOneSpectrum R) (hγ0 : γ ≠ 0)
    (hγI : γ ∈ I) (ht : t ∉ v.asIdeal) (hto : ∀ c ∈ I, ∃ o : R, t * c = γ * o)
    (hcopB : ∀ s : R, s ∉ v.asIdeal → IsCoprime s B) (Y : Submodule R (Matrix m n K)) {d : R} (hd : d ≠ 0)
    (hl : LowB d (Y : Set (Matrix m n K))) {w : Matrix m n K} (hB : B • w ∈ I • Y) :
    w ∈ I • Y ↔ matI v ((algebraMap R K γ)⁻¹ • w) ∈ hatY v Y := by
  rw [← SetLike.mem_coe (x := matI v _), gh_hatY_coe, hC R K v m n Y d hd hl]
  constructor
  · exact gh_read_fwd I v hγ0 ht hto Y
  · rintro ⟨s, hs, h⟩
    exact gh_read_bwd I v hγ0 hγI hcopB Y hB hs h

theorem gh_relIndex (hC : ClosChar) (hA : ApproxLow) (v : HeightOneSpectrum R) (I : Ideal R)
    {γ t π πb x y : R} {e : ℕ} {u : K} (hu : u = (algebraMap R K πb / algebraMap R K π) ^ e)
    (hγ0 : γ ≠ 0) (hγI : γ ∈ I) (ht : t ∉ v.asIdeal) (hto : ∀ c ∈ I, ∃ o : R, t * c = γ * o)
    (hπ0 : π ≠ 0) (hπb : πb ∉ v.asIdeal) (hcop : ∀ s : R, s ∉ v.asIdeal → IsCoprime s π)
    (hxy : x * (πb ^ e * πb ^ e) + y * (π ^ e * π ^ e) = 1)
    (Y₀ Y₁ Y₂ : Submodule R (Matrix m n K)) {d₁ d₂ : R} (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0)
    (hl₁ : LowB d₁ (Y₁ : Set (Matrix m n K))) (hl₂ : LowB d₂ (Y₂ : Set (Matrix m n K)))
    (h01 : ∀ z ∈ Y₀, (π * πb) ^ e • z ∈ Y₁) (h10 : ∀ z ∈ Y₁, (π * πb) ^ e • z ∈ Y₀)
    (h02 : ∀ z ∈ Y₀, (π * πb) ^ e • z ∈ Y₂) :
    (I • Y₂ ⊓ I • sMod u Y₀).toAddSubgroup.relIndex (I • Y₁ ⊓ I • sMod u Y₀).toAddSubgroup =
      (hatY v Y₂).relIndex (hatY v Y₁) := by
  have hP : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ0
  have hγ : algebraMap R K γ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hγ0
  have hcopB : ∀ s : R, s ∉ v.asIdeal → IsCoprime s (π ^ e * π ^ e) := fun s hs =>
    have h := (hcop s hs).pow_right (n := e); h.mul_right h
  have hB : ∀ Y : Submodule R (Matrix m n K), (∀ z ∈ Y₀, (π * πb) ^ e • z ∈ Y) →
      ∀ w ∈ I • sMod u Y₀, (π ^ e * π ^ e) • w ∈ I • Y := fun Y hY =>
    gh_fromHalf I hY (by rw [hu]; simp only [map_mul, map_pow]; exact pow_mul_pow_mul_div_pow_eq hP e)
  have hE : ∀ w ∈ I • Y₁, (x * (πb ^ e * πb ^ e)) • w ∈ I • sMod u Y₀ :=
    gh_toHalf I (r := x * (π * πb) ^ e) (fun z hz => by rw [mul_smul]; exact Y₀.smul_mem x (h10 z hz))
      (by rw [hu]; simp only [map_mul, map_pow]; exact div_pow_mul_prod_pow_left hP e)
  have hmem : ∀ w ∈ I • Y₁ ⊓ I • sMod u Y₀, matI v ((algebraMap R K γ)⁻¹ • w) ∈ hatY v Y₁ := fun w hw =>
    (gh_read_iff hC I v hγ0 hγI ht hto hcopB Y₁ hd₁ hl₁
      (hB Y₁ h01 w (Submodule.mem_inf.1 hw).2)).1 (Submodule.mem_inf.1 hw).1
  let φ : (I • Y₁ ⊓ I • sMod u Y₀).toAddSubgroup →+ hatY v Y₁ :=
    { toFun := fun w => ⟨matI v ((algebraMap R K γ)⁻¹ • (w : Matrix m n K)), hmem w w.2⟩
      map_zero' := by ext1; simp [gh_matI_zero]
      map_add' := fun w₁ w₂ => by ext1; simp [smul_add, gh_matI_add] }
  let ψ := (QuotientAddGroup.mk' ((hatY v Y₂).addSubgroupOf (hatY v Y₁))).comp φ
  have hker : ψ.ker = (I • Y₂ ⊓ I • sMod u Y₀).toAddSubgroup.addSubgroupOf
      (I • Y₁ ⊓ I • sMod u Y₀).toAddSubgroup := by
    ext w
    have hwA : (w : Matrix m n K) ∈ I • sMod u Y₀ := (Submodule.mem_inf.1 w.2).2
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff,
      AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup,
      Submodule.mem_inf, gh_read_iff hC I v hγ0 hγI ht hto hcopB Y₂ hd₂ hl₂ (hB Y₂ h02 w hwA)]
    exact ⟨fun h => ⟨h, hwA⟩, fun h => h.1⟩
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
    have hz : (z : Matrix m n (v.adicCompletion K)) ∈ closure (matI v '' (Y₁ : Set (Matrix m n K))) := by
      rw [← gh_hatY_coe]; exact z.2
    obtain ⟨A, hA1, hAz⟩ := hA R K v m n Y₁ (Y₁ ⊓ Y₂) (d₁ * d₂) (mul_ne_zero hd₁ hd₂) (gh_lowB_inf hl₁ hl₂) _ hz
    have hγA : γ • A ∈ I • Y₁ := Submodule.smul_mem_smul hγI hA1
    have hw : (x * (πb ^ e * πb ^ e)) • (γ • A) ∈ I • Y₁ ⊓ I • sMod u Y₀ :=
      Submodule.mem_inf.2 ⟨Submodule.smul_mem _ _ hγA, hE _ hγA⟩
    refine ⟨⟨_, hw⟩, ?_⟩
    rw [AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    show -(matI v ((algebraMap R K γ)⁻¹ • ((x * (πb ^ e * πb ^ e)) • (γ • A)))) +
      (z : Matrix m n (v.adicCompletion K)) ∈ hatY v Y₂
    have k1 : (algebraMap R K γ)⁻¹ • ((x * (πb ^ e * πb ^ e)) • (γ • A)) = (x * (πb ^ e * πb ^ e)) • A := by
      rw [gh_rsmul γ A, smul_comm (x * (πb ^ e * πb ^ e)) (algebraMap R K γ) A, smul_smul,
        inv_mul_cancel₀ hγ, one_smul]
    have hcf : (x * (πb ^ e * πb ^ e)) • A + (y * (π ^ e * π ^ e)) • A = A := by
      rw [← add_smul, hxy, one_smul]
    have hA' : matI v A = matI v ((x * (πb ^ e * πb ^ e)) • A) + matI v ((y * (π ^ e * π ^ e)) • A) := by
      rw [← gh_matI_add, hcf]
    have k2 : -(matI v ((x * (πb ^ e * πb ^ e)) • A)) + (z : Matrix m n (v.adicCompletion K)) =
        ((z : Matrix m n (v.adicCompletion K)) - matI v A) + matI v ((y * (π ^ e * π ^ e)) • A) := by
      rw [hA']; abel
    rw [k1, k2]
    refine add_mem ?_ ?_
    · rw [← SetLike.mem_coe, gh_hatY_coe]
      exact closure_mono (Set.image_mono (SetLike.coe_subset_coe.2 inf_le_right)) hAz
    · rw [← SetLike.mem_coe, gh_hatY_coe, hC R K v m n Y₂ d₂ hd₂ hl₂]
      refine ⟨πb ^ e * πb ^ e, fun h => (v.isPrime.mem_or_mem h).elim
        (fun h' => hπb (v.isPrime.mem_of_pow_mem _ h')) (fun h' => hπb (v.isPrime.mem_of_pow_mem _ h')), ?_⟩
      have : (πb ^ e * πb ^ e) • ((y * (π ^ e * π ^ e)) • A) = y • ((π * πb) ^ e • ((π * πb) ^ e • A)) := by
        simp only [smul_smul]
        congr 1
        ring
      rw [this]
      exact Y₂.smul_mem y (h02 _ (h10 A hA1))
  rw [AddSubgroup.relIndex, AddSubgroup.relIndex, AddSubgroup.index_eq_card, AddSubgroup.index_eq_card]
  exact Nat.card_congr ((QuotientAddGroup.quotientAddEquivOfEq hker.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective ψ hsurj)).toEquiv

end Gen

theorem genHalves_of (hC : ClosChar) (hA : ApproxLow) : GenHalves := by
  intro R _ _ K _ _ _ v m n _ _ I γ t π πb n₀ ι Y₀ Y hγ0 hγI ht hto hπ0 hπv hπb hcop hl0 hli h0i hi0 i
  obtain ⟨d₀, hd₀, hl₀⟩ := hl0
  obtain ⟨d₁, hd₁, hl₁⟩ := hli i
  have hP : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ0
  have hQ : algebraMap R K πb ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 (fun h => hπb (h ▸ v.asIdeal.zero_mem))
  have hcopB : ∀ s : R, s ∉ v.asIdeal → IsCoprime s (π ^ n₀ * π ^ n₀) := fun s hs =>
    have h := (hcop s hs).pow_right (n := n₀); h.mul_right h
  obtain ⟨x, y, hxy⟩ : IsCoprime (πb ^ n₀ * πb ^ n₀) (π ^ n₀ * π ^ n₀) := by
    have h := (hcop πb hπb).pow (m := n₀) (n := n₀)
    have h' := h.mul_left h
    exact h'.mul_right h'
  have h00 : ∀ z ∈ Y₀, (π * πb) ^ n₀ • z ∈ Y₀ := fun z hz => Y₀.smul_mem _ hz
  intro u MA MB
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    refine ⟨(x * (πb ^ n₀ * πb ^ n₀)) • w, Submodule.mem_inf.2 ⟨Submodule.smul_mem _ _ hw, ?_⟩,
      (y * (π ^ n₀ * π ^ n₀)) • w, Submodule.mem_inf.2 ⟨Submodule.smul_mem _ _ hw, ?_⟩, ?_⟩
    · exact gh_toHalf I (r := x * (π * πb) ^ n₀)
        (fun z hz => by rw [mul_smul]; exact Y₀.smul_mem x (hi0 i z hz))
        (by simp only [u, map_mul, map_pow]; exact div_pow_mul_prod_pow_left hP n₀) w hw
    · exact gh_toHalf I (r := y * (π * πb) ^ n₀)
        (fun z hz => by rw [mul_smul]; exact Y₀.smul_mem y (hi0 i z hz))
        (by simp only [u, map_mul, map_pow]; exact inv_div_pow_mul_prod_pow_right hQ n₀) w hw
    · rw [← add_smul, hxy, one_smul]
  · intro a ha b hb hab
    have hfa : (y * (π ^ n₀ * π ^ n₀)) • a ∈ I • Y i :=
      gh_fromHalf I (r := y * (π * πb) ^ n₀)
        (fun z hz => by rw [mul_smul]; exact (Y i).smul_mem y (h0i i z hz))
        (by simp only [u, map_mul, map_pow]; exact sq_pow_mul_div_pow_eq_prod_pow hP n₀) a ha
    have heb : (x * (πb ^ n₀ * πb ^ n₀)) • b ∈ I • Y i :=
      gh_fromHalf I (r := x * (π * πb) ^ n₀)
        (fun z hz => by rw [mul_smul]; exact (Y i).smul_mem x (h0i i z hz))
        (by simp only [u, map_mul, map_pow]; exact sq_pow_mul_inv_div_pow_eq_prod_pow hQ n₀) b hb
    have h1 : (x * (πb ^ n₀ * πb ^ n₀)) • (a + b) + (y * (π ^ n₀ * π ^ n₀)) • a -
        (x * (πb ^ n₀ * πb ^ n₀)) • b = (x * (πb ^ n₀ * πb ^ n₀) + y * (π ^ n₀ * π ^ n₀)) • a := by
      rw [smul_add, add_smul]; abel
    rw [hxy, one_smul] at h1
    rw [← h1]
    exact sub_mem (add_mem (Submodule.smul_mem _ _ hab) hfa) heb
  · intro a ha
    exact gh_read_iff hC I v hγ0 hγI ht hto hcopB (Y i) hd₁ hl₁
      (gh_fromHalf I (r := (π * πb) ^ n₀) (h0i i)
        (by simp only [u, map_mul, map_pow]; exact pow_mul_pow_mul_div_pow_eq hP n₀) a ha)
  · exact gh_relIndex hC hA v I rfl hγ0 hγI ht hto hπ0 hπb hcop hxy Y₀ (Y i) Y₀ hd₁ hd₀ hl₁ hl₀
      (h0i i) (hi0 i) h00
  · exact gh_relIndex hC hA v I rfl hγ0 hγI ht hto hπ0 hπb hcop hxy Y₀ Y₀ (Y i) hd₀ hd₁ hl₀ hl₁
      h00 h00 (h0i i)

end Formalism.L2.PairingIndexBounds.Rec
end
end

noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Rec

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.PairingIndexBounds.Mv Formalism.L2.Th1.H Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

theorem conj_conj' (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  have h1 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.star_conj D x
  have h2 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.star_conj D (D.host.conj x)
  let _ := D.host.cmStar
  rw [← h2, ← h1, star_star]

theorem lowB_YY (D : D7) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (h : admitted D N N' L L') :
    ∃ d : 𝓞 D.host.E, d ≠ 0 ∧ LowB d (YYl D L L' : Set (Matrix (Fin N') (Fin N) D.host.E)) := by
  obtain ⟨M, hM, hlow⟩ := FL.YY_lower D L L' h.2.2.1 h.2.2.2
  refine ⟨(M : 𝓞 D.host.E), by exact_mod_cast hM, fun A => ?_⟩
  have := hlow (A.map (algebraMap (𝓞 D.host.E) D.host.E)) (fun i j => (A i j).isIntegral_coe)
  simpa using this

theorem halvesRec_of_facts (hG : GenHalves) (hLa : LaEqMap) (hMM : MMeq) (hPhi : PhiInj) (hU : UnifElt)
    (hC : CcLoc) (hEq : EqOffBound) (hYY : YYBound) (hUA : UAdm) (hUY : UYY) (hGD : GoodDual)
    (hA : HfIntRec) (hB : SelfDualRec) : HalvesRec := by
  intro D cc δ hcc hδ hδ0 N N' L₀ L₀' hAdm P hP s hs
  classical
  obtain ⟨π, hπ0, hπP, hcop, hπb⟩ := hU D P hP
  obtain ⟨γ, hγ0, hγI, t, htP, ht⟩ := hC D cc hcc P

  have key : ∀ {M : ℕ} (Lx Ly : Submodule (𝓞 D.host.E) (Fin M → D.host.E)) (j : ℕ),
      (∀ x ∈ Lx, (π * cO D π) ^ j • x ∈ Ly) → ∀ k, j ≤ k → ∀ x ∈ Lx, (π * cO D π) ^ k • x ∈ Ly := by
    intro M Lx Ly j h k hk x hx
    rw [← Nat.sub_add_cancel hk, pow_add, mul_smul]
    exact Ly.smul_mem _ (h x hx)
  have hb : ∀ q ∈ s, ∃ j : ℕ, ∀ k, j ≤ k → (∀ x ∈ q.1, (π * cO D π) ^ k • x ∈ L₀) ∧
      (∀ x ∈ L₀', (π * cO D π) ^ k • x ∈ q.2) ∧ (∀ x ∈ q.2, (π * cO D π) ^ k • x ∈ L₀') ∧
      (∀ x ∈ L₀, (π * cO D π) ^ k • x ∈ q.1) := by
    intro q hq
    obtain ⟨j1, h1, h2⟩ := hEq D P π hπP N q.1 L₀ (hs q hq).2.1
    obtain ⟨j2, h3, h4⟩ := hEq D P π hπP N' q.2 L₀' (hs q hq).2.2
    exact ⟨j1 + j2, fun k hk => ⟨key _ _ _ h1 _ (by omega), key _ _ _ h4 _ (by omega),
      key _ _ _ h3 _ (by omega), key _ _ _ h2 _ (by omega)⟩⟩
  choose! jf hjf using hb
  set J := s.sup jf with hJ
  set w : 𝓞 D.host.E := (π * cO D π) ^ J with hw
  have hwb : ∀ q ∈ s, (∀ x ∈ q.1, w • x ∈ L₀) ∧ (∀ x ∈ L₀', w • x ∈ q.2) ∧ (∀ x ∈ q.2, w • x ∈ L₀') ∧
      (∀ x ∈ L₀, w • x ∈ q.1) := fun q hq => hjf q hq J (Finset.le_sup hq)

  let Yf : Option {q // q ∈ s} → Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E) :=
    fun o => match o with
      | none => YYl D L₀ L₀'
      | some q => YYl D q.1.1 q.1.2
  have hww : (π * cO D π) ^ (J + J) = w * w := by rw [pow_add]
  have hbd1 : ∀ o, ∀ y ∈ YYl D L₀ L₀', (π * cO D π) ^ (J + J) • y ∈ Yf o := by
    intro o y hy
    rw [hww]
    match o with
    | none => exact Submodule.smul_mem _ _ hy
    | some q => exact hYY D w N N' q.1.1 L₀ q.1.2 L₀' (hwb q.1 q.2).1 (hwb q.1 q.2).2.1 y hy
  have hbd2 : ∀ o, ∀ y ∈ Yf o, (π * cO D π) ^ (J + J) • y ∈ YYl D L₀ L₀' := by
    intro o y hy
    rw [hww]
    match o with
    | none => exact Submodule.smul_mem _ _ hy
    | some q => exact hYY D w N N' L₀ q.1.1 L₀' q.1.2 (hwb q.1 q.2).2.2.2 (hwb q.1 q.2).2.2.1 y hy
  have hlow : ∀ o, ∃ d : 𝓞 D.host.E, d ≠ 0 ∧ LowB d (Yf o : Set (Matrix (Fin N') (Fin N) D.host.E)) := by
    intro o
    match o with
    | none => exact lowB_YY D L₀ L₀' hAdm
    | some q => exact lowB_YY D q.1.1 q.1.2 (hs q.1 q.2).1
  have HG := hG (𝓞 D.host.E) D.host.E P (Fin N') (Fin N) (ccE D cc) γ t π (cO D π) (J + J)
    (Option {q // q ∈ s}) (YYl D L₀ L₀') Yf hγ0 hγI htP ht hπ0 hπP hπb hcop (lowB_YY D L₀ L₀' hAdm) hlow hbd1 hbd2
  have hπE0 : algebraMap (𝓞 D.host.E) D.host.E π ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)]; exact hπ0
  have hπbE0 : algebraMap (𝓞 D.host.E) D.host.E (cO D π) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)]
    rintro h0; exact hπb (h0 ▸ P.asIdeal.zero_mem)
  set u : D.host.E := (algebraMap (𝓞 D.host.E) D.host.E (cO D π) / algebraMap (𝓞 D.host.E) D.host.E π) ^ (J + J)
    with hu
  have hu0 : u ≠ 0 := pow_ne_zero _ (div_ne_zero hπbE0 hπE0)
  have hc1 : D.host.conj (algebraMap (𝓞 D.host.E) D.host.E (cO D π)) = algebraMap (𝓞 D.host.E) D.host.E π :=
    conj_conj' D _
  have hc2 : D.host.conj (algebraMap (𝓞 D.host.E) D.host.E π) = algebraMap (𝓞 D.host.E) D.host.E (cO D π) := rfl
  have hu1 : u * D.host.conj u = 1 := by
    rw [hu, map_pow, map_div₀, hc1, hc2, ← mul_pow]
    have e : algebraMap (𝓞 D.host.E) D.host.E (cO D π) / algebraMap (𝓞 D.host.E) D.host.E π *
        (algebraMap (𝓞 D.host.E) D.host.E π / algebraMap (𝓞 D.host.E) D.host.E (cO D π)) = 1 := by
      field_simp
    rw [e, one_pow]
  have hu1' : u⁻¹ * D.host.conj u⁻¹ = 1 := by rw [map_inv₀, ← mul_inv, hu1, inv_one]
  have hinj : Function.Injective (Phi D cc δ N N') := hPhi D cc δ N N' hδ0
  have hAdmA := hUA D N N' L₀ L₀' u hu1 hAdm
  have hAdmB := hUA D N N' L₀ L₀' u⁻¹ hu1' hAdm
  have hLaeq : ∀ (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
      La D (tor0 D cc δ) L L' = (ccE D cc • YYl D L L').toAddSubgroup.map (Phi D cc δ N N') := fun L L' => by
    rw [hLa, hMM]
  have hAeq : La D (tor0 D cc δ) L₀ (sLat D u L₀') =
      (ccE D cc • sMod u (YYl D L₀ L₀')).toAddSubgroup.map (Phi D cc δ N N') := by
    rw [hLaeq, hUY D N N' L₀ L₀' u hu0]
  have hBeq : La D (tor0 D cc δ) L₀ (sLat D u⁻¹ L₀') =
      (ccE D cc • sMod u⁻¹ (YYl D L₀ L₀')).toAddSubgroup.map (Phi D cc δ N N') := by
    rw [hLaeq, hUY D N N' L₀ L₀' u⁻¹ (inv_ne_zero hu0)]
  obtain ⟨hHerm, -, -, -, hSC⟩ := local_global_comparison_holds D (tor0 D cc δ) N N'
  have hIA := hA D cc hcc δ hδ hδ0 N N' L₀ _ hAdmA
  have hIB := hA D cc hcc δ hδ hδ0 N N' L₀ _ hAdmB
  have intOf : ∀ Λ : AddSubgroup (VC D N N'), IO.HfInt (tor0 D cc δ) Λ →
      ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ m : ℤ, altE (HfS D (tor0 D cc δ) N N') x y = m := by
    intro Λ hI x hx y hy
    obtain ⟨a, b, -, hab⟩ := hI x hx y hy
    exact ⟨b, by simp only [altE, HfS_apply, hab]; simp⟩
  have good : ∀ (o : Option {q // q ∈ s}) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → YYl D L L' = Yf o →
      GoodLat (HfS D (tor0 D cc δ) N N') (al D (tor0 D cc δ))
        ((ccE D cc • sMod u (YYl D L₀ L₀')).toAddSubgroup.map (Phi D cc δ N N'))
        ((ccE D cc • sMod u⁻¹ (YYl D L₀ L₀')).toAddSubgroup.map (Phi D cc δ N N')) (La D (tor0 D cc δ) L L') := by
    intro o L L' hLL hY
    obtain ⟨c1, c2, -, -, -⟩ := HG o
    have hΛ : La D (tor0 D cc δ) L L' = (ccE D cc • Yf o).toAddSubgroup.map (Phi D cc δ N N') := by
      rw [hLaeq, hY]
    have hsum : La D (tor0 D cc δ) L L' ≤
        (La D (tor0 D cc δ) L L' ⊓ (ccE D cc • sMod u (YYl D L₀ L₀')).toAddSubgroup.map (Phi D cc δ N N')) ⊔
        (La D (tor0 D cc δ) L L' ⊓ (ccE D cc • sMod u⁻¹ (YYl D L₀ L₀')).toAddSubgroup.map (Phi D cc δ N N')) := by
      rw [hΛ]
      intro z hz
      obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.1 hz
      obtain ⟨a, ha, b, hb, rfl⟩ := c1 y hy
      rw [map_add (f := _)]
      exact AddSubgroup.add_mem_sup
        ⟨AddSubgroup.mem_map_of_mem _ (Submodule.mem_inf.1 ha).1, AddSubgroup.mem_map_of_mem _ (Submodule.mem_inf.1 ha).2⟩
        ⟨AddSubgroup.mem_map_of_mem _ (Submodule.mem_inf.1 hb).1, AddSubgroup.mem_map_of_mem _ (Submodule.mem_inf.1 hb).2⟩
    have hsd : ∀ v : VC D N N', (∀ y ∈ La D (tor0 D cc δ) L L', ∃ b : ℤ, altE (HfS D (tor0 D cc δ) N N') v y = b) →
        v ∈ La D (tor0 D cc δ) L L' :=
      fun v hv => hB D cc hcc δ hδ hδ0 N N' L L' hLL v hv
    obtain ⟨d1, d2⟩ := hGD (VC D N N') (HfS D (tor0 D cc δ) N N') _ _ _ hHerm (intOf _ (hAeq ▸ hIA))
      (intOf _ (hBeq ▸ hIB)) hsum hsd
    refine ⟨hSC _ (hA D cc hcc δ hδ hδ0 N N' L L' hLL), hsum, ?_, d1, d2⟩
    intro a ha b hb hab
    obtain ⟨a', ha', rfl⟩ := AddSubgroup.mem_map.1 ha
    obtain ⟨b', hb', rfl⟩ := AddSubgroup.mem_map.1 hb
    rw [hΛ] at hab ⊢
    rw [← map_add (f := _), AddSubgroup.mem_map_iff_mem hinj] at hab
    exact AddSubgroup.mem_map_of_mem _ (c2 a' ha' b' hb' hab)
  have einf : ∀ X Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E),
      (X ⊓ Y).toAddSubgroup = X.toAddSubgroup ⊓ Y.toAddSubgroup := fun X Y => rfl
  let φ : ((ccE D cc • sMod u (YYl D L₀ L₀')).toAddSubgroup.map (Phi D cc δ N N')) →
      Matrix (Fin N') (Fin N) (EP D P) :=
    fun a => matI P ((algebraMap (𝓞 D.host.E) D.host.E γ)⁻¹ • Function.invFun (Phi D cc δ N N') (a : VC D N N'))
  refine ⟨_, _, φ, hAeq ▸ hSC _ hIA, hBeq ▸ hSC _ hIB, good none L₀ L₀' hAdm rfl, fun q hq => ?_⟩
  have hq' := hs q hq
  obtain ⟨-, -, c3, c4, c5⟩ := HG (some ⟨q, hq⟩)
  refine ⟨good (some ⟨q, hq⟩) q.1 q.2 hq'.1 rfl, ?_, ?_, ?_⟩
  · haveI := IO.La_index_finite cc hcc δ L₀ q.1 L₀' q.2 hAdm hq'.1
    exact AddSubgroup.index_ne_zero_of_finite
  · intro a
    obtain ⟨a', ha', hΦa⟩ := AddSubgroup.mem_map.1 a.2
    have hinv : Function.invFun (Phi D cc δ N N') (a : VC D N N') = a' := by
      rw [← hΦa]; exact Function.leftInverse_invFun hinj a'
    change _ ↔ matI P ((algebraMap (𝓞 D.host.E) D.host.E γ)⁻¹ •
      Function.invFun (Phi D cc δ N N') (a : VC D N N')) ∈ _
    rw [hinv, ← hΦa, hLaeq, AddSubgroup.mem_map_iff_mem hinj, YP_eq]
    exact c3 a' ha'
  · rw [volP, volA, hLaeq, hLaeq, ← AddSubgroup.map_inf_eq _ _ _ hinj, ← AddSubgroup.map_inf_eq _ _ _ hinj,
      AddSubgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.relIndex_map_map_of_injective _ _ hinj,
      YP_eq, YP_eq, ← einf, ← einf]
    have c4' := c4
    have c5' := c5
    simp only [AddSubgroup.relIndex] at c4' c5' ⊢
    rw [c4', c5']

theorem halvesRec_of_clos (hC : ClosChar) (hAp : ApproxLow) (hA : HfIntRec) (hB : SelfDualRec) : HalvesRec :=
  halvesRec_of_facts (genHalves_of hC hAp) lattice_equality_map_holds multiplicity_equality_holds phi_injective_holds uniformizer_element_holds central_character_local_holds
    equality_off_boundary_holds pairing_bound_holds admissible_unipotent_holds unipotent_pairing_holds good_duality_holds hA hB

end Formalism.L2.PairingIndexBounds.Rec
