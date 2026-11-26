module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DifferentIdealEqTop
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLocalizedModuleSubtype
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeOfLatMod
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.ExistsNsmulMem
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BinaryHermitianRepresents
open NumberField Formalism.HermitianLattices.Ext.L3

namespace GlobalTheory.Mass

theorem _root_.GlobalTheory.Mass.binary_hermitian_represents : _root_.Formalism.HermitianLattices.Ext.L3.HermRepUnram := by
  unfold _root_.Formalism.HermitianLattices.Ext.L3.HermRepUnram
  intro K _ _ _ hK a b n ha hb hn hpa hpb hpn
  obtain ⟨w, hw0, hw⟩ := _root_.Formalism.HermitianLattices.Ext.L3.exists_skew hK
  have memF : ∀ x : K, star x = x → x ∈ _root_.Formalism.HermitianLattices.Ext.L3.cmF K := fun x hx => (_root_.Formalism.HermitianLattices.Ext.L3.mem_cmF_iff K x).2 hx
  obtain ⟨ψ₀⟩ : Nonempty (K →+* ℂ) := inferInstance
  have ne_of_pos : ∀ x : K, _root_.Formalism.HermitianLattices.Ext.L3.TotPos x → x ≠ 0 := by
    intro x hx h
    have := hx ψ₀
    simp [h] at this
  let a' : _root_.Formalism.HermitianLattices.Ext.L3.cmF K := ⟨a, memF a ha⟩
  let b' : _root_.Formalism.HermitianLattices.Ext.L3.cmF K := ⟨b, memF b hb⟩
  let n' : _root_.Formalism.HermitianLattices.Ext.L3.cmF K := ⟨n, memF n hn⟩
  let δ : _root_.Formalism.HermitianLattices.Ext.L3.cmF K := ⟨w * w, memF _ (by rw [star_mul, hw]; ring)⟩
  have hnegδ : _root_.Formalism.HermitianLattices.Ext.L3.TotPos ((-δ : _root_.Formalism.HermitianLattices.Ext.L3.cmF K) : K) := by
    unfold _root_.Formalism.HermitianLattices.Ext.L3.TotPos
    intro ψ
    have h1 : ψ (star w) = (starRingEnd ℂ) (ψ w) := hK.2.1 ψ w
    rw [hw, map_neg] at h1
    have hre : (ψ w).re = 0 := by
      have := congrArg Complex.re h1
      simp at this
      linarith
    have hne : ψ w ≠ 0 := (map_ne_zero ψ).2 hw0
    have him : (ψ w).im ≠ 0 := by
      intro him
      exact hne (Complex.ext hre him)
    simp [δ, Complex.mul_re, hre]
    positivity
  have hδneg : ∀ φ : _root_.Formalism.HermitianLattices.Ext.L3.cmF K →+* ℝ, φ δ < 0 := by
    intro φ
    have := (_root_.Formalism.HermitianLattices.Ext.L3.totPos_iff hK (-δ)).1 hnegδ φ
    simpa using this
  have ha' : a' ≠ 0 := fun h => ne_of_pos a hpa (congrArg Subtype.val h)
  have hb' : b' ≠ 0 := fun h => ne_of_pos b hpb (congrArg Subtype.val h)
  have hn' : n' ≠ 0 := fun h => ne_of_pos n hpn (congrArg Subtype.val h)
  have hδ0 : δ ≠ 0 := fun h => hw0 (mul_self_eq_zero.1 (congrArg Subtype.val h))
  let c : Fin 5 → _root_.Formalism.HermitianLattices.Ext.L3.cmF K := ![a', -(a' * δ), b', -(b' * δ), -n']
  have hc : ∀ i, c i ≠ 0 := by
    intro i
    fin_cases i <;> simp [c, ha', hb', hn', hδ0]
  obtain ⟨x, hx0, hx⟩ := _root_.GlobalTheory.LocalQuad.isotropic_of_indefinite _root_.GlobalTheory.QNorm.hasseNormSt
    (_root_.Formalism.HermitianLattices.Ext.L3.cmF K) c (by simp) hc (by
      intro σ
      refine ⟨4, 0, ?_, ?_⟩
      · simpa [c] using (_root_.Formalism.HermitianLattices.Ext.L3.totPos_iff hK n').1 hpn σ
      · simpa [c] using (_root_.Formalism.HermitianLattices.Ext.L3.totPos_iff hK a').1 hpa σ)
  obtain ⟨y, hy4, hy⟩ := _root_.GlobalTheory.LocalQuad.HermClass.exists_zero_coord_ne_zero hc hx0 hx 4
  have h4 : (y 4 : K) ≠ 0 := fun h => hy4 (Subtype.ext h)
  have hy' := congrArg (fun z : _root_.Formalism.HermitianLattices.Ext.L3.cmF K => (z : K)) hy
  simp [Fin.sum_univ_five, c, a', b', n', δ] at hy'
  refine ⟨((y 0 : K) + (y 1 : K) * w) / (y 4 : K), ((y 2 : K) + (y 3 : K) * w) / (y 4 : K), ?_⟩
  simp only [star_div₀, star_add, star_mul, _root_.Formalism.HermitianLattices.Ext.L3.star_coe_cmF, hw]
  field_simp
  linear_combination hy'

end GlobalTheory.Mass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemOfForall
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open scoped nonZeroDivisors

namespace GlobalTheory.DegCnt.IdealPow

variable {K : Type} [Field K] [NumberField K] {𝔡 : Ideal (𝓞 K)}

theorem ipow_zero (𝔡 : Ideal (𝓞 K)) : ipow 𝔡 0 = 1 := by
  simp [ipow]

theorem ipow_mul (h : 𝔡 ≠ ⊥) (m n : ℤ) : ipow 𝔡 m * ipow 𝔡 n = ipow 𝔡 (m + n) := by
  have h0 : (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h
  unfold ipow
  rw [zpow_add₀ h0, FractionalIdeal.coe_mul]

theorem mul_mem (h : 𝔡 ≠ ⊥) {m n k : ℤ} (hk : m + n = k) {x y : K} (hx : x ∈ ipow 𝔡 m) (hy : y ∈ ipow 𝔡 n) :
    x * y ∈ ipow 𝔡 k := by
  rw [← hk, ← ipow_mul h]
  exact Submodule.mul_mem_mul hx hy

theorem mul_mem_one (h : 𝔡 ≠ ⊥) {m n : ℤ} (hk : m + n = 0) {x y : K} (hx : x ∈ ipow 𝔡 m) (hy : y ∈ ipow 𝔡 n) :
    x * y ∈ (1 : Submodule (𝓞 K) K) := by
  rw [← ipow_zero 𝔡]
  exact mul_mem h hk hx hy

theorem pow_mem (h : 𝔡 ≠ ⊥) {m : ℤ} {x : K} (hx : x ∈ ipow 𝔡 m) (s : ℕ) : x ^ s ∈ ipow 𝔡 (s * m) := by
  induction s with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul, ipow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
  | succ s ih => rw [pow_succ]; exact mul_mem h (by push_cast; ring) ih hx

theorem mem_of_forall (h : 𝔡 ≠ ⊥) {m n : ℤ} (hk : m + n = 0) {x : K}
    (hx : ∀ y ∈ ipow 𝔡 n, x * y ∈ (1 : Submodule (𝓞 K) K)) : x ∈ ipow 𝔡 m := by
  have h1 : (1 : K) ∈ ipow 𝔡 n * ipow 𝔡 m := by
    rw [ipow_mul h, add_comm, hk, ipow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
  have h2 : ∀ z ∈ ipow 𝔡 n * ipow 𝔡 m, x * z ∈ ipow 𝔡 m := by
    intro z hz
    refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hx a ha)
      rw [← mul_assoc, ← hc, ← Algebra.smul_def]
      exact Submodule.smul_mem _ c hb
    · rw [mul_add]; exact add_mem ha hb
  simpa using h2 1 h1

theorem prod_ipow (h : 𝔡 ≠ ⊥) {ι : Type} (s : Finset ι) (n : ι → ℤ) :
    ∏ i ∈ s, ipow 𝔡 (n i) = ipow 𝔡 (∑ i ∈ s, n i) := by
  induction s using Finset.induction_on with
  | empty => simp [ipow_zero]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ipow_mul h]

theorem ipow_sum_le (h : 𝔡 ≠ ⊥) {ι : Type} [Fintype ι] (n : ι → ℤ) (J : Submodule (𝓞 K) K)
    (hJ : ∀ α : ι → K, (∀ i, α i ∈ ipow 𝔡 (n i)) → ∏ i, α i ∈ J) : ipow 𝔡 (∑ i, n i) ≤ J := by
  rw [← prod_ipow h]
  have : ∏ i, ipow 𝔡 (n i) = ∏ i, Submodule.span (𝓞 K) (ipow 𝔡 (n i) : Set K) := by simp
  rw [this, Submodule.prod_span, Submodule.span_le]
  intro x hx
  obtain ⟨α, hα, rfl⟩ := (Set.mem_fintype_prod _ _).1 hx
  exact hJ α hα

variable [StarRing K]

theorem star_mem_nat (h : 𝔡 ≠ ⊥) (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) (n : ℕ) {x : K}
    (hx : x ∈ ipow 𝔡 n) : star x ∈ ipow 𝔡 n := by
  induction n generalizing x with
  | zero =>
    rw [Nat.cast_zero, ipow_zero] at hx ⊢
    exact GlobalTheory.UnimodQuot.star_mem_one hx
  | succ n ih =>
    rw [Nat.cast_succ, ← ipow_mul h] at hx ⊢
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [star_mul']
      refine Submodule.mul_mem_mul (ih ha) ?_
      simp only [ipow, zpow_one, FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal] at hb ⊢
      obtain ⟨y, hy, rfl⟩ := hb
      exact hs y hy
    · rw [star_add]; exact add_mem ha hb

theorem star_mem (h : 𝔡 ≠ ⊥) (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) {n : ℤ} {x : K}
    (hx : x ∈ ipow 𝔡 n) : star x ∈ ipow 𝔡 n := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · exact star_mem_nat h hs m hx
  · refine mem_of_forall h (neg_add_cancel _) fun y hy => ?_
    have := GlobalTheory.UnimodQuot.star_mem_one (mul_mem_one h (neg_add_cancel _) hx (star_mem_nat h hs m hy))
    rwa [star_mul', star_star] at this

end GlobalTheory.DegCnt.IdealPow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdxSupRight
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.Compl

section General

variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]

theorem idx_sup_right (X B : Submodule R W) : idx (X ⊔ B) B = idx X B :=
  DelScale.idx_sup le_rfl

theorem idx_glue (M U U' : Submodule R W) :
    idx (U ⊓ (M ⊔ U')) (M ⊓ U) = idx ((M ⊔ U) ⊓ (M ⊔ U')) M := by
  rw [sup_inf_assoc_of_le U (le_sup_left : M ≤ M ⊔ U'), sup_comm M (U ⊓ _), idx_sup_right,
    ← DelScale.idx_inf_left, ← DelScale.idx_inf_left _ M]
  congr 1
  exact le_antisymm (le_inf inf_le_left (inf_le_right.trans inf_le_left))
    (le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans inf_le_left)))

theorem gidx_glue (M U U' : Submodule R W) :
    gidx (U ⊓ (M ⊔ U')) (M ⊓ U) = idx ((M ⊔ U) ⊓ (M ⊔ U')) M := by
  have : idx (M ⊓ U) (U ⊓ (M ⊔ U')) = 1 :=
    AddSubgroup.relIndex_eq_one.2 fun x hx => ⟨hx.2, Submodule.mem_sup_left hx.1⟩
  rw [gidx, this, idx_glue]
  simp

theorem gen_glue (M U U' : Submodule R W) (t : Finset W)
    (h : U ⊓ (M ⊔ U') = (M ⊓ U) ⊔ Submodule.span R (t : Set W)) :
    ∃ t' : Finset W, t'.card ≤ t.card ∧ U' ⊓ (M ⊔ U) = (M ⊓ U') ⊔ Submodule.span R (t' : Set W) := by
  have h1 : ∀ x : W, ∃ y : W, x ∈ t → y ∈ U' ∧ x - y ∈ M := by
    intro x
    by_cases hx : x ∈ t
    · have : x ∈ U ⊓ (M ⊔ U') := h ▸ Submodule.mem_sup_right (Submodule.subset_span hx)
      obtain ⟨m, hm, y, hy, e⟩ := Submodule.mem_sup.1 this.2
      exact ⟨y, fun _ => ⟨hy, by rw [← e]; simpa using hm⟩⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose f hf using h1
  refine ⟨t.image f, Finset.card_image_le, ?_⟩
  have a : Submodule.span R (t.image f : Set W) ≤ U' := by
    rw [Submodule.span_le]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    exact (hf x hx).1
  have b : M ⊔ Submodule.span R (t : Set W) = M ⊔ Submodule.span R (t.image f : Set W) := by
    apply le_antisymm
    · refine sup_le le_sup_left (Submodule.span_le.2 fun x hx => ?_)
      exact Submodule.mem_sup.2 ⟨_, (hf x hx).2, f x,
        Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem f hx)), by abel⟩
    · refine sup_le le_sup_left (Submodule.span_le.2 fun y hy => ?_)
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
      exact Submodule.mem_sup.2 ⟨_, M.neg_mem (hf x hx).2, x, Submodule.subset_span hx, by abel⟩
  have c : (M ⊔ U) ⊓ (M ⊔ U') = M ⊔ Submodule.span R (t.image f : Set W) := by
    rw [sup_inf_assoc_of_le U (le_sup_left : M ≤ M ⊔ U'), h, ← sup_assoc, sup_inf_self, b]
  have d : U' ⊓ (M ⊔ U) = ((M ⊔ U) ⊓ (M ⊔ U')) ⊓ U' := by
    rw [inf_assoc, inf_comm U', inf_eq_right.2 (le_sup_right : U' ≤ M ⊔ U')]
  rw [d, c, sup_comm M, sup_inf_assoc_of_le M a, sup_comm]

end General

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] [FiniteDimensional K V] in
theorem exists_mult {M : Submodule (𝓞 K) V} {v : V} (hv : v ∈ Submodule.span K (M : Set V)) :
    ∃ c : K, c ≠ 0 ∧ c • v ∈ M := by
  obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K (M : Set V) v hv
  rw [Submodule.span_eq] at hs
  refine ⟨algebraMap (𝓞 K) K s, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2, ?_⟩
  rw [algebraMap_smul]
  exact hs

omit [StarRing K] [FiniteDimensional K V] in
theorem span_inf {M : Submodule (𝓞 K) V} {T : Submodule K V} (hT : T ≤ Submodule.span K (M : Set V)) :
    Submodule.span K ((M ⊓ rs (𝓞 K) T : Submodule (𝓞 K) V) : Set V) = T := by
  apply le_antisymm
  · exact Submodule.span_le.2 fun x hx => hx.2
  · intro v hv
    obtain ⟨c, hc, h⟩ := exists_mult (hT hv)
    rw [← Submodule.smul_mem_iff _ hc]
    exact Submodule.subset_span ⟨h, T.smul_mem c hv⟩

theorem key (H : HermSpace K V) {M : Submodule (𝓞 K) V} {S I : Submodule K V} (hIS : I ≤ S)
    (hrad : ∀ x ∈ S, (∀ y ∈ S, H.B x y = 0) ↔ x ∈ I) (hM : IsUnimodMod H M S I)
    {T : Submodule K V} (hIT : I ≤ T) (hTS : T ≤ S) :
    dual H (M ⊓ rs (𝓞 K) T) = rs (𝓞 K) T ⊓ (M ⊔ rs (𝓞 K) (S ⊓ perp H T)) ∧
      S ⊓ perp H (S ⊓ perp H T) = T := by
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective I.subtype (Submodule.ker_subtype I)
  have hr' : ∀ x (hx : x ∈ I), (r x : V) = x := fun x hx =>
    congrArg Subtype.val (LinearMap.congr_fun hr ⟨x, hx⟩)
  set p : V →ₗ[K] V := LinearMap.id - I.subtype ∘ₗ r with hp
  have hpx : ∀ x, p x = x - r x := fun x => rfl
  set C : Submodule K V := S ⊓ LinearMap.ker r with hCd
  have hCS : C ≤ S := inf_le_left
  have hpC : ∀ x ∈ S, p x ∈ C := fun x hx => ⟨S.sub_mem hx (hIS (r x).2), by
    change r (p x) = 0
    rw [hpx, map_sub, sub_eq_zero]
    exact (Subtype.ext (hr' _ (r x).2)).symm⟩
  have hpI : ∀ x, x - p x ∈ I := fun x => by rw [hpx]; simp
  have hI : ∀ x ∈ I, p x = 0 := fun x hx => by rw [hpx, hr' x hx, sub_self]
  have hC : ∀ x ∈ C, p x = x := fun x hx => by
    have : r x = 0 := hx.2
    rw [hpx, this]; simp
  have o1 : ∀ i ∈ I, ∀ y ∈ S, H.B i y = 0 := fun i hi => (hrad i (hIS hi)).2 hi
  have o2 : ∀ i ∈ I, ∀ y ∈ S, H.B y i = 0 := fun i hi y hy => by rw [← H.herm, o1 i hi y hy, star_zero]
  have o3 : ∀ y ∈ S, ∀ x, H.B y (p x) = H.B y x := fun y hy x => by
    rw [hpx, map_sub, o2 _ (r x).2 y hy, sub_zero]
  have o4 : ∀ y ∈ S, ∀ x, H.B (p x) y = H.B x y := fun y hy x => by
    rw [← H.herm, o3 y hy, H.herm]
  have hpT : ∀ x ∈ T, p x ∈ T := fun x hx => T.sub_mem hx (hIT (r x).2)
  let HC : HermSpace K C :=
    { B := H.B.domRestrict₁₂ C C
      herm := fun x y => H.herm x y
      nondeg := fun x hx => by
        have : (x : V) ∈ I := (hrad x (hCS x.2)).1 fun y hy => by
          rw [← o3 x (hCS x.2)]; exact hx ⟨_, hpC y hy⟩
        exact Subtype.ext ((hC x x.2).symm.trans (hI x this)) }
  have hB : ∀ x y : C, HC.B x y = H.B x y := fun _ _ => rfl
  obtain ⟨a, b⟩ := DelScale.le_of_latMod hM.1
  have hpM : ∀ x ∈ M, p x ∈ M := fun x hx => M.sub_mem hx (a (r x).2)
  have L := DelScale.latIn_isFullLattice p hCS hpC hpI hI hC hM.1
  have hMd : ∀ y, y ∈ M ↔ y ∈ S ∧ ∀ x ∈ M, H.B y x ∈ (1 : Submodule (𝓞 K) K) := fun y => by
    rw [← hM.1.2, ← mem_dual_iff, hM.2]
  have hU : IsUnimod HC (GlobalTheory.Mass.latIn C M) := by
    refine ⟨(isLatMod_top_bot_iff _).2 ⟨L.toIsLattice.fg, L.span_eq_top⟩, ?_⟩
    ext y
    rw [mem_dual_iff, L.span_eq_top]
    change _ ↔ (y : V) ∈ M
    rw [hMd]
    refine ⟨fun hy => ⟨hCS y.2, fun x hx => ?_⟩, fun hy => ⟨trivial, fun x hx => hy.2 x hx⟩⟩
    rw [← o3 y (hCS y.2)]
    exact hy.2 ⟨p x, hpC x (b hx)⟩ (hpM x hx)
  constructor
  · ext d
    rw [mem_dual_iff, span_inf (hM.1.2 ▸ hTS)]
    constructor
    · rintro ⟨hd, hdM⟩
      refine ⟨hd, ?_⟩
      have hx : ∀ x : ↥(GlobalTheory.Mass.latIn C M ⊓ rs (𝓞 K) (T.comap C.subtype)),
          IsIntegral ℤ (H.B ((x : C) : V) d) := by
        intro x
        rw [← UnimodQuot.mem_one_iff, ← H.herm]
        exact UnimodQuot.star_mem_one (hdM _ ⟨x.2.1, x.2.2⟩)
      let φ : ↥(GlobalTheory.Mass.latIn C M ⊓ rs (𝓞 K) (T.comap C.subtype)) →ₗ[𝓞 K] 𝓞 K :=
        { toFun := fun x => ⟨H.B ((x : C) : V) d, hx x⟩
          map_add' := fun a b => by
            apply RingOfIntegers.ext
            show H.B (((a : C) : V) + (b : C)) d = H.B (a : C) d + H.B (b : C) d
            simp
          map_smul' := fun a b => by
            apply RingOfIntegers.ext
            show H.B (a • ((b : C) : V)) d = algebraMap (𝓞 K) K a * H.B (b : C) d
            rw [← algebraMap_smul K a, map_smul]
            rfl }
      obtain ⟨y, hy, h'⟩ := UnimodQuot.exists_lattice_rep HC hU (T.comap C.subtype) φ
      refine Submodule.mem_sup.2 ⟨y, hy, d - y, ⟨S.sub_mem (hTS hd) (hCS y.2), ?_⟩, by abel⟩
      refine (mem_perp_iff H T _).2 fun x hx => ?_
      obtain ⟨c, hc, h⟩ := exists_mult (M := M) (v := x) (hM.1.2 ▸ hTS hx)
      have hcT := T.smul_mem c hx
      have h1 : H.B (p (c • x)) y = H.B (p (c • x)) d :=
        h' ⟨⟨p (c • x), hpC _ (hTS hcT)⟩, hpM _ h, hpT _ hcT⟩
      rw [o4 _ (hCS y.2), o4 _ (hTS hd), map_smul, LinearMap.smul_apply, LinearMap.smul_apply] at h1
      rw [← H.herm, map_sub, smul_right_injective K hc h1, sub_self, star_zero]
    · rintro ⟨hd, hdM⟩
      refine ⟨hd, fun x hx => ?_⟩
      obtain ⟨m, hm, u, hu, rfl⟩ := Submodule.mem_sup.1 hdM
      rw [map_add (f := _), LinearMap.add_apply, (mem_perp_iff H T u).1 hu.2 x hx.2, add_zero]
      exact ((hMd m).1 hm).2 x hx.1
  · apply le_antisymm
    · rintro s ⟨hs, hs'⟩
      have h1 : (⟨p s, hpC s hs⟩ : C) ∈ T.comap C.subtype := by
        apply UnimodQuot.mem_of_perp_perp HC
        intro x hx
        rw [hB]
        change H.B x (p s) = 0
        rw [o3 _ (hCS x.2), ← H.herm, (mem_perp_iff H _ s).1 hs' x ⟨hCS x.2, ?_⟩, star_zero]
        refine (mem_perp_iff H T _).2 fun z hz => ?_
        rw [← o3 _ (hCS x.2)]
        exact (mem_perp_iff HC _ x).1 hx ⟨p z, hpC z (hTS hz)⟩ (hpT z hz)
      have h2 : p s ∈ T := h1
      simpa using T.add_mem h2 (hIT (hpI s))
    · intro x hx
      refine ⟨hTS hx, (mem_perp_iff H _ _).2 fun y hy => ?_⟩
      rw [← H.herm, (mem_perp_iff H T y).1 hy.2 x hx, star_zero]

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (M : Submodule (𝓞 K) V) (S I U : Submodule K V), I ≤ U → U ≤ S → (∀ x ∈ S, (∀ y ∈ S, H.B x y = 0) ↔ x ∈ I) → (∀ x ∈ U, (∀ y ∈ U, H.B x y = 0) ↔ x ∈ I) → IsUnimodMod H M S I → del H (M ⊓ rs (𝓞 K) U) = del H (M ⊓ rs (𝓞 K) (S ⊓ perp H U)) ∧ ∀ e : ℕ, GenBy (dual H (M ⊓ rs (𝓞 K) U)) (M ⊓ rs (𝓞 K) U) e → GenBy (dual H (M ⊓ rs (𝓞 K) (S ⊓ perp H U))) (M ⊓ rs (𝓞 K) (S ⊓ perp H U)) e := by
  intro K V _ _ _ _ _ _ _ _ H _ M S I U hIU hUS hrad _ hM
  have hIS := hIU.trans hUS
  obtain ⟨h1, h2⟩ := key H hIS hrad hM hIU hUS
  have hI' : I ≤ S ⊓ perp H U := fun i hi =>
    ⟨hIS hi, (mem_perp_iff H U i).2 fun x hx => (hrad i (hIS hi)).2 hi x (hUS hx)⟩
  obtain ⟨h3, -⟩ := key H hIS hrad hM hI' inf_le_left
  rw [h2] at h3
  constructor
  · rw [del, del, h1, h3, gidx_glue, gidx_glue, inf_comm]
  · rintro e ⟨t, ht, h⟩
    rw [h1] at h
    obtain ⟨t', ht', h'⟩ := gen_glue _ _ _ t h
    exact ⟨t', ht'.trans ht, h3.trans h'⟩

end GlobalTheory.DegCnt.Compl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HilbertSchmidtLowerBoundInverseDifferent
open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset

namespace GlobalTheory.DualBound

theorem opNorm_sq_le_hs {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℂ) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖ ^ 2 ≤ ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  have hS : 0 ≤ ∑ i, ∑ j, ‖M i j‖ ^ 2 := by positivity
  have h : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖ ≤
      Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, Real.sq_sqrt hS, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M) x) i‖ ≤
        ∑ j, ‖M i j‖ * ‖x j‖ := by
      have : (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M) x) i =
          ∑ j, M i j * x j := by
        simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
      rw [this]
      exact (norm_sum_le _ _).trans (le_of_eq (by simp))
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  calc _ ≤ (Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt hS

theorem card_mul_geom_sq_le {ι : Type} [Fintype ι] [Nonempty ι] (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i) :
    (Fintype.card ι : ℝ) * ((∏ i, z i) ^ ((1 : ℝ) / (Fintype.card ι : ℝ))) ^ 2 ≤
      ∑ i, z i ^ 2 := by
  have hf : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ : ι => (1 : ℝ) / (Fintype.card ι : ℝ)) (fun i => z i ^ 2)
    (fun _ _ => by positivity) (by simp [hf.ne']) (fun _ _ => by positivity)
  have hp : 0 ≤ ∏ i, z i := Finset.prod_nonneg fun i _ => hz i
  rw [Real.finsetProd_rpow _ _ (fun _ _ => by positivity), Finset.prod_pow, ← Finset.mul_sum] at h
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp, mul_comm (1 / _ : ℝ), Real.rpow_mul hp,
    Real.rpow_natCast]
  calc _ ≤ (Fintype.card ι : ℝ) * (1 / (Fintype.card ι : ℝ) * ∑ i, z i ^ 2) :=
        mul_le_mul_of_nonneg_left h hf.le
    _ = _ := by field_simp

theorem size_different_smul {K : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K]
    {a : ℕ} (X : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ) (hX : ∀ w, IsUnit (X w).det)
    {N : Submodule (𝓞 K) (Fin a → K)} (hN : N.FG) (hN0 : N ≠ ⊥) :
    Formalism.HN.size (Pi.basisFun K (Fin a)) X (differentIdeal ℤ (𝓞 K) • N) =
      Formalism.HN.size (Pi.basisFun K (Fin a)) X N * |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HN.nPl K : ℝ))) := by
  have hd : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  have hrk : rkK (differentIdeal ℤ (𝓞 K) • N) = rkK N := by
    unfold rkK; rw [Formalism.HN.DualPolygon.twist_span_smul N _ hd]
  have hnorm : (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) = |(NumberField.discr K : ℝ)| := by
    rw [NumberField.absNorm_differentIdeal K (𝓞 K), Nat.cast_natAbs, Int.cast_abs]
  have hj : (rkK N : ℝ) ≠ 0 := by exact_mod_cast (Formalism.LFunctionChainParameters.slopeLatticeData.rkK_pos hN0).ne'
  have hf : (Formalism.HN.nPl K : ℝ) ≠ 0 := by
    have : 0 < Formalism.HN.nPl K := Fintype.card_pos
    exact_mod_cast this.ne'
  unfold Formalism.HN.size
  rw [Formalism.LFunctionChainParameters.slopeLatticeData.ht_ideal _ X hX hN hd, hrk, hnorm,
    Real.mul_rpow (Formalism.LFunctionChainParameters.slopeLatticeData.ht_pos _ X hX hN).le (by positivity),
    ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
  congr 2
  field_simp

theorem hs_lower_bound :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (a b : ℕ) (X : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ) (X' : InfinitePlace K → Matrix (Fin b) (Fin b) ℂ) (A : Submodule (𝓞 K) (Fin a → K)) (B : Submodule (𝓞 K) (Fin b → K)) (lo hi : ℝ), (∀ w, IsUnit (X w).det) → (∀ w, IsUnit (X' w).det) → A.FG → B.FG → 0 < lo → (∀ N, N ≤ A → N ≠ ⊥ → lo ≤ Formalism.HN.size (Pi.basisFun K (Fin a)) X N) → Formalism.HN.largestSize (Pi.basisFun K (Fin b)) X' B ≤ hi → ∀ ψ : Matrix (Fin a) (Fin b) K, (∃ y ∈ B, ψ *ᵥ y ≠ 0) → (∀ δ ∈ differentIdeal ℤ (𝓞 K), ∀ y ∈ B, δ • (ψ *ᵥ y) ∈ A) → (Formalism.HN.nPl K : ℝ) * (lo / (|(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HN.nPl K : ℝ))) * hi)) ^ 2 ≤ ∑ w, ∑ i, ∑ j, ‖((X w)⁻¹ * ψ.map w.embedding * X' w) i j‖ ^ 2 := by
  intro K _ _ _ _ a b X X' A B lo hi hX hX' _ hB hlo hA hhi ψ ⟨y, hyB, hy⟩ hψ
  set φ : (Fin b → K) →ₗ[K] (Fin a → K) := Matrix.toLin' ψ with hφ
  set A' : Submodule (𝓞 K) (Fin a → K) := B.map (φ.restrictScalars (𝓞 K)) with hA'
  set rd : ℝ := |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HN.nPl K : ℝ))) with hrd
  have hrdpos : 0 < rd :=
    Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero K)) _
  have hA'fg : A'.FG := hB.map _
  have hA'0 : A' ≠ ⊥ := by
    intro h
    have : ψ *ᵥ y ∈ A' := ⟨y, hyB, by simp [hφ]⟩
    rw [h] at this
    exact hy this
  have hB0 : B ≠ ⊥ := by
    rintro rfl
    exact hA'0 (by rw [hA', Submodule.map_bot])
  have hd : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  have hleast : lo / rd ≤ leastSize (Pi.basisFun K (Fin a)) X A' := by
    refine le_csInf ⟨_, A', le_rfl, hA'0, rfl⟩ ?_
    rintro t ⟨N, hN, hN0, rfl⟩
    have hNfg : N.FG := Submodule.FG.of_le hA'fg hN
    have h1 : differentIdeal ℤ (𝓞 K) • N ≤ A := by
      refine Submodule.smul_le.2 fun δ hδ v hv => ?_
      obtain ⟨z, hz, rfl⟩ := hN hv
      simpa [hφ] using hψ δ hδ z hz
    have h2 : differentIdeal ℤ (𝓞 K) • N ≠ ⊥ := by
      intro h
      have h3 := Formalism.HN.DualPolygon.twist_span_smul N _ hd
      rw [h] at h3
      apply hN0
      rw [eq_bot_iff]
      intro v hv
      have : v ∈ Submodule.span K (N : Set (Fin a → K)) := Submodule.subset_span hv
      rw [← h3] at this
      simpa using this
    have h3 := hA _ h1 h2
    rw [size_different_smul X hX hNfg hN0] at h3
    rw [div_le_iff₀ hrdpos]
    exact h3
  have hLpos : 0 < Formalism.HN.largestSize (Pi.basisFun K (Fin b)) X' B := by
    rw [(sizeMu K _ _ (Pi.basisFun K (Fin b)) X' hX' B hB hB0).2.2.2.2.1]
    exact Real.exp_pos _
  have hM := sizeIneq K _ _ _ _ (Pi.basisFun K (Fin b)) X' (Pi.basisFun K (Fin a)) X hX' hX φ B A'
    hB hA'fg le_rfl hA'0
  have hhipos : 0 < hi := hLpos.trans_le hhi
  have h4 : lo / (rd * hi) ≤
      (∏ v, opNormAt (Pi.basisFun K (Fin b)) X' (Pi.basisFun K (Fin a)) X v φ) ^
        ((1 : ℝ) / (Formalism.HN.nPl K : ℝ)) := by
    refine le_trans ?_ hM
    rw [← div_div]
    exact div_le_div₀ ((div_pos hlo hrdpos).le.trans hleast) hleast hLpos hhi
  have h5 := card_mul_geom_sq_le
    (fun v => opNormAt (Pi.basisFun K (Fin b)) X' (Pi.basisFun K (Fin a)) X v φ)
    (fun v => norm_nonneg _)
  calc _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h4 2) (Nat.cast_nonneg _)
    _ ≤ _ := h5
    _ ≤ _ := by
      refine Finset.sum_le_sum fun w _ => ?_
      have h6 : LinearMap.toMatrix (Pi.basisFun K (Fin b)) (Pi.basisFun K (Fin a)) φ = ψ := by
        ext i j
        simp [hφ]
      unfold opNormAt
      rw [h6]
      exact opNorm_sq_le_hs _

end GlobalTheory.DualBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairExistsUnipotentSplitLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairExistsUnipotentSplitLattice
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.SplitLift

section Lattice

variable {R K V : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem exists_smul_mem (M : Submodule R V) {x : V} (hx : x ∈ Submodule.span K (M : Set V)) :
    ∃ d : R, d ≠ 0 ∧ d • x ∈ M := by
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) K (M : Set V) x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t, nonZeroDivisors.coe_ne_zero t, ht⟩

theorem exists_split (Λ : Submodule R V) (hfg : Λ.FG) (hsp : Submodule.span K (Λ : Set V) = ⊤)
    (S I : Submodule K V) :
    ∃ W : Submodule K V, W ≤ S ∧ W ⊓ I = ⊥ ∧ S ≤ W ⊔ I ∧
      ∀ l ∈ Λ, l ∈ S → ∃ w ∈ Λ, w ∈ W ∧ l - w ∈ I := by
  set M : Submodule R V := Λ ⊓ S.restrictScalars R with hM
  have hMfg : M.FG := by
    have : Module.Finite R Λ := Module.Finite.iff_fg.2 hfg
    exact (Module.Finite.iff_fg (N := M)).1
      (Module.Finite.of_injective (Submodule.inclusion (inf_le_left : M ≤ Λ))
        (Submodule.inclusion_injective _))
  have : Module.Finite R M := Module.Finite.iff_fg.2 hMfg
  let π : M →ₗ[R] (V ⧸ I) := (I.mkQ.restrictScalars R) ∘ₗ M.subtype
  have : Module.IsTorsionFree R (V ⧸ I) := Module.IsTorsionFree.trans K
  have : Module.Finite R (LinearMap.range π) := inferInstance
  have : Module.Flat R (LinearMap.range π) := inferInstance
  have : Module.FinitePresentation R (LinearMap.range π) :=
    Module.finitePresentation_of_finite R _
  have : Module.Projective R (LinearMap.range π) := Module.Flat.projective_of_finitePresentation
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π.rangeRestrict LinearMap.id
    π.surjective_rangeRestrict
  have hσ' : ∀ y, π (σ y) = (y : V ⧸ I) := fun y => by
    have := congrArg Subtype.val (LinearMap.congr_fun hσ y)
    simpa using this
  set N : Submodule R V := LinearMap.range (M.subtype ∘ₗ σ) with hN
  have key : ∀ l ∈ Λ, l ∈ S → ∃ w ∈ Λ, w ∈ Submodule.span K (N : Set V) ∧ l - w ∈ I := by
    intro l hl hlS
    let y : LinearMap.range π := ⟨π ⟨l, hl, hlS⟩, _, rfl⟩
    refine ⟨(σ y : V), (σ y).2.1, Submodule.subset_span ⟨y, rfl⟩, ?_⟩
    rw [← Submodule.Quotient.eq]
    exact (hσ' y).symm
  have hinj : ∀ d : R, d ≠ 0 → algebraMap R K d ≠ 0 := fun d hd =>
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hd
  refine ⟨Submodule.span K (N : Set V), ?_, ?_, ?_, key⟩
  · rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    exact (σ y).2.2
  · rw [eq_bot_iff]
    rintro x ⟨hx, hxI⟩
    obtain ⟨d, hd, y, hy⟩ := exists_smul_mem N hx
    have hy' : ((σ y : M) : V) = d • x := hy
    have h0 : (y : V ⧸ I) = 0 := by
      rw [← hσ' y]
      show I.mkQ ((σ y : M) : V) = 0
      rw [hy', Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact I.smul_of_tower_mem d hxI
    have h1 : y = 0 := Subtype.ext h0
    rw [h1, map_zero, ← algebraMap_smul K d x] at hy'
    exact (smul_eq_zero.1 hy'.symm).resolve_left (hinj d hd)
  · intro x hx
    obtain ⟨d, hd, hdx⟩ := exists_smul_mem (K := K) Λ (x := x) (by rw [hsp]; trivial)
    obtain ⟨w, -, hw, hwI⟩ := key _ hdx (S.smul_of_tower_mem d hx)
    have h1 : d • x ∈ Submodule.span K (N : Set V) ⊔ I :=
      Submodule.mem_sup.2 ⟨w, hw, _, hwI, by abel⟩
    rw [← algebraMap_smul K d x] at h1
    exact (Submodule.smul_mem_iff _ (hinj d hd)).1 h1

end Lattice

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

section Geometry
omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem flip_zero {x y : V} (h : H.B x y = 0) : H.B y x = 0 := by
  rw [← H.herm, h, star_zero]

theorem mem_wSp_iff (F F' : FlagD H r) (w : V) : w ∈ wSp F F' ↔ ∀ y ∈ V0 F F', H.B y w = 0 := by
  rw [wSp, mem_perp_iff]
  exact ⟨fun h y hy => flip_zero (h y hy), fun h y hy => flip_zero (h y hy)⟩

theorem hermFlagPair_isotropic_sup_le_commonSpace (F F' : FlagD H r) : F.X ⊔ F'.X ≤ V0 F F' := le_sup_left

theorem isotropicMeet_le_jointSpan (F F' : FlagD H r) : II F F' ≤ V0 F F' :=
  (inf_le_left.trans le_sup_left).trans (hermFlagPair_isotropic_sup_le_commonSpace F F')

theorem flag_vector_mem_base_lattice (F F' : FlagD H r) (a : Fin (r + 1)) : F.e a ∈ V0 F F' := by
  induction a using Fin.lastCases with
  | last => exact Submodule.mem_sup_right (Submodule.subset_span (Or.inl rfl))
  | cast b =>
    exact hermFlagPair_isotropic_sup_le_commonSpace F F' (Submodule.mem_sup_left (Submodule.subset_span ⟨b, b.2, rfl⟩))

theorem X_perp (F : FlagD H r) {w x : V} (hw : ∀ a : Fin (r + 1), H.B (F.e a) w = 0) (hx : x ∈ F.X) :
    H.B x w = 0 := by
  have : F.X ≤ LinearMap.ker (H.B.flip w) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, -, rfl⟩
    exact hw _
  exact this hx

theorem aniso_right {F F' : FlagD H r} {j : ℕ} {hj : j ≤ r} {c : K} (h : NFFull F F' j hj c)
    (hF : F.Aniso) : F'.Aniso := by
  obtain ⟨-, -, -, -, -, h6, -, -, h9⟩ := h
  intro w hw hww
  obtain ⟨x, hx, hwx⟩ := h9 w hw
  have h1 : H.B (w - x) (w - x) = 0 := by
    have a1 : H.B x (w - x) = 0 := hwx x (hermFlagPair_isotropic_sup_le_commonSpace F F' (Submodule.mem_sup_right hx))
    have a2 : H.B w x = 0 := flip_zero (X_perp F' hw hx)
    rw [map_sub H.B, LinearMap.sub_apply, a1, map_sub, hww, a2]
    simp
  have h2 : w - x ∈ F.X := hF _ (fun a => hwx _ (flag_vector_mem_base_lattice F F' a)) h1
  have h3 : w - x ∈ F'.X := ((h6 _ h2).1 hwx).2
  simpa using add_mem h3 hx

end Geometry

theorem latTh_eq (F F' : FlagD H r) (hI : II F F' ≤ wSp F F') (Λ : Submodule (𝓞 K) V) :
    latTh F F' Λ = (Λ ⊓ rs (𝓞 K) (wSp F F')) ⊔ rs (𝓞 K) (II F F') := by
  have hu : ∀ y ∈ wSp F F', y ∈ uPerp F F' := fun y hy =>
    (mem_perp_iff H _ y).2 fun x hx => (mem_perp_iff H _ y).1 hy x (hermFlagPair_isotropic_sup_le_commonSpace F F' hx)
  have hp : ∀ y ∈ wSp F F', y ∈ perp H (II F F') := fun y hy =>
    (mem_perp_iff H _ y).2 fun x hx => (mem_perp_iff H _ y).1 hy x (isotropicMeet_le_jointSpan F F' hx)
  apply le_antisymm
  · rintro y ⟨⟨hy1, -⟩, hy3⟩
    obtain ⟨l, ⟨hl, -⟩, x, hx, rfl⟩ := Submodule.mem_sup.1 hy1
    refine Submodule.mem_sup.2 ⟨l, ⟨hl, ?_⟩, x, hx, rfl⟩
    have : l + x - x ∈ wSp F F' := sub_mem hy3 (hI hx)
    simpa using this
  · refine sup_le ?_ ?_
    · rintro l ⟨hl, hw⟩
      exact ⟨⟨Submodule.mem_sup_left ⟨hl, hp l hw⟩, hu l hw⟩, hw⟩
    · intro x hx
      exact ⟨⟨Submodule.mem_sup_right hx, hu x (hI hx)⟩, hI hx⟩

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∃ s ∈ N.R, N.Split (s • Λ) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ _ hΛ
  obtain ⟨hfull, hlift, -, -, -, -, hw, -⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  have hL := (isLatMod_top_bot_iff Λ).1 hΛ.1.1.1
  obtain ⟨W, hWS, hWI, hSW, hWΛ⟩ :=
    exists_split Λ hL.1 hΛ.1.1.1.2 (wSp N.F N.F') (II N.F N.F')
  have hW : IsLift N.F N.F' W :=
    ⟨fun w h => (mem_wSp_iff _ _ w).1 (hWS h), hWI, fun w h => hSW ((mem_wSp_iff _ _ w).2 h)⟩
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hA : N.F.Aniso := by
    intro w h1 h2
    by_contra hne
    have := N.posdef σ w h1 hne
    rw [h2] at this
    simp at this
  obtain ⟨f, hf, hf', hfix, hmap⟩ := Formalism.HermitianLatticeCounting.P.complementLiftTransitive K V H r N.F N.F' W N.Wt
    ⟨1, by rw [star_one]; norm_num⟩ hA (aniso_right hfull hA) hW hlift
  let s : V ≃ₗ[K] V := LinearEquiv.ofBijective f hf.2.1
  refine ⟨s, Subgroup.subset_closure ⟨hf, hf'⟩, ?_⟩
  have hI : II N.F N.F' ≤ wSp N.F N.F' := by rw [hw]; exact le_sup_right
  have hWt : N.Wt ≤ wSp N.F N.F' := by rw [hw]; exact le_sup_left
  rw [NF.Split, latTh_eq _ _ hI]
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    rintro y ⟨hy, hyw⟩
    obtain ⟨l, hl, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists y s Λ).1 hy
    have hlw : l ∈ wSp N.F N.F' := by
      refine (mem_wSp_iff _ _ l).2 fun y hy => ?_
      rw [← hf.1, hfix y hy]
      exact (mem_wSp_iff _ _ _).1 hyw y hy
    obtain ⟨w, hw1, hw2, hw3⟩ := hWΛ l hl hlw
    refine Submodule.mem_sup.2 ⟨f w, ⟨Submodule.smul_mem_pointwise_smul w s Λ hw1, ?_⟩, l - w, hw3, ?_⟩
    · show f w ∈ N.Wt
      rw [← hmap]
      exact ⟨w, hw2, rfl⟩
    · show f w + (l - w) = f l
      rw [← hfix _ (isotropicMeet_le_jointSpan _ _ hw3), map_sub]
      abel
  · exact sup_le_sup_right (inf_le_inf_left _ fun x hx => hWt hx) _

end GlobalTheory.DegCnt.SplitLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairExistsUnipotentSplitLatticeStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermFramePair_exists_unipotent_split_lattice : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∃ s ∈ N.R, N.Split (s • Λ) := by
  first | exact @GlobalTheory.DegCnt.SplitLift.main | exact GlobalTheory.DegCnt.SplitLift.main | (intros; apply GlobalTheory.DegCnt.SplitLift.main <;> assumption)
end
end
