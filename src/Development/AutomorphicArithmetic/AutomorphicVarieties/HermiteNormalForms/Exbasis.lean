module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.AltDoubleSum

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Exbasis
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.exbasis :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (M : Set (Lat L N)), Spans M →
    ∃ A : Matrix (Fin N) (Fin N) (𝓞 L), A.det ≠ 0 ∧ ∀ a, (fun i => A i a) ∈ M := by
  intro L _ _ N M hM
  classical
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent L (toL '' M)
  have htop : (⊤ : Submodule L (Fin N → L)) ≤ Submodule.span L (Set.range ((↑) : s → Fin N → L)) := by
    rw [Subtype.range_coe, hspan]
    exact hM.ge
  let B := Module.Basis.mk hli htop
  haveI : Fintype s := @Fintype.ofFinite s (Module.Finite.finite_basis B)
  have hcard : Fintype.card s = N := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fin_fun]
  let e : Fin N ≃ s := (Fintype.equivFinOfCardEq hcard).symm
  have hmem : ∀ a, ∃ y ∈ M, toL y = (e a : Fin N → L) := fun a => hs (e a).2
  choose y hyM hy using hmem
  refine ⟨fun i a => y a i, ?_, fun a => hyM a⟩
  intro h0
  have hli' : LinearIndependent L (fun a => ((e a : s) : Fin N → L)) := hli.comp e e.injective
  let C : Matrix (Fin N) (Fin N) L := fun i a => ((e a : s) : Fin N → L) i
  have hC : IsUnit C := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli'
  let A : Matrix (Fin N) (Fin N) (𝓞 L) := fun i a => y a i
  have hCA : C = (algebraMap (𝓞 L) L).mapMatrix A := by
    ext i a
    simp only [C, A, RingHom.mapMatrix_apply, Matrix.map_apply, ← hy]
    rfl
  have hdet : C.det = algebraMap (𝓞 L) L A.det := by
    rw [hCA]
    exact (RingHom.map_det (algebraMap (𝓞 L) L) A).symm
  have h0' : A.det = 0 := h0
  rw [h0', map_zero] at hdet
  exact (Matrix.isUnit_iff_isUnit_det C |>.mp hC).ne_zero hdet
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.RealVec
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.gramq :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (h : HS L N), (gram h).IsHermitian ∧
    (∀ x : Fin N × BI L → ℝ, x ⬝ᵥ (gram h *ᵥ x) = qR h (realVec x)) ∧
    (∀ c : Fin N × BI L → ℤ, realVec (fun s => (c s : ℝ)) = toR (intVec c)) ∧
    Function.Bijective (intVec : (Fin N × BI L → ℤ) → Lat L N) := by
  intro L _ _ N h
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Matrix.IsHermitian.ext fun s t => ?_
    simp only [gram, of_apply, star_trivial]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← (mat_herm h w).apply t.1 s.1]
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.mul_im]
    ring
  · intro x
    have key : ∀ w, (star (realVec x w) ⬝ᵥ mat h w *ᵥ realVec x w).re =
        ∑ s, ∑ t, x s * ((star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 *
          embO w (RingOfIntegers.basis L t.2)).re * x t) := by
      intro w
      have hr : ∀ s t, x s * ((star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 *
          embO w (RingOfIntegers.basis L t.2)).re * x t) =
          ((x s : ℂ) * (star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 *
          embO w (RingOfIntegers.basis L t.2)) * (x t : ℂ)).re := by
        intro s t
        rw [Complex.re_mul_ofReal, Complex.re_ofReal_mul]
        ring
      simp only [hr, ← Complex.re_sum]
      congr 1
      simp only [realVec, dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', Complex.star_def,
        Complex.conj_ofReal, Finset.mul_sum, Finset.sum_mul, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Eq.trans ?_ Finset.sum_comm.symm
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Eq.trans ?_ Finset.sum_comm.symm
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      ring
    simp only [qR, key]
    simp only [dotProduct, mulVec, gram, of_apply, Finset.mul_sum, Finset.sum_mul]
    calc ∑ s, ∑ t, ∑ w, x s * ((star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 *
          embO w (RingOfIntegers.basis L t.2)).re * x t)
        = ∑ s, ∑ w, ∑ t, x s * ((star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 *
          embO w (RingOfIntegers.basis L t.2)).re * x t) :=
          Finset.sum_congr rfl fun s _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  · intro c
    funext w a
    set_option synthInstance.maxHeartbeats 100000 in
      simp [realVec, toR, intVec, map_sum, zsmul_eq_mul]
  · let E : (Fin N × BI L → ℤ) ≃ Lat L N :=
      (Equiv.curry _ _ _).trans
        (Equiv.piCongrRight fun _ => (RingOfIntegers.basis L).equivFun.symm.toEquiv)
    have hE : (intVec : (Fin N × BI L → ℤ) → Lat L N) = E := by
      funext c a
      simp [E, intVec, Module.Basis.equivFun_symm_apply, Equiv.curry]
    rw [hE]
    exact E.bijective
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Spanpsd
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.spanpsd :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (M : Set (Lat L N)),
    (∀ k ∈ Psd L N, (∀ y ∈ M, q k y = 0) → k = 0) → Spans M := by
  intro L _ _ N M hM
  classical
  by_contra hS
  have hlt : spanL M < ⊤ := lt_top_iff_ne_top.mpr hS
  obtain ⟨f, hf0, hker⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  set c : Fin N → L := fun i => f (fun j => if i = j then 1 else 0) with hcdef
  have hfc : ∀ x : Fin N → L, f x = ∑ i, x i * c i := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ]
    rfl
  have hc0 : ∃ i, c i ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hf0
    refine LinearMap.ext fun x => ?_
    rw [hfc]
    simp [hc]
  obtain ⟨i0, hi0⟩ := hc0
  let u : InfinitePlace L → Fin N → ℂ := fun w i => w.embedding (c i)
  let A : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ := fun w => vecMulVec (star (u w)) (u w)
  have hA : ∀ w, (A w).PosSemidef := fun w => posSemidef_vecMulVec_star_self (u w)
  let k : HS L N := mkHS A (fun w => (hA w).isHermitian)
  have hmat : ∀ w, mat k w = A w := fun w => rfl
  have hkP : k ∈ Psd L N := by
    intro w
    rw [hmat]
    exact hA w
  have hq : ∀ y ∈ M, q k y = 0 := by
    intro y hy
    have hyk : f (toL y) = 0 := hker (Submodule.subset_span ⟨y, hy, rfl⟩)
    rw [hfc] at hyk
    show ∑ w, (star (toR y w) ⬝ᵥ mat k w *ᵥ toR y w).re = 0
    refine Finset.sum_eq_zero fun w _ => ?_
    have hsum : ∑ j, u w j * toR y w j = 0 := by
      have : w.embedding (∑ j, toL y j * c j) = 0 := by rw [hyk, map_zero]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, mul_comm]
      rfl
    have hAz : mat k w *ᵥ toR y w = 0 := by
      funext i
      rw [hmat]
      simp only [A, mulVec, dotProduct, vecMulVec_apply, mul_assoc, ← Finset.mul_sum, hsum,
        mul_zero, Pi.zero_apply]
    rw [hAz]
    simp
  have hk0 := hM k hkP hq
  have w0 : InfinitePlace L := Classical.arbitrary _
  have h1 : mat k w0 i0 i0 = 0 := by
    rw [hk0]
    rfl
  rw [hmat] at h1
  simp only [A, vecMulVec_apply, Pi.star_apply, u] at h1
  have hne : w0.embedding (c i0) ≠ 0 := (map_ne_zero _).mpr hi0
  exact hne (by
    rcases mul_eq_zero.mp h1 with h | h
    · exact star_eq_zero.mp h
    · exact h)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Scinv
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.scinv :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (A : Matrix (Fin N) (Fin N) (𝓞 L)), A.det ≠ 0 →
    0 < nrmDet A ∧ ∃ B : Matrix (Fin N) (Fin N) (𝓞 L), A * B = ((nrmDet A : ℕ) : 𝓞 L) • (1 : Matrix (Fin N) (Fin N) (𝓞 L)) ∧
      B * A = ((nrmDet A : ℕ) : 𝓞 L) • (1 : Matrix (Fin N) (Fin N) (𝓞 L)) := by
  intro L _ _ N A hA
  refine ⟨Int.natAbs_pos.mpr (Algebra.norm_ne_zero_iff.mpr hA), ?_⟩
  have hmem : ((Ideal.absNorm (Ideal.span {A.det}) : ℕ) : 𝓞 L) ∈ Ideal.span {A.det} :=
    Ideal.absNorm_mem _
  rw [Ideal.absNorm_span_singleton, Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hc' : ((nrmDet A : ℕ) : 𝓞 L) = A.det * c := hc
  refine ⟨c • A.adjugate, ?_, ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hc', mul_comm]
  · rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, hc', mul_comm]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Realsurj
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

open NumberField.InfinitePlace in
private theorem one_coord (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L]
    (z : InfinitePlace L → ℂ) :
    ∃ x : BI L → ℝ, ∀ w, ∑ i, (x i : ℂ) * embO w (RingOfIntegers.basis L i) = z w := by
  classical
  let m : mixedEmbedding.mixedSpace L := (0, fun w => z w.1)
  let c := (mixedEmbedding.latticeBasis L).repr m
  refine ⟨fun i => c i, fun w => ?_⟩
  have hw : w.IsComplex := IsTotallyComplex.isComplex w
  have hsum := (mixedEmbedding.latticeBasis L).sum_repr m
  have h2 := congrArg (fun p : mixedEmbedding.mixedSpace L => p.2 ⟨w, hw⟩) hsum
  simp only [Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply,
    mixedEmbedding.latticeBasis_apply, mixedEmbedding.mixedEmbedding_apply_isComplex,
    integralBasis_apply, Complex.real_smul, m] at h2
  rw [← h2]
  rfl

theorem UpperTheory.V.KT.realsurj :
    ∀ (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N : ℕ),
    Function.Surjective (realVec : (Fin N × BI L → ℝ) → VR L N) := by
  intro L _ _ _ N z
  choose x hx using fun a : Fin N => one_coord L (fun w => z w a)
  exact ⟨fun s => x s.1 s.2, funext fun w => funext fun a => hx a w⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Cntconj
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.cntconj :
    ∀ (L : Type) [Field L] [NumberField L] (R : ℕ),
    {a : 𝓞 L | ∀ w, ‖embO w a‖ ≤ R}.Finite ∧
      {a : 𝓞 L | ∀ w, ‖embO w a‖ ≤ R}.ncard ≤ (2 * R + 1) ^ Module.finrank ℚ L := by
  intro L _ _ R
  have hq : 2 * R + 1 ≠ 0 := by omega
  have hsep : ∀ a ∈ {a : 𝓞 L | ∀ w, ‖embO w a‖ ≤ R}, ∀ b ∈ {a : 𝓞 L | ∀ w, ‖embO w a‖ ≤ R},
      ∀ x : 𝓞 L, a - b = (2 * R + 1) • x → a = b := by
    intro a ha b hb x hab
    by_cases hx : x = 0
    · rw [hx, smul_zero, sub_eq_zero] at hab
      exact hab
    exfalso
    have key : ∀ w : InfinitePlace L, w (x : L) < 1 := by
      intro w
      have h1 : ‖embO w (a - b)‖ ≤ 2 * R := by
        rw [map_sub]
        calc ‖embO w a - embO w b‖ ≤ ‖embO w a‖ + ‖embO w b‖ := norm_sub_le _ _
          _ ≤ R + R := add_le_add (ha w) (hb w)
          _ = 2 * R := by ring
      rw [hab, map_nsmul, nsmul_eq_mul, norm_mul, Complex.norm_natCast] at h1
      have hn : ‖embO w x‖ = w (x : L) := InfinitePlace.norm_embedding_eq w (x : L)
      rw [hn] at h1
      push_cast at h1
      by_contra hc
      push_neg at hc
      have : (2 * (R : ℝ) + 1) * 1 ≤ (2 * (R : ℝ) + 1) * w (x : L) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      linarith
    obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace L))
    have := InfinitePlace.one_le_of_lt_one (w := w0) hx (fun z _ => key z)
    linarith [key w0]
  obtain ⟨hfin, hcard⟩ := cardsep (𝓞 L) (2 * R + 1) hq _ hsep
  refine ⟨hfin, ?_⟩
  rwa [RingOfIntegers.rank] at hcard
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.LowbdSmul
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

private theorem lowbd_cont (L : Type) [Field L] [NumberField L] (N : ℕ) :
    Continuous (fun p : HS L N × VR L N => qR p.1 p.2) := by
  unfold qR mat
  simp only [dotProduct, mulVec, Matrix.of_apply, Pi.star_apply]
  have hv : Continuous fun p : HS L N × VR L N => (p.1 : InfinitePlace L → Fin N → Fin N → ℂ) :=
    continuous_subtype_val.comp continuous_fst
  have hz : Continuous fun p : HS L N × VR L N => (p.2 : InfinitePlace L → Fin N → ℂ) := continuous_snd
  refine continuous_finsetSum _ fun w _ => Complex.continuous_re.comp ?_
  refine continuous_finsetSum _ fun i _ => ?_
  refine (continuous_star.comp ((continuous_apply i).comp ((continuous_apply w).comp hz))).mul ?_
  refine continuous_finsetSum _ fun j _ => ?_
  exact ((continuous_apply j).comp ((continuous_apply i).comp ((continuous_apply w).comp hv))).mul
    ((continuous_apply j).comp ((continuous_apply w).comp hz))

private theorem lowbd_smul {L : Type} [Field L] [NumberField L] {N : ℕ} (k : HS L N) (r : ℝ)
    (z : VR L N) : qR k (r • z) = r ^ 2 * qR k z := by
  unfold qR
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Pi.smul_apply, star_smul, star_trivial, mulVec_smul, dotProduct_smul, smul_dotProduct,
    Complex.smul_re, smul_eq_mul]
  ring

private theorem lowbd_pos {L : Type} [Field L] [NumberField L] {N : ℕ} {h : HS L N}
    (hh : h ∈ Pos L N) {z : VR L N} (hz : z ≠ 0) : 0 < qR h z := by
  have hne : ∃ w, z w ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hz (funext hc)
  obtain ⟨w0, hw0⟩ := hne
  have hp : ∀ w, (mat h w).PosDef := hh
  unfold qR
  apply Finset.sum_pos'
  · intro w _
    by_cases hw : z w = 0
    · simp [hw]
    · exact le_of_lt (Complex.pos_iff.mp ((hp w).dotProduct_mulVec_pos hw)).1
  · exact ⟨w0, Finset.mem_univ _, (Complex.pos_iff.mp ((hp w0).dotProduct_mulVec_pos hw0)).1⟩

theorem UpperTheory.V.KT.lowbd :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (h : HS L N), h ∈ Pos L N →
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in nhds h, ∀ z : VR L N, c * ‖z‖ ^ 2 ≤ qR k z := by
  intro L _ _ N h hh
  have hK : IsCompact (Metric.sphere (0 : VR L N) 1) := isCompact_sphere 0 1
  have hcont := lowbd_cont L N
  have hsec : Continuous fun z : VR L N => (h, z) := by fun_prop
  obtain ⟨m, hm, hmle⟩ := hK.exists_forall_le' (f := fun z => qR h z)
    (hcont.comp hsec).continuousOn (a := 0)
    (fun z hz => lowbd_pos hh (by
      intro h0
      rw [h0] at hz
      simp at hz))
  refine ⟨m / 2, by positivity, ?_⟩
  have hev : ∀ᶠ k in nhds h, ∀ z ∈ Metric.sphere (0 : VR L N) 1, m / 2 < qR k z := by
    apply hK.eventually_forall_of_forall_eventually
    intro z hz
    have hlt : m / 2 < qR h z := by linarith [hmle z hz]
    exact (hcont.tendsto (h, z)).eventually (lt_mem_nhds hlt)
  filter_upwards [hev] with k hk z
  by_cases hz : z = 0
  · subst hz
    have h0 : qR k (0 : VR L N) = 0 := by simpa using lowbd_smul k 0 (0 : VR L N)
    simp [h0]
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hu : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : VR L N) 1 := by
      simp [norm_smul, hn.ne']
    have hzu : ‖z‖ • (‖z‖⁻¹ • z) = z := by
      rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have hlt := hk _ hu
    calc m / 2 * ‖z‖ ^ 2 ≤ ‖z‖ ^ 2 * qR k (‖z‖⁻¹ • z) := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left hlt.le (by positivity)
      _ = qR k (‖z‖ • (‖z‖⁻¹ • z)) := (lowbd_smul k ‖z‖ _).symm
      _ = qR k z := by rw [hzu]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Faceexact
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

private theorem UpperTheory.V.KT.fe_lift {X : Type} (s : Set X) (c : X →₀ ℤ)
    (hc : c ∈ Finsupp.supported ℤ ℤ s) :
    ∃ f : {t // t ∈ s} →₀ ℤ, Finsupp.mapDomain Subtype.val f = c := by
  have h := Finsupp.lmapDomain_supported ℤ ℤ (Subtype.val : {t // t ∈ s} → X) Set.univ
  rw [Set.image_univ, Subtype.range_coe_subtype, Set.setOf_mem_eq] at h
  rw [← h] at hc
  obtain ⟨f, -, hf⟩ := hc
  exact ⟨f, hf⟩

private theorem UpperTheory.V.KT.fe_mem {X : Type} (s : Set X) (f : {t // t ∈ s} →₀ ℤ) :
    Finsupp.mapDomain Subtype.val f ∈ Finsupp.supported ℤ ℤ s := by
  have h := Finsupp.lmapDomain_supported (M := ℤ) (R := ℤ) (Subtype.val : {t // t ∈ s} → X) Set.univ
  rw [Set.image_univ, Subtype.range_coe] at h
  rw [← h]
  exact Submodule.mem_map_of_mem (by simp [Finsupp.supported_univ])

private theorem UpperTheory.V.KT.fe_comm {I : Type} (S : ∀ n, Set (Fin n → I)) (hS : ConeExtensionAcyclic.FaceClosed S)
    (p : ℕ) (f : {t : Fin (p + 1) → I // t ∈ S (p + 1)} →₀ ℤ) :
    Finsupp.mapDomain Subtype.val
      (KH.faceD (fun (i : Fin (p + 1)) (t : {t : Fin (p + 1) → I // t ∈ S (p + 1)}) =>
        (⟨t.1 ∘ i.succAbove, hS _ t.1 t.2 i⟩ : {t : Fin p → I // t ∈ S p})) f) =
      ConeExtensionAcyclic.bd I p (Finsupp.mapDomain Subtype.val f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add (f := _), Finsupp.mapDomain_add, hf, hg, Finsupp.mapDomain_add, map_add (f := _)]
  | single t c =>
    rw [KH.faceD_single, Finsupp.mapDomain_single]
    simp only [ConeExtensionAcyclic.bd, Finsupp.linearCombination_single, Finset.smul_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finsupp.lmapDomain_apply ℤ ℤ, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_zsmul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [mul_comm]

private theorem UpperTheory.V.KT.fe_aug {I : Type} (s : Set (Fin 1 → I)) (f : {t // t ∈ s} →₀ ℤ) :
    ConeExtensionAcyclic.bd I 0 (Finsupp.mapDomain Subtype.val f) =
      Finsupp.single (Fin.elim0 : Fin 0 → I) (KH.aug _ f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.mapDomain_add, map_add (f := _), hf, hg, map_add (f := _), Finsupp.single_add]
  | single t c =>
    rw [Finsupp.mapDomain_single, KH.aug_single]
    simp only [ConeExtensionAcyclic.bd, Finsupp.linearCombination_single]
    rw [Fin.sum_univ_one]
    simp only [Fin.val_zero, pow_zero, one_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
    congr 1
    funext k
    exact Fin.elim0 k

theorem UpperTheory.V.KT.faceexact :
    ∀ (I : Type) (S : ∀ n, Set (Fin n → I)) (hS : ConeExtensionAcyclic.FaceClosed S), S 0 = Set.univ → ConeExtensionAcyclic.Acyc S → ∀ m : ℕ,
    KH.FaceExactTo (fun p => {t : Fin (p + 1) → I // t ∈ S (p + 1)})
      (fun p i t => ⟨t.1 ∘ i.succAbove, hS _ t.1 t.2 i⟩) m := by
  intro I S hS hS0 hA m
  obtain ⟨hA0, hAn⟩ := hA
  have inj : ∀ n, Function.Injective (Finsupp.mapDomain (M := ℤ) (Subtype.val : {t : Fin n → I // t ∈ S n} → (Fin n → I))) :=
    fun n => Finsupp.mapDomain_injective Subtype.val_injective
  refine ⟨?_, ?_, ?_⟩
  · have hc : Finsupp.single (Fin.elim0 : Fin 0 → I) (1 : ℤ) ∈ Finsupp.supported ℤ ℤ (S 0) := by
      rw [hS0, Finsupp.supported_univ]
      exact Submodule.mem_top
    obtain ⟨b, hb, hbc⟩ := hA0 _ hc
    obtain ⟨f, rfl⟩ := fe_lift (S 1) b hb
    rw [fe_aug] at hbc
    have h1 : KH.aug _ f = 1 := Finsupp.single_injective _ hbc
    intro n
    exact ⟨n • f, by rw [map_zsmul, h1, smul_eq_mul, mul_one]⟩
  · intro y
    constructor
    · intro hy
      have hc := fe_mem (S 1) y
      have hbd : ConeExtensionAcyclic.bd I 0 (Finsupp.mapDomain Subtype.val y) = 0 := by
        rw [fe_aug, hy, Finsupp.single_zero]
      obtain ⟨b, hb, hbc⟩ := hAn 0 _ hc hbd
      obtain ⟨g, rfl⟩ := fe_lift (S 2) b hb
      refine ⟨g, inj 1 ?_⟩
      rw [fe_comm S hS 1 g, hbc]
    · rintro ⟨g, rfl⟩
      have h := fe_aug (S 1) (KH.faceD (fun (i : Fin 2) (t : {t : Fin 2 → I // t ∈ S 2}) =>
        (⟨t.1 ∘ i.succAbove, hS _ t.1 t.2 i⟩ : {t : Fin 1 → I // t ∈ S 1})) g)
      rw [fe_comm S hS 1 g, ConeExtensionAcyclic.bd_bd] at h
      exact Finsupp.single_eq_zero.mp h.symm
  · intro p _ y
    constructor
    · intro hy
      have hc := fe_mem (S (p + 2)) y
      have hbd : ConeExtensionAcyclic.bd I (p + 1) (Finsupp.mapDomain Subtype.val y) = 0 := by
        rw [← fe_comm S hS (p + 1) y, hy, Finsupp.mapDomain_zero]
      obtain ⟨b, hb, hbc⟩ := hAn (p + 1) _ hc hbd
      obtain ⟨g, rfl⟩ := fe_lift (S (p + 3)) b hb
      refine ⟨g, inj (p + 2) ?_⟩
      rw [fe_comm S hS (p + 2) g, hbc]
    · rintro ⟨g, rfl⟩
      apply inj (p + 1)
      rw [fe_comm S hS (p + 1), fe_comm S hS (p + 2) g, ConeExtensionAcyclic.bd_bd, Finsupp.mapDomain_zero]
end
