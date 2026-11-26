module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PowMulMem
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K]
  [IsScalarTower ℂ F K] {d : ℕ} {x : Fin (d + 1) → Fˣ}

private lemma ratio_mem (i j : Fin (d + 1)) :
    algebraMap F K ((x j : F) / x i) ∈ rB ℂ K (xv x) {i} := by
  have hm : ((x j : F) / x i) ∈ rA ℂ (xv x) {i} :=
    Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, j, rfl⟩
  rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  exact isIntegral_algebraMap (R := rA ℂ (xv x) {i}) (x := ⟨_, hm⟩)

private lemma pow_mul_mem (h : IsFinCover ℂ K (xv x)) (i i' : Fin (d + 1)) (b : K)
    (hb : b ∈ rB ℂ K (xv x) {i}) :
    ∃ N0 : ℕ, ∀ N, N0 ≤ N → (algebraMap F K ((x i : F) / x i')) ^ N * b ∈ rB ℂ K (xv x) {i'} := by
  by_cases hne : i = i'
  · subst hne
    refine ⟨0, fun N _ => ?_⟩
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (ratio_mem i i) N) hb
  have hb' : b ∈ rB ℂ K (xv x) {i, i'} :=
    (GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K d (xv x) h {i} i (by simp)).1 {i, i'} (by simp) hb
  obtain ⟨N0, hN0⟩ :=
    ((GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K d (xv x) h {i, i'} i' (by simp)).2 b).mp hb'
  rw [Finset.prod_pair hne, div_self (Units.ne_zero (x i')), mul_one] at hN0
  refine ⟨N0, fun N hN => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  have e : algebraMap F K ((x i : F) / x i') ^ (N0 + k) * b =
      algebraMap F K ((x i : F) / x i') ^ k * (b * algebraMap F K ((x i : F) / x i') ^ N0) := by
    ring
  rw [e]
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (ratio_mem i' i) k) hN0

private lemma gens (h : IsFinCover ℂ K (xv x)) (i : Fin (d + 1)) :
    ∃ G : Finset K, Algebra.adjoin ℂ (G : Set K) = rB ℂ K (xv x) {i} := by
  haveI := h.smooth i
  exact (Subalgebra.fg_iff_finiteType _).mpr inferInstance

private lemma tensor_id (a a' a'' b : K) (ha' : a' ≠ 0) (ha'' : a'' ≠ 0) (N : ℕ) :
    (((a ^ N) ⊗ₜ[ℂ] (1 : K)) * ((1 : K) ⊗ₜ[ℂ] (a ^ N))) * (b ⊗ₜ[ℂ] (1 : K) - (1 : K) ⊗ₜ[ℂ] b) =
      ((((a / a') ^ N * b) ⊗ₜ[ℂ] ((a / a'') ^ N)) - (((a / a') ^ N) ⊗ₜ[ℂ] ((a / a'') ^ N * b))) *
        (((a' ^ N) ⊗ₜ[ℂ] (1 : K)) * ((1 : K) ⊗ₜ[ℂ] (a'' ^ N))) := by
  have e1 : (a / a') ^ N * a' ^ N = a ^ N := by rw [← mul_pow, div_mul_cancel₀ a ha']
  have e2 : (a / a'') ^ N * a'' ^ N = a ^ N := by rw [← mul_pow, div_mul_cancel₀ a ha'']
  have e3 : (a / a') ^ N * b * a' ^ N = a ^ N * b := by rw [mul_right_comm, e1]
  have e4 : (a / a'') ^ N * b * a'' ^ N = a ^ N * b := by rw [mul_right_comm, e2]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, sub_mul, mul_sub, mul_one, one_mul, e1, e2, e3, e4]
  done

private lemma coe_XY (i j : Fin (d + 1)) (N : ℕ) :
    (((sysZ K x 0).X i ^ N * (sysZ K x 0).Y j ^ N : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) =
      (((algebraMap F K (x i)) ^ N) ⊗ₜ[ℂ] (1 : K)) * ((1 : K) ⊗ₜ[ℂ] ((algebraMap F K (x j)) ^ N)) := by
  simp [sysZ, Units.val_pow_eq_pow_val, Algebra.TensorProduct.tmul_pow]

end

theorem UpperTheory.Gal.productCup_of_system.zFam_of :
    ZFam := by
  classical
  intro F K _ _ _ _ _ _ d x h
  choose G hG using fun i => gens (x := x) h i
  have hGm : ∀ i, ∀ b ∈ G i, b ∈ rB ℂ K (xv x) {i} := fun i b hb =>
    hG i ▸ Algebra.subset_adjoin hb
  have hP : ∀ i b, b ∈ G i → ∀ i', ∃ N0 : ℕ, ∀ N, N0 ≤ N →
      (algebraMap F K ((x i : F) / x i')) ^ N * b ∈ rB ℂ K (xv x) {i'} :=
    fun i b hb i' => pow_mul_mem h i i' b (hGm i b hb)
  choose! Nb hNb using hP
  let Nq : Fin (d + 1) × K → ℕ := fun q => Finset.univ.sup (fun i' => Nb q.1 q.2 i')
  let P : Finset (Fin (d + 1) × K) :=
    Finset.univ.biUnion (fun i => (G i).image (fun b => (i, b)))
  have hPm : ∀ q ∈ P, q.2 ∈ G q.1 := by
    intro q hq
    simp only [P, Finset.mem_biUnion, Finset.mem_image] at hq
    obtain ⟨i, _, b, hb, rfl⟩ := hq
    exact hb
  let e := P.equivFin.symm
  let zz : Fin (d + 1) × K → K ⊗[ℂ] K := fun q =>
    (((sysZ K x 0).X q.1 ^ Nq q * (sysZ K x 0).Y q.1 ^ Nq q : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) *
      (q.2 ⊗ₜ[ℂ] (1 : K) - (1 : K) ⊗ₜ[ℂ] q.2)
  refine ⟨P.card, fun l => (Nq (e l).1, Nq (e l).1), fun l => zz (e l).1, ⟨?_, ?_, ?_⟩⟩
  · intro i' j' l
    show zz (e l).1 * ↑((sysZ K x 0).X i' ^ Nq (e l).1 * (sysZ K x 0).Y j' ^ Nq (e l).1)⁻¹ ∈ _
    have hb := hPm _ (e l).2
    generalize (e l).1 = q at hb ⊢
    obtain ⟨i, b⟩ := q
    dsimp only [zz] at hb ⊢
    have hN1 : Nb i b i' ≤ Nq (i, b) :=
      Finset.le_sup (f := fun i' => Nb i b i') (Finset.mem_univ i')
    have hN2 : Nb i b j' ≤ Nq (i, b) :=
      Finset.le_sup (f := fun i' => Nb i b i') (Finset.mem_univ j')
    have hA := hNb i b hb i' _ hN1
    have hD := hNb i b hb j' _ hN2
    have hB := Subalgebra.pow_mem _ (ratio_mem (K := K) (x := x) j' i) (Nq (i, b))
    have hC := Subalgebra.pow_mem _ (ratio_mem (K := K) (x := x) i' i) (Nq (i, b))
    rw [coe_XY, tensor_id (algebraMap F K (x i)) (algebraMap F K (x i')) (algebraMap F K (x j')) b
      (by simp) (by simp) _, ← coe_XY i' j' _, Units.mul_inv_cancel_right]
    simp only [map_div₀] at hA hB hC hD
    exact Subalgebra.sub_mem _ ((AlgHom.mem_range _).mpr ⟨⟨_, hA⟩ ⊗ₜ ⟨_, hB⟩, by simp⟩)
      ((AlgHom.mem_range _).mpr ⟨⟨_, hC⟩ ⊗ₜ ⟨_, hD⟩, by simp⟩)
  · intro l
    simp [zz, Algebra.TensorProduct.lmul'_apply_tmul]
  · intro i
    apply le_antisymm
    · exact Algebra.adjoin_le (fun b hb => hb.1)
    · refine (hG i).symm.le.trans (Algebra.adjoin_mono ?_)
      intro b hb
      have hq : (i, b) ∈ P := by
        simp only [P, Finset.mem_biUnion, Finset.mem_image]
        exact ⟨i, Finset.mem_univ _, b, hb, rfl⟩
      refine ⟨hGm i b hb, e.symm ⟨(i, b), hq⟩, Nq (i, b), ?_, ?_⟩ <;> simp [e, zz]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ImgTransInlE
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma uni_empty_eq {α β : Type} [LinearOrder α] [LinearOrder β] (L : Finset α) :
    uni L (∅ : Finset β) = L.map (inlE : α ↪o α ⊕ₗ β).toEmbedding := by
  ext z
  simp only [uni, inlE, Finset.disjSum_empty, Finset.map_map, Finset.mem_map]
  simp

private lemma lft_uni' {α β : Type} [LinearOrder α] [LinearOrder β] (I : Finset α) (J : Finset β) :
    lft (uni I J) = I := by
  ext t
  simp [lft, uni]

private lemma rgt_uni' {α β : Type} [LinearOrder α] [LinearOrder β] (I : Finset α) (J : Finset β) :
    rgt (uni I J) = J := by
  ext t
  simp [rgt, uni]

private lemma img_trans_inlE {d : ℕ} {α β : Type} [LinearOrder α] [LinearOrder β] (e : Fin d ↪o α) :
    img (e.trans (inlE : α ↪o α ⊕ₗ β)) = uni (img e) (∅ : Finset β) := by
  rw [uni_empty_eq]
  ext t
  simp [img]

private lemma img_card {d : ℕ} {α : Type} [LinearOrder α] (e : Fin d ↪o α) : (img e).card = d := by
  simp [img]

theorem UpperTheory.Gal.productCup_of_system.zEx_of :
    ZCol → ColZ → CechKoszulSystemCocycleGluing → KoszulBoundaryOfComponentMemIdeal → KSub → RS → ActsLin → SysOk → GoodZ → ThMuLat → ZEx := by
  intro hZCol hColZ hSysL2 hK2 hKSub hRS hActsLin hSysOk hGoodZ hThMu
  intro F K _ _ _ _ _ _ d x hcov τ htop a ha κ _ _ n z hz
  have hGood : (sysZ K x a).Good := (hGoodZ F K d x hcov a).1
  have hAdm : (sysZ K x a).admitted (app n11 n) (app (sysZ K x a).mu z) := by
    intro i j l
    obtain ⟨l, rfl⟩ : ∃ l', toLex l' = l := ⟨ofLex l, rfl⟩
    cases l with
    | inl m => exact (hThMu d _ _ (sysZ K x a) hGood).1 i j m
    | inr k => exact hz.adm i j k
  have gen : ∀ (T : Sys d (K ⊗[ℂ] K) (DR ℂ K ⊗[ℂ] DR ℂ K)) (i j : Fin (d + 1)),
      (fun l => T.r (app n11 n) (app T.mu z) i j (((dj j).trans (inlE (κ := κ))) l)) =
        fun l => T.r n11 T.mu i j (dj j l) := fun T i j => rfl
  have hOk := hSysOk d _ _ (sysZ K x a) _ (app n11 n) (app (sysZ K x a).mu z) hGood hAdm
  have key : ∀ (I J : Finset (Fin (d + 1))) (i j : Fin (d + 1)), i ∈ I → j ∈ J →
      ∀ D ∈ ((sysZ K x a).colCx (app n11 n) (app (sysZ K x a).mu z) I J).Z d,
      Acts (F := F) K τ a (D (uni (img (dj j)) ∅)) 0 →
      D ∈ ((sysZ K x a).colCx (app n11 n) (app (sysZ K x a).mu z) I J).B d := by
    intro I J i j hi hj D hD hA
    have hI : I.Nonempty := ⟨i, hi⟩
    have hJ : J.Nonempty := ⟨j, hj⟩
    obtain ⟨hr, hcol⟩ := hOk.2.1 I J i hi j hj
    rw [hcol] at hD ⊢
    have hR := hRS _ _ (sysZ K x a).act _ ((sysZ K x a).M I J) ((sysZ K x a).u (app n11 n) i j)
      ((sysZ K x a).r (app n11 n) (app (sysZ K x a).mu z) i j) (app (sysZ K x a).mu z) (fun l => rfl) d D
    rw [hR.2.2.1]
    rw [hR.2.1] at hD
    have hCZ := hColZ F K d x hcov τ htop a ha I J i hi j hj
    refine hK2 _ _ (sysZ K x a).act _ ((sysZ K x a).R I J) ((sysZ K x a).M I J) _ d ((dj j).trans inlE)
      (hGood.stab I J hI hJ) hr (by rw [gen]; exact hCZ.1) _ hD ?_
    rw [img_trans_inlE, gen]
    refine hCZ.2 _ ?_ ?_
    · have hC := (Submodule.mem_inf.1 hD).1
      simp only [kos, acx] at hC
      have h1 := (Submodule.mem_pi.1 hC) (uni (img (dj j)) ∅) (Set.mem_univ _)
      have hcard : (uni (img (dj j)) (∅ : Finset κ)).card = d := by
        rw [← img_trans_inlE, img_card]
      rw [hcard, if_pos rfl] at h1
      exact h1
    · have h2 := fun s => (hActsLin F K d x hcov τ htop a).2.1 _ 0 s hA
      simp only [mul_zero] at h2
      exact h2 _
  have hKE : ∀ I J : Finset (Fin (d + 1)), I.Nonempty → J.Nonempty →
      KE ((sysZ K x a).colCx (app n11 n) (app (sysZ K x a).mu z) I J) d := by
    intro I J hI hJ
    obtain ⟨i, hi⟩ := hI
    obtain ⟨j, hj⟩ := hJ
    obtain ⟨hr, hcol⟩ := hOk.2.1 I J i hi j hj
    rw [hcol]
    have hks := (hKSub _ _ (sysZ K x a).act _ ((sysZ K x a).R I J) ((sysZ K x a).M I J)
      ((sysZ K x a).r (app n11 n) (app (sysZ K x a).mu z) i j) (hGood.stab I J ⟨i, hi⟩ ⟨j, hj⟩) hr).1 d
      ((dj j).trans inlE) (by rw [gen]; exact (hColZ F K d x hcov τ htop a ha I J i hi j hj).1)
    intro m hm c hc
    have hR := hRS _ _ (sysZ K x a).act _ ((sysZ K x a).M I J) ((sysZ K x a).u (app n11 n) i j)
      ((sysZ K x a).r (app n11 n) (app (sysZ K x a).mu z) i j) (app (sysZ K x a).mu z) (fun l => rfl) m c
    rw [hR.2.2.1]
    exact hks m hm (hR.2.1.1 hc)
  have hc0 := fun i j => hZCol F K d x hcov τ htop a ha κ n z hz i j
  choose c0 hc0Z hc0A using hc0
  have hAct := (hActsLin F K d x hcov τ htop a).1
  obtain ⟨c, hcZ, hcol⟩ := hSysL2 d _ _ (sysZ K x a) _ (app n11 n) (app (sysZ K x a).mu z) hGood hAdm hKE c0 hc0Z
    (fun i i' j => by
      apply key {i, i'} {j} i j (by simp) (by simp)
      · exact Submodule.sub_mem _
          (hOk.2.2 {i} {i, i'} {j} {j} (by simp) (by simp) (by simp) le_rfl d (hc0Z i j))
          (hOk.2.2 {i'} {i, i'} {j} {j} (by simp) (by simp) (by simp) le_rfl d (hc0Z i' j))
      · have h3 := (hAct _ _ _ _ (hc0A i j _ (img_card (dj j))) (hc0A i' j _ (img_card (dj j)))).2
        rw [sub_self] at h3
        exact h3)
    (fun i j j' => by
      apply key {i} {j, j'} i j (by simp) (by simp)
      · exact Submodule.sub_mem _
          (hOk.2.2 {i} {i} {j} {j, j'} (by simp) (by simp) le_rfl (by simp) d (hc0Z i j))
          (hOk.2.2 {i} {i} {j'} {j, j'} (by simp) (by simp) le_rfl (by simp) d (hc0Z i j'))
      · have h3 := (hAct _ _ _ _ (hc0A i j _ (img_card (dj j))) (hc0A i j' _ (img_card (dj j)))).2
        rw [sub_self] at h3
        exact h3)
  refine ⟨c, hcZ, ?_⟩
  intro i j L hLc
  have e : resK inlE c (uni (uni {i} {j}) L) = c0 i j (uni L ∅) := by
    rw [← hcol i j]
    simp only [resK, col, lft_uni', rgt_uni', uni_empty_eq]
  rw [e]
  exact hc0A i j L hLc
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PRegLat
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

section
variable {F V V' : Type} [Field F] [Algebra ℂ F] [AddCommGroup V] [Module F V] [Module ℂ V]
  [IsScalarTower ℂ F V] [AddCommGroup V'] [Module F V'] [Module ℂ V'] [IsScalarTower ℂ F V']

private lemma actF_tmul (a b : F) (v : V) (v' : V') :
    actF F V V' (a ⊗ₜ b) (v ⊗ₜ v') = (a • v) ⊗ₜ (b • v') := by
  simp [actF, Module.endTensorEndAlgHom_apply]

private noncomputable def Ph (ψ : V →ₗ[F] F) (ψ' : V' →ₗ[F] F) : V ⊗[ℂ] V' →ₗ[ℂ] F ⊗[ℂ] F :=
  TensorProduct.map (ψ.restrictScalars ℂ) (ψ'.restrictScalars ℂ)

private lemma Ph_tmul (ψ : V →ₗ[F] F) (ψ' : V' →ₗ[F] F) (a : V) (b : V') :
    Ph ψ ψ' (a ⊗ₜ b) = ψ a ⊗ₜ ψ' b := rfl

private lemma Ph_act (ψ : V →ₗ[F] F) (ψ' : V' →ₗ[F] F) (s : F ⊗[ℂ] F) (t : V ⊗[ℂ] V') :
    Ph ψ ψ' (actF F V V' s t) = s * Ph ψ ψ' t := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, add_mul, ha, hb]
  | tmul a b =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add c e hc he => simp only [map_add (f := _), mul_add, hc, he]
    | tmul c e => simp [actF_tmul, Ph_tmul]

private lemma Ph_lmul (ψ : V →ₗ[F] F) (ψ' : V' →ₗ[F] F) (t : V ⊗[ℂ] V') :
    Algebra.TensorProduct.lmul' ℂ (Ph ψ ψ' t) = ψ' (ctrF V' ψ t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add c e hc he => simp only [map_add (f := _), hc, he]
  | tmul c e => simp [Ph_tmul, ctrF]

variable {A A' : Subalgebra ℂ F} {M : Submodule ℂ V} {M' : Submodule ℂ V'}

private lemma Ph_mem {ψ : V →ₗ[F] F} {ψ' : V' →ₗ[F] F} (h : ∀ m ∈ M, ψ m ∈ A) (h' : ∀ m ∈ M', ψ' m ∈ A')
    {t : V ⊗[ℂ] V'} (ht : t ∈ Submodule.map₂ (TensorProduct.mk ℂ _ _) M M') :
    Ph ψ ψ' t ∈ (Algebra.TensorProduct.map A.val A'.val).range := by
  have key : Submodule.map₂ (TensorProduct.mk ℂ V V') M M' ≤
      (Subalgebra.toSubmodule (Algebra.TensorProduct.map A.val A'.val).range).comap (Ph ψ ψ') := by
    refine Submodule.map₂_le.2 fun m hm m' hm' => ?_
    exact ⟨(⟨ψ m, h m hm⟩ : A) ⊗ₜ (⟨ψ' m', h' m' hm'⟩ : A'), by simp [Ph_tmul]⟩
  exact key ht

private lemma act_mem (hA : ∀ a ∈ A, ∀ m ∈ M, a • m ∈ M) (hA' : ∀ a ∈ A', ∀ m ∈ M', a • m ∈ M')
    {v : V} {v' : V'} (hv : v ∈ M) (hv' : v' ∈ M') {s : F ⊗[ℂ] F}
    (hs : s ∈ (Algebra.TensorProduct.map A.val A'.val).range) :
    actF F V V' s (v ⊗ₜ v') ∈ Submodule.map₂ (TensorProduct.mk ℂ _ _) M M' := by
  obtain ⟨r, rfl⟩ := hs
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul a a' =>
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      Subalgebra.coe_val, actF_tmul]
    exact Submodule.apply_mem_map₂ _ (hA _ a.2 _ hv) (hA' _ a'.2 _ hv')
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply]
    exact add_mem hx hy

private lemma decomp {n n' : ℕ} {v : Fin n → V} {φ : Fin n → V →ₗ[F] F} {v' : Fin n' → V'}
    {φ' : Fin n' → V' →ₗ[F] F} (h : ∀ m ∈ M, m = ∑ k, φ k m • v k) (h' : ∀ m ∈ M', m = ∑ k, φ' k m • v' k)
    {t : V ⊗[ℂ] V'} (ht : t ∈ Submodule.map₂ (TensorProduct.mk ℂ _ _) M M') :
    t = ∑ k, ∑ l, actF F V V' (Ph (φ k) (φ' l) t) (v k ⊗ₜ v' l) := by
  rw [Submodule.map₂_eq_span_image2] at ht
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨a, ha, b, hb, rfl⟩ := ht
    simp only [TensorProduct.mk_apply, Ph_tmul, actF_tmul]
    conv_lhs => rw [h a ha, h' b hb]
    simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum]
    rw [Finset.sum_comm]
  | zero => simp
  | add a b _ _ ha hb =>
    conv_lhs => rw [ha, hb]
    simp only [map_add (f := _), LinearMap.add_apply, Finset.sum_add_distrib]
  | smul c a _ ha =>
    conv_lhs => rw [ha]
    simp only [map_smul, LinearMap.smul_apply, Finset.smul_sum]

private lemma Ph_sm {ψ : V →ₗ[F] F} {ψ' : V' →ₗ[F] F} (h : ∀ m ∈ M, ψ m ∈ A) (h' : ∀ m ∈ M', ψ' m ∈ A')
    {T : Set (F ⊗[ℂ] F)} {t : V ⊗[ℂ] V'}
    (ht : t ∈ sm (actF F V V') (Submodule.map₂ (TensorProduct.mk ℂ _ _) M M') T) :
    Ph ψ ψ' t ∈ sm (Algebra.lmul ℂ (F ⊗[ℂ] F))
      (Subalgebra.toSubmodule (Algebra.TensorProduct.map A.val A'.val).range) T := by
  have hle : sm (actF F V V') (Submodule.map₂ (TensorProduct.mk ℂ V V') M M') T ≤
      (sm (Algebra.lmul ℂ (F ⊗[ℂ] F))
        (Subalgebra.toSubmodule (Algebra.TensorProduct.map A.val A'.val).range) T).comap (Ph ψ ψ') := by
    unfold sm
    refine iSup₂_le fun r hr => ?_
    rintro _ ⟨u, hu, rfl⟩
    rw [Submodule.mem_comap, Ph_act]
    exact Submodule.mem_iSup_of_mem r (Submodule.mem_iSup_of_mem hr ⟨_, Ph_mem h h' hu, by simp⟩)
  exact hle ht

private lemma act_sm (hA : ∀ a ∈ A, ∀ m ∈ M, a • m ∈ M) (hA' : ∀ a ∈ A', ∀ m ∈ M', a • m ∈ M')
    {v : V} {v' : V'} (hv : v ∈ M) (hv' : v' ∈ M') {T : Set (F ⊗[ℂ] F)} {s : F ⊗[ℂ] F}
    (hs : s ∈ sm (Algebra.lmul ℂ (F ⊗[ℂ] F))
      (Subalgebra.toSubmodule (Algebra.TensorProduct.map A.val A'.val).range) T) :
    actF F V V' s (v ⊗ₜ v') ∈ sm (actF F V V') (Submodule.map₂ (TensorProduct.mk ℂ _ _) M M') T := by
  let L : (F ⊗[ℂ] F) →ₗ[ℂ] V ⊗[ℂ] V' :=
    (LinearMap.applyₗ (v ⊗ₜ v')) ∘ₗ (actF F V V').toLinearMap
  have hle : sm (Algebra.lmul ℂ (F ⊗[ℂ] F))
      (Subalgebra.toSubmodule (Algebra.TensorProduct.map A.val A'.val).range) T ≤
      (sm (actF F V V') (Submodule.map₂ (TensorProduct.mk ℂ V V') M M') T).comap L := by
    unfold sm
    refine iSup₂_le fun r hr => ?_
    rintro _ ⟨u, hu, rfl⟩
    rw [Submodule.mem_comap]
    refine Submodule.mem_iSup_of_mem r (Submodule.mem_iSup_of_mem hr
      ⟨actF F V V' u (v ⊗ₜ v'), act_mem hA hA' hv hv' hu, ?_⟩)
    simp [L, Module.End.mul_apply]
  exact hle hs

end

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.regLat_of :
    Reg0 → Ker0 → RegLat := by
  intro h0 hK F _ _ d x hx V V' _ _ _ _ _ _ _ _ I J M M' hL hL' j hjI hjJ
  obtain ⟨hA, n, v, φ, hv, hφ, hdec⟩ := hL
  obtain ⟨hA', n', v', φ', hv', hφ', hdec'⟩ := hL'
  have back : ∀ (T : Set (F ⊗[ℂ] F)) (t : V ⊗[ℂ] V'), t ∈ Submodule.map₂ (TensorProduct.mk ℂ _ _) M M' →
      (∀ k l, Ph (φ k) (φ' l) t ∈ sm (Algebra.lmul ℂ (F ⊗[ℂ] F)) (Subalgebra.toSubmodule (R0 x I J)) T) →
      t ∈ sm (actF F V V') (Submodule.map₂ (TensorProduct.mk ℂ _ _) M M') T := by
    intro T t ht h
    rw [decomp hdec hdec' ht]
    exact Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun l _ =>
      act_sm hA hA' (hv k) (hv' l) (h k l)
  refine ⟨?_, ?_⟩
  · intro k m hm hk
    refine back _ m hm fun a b => ?_
    refine h0 F d x hx I J j hjI hjJ k _ (Ph_mem (hφ a) (hφ' b) hm) ?_
    have := Ph_sm (ψ := φ a) (ψ' := φ' b) (fun m hm => hφ a m hm) (fun m hm => hφ' b m hm) hk
    rw [Ph_act] at this
    exact this
  · intro m hm hψ
    refine back _ m hm fun a b => ?_
    refine hK F d x hx I J j hjI hjJ _ (Ph_mem (hφ a) (hφ' b) hm) ?_
    rw [Ph_lmul, hψ, map_zero]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PActsLin
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

section
variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K]

private lemma muP_tmul (τ : DR ℂ K →ₗ[K] K) (w' w'' w : DR ℂ K) :
    muP F K τ (w' ⊗ₜ w'') w = (Algebra.trace F K (τ (w' * w))) ⊗ₜ[ℂ] w'' := by
  simp [muP]

private lemma mulP_tmul (f : F) (w : DR ℂ K) : mulP F K (f ⊗ₜ w) = algebraMap F K f • w := by
  simp [mulP]

private lemma actZ_tmul (a b : K) (w' w'' : DR ℂ K) :
    actZ K (a ⊗ₜ b) (w' ⊗ₜ w'') = (a • w') ⊗ₜ[ℂ] (b • w'') := by
  simp [actZ]
  rfl

private lemma key1 (τ : DR ℂ K →ₗ[K] K) (a b : K) (m : DR ℂ K ⊗[ℂ] DR ℂ K) (w : DR ℂ K) :
    mulP F K (muP F K τ (actZ K (a ⊗ₜ b) m) w) = b • mulP F K (muP F K τ m (a • w)) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul w' w'' =>
    rw [actZ_tmul, muP_tmul, muP_tmul, mulP_tmul, mulP_tmul, smul_mul_assoc, mul_smul_comm]
    exact smul_comm _ _ _
  | add x y hx hy => simp only [map_add (f := _), LinearMap.add_apply, hx, hy, smul_add]

private lemma key2 (τ : DR ℂ K →ₗ[K] K) (f : F) (m : DR ℂ K ⊗[ℂ] DR ℂ K) (w : DR ℂ K) :
    mulP F K (muP F K τ m (algebraMap F K f • w)) = algebraMap F K f • mulP F K (muP F K τ m w) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul w' w'' =>
    rw [muP_tmul, muP_tmul, mulP_tmul, mulP_tmul, mul_smul_comm, map_smul, smul_eq_mul, ← Algebra.smul_def,
      map_smul, smul_eq_mul, map_mul, mul_smul]
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hp, hq]

private lemma key3 (τ : DR ℂ K →ₗ[K] K) (f g : F) (m : DR ℂ K ⊗[ℂ] DR ℂ K) (w : DR ℂ K) :
    mulP F K (muP F K τ (actZ K (algebraMap F K f ⊗ₜ algebraMap F K g) m) w) =
      algebraMap F K (f * g) • mulP F K (muP F K τ m w) := by
  rw [key1, key2, ← mul_smul, ← map_mul, mul_comm g f]

private lemma sysP_act_tmul {d : ℕ} (x : Fin (d + 1) → Fˣ) (a : ℕ) (f f' : F) (k : K) (w : DR ℂ K) :
    (sysP K x a).act (f ⊗ₜ k) (f' ⊗ₜ w) = (f * f') ⊗ₜ[ℂ] (k • w) := by
  simp [sysP]
  rfl

private lemma r_eq {d : ℕ} (x : Fin (d + 1) → Fˣ) (a : ℕ) (i j : Fin (d + 1)) (l : Mi d) :
    (sysZ K x a).r n11 (sysZ K x a).mu i j l =
      algebraMap F K (x (ofLex l).1 / x i : Fˣ) ⊗ₜ algebraMap F K (x (ofLex l).2 / x j : Fˣ) -
      algebraMap F K (x (ofLex l).2 / x i : Fˣ) ⊗ₜ algebraMap F K (x (ofLex l).1 / x j : Fˣ) := by
  simp [Sys.r, Sys.mu, Sys.u, n11, sysZ, sub_mul, div_eq_mul_inv]

end

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.actsLin_of :
    ActsLin := by
  intro F K _ _ _ _ _ _ d x _ τ _ a
  have hadd : ∀ (m m' : DR ℂ K ⊗[ℂ] DR ℂ K) (c c' : K),
      Acts (F := F) K τ a m c → Acts (F := F) K τ a m' c' →
        Acts (F := F) K τ a (m + m') (c + c') ∧ Acts (F := F) K τ a (m - m') (c - c') := by
    intro m m' c c' hm hm'
    unfold Acts at hm hm' ⊢
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · rw [map_add (f := _), LinearMap.add_apply, map_add (f := _), hm w hw, hm' w hw, add_smul]
    · rw [map_sub, LinearMap.sub_apply, map_sub, hm w hw, hm' w hw, sub_smul]
  have hr : ∀ (i j : Fin (d + 1)) (l : Mi d) (m : DR ℂ K ⊗[ℂ] DR ℂ K),
      Acts (F := F) K τ a (actZ K ((sysZ K x a).r n11 (sysZ K x a).mu i j l) m) 0 := by
    intro i j l m
    unfold Acts
    intro w _
    rw [r_eq, map_sub, LinearMap.sub_apply, map_sub, LinearMap.sub_apply, map_sub, key3, key3,
      ← Units.val_mul, ← Units.val_mul, div_mul_div_comm, div_mul_div_comm,
      mul_comm (x (ofLex l).1) (x (ofLex l).2), sub_self, zero_smul]
  have hsm : ∀ (i j : Fin (d + 1)) (M : Submodule ℂ (DR ℂ K ⊗[ℂ] DR ℂ K)),
      ∀ m ∈ sm (actZ K) M (Set.range ((sysZ K x a).r n11 (sysZ K x a).mu i j)),
        Acts (F := F) K τ a m 0 := by
    intro i j M m hm
    let N : Submodule ℂ (DR ℂ K ⊗[ℂ] DR ℂ K) :=
      { carrier := {m | Acts (F := F) K τ a m 0}
        add_mem' := fun {m m'} hm hm' => by simpa using (hadd m m' 0 0 hm hm').1
        zero_mem' := by
          simp only [Set.mem_setOf_eq, Acts]
          intro w _
          simp
        smul_mem' := fun c m hm => by
          simp only [Set.mem_setOf_eq, Acts] at hm ⊢
          intro w hw
          rw [map_smul, LinearMap.smul_apply, map_smul, hm w hw]
          simp }
    have hle : sm (actZ K) M (Set.range ((sysZ K x a).r n11 (sysZ K x a).mu i j)) ≤ N := by
      unfold sm
      refine iSup₂_le fun s hs => ?_
      rintro _ ⟨u, _, rfl⟩
      obtain ⟨l, rfl⟩ := hs
      exact hr i j l u
    exact hle hm
  refine ⟨hadd, ?_, hsm, ?_, ?_, ?_⟩
  · intro m c s hm
    induction s using TensorProduct.induction_on with
    | zero =>
      unfold Acts
      intro w _
      simp
    | tmul p q =>
      unfold Acts at hm ⊢
      intro w hw
      rw [key1, hm _ (Submodule.smul_mem _ p hw)]
      simp only [Algebra.TensorProduct.lmul'_apply_tmul, smul_smul]
      congr 1
      ring
    | add s s' hs hs' =>
      simpa only [map_add (f := _), LinearMap.add_apply, add_mul] using (hadd _ _ _ _ hs hs').1
  · intro u M m i j hm
    apply hsm i j (M.map (actZ K u))
    have hle : sm (actZ K) M (Set.range ((sysZ K x a).r n11 (sysZ K x a).mu i j)) ≤
        (sm (actZ K) (M.map (actZ K u))
          (Set.range ((sysZ K x a).r n11 (sysZ K x a).mu i j))).comap (actZ K u) := by
      unfold sm
      refine iSup₂_le fun s hs => ?_
      rintro _ ⟨v, hv, rfl⟩
      rw [Submodule.mem_comap]
      refine Submodule.mem_iSup_of_mem s (Submodule.mem_iSup_of_mem hs ⟨actZ K u v, ⟨v, hv, rfl⟩, ?_⟩)
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
    exact hle hm
  · intro s m
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul f k =>
      induction m using TensorProduct.induction_on with
      | zero => simp
      | tmul f' w =>
        rw [sysP_act_tmul, mulP_tmul, mulP_tmul]
        simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]
        rw [← algebraMap_smul K f' w, smul_smul]
        congr 1
        ring
      | add y z hy hz => simp only [map_add (f := _), smul_add, hy, hz]
    | add y z hy hz => simp only [map_add (f := _), LinearMap.add_apply, add_smul, hy, hz]
  · intro s m w
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul f k =>
      induction m using TensorProduct.induction_on with
      | zero => simp
      | tmul w' w'' =>
        rw [Algebra.TensorProduct.map_tmul, actZ_tmul, muP_tmul, muP_tmul, sysP_act_tmul]
        simp only [IsScalarTower.coe_toAlgHom', AlgHom.coe_id, id_eq, smul_mul_assoc, map_smul,
          smul_eq_mul]
        rw [← Algebra.smul_def, map_smul, smul_eq_mul]
      | add y z hy hz => simp only [map_add (f := _), LinearMap.add_apply, hy, hz]
    | add y z hy hz => simp only [map_add (f := _), LinearMap.add_apply, hy, hz]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PDualForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceWedgePairingPerfectRationalForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceWedgePairingPerfectRationalForms
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.PD

theorem wedge_pairing_sep {K V : Type} [Field K] [AddCommGroup V] [Module K V] {p q : ℕ}
    (b : Module.Basis (Fin (p + q)) K V) (τ : ExteriorAlgebra K V →ₗ[K] K)
    (hτ : τ (ExteriorAlgebra.ιMulti K (p + q) b) ≠ 0) (y : ExteriorAlgebra K V) (hy : y ∈ ⋀[K]^q V)
    (h : ∀ a ∈ ⋀[K]^p V, τ (a * y) = 0) : y = 0 := by
  classical
  have hdet : ∀ v : Fin (p + q) → V,
      τ (ExteriorAlgebra.ιMulti K (p + q) v) = τ (ExteriorAlgebra.ιMulti K (p + q) b) * b.det v := by
    intro v
    have e := congrArg (fun f => f v)
      (AlternatingMap.eq_smul_basis_det b (τ.compAlternatingMap (ExteriorAlgebra.ιMulti K (p + q))))
    simpa [mul_comm] using e
  have htop : ∀ U : Set.powersetCard (Fin (p + q)) (p + q),
      τ (ExteriorAlgebra.ιMulti_family K (p + q) b U) ≠ 0 := by
    intro U
    set e := Set.powersetCard.ofFinEmbEquiv.symm U
    have hinj : Function.Injective e := e.injective
    have hbij : Function.Bijective e := ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
    let σ := Equiv.ofBijective e hbij
    have hb : (b ∘ e) = ⇑(b.reindex σ.symm) := by
      funext i; simp [σ]
    rw [ExteriorAlgebra.ιMulti_family, hdet, hb]
    exact mul_ne_zero hτ (b.isUnit_det _).ne_zero
  have hcoe : ∀ {n : ℕ} (I : Set.powersetCard (Fin (p + q)) n),
      ((Module.Basis.exteriorPower n b I : ⋀[K]^n V) : ExteriorAlgebra K V) =
        ExteriorAlgebra.ιMulti_family K n b I := by
    intro n I
    simp [exteriorPower.basis_apply, exteriorPower.ιMulti_family, ExteriorAlgebra.ιMulti_family]
  set B := Module.Basis.exteriorPower q b
  set Y : ⋀[K]^q V := ⟨y, hy⟩
  suffices hY : B.repr Y = 0 by
    have : Y = 0 := B.repr.injective (by rw [hY, map_zero])
    exact congrArg Subtype.val this
  ext J
  have hJc : (J.valᶜ : Finset (Fin (p + q))).card = p := by
    rw [Finset.card_compl, Fintype.card_fin, show (J.val).card = q from J.prop]; omega
  let Jc : Set.powersetCard (Fin (p + q)) p := ⟨J.valᶜ, by simpa using hJc⟩
  have hdisj : Disjoint Jc.val J.val := disjoint_compl_left
  set a : ExteriorAlgebra K V := ExteriorAlgebra.ιMulti_family K p b Jc
  have ha : a ∈ ⋀[K]^p V := by
    rw [show a = _ from (hcoe Jc).symm]; exact (Module.Basis.exteriorPower p b Jc).2
  have hy' : y = ∑ I, B.repr Y I • (ExteriorAlgebra.ιMulti_family K q b I) := by
    have := congrArg Subtype.val (B.sum_repr Y)
    change (Y : ExteriorAlgebra K V) = _
    rw [← this, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Submodule.coe_smul, hcoe]
  have key := h a ha
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hy', Finset.mul_sum, map_sum, Finset.sum_eq_single J] at key
  · rw [mul_smul_comm, map_smul, ExteriorAlgebra.ιMulti_family_mul_of_disjoint _ _ _ _ hdisj,
      Units.smul_def, map_zsmul, smul_eq_mul] at key
    rcases mul_eq_zero.1 key with h0 | h0
    · simpa using h0
    · exfalso
      rcases Int.units_eq_one_or (Set.powersetCard.permOfDisjoint hdisj).sign with hs | hs <;>
        rw [hs] at h0 <;> simp at h0 <;> exact htop _ h0
  · intro I _ hI
    rw [mul_smul_comm, ExteriorAlgebra.ιMulti_family_mul_of_not_disjoint, smul_zero, map_zero]
    intro hd
    apply hI
    have hsub : I.val ⊆ J.val := by
      intro i hi
      by_contra hj
      exact Finset.disjoint_left.1 hd (show i ∈ J.valᶜ from Finset.mem_compl.2 hj) hi
    have hle : J.val.card ≤ I.val.card := by
      rw [show (I.val).card = q from I.prop, show (J.val).card = q from J.prop]
    exact Subtype.ext (Finset.eq_of_subset_of_card_le hsub hle)
  · intro hJ; exact absurd (Finset.mem_univ J) hJ

end GlobalTheory.PD

namespace GlobalTheory.PD

theorem IsFinCover.trace_wedge_perfect : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ p q : ℕ, p + q = d → (∀ y ∈ ⋀[K]^q Ω[K⁄k], (∀ a ∈ ⋀[K]^p Ω[K⁄k], Algebra.trace F K (τ (a * y)) = 0) → y = 0) ∧ Module.finrank K (⋀[K]^p Ω[K⁄k]) = Module.finrank K (⋀[K]^q Ω[K⁄k]) ∧ FiniteDimensional K (⋀[K]^p Ω[K⁄k]) := by
  intro k _ _ F K _ _ _ _ _ _ d x h τ hτ p q hpq
  haveI := h.fin
  haveI := h.sep
  obtain ⟨b, hb⟩ := h.exists_basis
  haveI : Module.Finite K Ω[K⁄k] := Module.Finite.of_basis b
  haveI : Module.Free K Ω[K⁄k] := Module.Free.of_basis b
  have hfr : Module.finrank K Ω[K⁄k] = d := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  refine ⟨fun y hy hy0 => ?_, ?_, inferInstance⟩
  · have hτb : τ (ExteriorAlgebra.ιMulti K d b) ≠ 0 := by
      intro h0
      have hv : vol0 k K x =
          (∏ j : Fin d, (algebraMap F K (x j.succ / x 0))⁻¹) • ExteriorAlgebra.ιMulti K d b := by
        rw [← AlternatingMap.map_smul_univ]
        simp only [vol0, hb]
      have h1 := hτ.1
      rw [hv, map_smul, h0, smul_zero] at h1
      exact zero_ne_one h1
    have h2 : ∀ a ∈ ⋀[K]^p Ω[K⁄k], τ (a * y) = 0 := by
      intro a ha
      refine (traceForm_nondegenerate F K).1 _ fun c => ?_
      rw [Algebra.traceForm_apply, mul_comm, ← smul_eq_mul, ← map_smul, ← smul_mul_assoc]
      exact hy0 _ (Submodule.smul_mem _ c ha)
    subst hpq
    exact wedge_pairing_sep b τ hτb y hy h2
  · rw [exteriorPower.finrank_eq, exteriorPower.finrank_eq, hfr]
    exact Nat.choose_symm_of_eq_add hpq.symm

end GlobalTheory.PD
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceWedgePairingPerfectRationalFormsStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_wedge_pairing_perfect_rational_forms : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ p q : ℕ, p + q = d → (∀ y ∈ ⋀[K]^q Ω[K⁄k], (∀ a ∈ ⋀[K]^p Ω[K⁄k], Algebra.trace F K (τ (a * y)) = 0) → y = 0) ∧ Module.finrank K (⋀[K]^p Ω[K⁄k]) = Module.finrank K (⋀[K]^q Ω[K⁄k]) ∧ FiniteDimensional K (⋀[K]^p Ω[K⁄k]) := by
  first | (exact @GlobalTheory.PD.IsFinCover.trace_wedge_perfect) | (exact GlobalTheory.PD.IsFinCover.trace_wedge_perfect) | (intros; apply GlobalTheory.PD.IsFinCover.trace_wedge_perfect <;> assumption)
end
end

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma perfectPairing_surjective {F Q P : Type*} [Field F] [AddCommGroup Q] [Module F Q] [AddCommGroup P] [Module F P]
    [FiniteDimensional F Q] [FiniteDimensional F P] (hr : Module.finrank F Q = Module.finrank F P)
    (B : Q →ₗ[F] P →ₗ[F] F) (hB : ∀ w, (∀ y, B w y = 0) → w = 0) :
    Function.Surjective B ∧ Function.Surjective B.flip := by
  have hinj : Function.Injective B :=
    (injective_iff_map_eq_zero B).2 fun w hw => hB w fun y => by simp [hw]
  have hs : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [show Module.finrank F (P →ₗ[F] F) = Module.finrank F P from Subspace.dual_finrank_eq, hr])).1 hinj
  refine ⟨hs, ?_⟩
  have hinj' : Function.Injective B.flip := by
    refine (injective_iff_map_eq_zero B.flip).2 fun y hy => ?_
    refine (Module.forall_dual_apply_eq_zero_iff F y).1 fun f => ?_
    obtain ⟨w, rfl⟩ := hs f
    exact LinearMap.congr_fun hy w
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [show Module.finrank F (Q →ₗ[F] F) = Module.finrank F Q from Subspace.dual_finrank_eq, hr])).1 hinj'

theorem UpperTheory.Gal.productCup_of_system.dualForm_of :
    DualForm := by
  intro F K _ _ _ _ _ _ d x hc τ ht a ha ψ
  obtain ⟨hinj, hrk, hfdP⟩ := GlobalTheory.T.trace_wedge_pairing_perfect_rational_forms ℂ F K d (xv x) hc τ ht (d - a) a (by omega)
  obtain ⟨-, -, hfdQ⟩ := GlobalTheory.T.trace_wedge_pairing_perfect_rational_forms ℂ F K d (xv x) hc τ ht a (d - a) (by omega)
  haveI : FiniteDimensional F K := hc.fin
  haveI : FiniteDimensional F (⋀[K]^(d - a) Ω[K⁄ℂ]) := Module.Finite.trans K _
  haveI : FiniteDimensional F (⋀[K]^a Ω[K⁄ℂ]) := Module.Finite.trans K _
  let T : DR ℂ K →ₗ[F] F := (Algebra.trace F K) ∘ₗ (τ.restrictScalars F)
  let B : (⋀[K]^a Ω[K⁄ℂ]) →ₗ[F] (⋀[K]^(d - a) Ω[K⁄ℂ]) →ₗ[F] F :=
    LinearMap.mk₂ F (fun w y => T ((y : DR ℂ K) * (w : DR ℂ K)))
      (fun w w' y => by simp [mul_add])
      (fun c w y => by simp [mul_smul_comm])
      (fun w y y' => by simp [add_mul])
      (fun c w y => by simp [smul_mul_assoc])
  have hr : Module.finrank F (⋀[K]^a Ω[K⁄ℂ]) = Module.finrank F (⋀[K]^(d - a) Ω[K⁄ℂ]) := by
    rw [← Module.finrank_mul_finrank F K (⋀[K]^a Ω[K⁄ℂ]),
      ← Module.finrank_mul_finrank F K (⋀[K]^(d - a) Ω[K⁄ℂ]), hrk]
  obtain ⟨hs, hs'⟩ := perfectPairing_surjective hr B (fun w hw => Subtype.ext (hinj w.1 w.2 fun y hy => hw ⟨y, hy⟩))
  constructor
  · obtain ⟨w, hw⟩ := hs (ψ ∘ₗ (Submodule.subtype _).restrictScalars F)
    exact ⟨w.1, w.2, fun y hy => (LinearMap.congr_fun hw ⟨y, hy⟩).symm⟩
  · obtain ⟨w, hw⟩ := hs' (ψ ∘ₗ (Submodule.subtype _).restrictScalars F)
    exact ⟨w.1, w.2, fun y hy => (LinearMap.congr_fun hw ⟨y, hy⟩).symm⟩
end
