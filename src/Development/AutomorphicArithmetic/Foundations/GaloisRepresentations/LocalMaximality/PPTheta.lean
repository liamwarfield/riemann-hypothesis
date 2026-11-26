module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PPTheta
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma pk_mem {d : ℕ} {I : Finset (Fin (d + 1))} (h : I.Nonempty) : pk I ∈ I := by
  unfold pk
  rw [dite_eq_left h]
  exact Finset.min'_mem _ _

private lemma lat_mem (hA : LatA) {F : Type} [Field F] [Algebra ℂ F] {d : ℕ} (x : Fin (d + 1) → Fˣ)
    (hpd : IsPd ℂ (xv x)) (I : Finset (Fin (d + 1))) (i : Fin (d + 1)) (hi : i ∈ I) :
    (∏ m ∈ Iᶜ, ((x m : F) / x i)) ∈ omA ℂ (xv x) I := by
  rw [(hA F d x hpd I i hi).2.1]
  have hne : (∏ m ∈ Iᶜ, ((x m : F) / x i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun m _ => div_ne_zero (x m).ne_zero (x i).ne_zero
  have e : (∏ m ∈ Iᶜ, ((x m : F) / x i)) / omG x i = ∏ m ∈ I, ((x i : F) / x m) := by
    unfold omG
    rw [← Finset.prod_mul_prod_compl I (fun l => (x l : F) / x i), div_mul_cancel_right₀ hne,
      ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun m _ => inv_div _ _
  rw [e]
  exact Subalgebra.prod_mem _ fun m hm => Algebra.subset_adjoin ⟨m, hm, i, rfl⟩

private lemma prod_split {F : Type} [Field F] {d : ℕ} (x : Fin (d + 1) → Fˣ) (I : Finset (Fin (d + 1)))
    (i : Fin (d + 1)) : ∏ m ∈ Iᶜ, (x m : F) = (∏ m ∈ Iᶜ, ((x m : F) / x i)) * (x i : F) ^ Iᶜ.card := by
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun m _ => (div_mul_cancel₀ _ (x i).ne_zero).symm

section
variable {F : Type} (K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K]
  {d : ℕ} (x : Fin (d + 1) → Fˣ) (a : ℕ)

private lemma act_tmul (f g : F) (k : K) (w : DR ℂ K) :
    (sysP K x a).act (f ⊗ₜ k) (g ⊗ₜ w) = (f * g) ⊗ₜ (k • w) := by
  simp [sysP, Module.endTensorEndAlgHom_apply]

private lemma mulP_one (w : DR ℂ K) : mulP F K ((1 : F) ⊗ₜ[ℂ] w) = w := by
  simp [mulP]

private lemma X_val (i : Fin (d + 1)) : (((sysP K x a).X i : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) = (x i : F) ⊗ₜ 1 := rfl

private lemma Y_val (i : Fin (d + 1)) : (((sysP K x a).Y i : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) =
    1 ⊗ₜ algebraMap F K (x i) := rfl

end

theorem UpperTheory.Gal.productCup_of_system.pTheta_of :
    MJ → ThMu → ThMuLat → KapInd → LatA → ActsLin → GoodZ → SysBasic → SysOk → PTheta := by
  intro hMJ hTh hLat hKap hLA hAL hG hSB _ F K _ _ _ _ _ _ d x hc a p β hβ
  have hU := wdUni_of
  have hl : ∀ {A B : Type} [LinearOrder A] [LinearOrder B] (b : Finset A) (L : Finset B), lft (uni b L) = b :=
    fun {A B} _ _ b L => (hU A B ℂ (fun _ => 0) (fun _ => 0) b L).2.1
  have hr : ∀ {A B : Type} [LinearOrder A] [LinearOrder B] (b : Finset A) (L : Finset B), rgt (uni b L) = L :=
    fun {A B} _ _ b L => (hU A B ℂ (fun _ => 0) (fun _ => 0) b L).2.2.1
  have hcard : ∀ {A B : Type} [LinearOrder A] [LinearOrder B] (b : Finset A) (L : Finset B),
      (uni b L).card = b.card + L.card :=
    fun {A B} _ _ b L => (hU A B ℂ (fun _ => 0) (fun _ => 0) b L).2.2.2.1
  have hlr : ∀ {A B : Type} [LinearOrder A] [LinearOrder B] (s : Finset (A ⊕ₗ B)), uni (lft s) (rgt s) = s :=
    fun {A B} _ _ s => (hU A B ℂ (fun _ => 0) (fun _ => 0) ∅ ∅).2.2.2.2 s
  have hGood : (sysP K x a).Good := (hG F K d x hc a).2.1
  have hβC : ∀ J, β J ∈ (if J.Nonempty ∧ (J.card : ℤ) = (p : ℤ) + 1 then omB ℂ K (rB ℂ K (xv x) J) a else ⊥) :=
    fun J => hβ.1 J (Set.mem_univ J)
  set b : Finset (Fin (d + 1)) → F ⊗[ℂ] DR ℂ K := fun J => (1 : F) ⊗ₜ[ℂ] β J with hbdef
  have hb0 : ∀ J, ¬ (J.Nonempty ∧ J.card = p + 1) → b J = 0 := by
    intro J hJ
    have h := hβC J
    rw [if_neg (by rintro ⟨h1, h2⟩; exact hJ ⟨h1, by exact_mod_cast h2⟩)] at h
    simp only [hbdef, (Submodule.mem_bot ℂ).1 h, TensorProduct.tmul_zero]
  have hb1 : deltaL ℂ _ _ b = 0 := by
    funext t
    have h0 : deltaL ℂ _ _ β t = 0 := congrFun hβ.2 t
    change ∑ i ∈ t, GlobalTheory.cubeSign t i • b (t.erase i) = 0
    have h1 : ∑ i ∈ t, GlobalTheory.cubeSign t i • β (t.erase i) = 0 := h0
    have h2 := congrArg (TensorProduct.mk ℂ F (DR ℂ K) 1) h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun i _ => by simp only [hbdef, Units.smul_def, map_zsmul, TensorProduct.mk_apply]
  have hb2 : ∀ J, J.card ≠ p + 1 → b J = 0 := fun J hJ => hb0 J fun h => hJ h.2
  have hθ0 : ∀ (I : Finset (Fin (d + 1))) (L : Finset (Mi d)), I.card + L.card ≠ d + 1 →
      detC (sysP K x a).rowMu (uni I L) = 0 := by
    intro I L h
    unfold detC
    rw [dite_eq_right (by rw [hcard]; exact h)]
  have hθe : ∀ L : Finset (Mi d), detC (sysP K x a).rowMu (uni ∅ L) = 0 :=
    (hTh d _ _ (sysP K x a)).2.1
  have hval : ∀ (I J : Finset (Fin (d + 1))) (L : Finset (Mi d)),
      (sysP K x a).mj p (detC (sysP K x a).rowMu) b (uni (uni I J) L) =
        ((-1 : ℤ) ^ ((p + 1) * L.card)) • (sysP K x a).act (detC (sysP K x a).rowMu (uni I L)) (b J) := by
    intro I J L
    simp only [Sys.mj, hl, hr]
  have hzero : ∀ (I J : Finset (Fin (d + 1))) (L : Finset (Mi d)),
      (I = ∅ ∨ ¬ (J.Nonempty ∧ J.card = p + 1) ∨ I.card + L.card ≠ d + 1) →
      (sysP K x a).mj p (detC (sysP K x a).rowMu) b (uni (uni I J) L) = 0 := by
    intro I J L h
    rw [hval]
    rcases h with rfl | h | h
    · rw [hθe]; simp
    · rw [hb0 J h]; simp
    · rw [hθ0 I L h]; simp
  refine ⟨(sysP K x a).mj p (detC (sysP K x a).rowMu) b, ?_, ?_, ?_, ?_⟩
  · refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · rw [(hSB d _ _ (sysP K x a) (Mi d) n11 (sysP K x a).mu _).2.1]
      intro I J
      split_ifs with hIJ
      · obtain ⟨hI, hJ⟩ := hIJ
        intro L _
        change (sysP K x a).mj p (detC (sysP K x a).rowMu) b (uni (uni I J) L) ∈ _
        dsimp only
        rw [SetLike.mem_coe]
        split_ifs with hL
        · by_cases hJc : J.card = p + 1
          · have hIL : I.card + L.card = d + 1 := by push_cast [hJc] at hL; omega
            have hi := pk_mem hI
            have hj := pk_mem hJ
            obtain ⟨s, hs, hdet⟩ := (hLat d _ _ (sysP K x a) hGood).2 I J L hI (pk J) hj
            have hbJ : β J ∈ omB ℂ K (rB ℂ K (xv x) J) a := by
              have h := hβC J
              rwa [if_pos ⟨hJ, by exact_mod_cast hJc⟩] at h
            have hcompl : Iᶜ.card = L.card := by
              rw [Finset.card_compl, Fintype.card_fin]; omega
            have hfm := lat_mem hLA x hc.pd I (pk I) hi
            have hsplit := prod_split x I (pk I)
            generalize (∏ m ∈ Iᶜ, ((x m : F) / x (pk I))) = f at hfm hsplit
            have hm : f ⊗ₜ[ℂ] β J ∈ (sysP K x a).M I J := Submodule.apply_mem_map₂ _ hfm hbJ
            have hm' := hGood.stab I J hI hJ s hs _ hm
            have hXprod : ∏ m ∈ Iᶜ, (((sysP K x a).X m : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) =
                (f ⊗ₜ (1 : K)) * (((sysP K x a).X (pk I) : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) ^ L.card := by
              have e := congrArg (Algebra.TensorProduct.includeLeftRingHom : F →+* F ⊗[ℂ] K) hsplit
              rw [map_prod, map_mul, map_pow, hcompl] at e
              exact e
            have hU' : (((∏ l ∈ L, (sysP K x a).u n11 (pk I) (pk J) l : (F ⊗[ℂ] K)ˣ)) : F ⊗[ℂ] K) =
                (((sysP K x a).X (pk I) : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) ^ L.card *
                  (((sysP K x a).Y (pk J) : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) ^ L.card := by
              have : ∀ l : Mi d, (sysP K x a).u n11 (pk I) (pk J) l = (sysP K x a).X (pk I) * (sysP K x a).Y (pk J) := by
                intro l; simp [Sys.u, n11]
              simp only [this, Finset.prod_const, mul_pow, Units.val_mul, Units.val_pow_eq_pow_val]
            have hact : (sysP K x a).act (f ⊗ₜ (1 : K)) (b J) = f ⊗ₜ[ℂ] β J := by
              simp [hbdef, act_tmul]
            rw [hval]
            apply zsmul_mem
            refine ⟨(sysP K x a).act s (f ⊗ₜ[ℂ] β J), hm', ?_⟩
            rw [hdet, hXprod, hU', ← hact, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
            congr 2
            ring
          · rw [hzero I J L (Or.inr (Or.inl fun h => hJc h.2))]
            exact Submodule.zero_mem _
        · have : (sysP K x a).mj p (detC (sysP K x a).rowMu) b (uni (uni I J) L) = 0 := by
            refine hzero I J L ?_
            by_cases hJc : J.card = p + 1
            · refine Or.inr (Or.inr fun h => hL ?_)
              push_cast [hJc]; omega
            · exact Or.inr (Or.inl fun h => hJc h.2)
          rw [this]
          exact Submodule.zero_mem _
      · funext L
        refine hzero I J L ?_
        by_cases hI : I.Nonempty
        · exact Or.inr (Or.inl fun h => hIJ ⟨hI, h.1⟩)
        · exact Or.inl (Finset.not_nonempty_iff_eq_empty.1 hI)
    · exact hMJ d _ _ (sysP K x a) (Mi d) (sysP K x a).mu p _ b (hTh d _ _ (sysP K x a)).1 hb1 hb2
  · intro s L hL
    obtain ⟨I, J, rfl⟩ : ∃ I J, s = uni I J := ⟨lft s, rgt s, (hlr s).symm⟩
    refine hzero I J L ?_
    by_cases hI : I = ∅
    · exact Or.inl hI
    · refine Or.inr (Or.inr fun h => hI ?_)
      exact Finset.card_eq_zero.1 (by omega)
  · intro s L hL
    obtain ⟨I, J, rfl⟩ : ∃ I J, s = uni I J := ⟨lft s, rgt s, (hlr s).symm⟩
    have hedge : edge2 β (uni I J) = if I.card = 1 then β J else 0 := by simp only [edge2, hl, hr]
    rw [hedge]
    by_cases hI : I.card = 1
    · rw [if_pos hI]
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hI
      obtain ⟨τ, hτ⟩ := hc.exists_isTop
      have h5 := (hAL F K d x hc τ hτ a).2.2.2.2.1
      have hk := hKap F K d x hc _ _ (sysP K x a)
        (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom ℂ F K) (AlgHom.id ℂ K))
        (fun m => by rw [X_val]; simp) (fun m => by rw [Y_val]; simp) i L hL
      rw [hval, hL, map_zsmul, h5, hk, hbdef]
      simp only [mulP_one]
      rw [smul_comm]
    · rw [if_neg hI, hzero I J L (Or.inr (Or.inr (by omega)))]
      simp
  · intro J
    rw [hval, (hTh d _ _ (sysP K x a)).2.2.1]
    simp [hbdef]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PGoodZ
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemOmAOfMemRA
set_option autoImplicit false

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

section DualMono

variable {k : Type} [Field k] {F : Type} [Field F] [Algebra k F] {d : ℕ} {x : Fin (d + 1) → F}

theorem rA_le_of_subset {I J : Finset (Fin (d + 1))} (h : I ⊆ J) : rA k x I ≤ rA k x J := by
  refine Algebra.adjoin_mono ?_
  rintro y ⟨i, hi, j, rfl⟩
  exact ⟨i, h hi, j, rfl⟩

theorem div_mem_rA_of_mem {J : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ J) (j : Fin (d + 1)) :
    x j / x i ∈ rA k x J :=
  Algebra.subset_adjoin ⟨i, hi, j, rfl⟩

theorem mem_omA_iff_mul {I : Finset (Fin (d + 1))} {y : F} :
    y ∈ omA k x I ↔ ∀ i ∈ I, (∏ j, x i / x j) * y ∈ rA k x I := by
  simp [omA, Submodule.mem_iInf]

theorem mul_mem_omA_of_mem_rA {J : Finset (Fin (d + 1))} {r y : F} (hr : r ∈ rA k x J) (hy : y ∈ omA k x J) :
    r * y ∈ omA k x J := by
  rw [mem_omA_iff_mul] at hy ⊢
  intro i hi
  rw [mul_left_comm]
  exact (rA k x J).mul_mem hr (hy i hi)

theorem omA_le_of_subset (hx : ∀ i, x i ≠ 0) {I J : Finset (Fin (d + 1))} (hI : I.Nonempty) (h : I ⊆ J) :
    omA k x I ≤ omA k x J := by
  obtain ⟨i₀, hi₀⟩ := hI
  intro y hy
  rw [mem_omA_iff_mul] at hy ⊢
  intro i hi
  have e : (∏ j, x i / x j) = (x i / x i₀) ^ (d + 1) * ∏ j, x i₀ / x j := by
    have hc : (x i / x i₀) ^ (d + 1) = ∏ _j : Fin (d + 1), (x i / x i₀) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hc, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    field_simp [hx i₀, hx j]
  rw [e, mul_assoc]
  exact (rA k x J).mul_mem ((rA k x J).pow_mem (div_mem_rA_of_mem (h hi₀) i) _) (rA_le_of_subset h (hy i₀ hi₀))

variable {W W' : Type} [AddCommGroup W] [Module F W] [Module k W] [IsScalarTower k F W]
  [AddCommGroup W'] [Module F W'] [Module k W'] [IsScalarTower k F W']

end DualMono

end GlobalTheory.PD
end

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section Tensor
variable {S S' E E' : Type} [CommRing S] [CommRing S'] [Algebra ℂ S] [Algebra ℂ S']
  [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']

private theorem range_mono {A A' : Subalgebra ℂ S} {B B' : Subalgebra ℂ S'} (hA : A ≤ A') (hB : B ≤ B') :
    (Algebra.TensorProduct.map A.val B.val).range ≤ (Algebra.TensorProduct.map A'.val B'.val).range := by
  rintro _ ⟨z, rfl⟩
  refine ⟨Algebra.TensorProduct.map (Subalgebra.inclusion hA) (Subalgebra.inclusion hB) z, ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add p q hp hq => simp only [map_add (f := _)] at *; rw [hp, hq]

private theorem tmul_mem_range {A : Subalgebra ℂ S} {B : Subalgebra ℂ S'} {a : S} {b : S'} (ha : a ∈ A) (hb : b ∈ B) :
    a ⊗ₜ[ℂ] b ∈ (Algebra.TensorProduct.map A.val B.val).range :=
  ⟨(⟨a, ha⟩ : A) ⊗ₜ[ℂ] (⟨b, hb⟩ : B), by simp⟩

private theorem stab_tensor (f : S →ₐ[ℂ] Module.End ℂ E) (g : S' →ₐ[ℂ] Module.End ℂ E')
    {A : Subalgebra ℂ S} {B : Subalgebra ℂ S'} {P : Submodule ℂ E} {Q : Submodule ℂ E'}
    (hP : ∀ a ∈ A, ∀ m ∈ P, f a m ∈ P) (hQ : ∀ b ∈ B, ∀ m ∈ Q, g b m ∈ Q) :
    Stab ((Module.endTensorEndAlgHom).comp (Algebra.TensorProduct.map f g))
      (Algebra.TensorProduct.map A.val B.val).range (Submodule.map₂ (TensorProduct.mk ℂ _ _) P Q) := by
  rintro _ ⟨z, rfl⟩ m hm
  induction z using TensorProduct.induction_on generalizing m with
  | zero => simp
  | tmul a b =>
    have hle : Submodule.map₂ (TensorProduct.mk ℂ E E') P Q ≤
        (Submodule.map₂ (TensorProduct.mk ℂ E E') P Q).comap (TensorProduct.map (f a) (g b)) := by
      rw [Submodule.map₂_le]
      intro p hp q hq
      simp only [Submodule.mem_comap, TensorProduct.mk_apply, TensorProduct.map_tmul]
      exact Submodule.apply_mem_map₂ _ (hP _ a.2 _ hp) (hQ _ b.2 _ hq)
    have h2 := hle hm
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, Subalgebra.coe_val]
    exact h2
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply]
    exact add_mem (hp m hm) (hq m hm)

private theorem units_ratio {F : Type} [Field F] (f : F →+* S) (u v : Fˣ) :
    ((Units.map (f : F →* S) u * (Units.map (f : F →* S) v)⁻¹ : Sˣ) : S) = f ((u : F) / v) := by
  simp [div_eq_mul_inv]

end Tensor

section Forms
variable {K : Type} [Field K] [Algebra ℂ K]

private theorem omB_mono' {B B' : Subalgebra ℂ K} (h : B ≤ B') (q : ℕ) : omB ℂ K B q ≤ omB ℂ K B' q := by
  unfold omB
  exact Submodule.span_mono (fun y ⟨b, hb, v, hv, e⟩ => ⟨b, h hb, v, fun j => h (hv j), e⟩)

private theorem omB_smul (B : Subalgebra ℂ K) (q : ℕ) {c : K} (hc : c ∈ B) {m : DR ℂ K} (hm : m ∈ omB ℂ K B q) :
    Algebra.lsmul ℂ ℂ (DR ℂ K) c m ∈ omB ℂ K B q := by
  show c • m ∈ omB ℂ K B q
  unfold omB at hm ⊢
  induction hm using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, v, hv, rfl⟩ := hy
    exact Submodule.subset_span ⟨c * b, B.mul_mem hc hb, v, hv, by rw [mul_smul]⟩
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | smul r y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ r hy

end Forms

section Chart
variable {F : Type} (K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}
  (x : Fin (d + 1) → Fˣ)

private theorem ratio_mem_rA {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (a : Fin (d + 1)) :
    (x a : F) / x i ∈ rA ℂ (xv x) I := by
  unfold rA
  exact Algebra.subset_adjoin ⟨i, hi, a, rfl⟩

private theorem ratio_mem_rB {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (a : Fin (d + 1)) :
    algebraMap F K ((x a : F) / x i) ∈ rB ℂ K (xv x) I := by
  unfold rB
  exact (integralClosure (rA ℂ (xv x) I) K).algebraMap_mem (⟨_, ratio_mem_rA x hi a⟩ : rA ℂ (xv x) I)

private theorem sysZ_X (a : ℕ) (b i : Fin (d + 1)) :
    (((sysZ K x a).X b * ((sysZ K x a).X i)⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) =
      algebraMap F K ((x b : F) / x i) ⊗ₜ[ℂ] 1 := by
  unfold sysZ
  exact (units_ratio _ (x b) (x i)).trans rfl

private theorem sysZ_Y (a : ℕ) (b i : Fin (d + 1)) :
    (((sysZ K x a).Y b * ((sysZ K x a).Y i)⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) =
      1 ⊗ₜ[ℂ] algebraMap F K ((x b : F) / x i) := by
  unfold sysZ
  exact (units_ratio _ (x b) (x i)).trans rfl

private theorem sysP_X (a : ℕ) (b i : Fin (d + 1)) :
    (((sysP K x a).X b * ((sysP K x a).X i)⁻¹ : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) =
      ((x b : F) / x i) ⊗ₜ[ℂ] 1 := by
  unfold sysP
  exact (units_ratio _ (x b) (x i)).trans rfl

private theorem sysP_Y (a : ℕ) (b i : Fin (d + 1)) :
    (((sysP K x a).Y b * ((sysP K x a).Y i)⁻¹ : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) =
      1 ⊗ₜ[ℂ] algebraMap F K ((x b : F) / x i) := by
  unfold sysP
  exact (units_ratio _ (x b) (x i)).trans rfl

end Chart

theorem UpperTheory.Gal.productCup_of_system.goodZ_of :
    GoodZ := by
  intro F K _ _ _ _ _ _ d x hx a
  have hrB : ∀ I J : Finset (Fin (d + 1)), I.Nonempty → I ⊆ J → rB ℂ K (xv x) I ≤ rB ℂ K (xv x) J := by
    intro I J hI hIJ
    obtain ⟨i, hi⟩ := hI
    exact (GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K d (xv x) hx I i hi).1 J hIJ
  have hx0 : ∀ i, xv x i ≠ 0 := fun i => (x i).ne_zero
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro I I' J J' hI hJ hII hJJ
    exact range_mono (hrB I I' hI hII) (hrB J J' hJ hJJ)
  · intro I I' J J' hI hJ hII hJJ
    show MZ F K (xv x) a I J ≤ MZ F K (xv x) a I' J'
    unfold MZ
    exact Submodule.map₂_le_map₂ (omB_mono' (hrB I I' hI hII) _) (omB_mono' (hrB J J' hJ hJJ) _)
  · intro I J hI hJ
    exact stab_tensor (Algebra.lsmul ℂ ℂ (DR ℂ K)) (Algebra.lsmul ℂ ℂ (DR ℂ K))
      (fun c hc m hm => omB_smul _ _ hc hm) (fun c hc m hm => omB_smul _ _ hc hm)
  · intro I J hJ i hi b
    rw [sysZ_X]
    exact tmul_mem_range (ratio_mem_rB K x hi b) (Subalgebra.one_mem _)
  · intro I J hI j hj b
    rw [sysZ_Y]
    exact tmul_mem_range (Subalgebra.one_mem _) (ratio_mem_rB K x hj b)
  · intro I I' J J' hI hJ hII hJJ
    exact range_mono (rA_le_of_subset hII) (hrB J J' hJ hJJ)
  · intro I I' J J' hI hJ hII hJJ
    exact Submodule.map₂_le_map₂ (omA_le_of_subset hx0 hI hII) (omB_mono' (hrB J J' hJ hJJ) _)
  · intro I J hI hJ
    exact stab_tensor (Algebra.lsmul ℂ ℂ F) (Algebra.lsmul ℂ ℂ (DR ℂ K))
      (fun c hc m hm => mul_mem_omA_of_mem_rA hc hm) (fun c hc m hm => omB_smul _ _ hc hm)
  · intro I J hJ i hi b
    rw [sysP_X]
    exact tmul_mem_range (ratio_mem_rA x hi b) (Subalgebra.one_mem _)
  · intro I J hI j hj b
    rw [sysP_Y]
    exact tmul_mem_range (Subalgebra.one_mem _) (ratio_mem_rB K x hj b)
  · intro s t hs hst
    exact omB_mono' (hrB s t hs hst) a
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.TmulMemTensorRing
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

noncomputable section

namespace UpperTheory.Gal.productCup_of_system

section
variable {F : Type} [Field F] [Algebra ℂ F] {d : ℕ} (x : Fin (d + 1) → Fˣ)

private lemma rA_single_le {I : Finset (Fin (d + 1))} {j : Fin (d + 1)} (hj : j ∈ I) :
    rA ℂ (xv x) {j} ≤ rA ℂ (xv x) I := by
  refine Algebra.adjoin_mono ?_
  rintro y ⟨i, hi, a, rfl⟩
  obtain rfl := Finset.mem_singleton.1 hi
  exact ⟨i, hj, a, rfl⟩

private lemma tmul_mem_tensorRing {I J : Finset (Fin (d + 1))} {a b : F} (ha : a ∈ rA ℂ (xv x) I)
    (hb : b ∈ rA ℂ (xv x) J) : a ⊗ₜ[ℂ] b ∈ R0 x I J :=
  ⟨(⟨a, ha⟩ : rA ℂ (xv x) I) ⊗ₜ[ℂ] (⟨b, hb⟩ : rA ℂ (xv x) J), by
    simp [Algebra.TensorProduct.map_tmul]⟩

private abbrev PP (I J : Finset (Fin (d + 1))) (j : Fin (d + 1)) : Submodule ℂ (F ⊗[ℂ] F) :=
  sm (Algebra.lmul ℂ (F ⊗[ℂ] F)) (Subalgebra.toSubmodule (R0 x I J)) (Set.range (f0 x j))

private lemma f_mul_mem {I J : Finset (Fin (d + 1))} {j : Fin (d + 1)} {t m : F ⊗[ℂ] F}
    (ht : t ∈ Set.range (f0 x j)) (hm : m ∈ R0 x I J) : t * m ∈ PP x I J j := by
  have h : (Subalgebra.toSubmodule (R0 x I J)).map (Algebra.lmul ℂ (F ⊗[ℂ] F) t) ≤ PP x I J j :=
    le_iSup₂ (f := fun r (_ : r ∈ Set.range (f0 x j)) =>
      (Subalgebra.toSubmodule (R0 x I J)).map (Algebra.lmul ℂ (F ⊗[ℂ] F) r)) t ht
  exact h ⟨m, hm, rfl⟩

private lemma mul_mem_PP {I J : Finset (Fin (d + 1))} {j : Fin (d + 1)} {r p : F ⊗[ℂ] F}
    (hr : r ∈ R0 x I J) (hp : p ∈ PP x I J j) : r * p ∈ PP x I J j := by
  have h : PP x I J j ≤ (PP x I J j).comap (LinearMap.mulLeft ℂ r) := by
    refine iSup₂_le fun t ht => ?_
    rintro _ ⟨m, hm, rfl⟩
    show r * (t * m) ∈ PP x I J j
    rw [mul_left_comm]
    exact f_mul_mem x ht ((R0 x I J).mul_mem hr hm)
  exact h hp

private lemma diff_mem {I J : Finset (Fin (d + 1))} {j : Fin (d + 1)} (hI : j ∈ I) (hJ : j ∈ J) {a : F}
    (ha : a ∈ rA ℂ (xv x) {j}) : a ⊗ₜ[ℂ] (1 : F) - (1 : F) ⊗ₜ[ℂ] a ∈ PP x I J j := by
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, hi, a, rfl⟩ := hy
    obtain rfl := Finset.mem_singleton.1 hi
    by_cases hne : a = i
    · subst hne
      simp
    · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hne
      have := f_mul_mem x (I := I) (J := J) (j := i) ⟨l, rfl⟩ (one_mem _)
      simpa [f0] using this
  | algebraMap c =>
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, sub_self]
    exact zero_mem _
  | add a b _ _ ha hb =>
    have e : (a + b) ⊗ₜ[ℂ] (1 : F) - (1 : F) ⊗ₜ[ℂ] (a + b) =
        (a ⊗ₜ[ℂ] (1 : F) - (1 : F) ⊗ₜ[ℂ] a) + (b ⊗ₜ[ℂ] (1 : F) - (1 : F) ⊗ₜ[ℂ] b) := by
      rw [TensorProduct.add_tmul, TensorProduct.tmul_add]; abel
    rw [e]
    exact add_mem ha hb
  | mul a b ha' hb' ha hb =>
    have e : (a * b) ⊗ₜ[ℂ] (1 : F) - (1 : F) ⊗ₜ[ℂ] (a * b) =
        (a ⊗ₜ[ℂ] (1 : F)) * (b ⊗ₜ[ℂ] (1 : F) - (1 : F) ⊗ₜ[ℂ] b) +
          ((1 : F) ⊗ₜ[ℂ] b) * (a ⊗ₜ[ℂ] (1 : F) - (1 : F) ⊗ₜ[ℂ] a) := by
      simp only [mul_sub, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_comm b a]
      abel
    rw [e]
    exact add_mem (mul_mem_PP x (tmul_mem_tensorRing x (rA_single_le x hI ha') (one_mem _)) hb)
      (mul_mem_PP x (tmul_mem_tensorRing x (one_mem _) (rA_single_le x hJ hb')) ha)

private lemma diag_mem {I J : Finset (Fin (d + 1))} {j : Fin (d + 1)} (hI : j ∈ I) (hJ : j ∈ J)
    (w : rA ℂ (xv x) {j} ⊗[ℂ] rA ℂ (xv x) {j}) :
    Algebra.TensorProduct.map (rA ℂ (xv x) {j}).val (rA ℂ (xv x) {j}).val w -
      (1 : F) ⊗ₜ[ℂ] Algebra.TensorProduct.lmul' ℂ
        (Algebra.TensorProduct.map (rA ℂ (xv x) {j}).val (rA ℂ (xv x) {j}).val w) ∈ PP x I J j := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    have e : (a : F) ⊗ₜ[ℂ] (b : F) - (1 : F) ⊗ₜ[ℂ] ((a : F) * b) =
        ((1 : F) ⊗ₜ[ℂ] (b : F)) * ((a : F) ⊗ₜ[ℂ] (1 : F) - (1 : F) ⊗ₜ[ℂ] (a : F)) := by
      simp only [mul_sub, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_comm (b : F) (a : F)]
    simp only [Algebra.TensorProduct.map_tmul, Subalgebra.coe_val, Algebra.TensorProduct.lmul'_apply_tmul]
    rw [e]
    exact mul_mem_PP x (tmul_mem_tensorRing x (one_mem _) (rA_single_le x hJ b.2)) (diff_mem x hI hJ a.2)
  | add a b ha hb =>
    have := add_mem ha hb
    simp only [map_add (f := _), TensorProduct.tmul_add]
    convert this using 1
    abel

private lemma prod_mem_single (I : Finset (Fin (d + 1))) (j : Fin (d + 1)) :
    (∏ i ∈ I, (x i : F) / x j) ∈ rA ℂ (xv x) {j} :=
  prod_mem fun i _ => Algebra.subset_adjoin ⟨j, Finset.mem_singleton_self j, i, rfl⟩

private lemma pow_mul_mem (I : Finset (Fin (d + 1))) (j : Fin (d + 1)) {a : F} (ha : a ∈ rA ℂ (xv x) I) :
    ∃ N : ℕ, (∏ i ∈ I, (x i : F) / x j) ^ N * a ∈ rA ℂ (xv x) {j} := by
  have hs := prod_mem_single x I j
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, hi, b, rfl⟩ := hy
    refine ⟨1, ?_⟩
    have e : (∏ i ∈ I, (x i : F) / x j) ^ 1 * (xv x b / xv x i) =
        (∏ i' ∈ I.erase i, (x i' : F) / x j) * ((x b : F) / x j) := by
      rw [pow_one, ← Finset.mul_prod_erase I _ hi]
      have h1 : (x i : F) ≠ 0 := (x i).ne_zero
      have h2 : (x j : F) ≠ 0 := (x j).ne_zero
      simp only [xv]
      field_simp
    rw [e]
    exact mul_mem (prod_mem_single x _ j) (Algebra.subset_adjoin ⟨j, Finset.mem_singleton_self j, b, rfl⟩)
  | algebraMap c => exact ⟨0, by simpa using (rA ℂ (xv x) {j}).algebraMap_mem c⟩
  | add a b _ _ ha hb =>
    obtain ⟨N, hN⟩ := ha
    obtain ⟨N', hN'⟩ := hb
    refine ⟨N + N', ?_⟩
    have e : (∏ i ∈ I, (x i : F) / x j) ^ (N + N') * (a + b) =
        (∏ i ∈ I, (x i : F) / x j) ^ N' * ((∏ i ∈ I, (x i : F) / x j) ^ N * a) +
          (∏ i ∈ I, (x i : F) / x j) ^ N * ((∏ i ∈ I, (x i : F) / x j) ^ N' * b) := by
      rw [pow_add]; ring
    rw [e]
    exact add_mem (mul_mem (pow_mem hs _) hN) (mul_mem (pow_mem hs _) hN')
  | mul a b _ _ ha hb =>
    obtain ⟨N, hN⟩ := ha
    obtain ⟨N', hN'⟩ := hb
    refine ⟨N + N', ?_⟩
    have e : (∏ i ∈ I, (x i : F) / x j) ^ (N + N') * (a * b) =
        ((∏ i ∈ I, (x i : F) / x j) ^ N * a) * ((∏ i ∈ I, (x i : F) / x j) ^ N' * b) := by
      rw [pow_add]; ring
    rw [e]
    exact mul_mem hN hN'

private lemma inv_prod_mem {I : Finset (Fin (d + 1))} {j : Fin (d + 1)} (hj : j ∈ I) :
    (∏ i ∈ I, (x j : F) / x i) ∈ rA ℂ (xv x) I :=
  prod_mem fun i hi => Algebra.subset_adjoin ⟨i, hi, j, rfl⟩

private lemma prod_mul_inv (I : Finset (Fin (d + 1))) (j : Fin (d + 1)) :
    (∏ i ∈ I, (x j : F) / x i) * (∏ i ∈ I, (x i : F) / x j) = 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  have h1 : (x i : F) ≠ 0 := (x i).ne_zero
  have h2 : (x j : F) ≠ 0 := (x j).ne_zero
  field_simp

private lemma scale_mem {I J : Finset (Fin (d + 1))} {j : Fin (d + 1)} (w : rA ℂ (xv x) I ⊗[ℂ] rA ℂ (xv x) J) :
    ∃ N : ℕ, ((∏ i ∈ I, (x i : F) / x j) ⊗ₜ[ℂ] (∏ i ∈ J, (x i : F) / x j)) ^ N *
      Algebra.TensorProduct.map (rA ℂ (xv x) I).val (rA ℂ (xv x) J).val w ∈ R0 x {j} {j} := by
  have hs := prod_mem_single x I j
  have ht := prod_mem_single x J j
  have hst := tmul_mem_tensorRing x hs ht
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a b =>
    obtain ⟨N, hN⟩ := pow_mul_mem x I j a.2
    obtain ⟨N', hN'⟩ := pow_mul_mem x J j b.2
    refine ⟨N + N', ?_⟩
    have e : ((∏ i ∈ I, (x i : F) / x j) ⊗ₜ[ℂ] (∏ i ∈ J, (x i : F) / x j)) ^ (N + N') *
        Algebra.TensorProduct.map (rA ℂ (xv x) I).val (rA ℂ (xv x) J).val (a ⊗ₜ[ℂ] b) =
        (((∏ i ∈ I, (x i : F) / x j) ^ N') ⊗ₜ[ℂ] ((∏ i ∈ J, (x i : F) / x j) ^ N)) *
          (((∏ i ∈ I, (x i : F) / x j) ^ N * (a : F)) ⊗ₜ[ℂ] ((∏ i ∈ J, (x i : F) / x j) ^ N' * (b : F))) := by
      simp only [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.map_tmul, Subalgebra.coe_val,
        Algebra.TensorProduct.tmul_mul_tmul, pow_add]
      congr 1 <;> ring
    rw [e]
    exact (R0 x {j} {j}).mul_mem (tmul_mem_tensorRing x (pow_mem hs _) (pow_mem ht _)) (tmul_mem_tensorRing x hN hN')
  | add a b ha hb =>
    obtain ⟨N, hN⟩ := ha
    obtain ⟨N', hN'⟩ := hb
    refine ⟨N + N', ?_⟩
    rw [map_add (f := _), mul_add, pow_add]
    refine add_mem ?_ ?_
    · rw [mul_comm (_ ^ N), mul_assoc]
      exact (R0 x {j} {j}).mul_mem (pow_mem hst _) hN
    · rw [mul_assoc]
      exact (R0 x {j} {j}).mul_mem (pow_mem hst _) hN'

end

theorem kernelZero_holds :
    Ker0 := by
  intro F _ _ d x _ I J j hI hJ m hm h0
  obtain ⟨w, rfl⟩ := hm
  obtain ⟨N, hN⟩ := scale_mem x (j := j) w
  set m := Algebra.TensorProduct.map (rA ℂ (xv x) I).val (rA ℂ (xv x) J).val w with hm
  set c := (∏ i ∈ I, (x i : F) / x j) ⊗ₜ[ℂ] (∏ i ∈ J, (x i : F) / x j) with hc
  set u := (∏ i ∈ I, (x j : F) / x i) ⊗ₜ[ℂ] (∏ i ∈ J, (x j : F) / x i) with hu
  have huR : u ∈ R0 x I J := tmul_mem_tensorRing x (inv_prod_mem x hI) (inv_prod_mem x hJ)
  have huc : u * c = 1 := by
    rw [hu, hc, Algebra.TensorProduct.tmul_mul_tmul, prod_mul_inv, prod_mul_inv]
    rfl
  obtain ⟨w', hw'⟩ := hN
  have h1 := diag_mem x hI hJ w'
  have hz : Algebra.TensorProduct.lmul' ℂ (c ^ N * m) = 0 := by
    have h0' : Algebra.TensorProduct.lmul' ℂ m = 0 := h0
    rw [map_mul, h0', mul_zero]
  have h2 : c ^ N * m ∈ PP x I J j := by
    have e : Algebra.TensorProduct.map (rA ℂ (xv x) {j}).val (rA ℂ (xv x) {j}).val w' = c ^ N * m := hw'
    rw [e, hz] at h1
    simpa using h1
  have h3 := mul_mem_PP x (pow_mem huR N) h2
  rwa [← mul_assoc, ← mul_pow, huc, one_pow, one_mul] at h3

end UpperTheory.Gal.productCup_of_system

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PRCupTop
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open GlobalTheory.W1.Lef
open scoped TensorProduct

set_option autoImplicit false

namespace UpperTheory.Gal.productCup_of_system.RCT

private theorem wd_one {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] (c : Finset ι → E) (s : Finset ι) :
    wd (fun _ : ι => (1 : Module.End ℂ E)) c s = deltaL ℂ ι E c s := by
  show _ = ∑ i ∈ s, GlobalTheory.cubeSign s i • c (s.erase i)
  simp [wd, Units.smul_def]

private theorem card_filters {n : ℕ} (i : Fin n) :
    (Finset.univ.filter (· ≤ i)).card + (Finset.univ.filter (i ≤ ·)).card = n + 1 := by
  have h1 : (Finset.univ.filter (· ≤ i)) ∪ (Finset.univ.filter (i ≤ ·)) = Finset.univ := by
    ext j; simp [le_total]
  have h2 : (Finset.univ.filter (· ≤ i)) ∩ (Finset.univ.filter (i ≤ ·)) = {i} := by
    ext j
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact (le_antisymm_iff : j = i ↔ j ≤ i ∧ i ≤ j).symm
  have := Finset.card_union_add_card_inter (Finset.univ.filter (· ≤ i)) (Finset.univ.filter (i ≤ ·))
  rw [h1, h2] at this
  simp at this
  omega

variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K]

private theorem muP_tmul (τ : DR ℂ K →ₗ[K] K) (w' w'' w : DR ℂ K) :
    muP F K τ (w' ⊗ₜ w'') w = (Algebra.trace F K (τ (w' * w))) ⊗ₜ w'' := by
  simp [muP]

private theorem res_tmul (ρ : F →ₗ[ℂ] ℂ) (f : F) (w : DR ℂ K) : resP (DR ℂ K) ρ (f ⊗ₜ w) = ρ f • w := by
  simp [resP]

private noncomputable def bil (τ : DR ℂ K →ₗ[K] K) (ρ : F →ₗ[ℂ] ℂ) :
    DR ℂ K ⊗[ℂ] DR ℂ K →ₗ[ℂ] DR ℂ K →ₗ[ℂ] DR ℂ K :=
  (muP F K τ).compr₂ (resP (DR ℂ K) ρ)

private theorem bil_tmul (τ : DR ℂ K →ₗ[K] K) (ρ : F →ₗ[ℂ] ℂ) (w' w'' w : DR ℂ K) :
    bil τ ρ (w' ⊗ₜ w'') w = ρ (Algebra.trace F K (τ (w' * w))) • w'' := by
  simp [bil, muP_tmul, res_tmul]

variable {d : ℕ} {x : Fin (d + 1) → Fˣ}

private theorem bil_mem (τ : DR ℂ K →ₗ[K] K) (ρ : F →ₗ[ℂ] ℂ) {a : ℕ} {I J : Finset (Fin (d + 1))}
    {e : DR ℂ K ⊗[ℂ] DR ℂ K} (he : e ∈ MZ F K (xv x) a I J) (v : DR ℂ K) :
    bil τ ρ e v ∈ omB ℂ K (rB ℂ K (xv x) J) a := by
  have h : MZ F K (xv x) a I J ≤ (omB ℂ K (rB ℂ K (xv x) J) a).comap ((bil τ ρ).flip v) :=
    Submodule.map₂_le.2 fun m _ n hn => by
      show bil τ ρ (m ⊗ₜ n) v ∈ omB ℂ K (rB ℂ K (xv x) J) a
      rw [bil_tmul]
      exact Submodule.smul_mem _ _ hn
  exact h he

private theorem bil_face (hc : IsFinCover ℂ K (xv x)) {τ : DR ℂ K →ₗ[K] K} (hτ : IsTop ℂ K (xv x) τ)
    {ρ : F →ₗ[ℂ] ℂ} (hρ : IsRes ℂ (xv x) ρ) {a : ℕ} (had : a ≤ d) (i : Fin (d + 1))
    (hne : (Finset.univ.erase i).Nonempty) (J : Finset (Fin (d + 1)))
    {e : DR ℂ K ⊗[ℂ] DR ℂ K} (he : e ∈ MZ F K (xv x) a (Finset.univ.erase i) J)
    {v : DR ℂ K} (hv : v ∈ omB ℂ K (rB ℂ K (xv x) (Finset.univ.erase i)) a) :
    bil τ ρ e v = 0 := by
  have hdeg : v ∈ ⋀[K]^a Ω[K⁄ℂ] := ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties ℂ K _ a 0).2.1 v hv).2.2.1
  have h : MZ F K (xv x) a (Finset.univ.erase i) J ≤ LinearMap.ker ((bil τ ρ).flip v) :=
    Submodule.map₂_le.2 fun m hm n _ => by
      show bil τ ρ (m ⊗ₜ n) v = 0
      rw [bil_tmul]
      have hmem := (GlobalTheory.T.twistedDual_regularForms_finiteCover ℂ F K d (xv x) hc τ hτ (Finset.univ.erase i) hne (d - a) a
        (by omega) v hdeg).2 hv m hm
      rw [GlobalTheory.T.residue_functional_vanishes_on_omega_forms ℂ F d (xv x) hc.pd ρ hρ i _ hne (Finset.notMem_erase i _) _ hmem, zero_smul]
  exact h he

private theorem top_zero (hc : IsFinCover ℂ K (xv x)) {τ : DR ℂ K →ₗ[K] K} (hτ : IsTop ℂ K (xv x) τ)
    {ρ : F →ₗ[ℂ] ℂ} (hρ : IsRes ℂ (xv x) ρ) {a p : ℕ} (had : a ≤ d)
    (monoM : ∀ I I' J J' : Finset (Fin (d + 1)), I.Nonempty → J.Nonempty → I ⊆ I' → J ⊆ J' →
      MZ F K (xv x) a I J ≤ MZ F K (xv x) a I' J')
    (monoB : ∀ s t : Finset (Fin (d + 1)), s.Nonempty → s ⊆ t →
      omB ℂ K (rB ℂ K (xv x) s) a ≤ omB ℂ K (rB ℂ K (xv x) t) a)
    (α : Finset (Fin (d + 1)) → DR ℂ K) (hα : α ∈ (omCx (rB ℂ K (xv x)) a).Z p)
    (J : Finset (Fin (d + 1))) (u : Finset (Fin (d + 1)) → DR ℂ K ⊗[ℂ] DR ℂ K)
    (hJ : J.Nonempty)
    (hu : u ∈ (cech fun I => MZ F K (xv x) a I J).C ((d : ℤ) - p - 1)) :
    ∑ i, bil τ ρ (deltaL ℂ _ _ u (Finset.univ.filter (· ≤ i))) (α (Finset.univ.filter (i ≤ ·))) = 0 := by
  obtain ⟨hαC, hαZ⟩ := Submodule.mem_inf.1 hα
  have hαZ' : deltaL ℂ _ _ α = 0 := LinearMap.mem_ker.1 hαZ
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun φ => ?_
  have adj := GlobalTheory.T.cechDifferential_adjoint_cupProductPairing ℂ d _ _ (fun I => MZ F K (xv x) a I J)
    (fun I => omB ℂ K (rB ℂ K (xv x) I) a) ((bil τ ρ).compr₂ φ)
    (fun s t hs hst => monoM s t J J hs hJ hst subset_rfl) monoB
    (fun i hne e he v hv => by
      show φ (bil τ ρ e v) = 0
      rw [bil_face hc hτ hρ had i hne J he hv, map_zero])
  obtain ⟨ε, hε⟩ := adj ((d : ℤ) - p - 1)
  have h1 := hε u hu α (by
    have : (d : ℤ) - ((d : ℤ) - p - 1) - 1 = p := by ring
    rw [this]; exact hαC)
  have h2 : (cech fun I => omB ℂ K (rB ℂ K (xv x) I) a).D α = 0 := hαZ'
  rw [h2, map_zero, smul_zero] at h1
  have h3 : cupPair ((bil τ ρ).compr₂ φ) ((cech fun I => MZ F K (xv x) a I J).D u) α =
      φ (∑ i, bil τ ρ (deltaL ℂ _ _ u (Finset.univ.filter (· ≤ i))) (α (Finset.univ.filter (i ≤ ·)))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [cupPair, cech, map_sum]
  rw [← h3]; exact h1

end UpperTheory.Gal.productCup_of_system.RCT

open UpperTheory.Gal.productCup_of_system.RCT in
theorem UpperTheory.Gal.productCup_of_system.rCupTop_of :
    WdUni → GoodZ → RCupTop := by
  intro hW hG F K _ _ _ _ _ _ d x hc τ hτ ρ hρ a p had t ht α hα
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 ht
  have hgood := hG F K d x hc a
  have monoM : ∀ I I' J J' : Finset (Fin (d + 1)), I.Nonempty → J.Nonempty → I ⊆ I' → J ⊆ J' →
      MZ F K (xv x) a I J ≤ MZ F K (xv x) a I' J' := hgood.1.monoM
  have monoB := hgood.2.2
  have hU := fun I J => hW (Fin (d + 1)) (Fin (d + 1)) (DR ℂ K ⊗[ℂ] DR ℂ K) (fun _ => 1) y I J
  have hs : ∀ s, y s ∈ (if (s.card : ℤ) = ((d : ℤ) + 2 - 1) then mixF (sysZ K x a).M s else ⊥ :
      Submodule ℂ (DR ℂ K ⊗[ℂ] DR ℂ K)) := fun s => (Submodule.mem_pi.1 hy) s (Set.mem_univ _)
  have hy0 : ∀ I J : Finset (Fin (d + 1)), ¬ (I.Nonempty ∧ J.Nonempty ∧ I.card + J.card = d + 1) →
      y (uni I J) = 0 := by
    intro I J hn
    obtain ⟨e1, e2, e3, -⟩ := (hU I J).2
    have h := hs (uni I J)
    rw [e3] at h
    by_cases hcd : (((I.card + J.card : ℕ)) : ℤ) = (d : ℤ) + 2 - 1
    · rw [if_pos hcd, mixF, e1, e2, if_neg (fun hh => hn ⟨hh.1, hh.2, by omega⟩)] at h
      exact (Submodule.mem_bot ℂ).1 h
    · rw [if_neg hcd] at h
      exact (Submodule.mem_bot ℂ).1 h
  have hy1 : ∀ I J : Finset (Fin (d + 1)), y (uni I J) ∈ MZ F K (xv x) a I J := by
    intro I J
    by_cases hn : I.Nonempty ∧ J.Nonempty ∧ I.card + J.card = d + 1
    · obtain ⟨e1, e2, e3, -⟩ := (hU I J).2
      have h := hs (uni I J)
      rw [e3, if_pos (by omega), mixF, e1, e2, if_pos ⟨hn.1, hn.2.1⟩] at h
      exact h
    · rw [hy0 I J hn]; exact Submodule.zero_mem _
  have hα0 : ∀ s : Finset (Fin (d + 1)), s.card ≠ p + 1 → α s = 0 := by
    intro s hsc
    have h : α s ∈ (if s.Nonempty ∧ (s.card : ℤ) = (p : ℤ) + 1 then omB ℂ K (rB ℂ K (xv x) s) a else ⊥ :
        Submodule ℂ (DR ℂ K)) := (Submodule.mem_pi.1 (Submodule.mem_inf.1 hα).1) s (Set.mem_univ _)
    rw [if_neg (fun hh => hsc (by omega))] at h
    exact (Submodule.mem_bot ℂ).1 h
  refine Submodule.mem_map.2 ⟨fun J' => ∑ i, ((-1 : ℤ) ^ (Finset.univ.filter (· ≤ i)).card) •
    bil τ ρ (y (uni (Finset.univ.filter (· ≤ i)) J')) (α (Finset.univ.filter (i ≤ ·))), ?_, ?_⟩
  · refine Submodule.mem_pi.2 fun J' _ => ?_
    show _ ∈ (if J'.Nonempty ∧ (J'.card : ℤ) = (p : ℤ) - 1 + 1 then omB ℂ K (rB ℂ K (xv x) J') a else ⊥ :
      Submodule ℂ (DR ℂ K))
    split_ifs with hJ
    · exact Submodule.sum_mem _ fun i _ => Submodule.smul_of_tower_mem _ _ (bil_mem τ ρ (hy1 _ _) _)
    · refine (Submodule.mem_bot ℂ).2 (Finset.sum_eq_zero fun i _ => ?_)
      have hcf := card_filters i
      by_cases h2 : (Finset.univ.filter (i ≤ ·)).card = p + 1
      · rw [hy0 _ J' ?_, map_zero, LinearMap.zero_apply, smul_zero]
        rintro ⟨-, hJn, hcard⟩
        exact hJ ⟨hJn, by omega⟩
      · rw [hα0 _ h2, map_zero, smul_zero]
  · funext J
    have hD : ∀ i, (sysZ K x a).mix.D y (uni (Finset.univ.filter (· ≤ i)) J) =
        deltaL ℂ _ _ (fun b' => y (uni b' J)) (Finset.univ.filter (· ≤ i)) +
        ((-1 : ℤ) ^ (Finset.univ.filter (· ≤ i)).card) •
          deltaL ℂ _ _ (fun L' => y (uni (Finset.univ.filter (· ≤ i)) L')) J := by
      intro i
      have h := (hU (Finset.univ.filter (· ≤ i)) J).1
      refine Eq.trans h ?_
      rw [wd_one, wd_one]
    have hI : ∑ i, bil τ ρ (deltaL ℂ _ _ (fun b' => y (uni b' J)) (Finset.univ.filter (· ≤ i)))
        (α (Finset.univ.filter (i ≤ ·))) = 0 := by
      by_cases hJ : J.Nonempty ∧ J.card = p + 1
      · refine top_zero hc hτ hρ had monoM monoB α hα J _ hJ.1 ?_
        refine Submodule.mem_pi.2 fun s _ => ?_
        show _ ∈ (if s.Nonempty ∧ (s.card : ℤ) = (d : ℤ) - p - 1 + 1 then MZ F K (xv x) a s J else ⊥ :
          Submodule ℂ (DR ℂ K ⊗[ℂ] DR ℂ K))
        split_ifs with hsc
        · exact hy1 s J
        · exact (Submodule.mem_bot ℂ).2 (hy0 s J fun hh => hsc ⟨hh.1, by omega⟩)
      · refine Finset.sum_eq_zero fun i _ => ?_
        have hcf := card_filters i
        by_cases h2 : (Finset.univ.filter (i ≤ ·)).card = p + 1
        · have hz : deltaL ℂ _ _ (fun b' => y (uni b' J)) (Finset.univ.filter (· ≤ i)) = 0 := by
            show ∑ s ∈ Finset.univ.filter (· ≤ i), GlobalTheory.cubeSign (Finset.univ.filter (· ≤ i)) s •
              y (uni ((Finset.univ.filter (· ≤ i)).erase s) J) = 0
            refine Finset.sum_eq_zero fun s hs' => ?_
            rw [hy0 _ J ?_, smul_zero]
            rintro ⟨-, hJn, hcard⟩
            rw [Finset.card_erase_of_mem hs'] at hcard
            have := Finset.card_pos.2 ⟨s, hs'⟩
            exact hJ ⟨hJn, by omega⟩
          rw [hz, map_zero, LinearMap.zero_apply]
        · rw [hα0 _ h2, map_zero]
    have hB : ∀ i, bil τ ρ (((-1 : ℤ) ^ (Finset.univ.filter (· ≤ i)).card) •
          deltaL ℂ _ _ (fun L' => y (uni (Finset.univ.filter (· ≤ i)) L')) J) (α (Finset.univ.filter (i ≤ ·))) =
        ∑ j ∈ J, GlobalTheory.cubeSign J j • (((-1 : ℤ) ^ (Finset.univ.filter (· ≤ i)).card) •
          bil τ ρ (y (uni (Finset.univ.filter (· ≤ i)) (J.erase j))) (α (Finset.univ.filter (i ≤ ·)))) := by
      intro i
      show (bil τ ρ).flip _ (((-1 : ℤ) ^ (Finset.univ.filter (· ≤ i)).card) •
        ∑ j ∈ J, GlobalTheory.cubeSign J j • y (uni (Finset.univ.filter (· ≤ i)) (J.erase j))) = _
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Units.smul_def, map_zsmul, map_sum, LinearMap.flip_apply, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
    show ∑ j ∈ J, GlobalTheory.cubeSign J j • ∑ i, ((-1 : ℤ) ^ (Finset.univ.filter (· ≤ i)).card) •
        bil τ ρ (y (uni (Finset.univ.filter (· ≤ i)) (J.erase j))) (α (Finset.univ.filter (i ≤ ·))) =
      resP (DR ℂ K) ρ (∑ i, muP F K τ ((sysZ K x a).mix.D y (uni (Finset.univ.filter (· ≤ i)) J))
        (α (Finset.univ.filter (i ≤ ·))))
    have hR : resP (DR ℂ K) ρ (∑ i, muP F K τ ((sysZ K x a).mix.D y (uni (Finset.univ.filter (· ≤ i)) J))
        (α (Finset.univ.filter (i ≤ ·)))) =
        ∑ i, bil τ ρ ((sysZ K x a).mix.D y (uni (Finset.univ.filter (· ≤ i)) J))
          (α (Finset.univ.filter (i ≤ ·))) := map_sum _ _ _
    rw [hR]
    simp only [hD, map_add (f := _), LinearMap.add_apply, Finset.sum_add_distrib, hI, zero_add, hB]
    rw [Finset.sum_comm]
    simp only [Finset.smul_sum]
end
