module

public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatDetHMapInjectiveIsometry
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeSeenInDefiniteSpaceDetRankIndex
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeSeenInDefiniteSpaceDetRankIndex
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

namespace GlobalTheory.LoopC.SeenIso

section General

variable {K U V W : Type} [Field K] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem exists_proj [StarRing K] {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {h0 : W →ₗ⋆[K] W →ₗ[K] K}
    (ι : W →ₗ[K] V) (hι : ∀ x y, h (ι x) (ι y) = h0 x y) (X H : Submodule K V)
    (hWX : ∀ w, ι w ∈ X → w = 0)
    (hXι : ∀ x ∈ X, ∀ w, h x (ι w) = 0) (hXH : ∀ x ∈ X, ∀ v ∈ H, h x v = 0)
    (hsp : ∀ v ∈ H, ∃ w, v - ι w ∈ X) (hHX : H ⊓ X = ⊥) :
    ∃ π : H →ₗ[K] W, Function.Injective π ∧ (∀ x y, h0 (π x) (π y) = h x y) ∧
      ∀ x : H, (x : V) - ι (π x) ∈ X := by
  obtain ⟨g, hg⟩ := (X.mkQ ∘ₗ ι).exists_leftInverse_of_injective (by
    rw [eq_bot_iff]
    intro w hw
    exact hWX w ((Submodule.Quotient.mk_eq_zero X).1 hw))
  let p : V →ₗ[K] W := g ∘ₗ X.mkQ
  have hpι : ∀ w, p (ι w) = w := fun w => LinearMap.congr_fun hg w
  have hpX : ∀ u ∈ X, p u = 0 := fun u hu => by
    have : X.mkQ u = 0 := (Submodule.Quotient.mk_eq_zero X).2 hu
    simp only [p, LinearMap.comp_apply, this, map_zero]
  have hF : ∀ x : H, (x : V) - ι (p x) ∈ X := fun x => by
    obtain ⟨w, hw⟩ := hsp x x.2
    have := hpX _ hw
    rw [map_sub, hpι, sub_eq_zero] at this
    rwa [this]
  refine ⟨p ∘ₗ H.subtype, ?_, fun x y => ?_, hF⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    have h1 : p x = 0 := hx
    have h2 := hF x
    rw [h1, map_zero, sub_zero] at h2
    have h3 : (x : V) ∈ H ⊓ X := ⟨x.2, h2⟩
    rw [hHX] at h3
    exact Subtype.ext h3
  · change h0 (p x) (p y) = _
    have a := hXH _ (hF x) _ y.2
    have b := hXι _ (hF y) (p x)
    have c : h (ι (p x)) ((y : V) - ι (p y)) = 0 := by rw [← hs.eq, b, map_zero]
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at a
    rw [map_sub, sub_eq_zero] at c
    rw [a, c, hι]

variable [NumberField K] [Module (𝓞 K) U] [IsScalarTower (𝓞 K) K U] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem finrank_span_map (i : U →ₗ[K] V) (hi : Function.Injective i) (N : Submodule (𝓞 K) U) :
    finrank K (Submodule.span K ((N.map (i.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V)) =
      finrank K (Submodule.span K (N : Set U)) := by
  have : ((N.map (i.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V) = i '' (N : Set U) := rfl
  rw [this, ← Submodule.map_span]
  exact (Submodule.equivMapOfInjective i hi _).finrank_eq.symm

theorem card_quot_map (i : U →ₗ[K] V) (hi : Function.Injective i) (A B : Submodule (𝓞 K) U) :
    Nat.card (↥(A.map (i.restrictScalars (𝓞 K))) ⧸
      (B.map (i.restrictScalars (𝓞 K))).comap (A.map (i.restrictScalars (𝓞 K))).subtype) =
      Nat.card (A ⧸ B.comap A.subtype) := by
  have := AddSubgroup.relIndex_map_map_of_injective (f := i.toAddMonoidHom) B.toAddSubgroup A.toAddSubgroup hi
  exact this

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem main : ∀ (D : D7) (T : D.host.E) (F : Fg D T) (H : Submodule D.host.E (hS D).V), WHyp D F (Wsp D) → H ≤ orth (hS D) (Xplus F) → H ⊓ Xsp F = ⊥ → ∀ N N' : LatV D, N ≤ toO (hS D) H → N' ≤ toO (hS D) H → detW D (seen D F N) = latDet (hS D) N ∧ rkW D (seen D F N) = finrank D.host.E (spanE (hS D) N) ∧ idxW D (seen D F N) (seen D F N') = idx (hS D) N N' := by
  intro D T F H hW hH hHX N N' hN hN'
  have hm : 0 < D.R.m := lt_of_lt_of_le (by norm_num) D.R.two_le_m
  have hiso : ∀ x y, (hS D).hT (D.sp.iXY 0 x) (D.sp.iXY 0 y) = (D.sp.X 0).hT x y := D.sp.iXY_isom 0 hm
  have hXι : ∀ x ∈ Xsp F, ∀ w, (hS D).hT x (D.sp.iXY 0 w) = 0 := fun x hx w =>
    (Formalism.MainNotions.mem_orth_iff _ _).1 (hW.1.le (Submodule.mem_sup_left ⟨w, rfl⟩)) x (Submodule.mem_sup_left hx)
  have hWX : ∀ w, D.sp.iXY 0 w ∈ Xsp F → w = 0 := fun w hw =>
    (D.sp.X 0).nondeg.1 w fun y => by rw [← hiso]; exact hXι _ hw y
  obtain ⟨π, hinj, hπ, hF⟩ := exists_proj (hS D).herm (D.sp.iXY 0) hiso (Xsp F) H hWX hXι
    (fun x hx v hv => (Formalism.MainNotions.mem_orth_iff _ _).1 (hH hv) x (Submodule.mem_sup_left hx))
    (fun v hv => by
      obtain ⟨_, ⟨w, rfl⟩, x, hx, rfl⟩ := Submodule.mem_sup.1 (hW.1.ge (hH hv))
      exact ⟨w, by simpa using hx⟩) hHX
  have key : ∀ M : LatV D, M ≤ toO (hS D) H → ∃ M₀ : Submodule (𝓞 D.host.E) H,
      M = M₀.map (H.subtype.restrictScalars (𝓞 D.host.E)) ∧
        seen D F M = M₀.map (π.restrictScalars (𝓞 D.host.E)) := by
    intro M hM
    refine ⟨M.comap (H.subtype.restrictScalars (𝓞 D.host.E)), ?_, ?_⟩
    · ext x
      constructor
      · intro hx
        exact ⟨⟨x, hM hx⟩, hx, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact hy
    · ext w
      constructor
      · intro hw
        obtain ⟨l, hl, x, hx, e⟩ := Submodule.mem_sup.1 hw
        refine ⟨⟨l, hM hl⟩, hl, ?_⟩
        have e' : l + x = D.sp.iXY 0 w := e
        have h1 := (Xsp F).add_mem (hF ⟨l, hM hl⟩) hx
        have h2 : w - π ⟨l, hM hl⟩ = 0 := hWX _ (by
          rw [map_sub, ← e']
          convert h1 using 1
          abel)
        exact (sub_eq_zero.1 h2).symm
      · rintro ⟨y, hy, rfl⟩
        refine Submodule.mem_sup.2 ⟨y, hy, _, (Xsp F).neg_mem (hF y), ?_⟩
        change _ = D.sp.iXY 0 (π y)
        abel
  obtain ⟨A, rfl, a⟩ := key N hN
  obtain ⟨B, rfl, b⟩ := key N' hN'
  rw [a, b]
  refine ⟨?_, ?_, ?_⟩
  · exact (GlobalTheory.T.latDetH_map_injective_isometry _ _ _ ((hS D).hT.domRestrict₁₂ H H) _ π hinj hπ A).trans
      (GlobalTheory.T.latDetH_map_injective_isometry _ _ _ ((hS D).hT.domRestrict₁₂ H H) _ H.subtype H.injective_subtype (fun _ _ => rfl) A).symm
  · exact (finrank_span_map π hinj A).trans (finrank_span_map H.subtype H.injective_subtype A).symm
  · exact (card_quot_map π hinj A B).trans (card_quot_map H.subtype H.injective_subtype A B).symm

end GlobalTheory.LoopC.SeenIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeSeenInDefiniteSpaceDetRankIndexStatement
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeSeenInDefiniteSpace_det_rank_index : ∀ (D : D7) (T : D.host.E) (F : Fg D T) (H : Submodule D.host.E (hS D).V), WHyp D F (Wsp D) → H ≤ orth (hS D) (Xplus F) → H ⊓ Xsp F = ⊥ → ∀ N N' : LatV D, N ≤ toO (hS D) H → N' ≤ toO (hS D) H → detW D (seen D F N) = latDet (hS D) N ∧ rkW D (seen D F N) = finrank D.host.E (spanE (hS D) N) ∧ idxW D (seen D F N) (seen D F N') = idx (hS D) N N' := by
  first | exact @GlobalTheory.LoopC.SeenIso.main | exact GlobalTheory.LoopC.SeenIso.main | (intros; apply GlobalTheory.LoopC.SeenIso.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralUnipotentLiftCorner
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralUnipotentLiftCorner
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.LiftCorner

lemma hpk_eI (k r : ℕ) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) j = if j = esI k r a then 1 else 0 := by
  have ha := a.isLt
  have hj := j.isLt
  simp only [Hpk, eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

lemma herm_bvec (k r : ℕ) (a : Fin r) (j : Fin (2 * r + k + 1)) (x : ℂ) :
    herm (Hpk k r) (bvec j) (x • bvec (eI k r a)) = star x * (if j = esI k r a then 1 else 0) := by
  rw [← hpk_eI]
  simp [herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply, apply_ite (starRingEnd ℂ), ite_mul]

lemma form_smul_left {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (u v : Fin n → E) (x : E) : form σ J (x • u) v = x * form σ J u v := by
  simp [form, Matrix.mulVec_smul, dotProduct_smul]

lemma form_smul_right {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (u v : Fin n → E) (x : E) : form σ J u (x • v) = σ x * form σ J u v := by
  simp [form, dotProduct, Finset.mul_sum, mul_assoc]

lemma form_cols {E : Type} [Field E] (σ : E →+* E) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (P : Matrix (Fin n) (Fin m) E) (x z : Fin m) :
    form σ J (fun i => P i z) (fun i => P i x) = pairM σ J P P x z := by
  simp only [form, pairM, cT, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply,
    Matrix.map_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem lift_corner : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (p : UTr r) (l : InfinitePlace E → ℂ), l ∈ ideLat (dInv E (r - p.1.1.val) * dInv E (r - p.1.2.val)) (s p.1.1 * s p.1.2) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inr (.inr (.inl p))) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inr (.inr (.inl p))) → degB r β ≤ degB r (.inr (.inr (.inl p))) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV p l hl
  obtain ⟨⟨a, b⟩, hab⟩ := p
  have hab' : a.val < b.val := hab
  have ha := a.isLt
  have hb := b.isLt
  obtain ⟨-, -, -, -, hFr, -, hLat, -, -, hAd⟩ := id hV
  obtain ⟨c, hc, hlc⟩ := hl
  dsimp only at hc hlc
  let e : Fin (2 * r + k + 1) → E := fun i => P i a.castSucc
  let y : Fin (2 * r + k + 1) → E := c • e
  have hiso : ∀ x z : Fin r,
      form (σ : E →+* E) J (fun i => P i z.castSucc) (fun i => P i x.castSucc) = 0 := by
    intro x z
    rw [form_cols, hFr.2]
    simp [TF, Matrix.diagonal_apply, Fin.castSucc_ne_last]
  have hd : ∀ j, dInv E j ≠ 0 := fun j =>
    pow_ne_zero _ (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot))
  have hG : rowE (σ : E →+* E) J (fun i => P i b.castSucc) y 0 ∈ GN (σ : E →+* E) J Λ P := by
    refine GlobalTheory.T.rowE_mem_GN_of_form_add_trace_eq_zero F E σ k r J Λ P f T A s hV b y 0 ?_ ?_ ?_ ?_
    · intro c' _
      show form _ J (c • e) _ = 0
      rw [form_smul_left, hiso, mul_zero]
    · show form _ J (c • e) (c • e) + 0 + (σ : E →+* E) 0 = 0
      rw [form_smul_left, form_smul_right, hiso]
      simp
    · intro c' hc'
      have hmem : c' * c ∈ dInv E (r - a.val) := by
        have := FractionalIdeal.mul_mem_mul hc' hc
        rwa [mul_comm (dInv E (r - a.val)), ← mul_assoc, inv_mul_cancel₀ (hd _), one_mul] at this
      have hy : c' • y = (c' * c) • e := by
        simp only [y, smul_smul]
      rw [hy]
      apply hLat
      apply Submodule.subset_span
      refine ⟨Fin.castAdd r a.castSucc, c' * c, ?_, ?_⟩
      · simpa [id1, Fin.append_left] using hmem
      · ext i
        simp [sideM, Fin.append_left, e]
    · exact (dInv E _ : Submodule (𝓞 E) E).zero_mem
  have hAy : ∀ w : InfinitePlace E, (A w).mulVec (fun l => w.embedding (y l)) =
      (w.embedding c * (s a : ℂ)) • bvec (eI k r a) := by
    intro w
    have h1 : (fun l => w.embedding (y l)) = w.embedding c • fun l => w.embedding (P l a.castSucc) := by
      ext l
      simp [y, e]
    rw [h1, Matrix.mulVec_smul, (hAd w a).1, smul_smul]
  have hent : ∀ w i j, gM A (rowE (σ : E →+* E) J (fun i => P i b.castSucc) y 0) w i j =
      (if i = j then 1 else 0) +
        (if i = eI k r a ∧ j = esI k r b then (s a : ℂ) * s b * w.embedding c else 0) -
        (if i = eI k r b ∧ j = esI k r a then (s b : ℂ) * star (w.embedding c * (s a : ℂ)) else 0) := by
    intro w i j
    rw [GlobalTheory.T.rowIsometry_entries_in_modelCoordinates F E σ k r J Λ P f T A s hV b y 0 w i j, hAy w, herm_bvec]
    simp only [bvec, Pi.smul_apply, Pi.single_apply, smul_eq_mul, map_zero, mul_zero, add_zero, ite_and]
    split_ifs <;> ring
  refine ⟨_, hG, fun w => ?_, fun β hβ _ w => ?_⟩
  · show gM A _ w (eI k r a) (esI k r b) = l w
    rw [hent, hlc w]
    have h1 : eI k r a ≠ esI k r b := by simp [Fin.ext_iff, eI, esI]; omega
    have h2 : eI k r a ≠ eI k r b := by simp [Fin.ext_iff, eI]; omega
    simp [h1, h2]
    first | done | (push_cast; ring)
  · rcases β with p' | a' | p' | a'
    · obtain ⟨⟨a', b'⟩, h'⟩ := p'
      have h'' : a'.val < b'.val := h'
      show gM A _ w (eI k r a') (eI k r b') = 0
      rw [hent]
      simp only [eI, esI, Fin.ext_iff]
      split_ifs <;> first | omega | simp
    · show (fun j' => gM A _ w (eI k r a') (wI k r j')) = (0 : Fin (k + 1) → ℂ)
      funext j'
      have := j'.isLt
      rw [hent]
      simp only [eI, esI, wI, Fin.ext_iff]
      split_ifs <;> first | omega | simp
    · obtain ⟨⟨a', b'⟩, h'⟩ := p'
      have h'' : a'.val < b'.val := h'
      have hne : ¬ (a'.val = a.val ∧ b'.val = b.val) := by
        rintro ⟨e1, e2⟩
        obtain rfl := Fin.ext e1
        obtain rfl := Fin.ext e2
        exact hβ rfl
      show gM A _ w (eI k r a') (esI k r b') = 0
      rw [hent]
      simp only [eI, esI, Fin.ext_iff]
      split_ifs <;> first | omega | simp
    · show (gM A _ w (eI k r a') (esI k r a')).im = 0
      rw [hent]
      simp only [eI, esI, Fin.ext_iff]
      split_ifs <;> first | omega | simp

end GlobalTheory.SnMass.VolN.LiftCorner
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralUnipotentLiftCornerStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_unipotent_lift_corner : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (p : UTr r) (l : InfinitePlace E → ℂ), l ∈ ideLat (dInv E (r - p.1.1.val) * dInv E (r - p.1.2.val)) (s p.1.1 * s p.1.2) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inr (.inr (.inl p))) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inr (.inr (.inl p))) → degB r β ≤ degB r (.inr (.inr (.inl p))) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  first | exact @GlobalTheory.SnMass.VolN.LiftCorner.lift_corner | exact GlobalTheory.SnMass.VolN.LiftCorner.lift_corner | (intros; apply GlobalTheory.SnMass.VolN.LiftCorner.lift_corner <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralUnipotentLiftEntry
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralUnipotentLiftEntry
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.LiftEntry

theorem eI_inj {k r : ℕ} {a b : Fin r} : eI k r a = eI k r b ↔ a = b := by
  simp [eI, Fin.ext_iff]

theorem eI_ne_esI {k r : ℕ} (a b : Fin r) : eI k r a ≠ esI k r b := by
  simp only [eI, esI, ne_eq, Fin.ext_iff]; omega

theorem eI_ne_wI {k r : ℕ} (a : Fin r) (j : Fin (k + 1)) : eI k r a ≠ wI k r j := by
  simp only [eI, wI, ne_eq, Fin.ext_iff]; omega

theorem Hpk_esI {k r : ℕ} (b : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r b) j = if j = eI k r b then 1 else 0 := by
  simp only [Hpk, esI, eI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem herm_single {k r : ℕ} (b : Fin r) (c : ℂ) (j : Fin (2 * r + k + 1)) :
    herm (Hpk k r) (bvec j) (c • bvec (esI k r b)) = if j = eI k r b then star c else 0 := by
  simp only [herm, bvec, dotProduct, mulVec, Pi.star_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  rw [Finset.sum_eq_single (esI k r b)]
  · simp only [if_true, mul_one, star_mul', star_one]
    rw [Finset.sum_eq_single j]
    · simp [Hpk_esI]
    · intro m _ hm; simp [hm]
    · simp
  · intro m _ hm; simp [hm]
  · simp

theorem wI_ne_eI {k r : ℕ} (j : Fin (k + 1)) (a : Fin r) : wI k r j ≠ eI k r a := (eI_ne_wI a j).symm

theorem esI_ne_eI {k r : ℕ} (a b : Fin r) : esI k r a ≠ eI k r b := (eI_ne_esI b a).symm

end GlobalTheory.SnMass.VolN.LiftEntry

namespace GlobalTheory.SnMass.VolN.LiftEntry

theorem form_smul_left {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (c : E) (x z : Fin n → E) : form σ J (c • x) z = c * form σ J x z := by
  simp [form, mulVec_smul, dotProduct_smul]

theorem form_smul_right {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (c : E) (x z : Fin n → E) : form σ J x (c • z) = σ c * form σ J x z := by
  simp only [form, dotProduct, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem form_col {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} {a b : Type} [Fintype a] [Fintype b]
    (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) b E) (Y : Matrix (Fin n) a E) (i : a) (j : b) :
    form σ J (fun l => X l j) (fun l => Y l i) = pairM σ J X Y i j := by
  simp only [form, pairM, cT, dotProduct, mulVec, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

end GlobalTheory.SnMass.VolN.LiftEntry

namespace GlobalTheory.SnMass.VolN.LiftEntry

theorem lift_entry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (p : UTr r) (l : InfinitePlace E → ℂ), l ∈ ideLat (dInv E (r - p.1.1.val) * (dInv E (r - p.1.2.val))⁻¹) (s p.1.1 / s p.1.2) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inl p) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inl p) → degB r β ≤ degB r (.inl p) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV p l hl
  have hV' := hV
  obtain ⟨hcm, -, -, -, -, hdu, htup, -, hs, had⟩ := hV'
  have hi : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    change τ (σ (σ x)) = _
    rw [hcm.2.2.2, hcm.2.2.2, star_star]
  obtain ⟨u, hu, hlu⟩ := hl
  obtain ⟨⟨a, b⟩, hab⟩ := p
  simp only at hu hlu hab ⊢
  set y : Fin (2 * r + k + 1) → E := (-(σ u)) • fun i => f i b with hy
  refine ⟨rowE (σ : E →+* E) J (fun i => P i a.castSucc) y 0, ?_, ?_⟩
  · refine GlobalTheory.T.rowE_mem_GN_of_form_add_trace_eq_zero F E σ k r J Λ P f T A s hV a y 0 (fun c hc => ?_) ?_ (fun c hc => ?_)
      (FractionalIdeal.zero_mem _)
    · rw [hy, form_smul_left, form_col, hdu.1]
      have : c.castSucc ≠ b.castSucc := fun h => absurd (Fin.castSucc_injective _ h ▸ hc) (not_le.2 hab)
      simp [this]
    · rw [hy, form_smul_left, form_smul_right, form_col, hdu.2]
      simp
    · have hsu : (σ : E →+* E) u ∈ dInv E (r - a.val) * (dInv E (r - b.val))⁻¹ :=
        (GlobalTheory.SnMass.FrameDual.Stab.mul (GlobalTheory.SnMass.FrameDual.stab_dInv hi _)
          ((GlobalTheory.SnMass.FrameDual.stab_dInv hi _).inv hi (GlobalTheory.SnMass.FrameDual.dInv_ne_zero _))) u hu
      have hm : c * σ u ∈ (dInv E (r - b.val))⁻¹ := by
        have := FractionalIdeal.mul_mem_mul hc hsu
        rwa [← mul_assoc, inv_mul_cancel₀ (GlobalTheory.SnMass.FrameDual.dInv_ne_zero _), one_mul] at this
      have e : c • y = (-(c * σ u)) • fun i => sideM P f i (Fin.natAdd (r + 1) b) := by
        ext i; simp [hy, sideM, mul_comm, mul_left_comm]
      rw [e]
      refine htup (Submodule.subset_span ⟨Fin.natAdd (r + 1) b, -(c * σ u), ?_, rfl⟩)
      rw [GlobalTheory.SnMass.FrameDual.frameDualTupleIdeals_natAdd]
      exact Submodule.neg_mem _ hm
  · have hv : ∀ w : InfinitePlace E, (A w).mulVec (fun l => w.embedding (y l)) =
        (-(star (w.embedding u)) * ((s b)⁻¹ : ℂ)) • bvec (esI k r b) := by
      intro w
      have e : (fun l => w.embedding (y l)) = (-(w.embedding (σ u))) • fun l => w.embedding (f l b) := by
        ext l; simp [hy]
      rw [e, mulVec_smul, (had w b).2, smul_smul, hcm.2.2.2]
    have key : ∀ (w : InfinitePlace E) (a' : Fin r) (j : Fin (2 * r + k + 1)),
        gM A (rowE (σ : E →+* E) J (fun i => P i a.castSucc) y 0) w (eI k r a') j =
          (if eI k r a' = j then 1 else 0) - (if a' = a ∧ j = eI k r b then
            (s a : ℂ) * star (-(star (w.embedding u)) * ((s b)⁻¹ : ℂ)) else 0) := by
      intro w a' j
      rw [GlobalTheory.T.rowIsometry_entries_in_modelCoordinates F E σ k r J Λ P f T A s hV a y 0 w, hv w, herm_single]
      simp [bvec, Pi.single_apply, eI_ne_esI, eI_inj, ite_and]
    refine ⟨fun w => ?_, fun β hβ _ w => ?_⟩
    · change gM A _ w (eI k r a) (eI k r b) = l w
      rw [key, hlu]
      simp only [eI_inj, hab.ne, if_false, true_and, if_true, zero_sub]
      push_cast
      simp only [star_mul', star_neg, star_star, Complex.star_def, Complex.conj_ofReal, map_inv₀, Complex.conj_conj]
      ring
    · rcases β with ⟨⟨a', b'⟩, hab'⟩ | a' | ⟨⟨a', b'⟩, hab'⟩ | a'
      · change gM A _ w (eI k r a') (eI k r b') = 0
        rw [key]
        have hne : ¬ (a' = a ∧ eI k r b' = eI k r b) := by
          rintro ⟨rfl, h⟩
          obtain rfl := eI_inj.1 h
          exact hβ rfl
        have hne' : a' ≠ b' := ne_of_lt hab'
        rw [if_neg hne, if_neg (fun h => hne' (eI_inj.1 h)), sub_zero]
      · change (fun j => gM A _ w (eI k r a') (wI k r j)) = (0 : Fin (k + 1) → ℂ)
        funext j
        rw [key]
        simp [eI_ne_wI, wI_ne_eI]
      · change gM A _ w (eI k r a') (esI k r b') = 0
        rw [key]
        simp [eI_ne_esI, esI_ne_eI]
      · change (gM A _ w (eI k r a') (esI k r a')).im = 0
        rw [key]
        simp [eI_ne_esI, esI_ne_eI]

end GlobalTheory.SnMass.VolN.LiftEntry
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralUnipotentLiftEntryStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_unipotent_lift_entry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (p : UTr r) (l : InfinitePlace E → ℂ), l ∈ ideLat (dInv E (r - p.1.1.val) * (dInv E (r - p.1.2.val))⁻¹) (s p.1.1 / s p.1.2) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inl p) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inl p) → degB r β ≤ degB r (.inl p) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  first | exact @GlobalTheory.SnMass.VolN.LiftEntry.lift_entry | exact GlobalTheory.SnMass.VolN.LiftEntry.lift_entry | (intros; apply GlobalTheory.SnMass.VolN.LiftEntry.lift_entry <;> assumption)
end
end
