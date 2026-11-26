module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LinearIndependentRatTupOfDetNeZero
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.FrameGram

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

theorem _root_.GlobalTheory.FrameGram.hE_swap (hσ : ∀ x, σ (σ x) = x)
    (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → E) :
    σ (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J y x) = _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J x y := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, _root_.Formalism.UG.P.hform_eq_dot, dotProduct, Matrix.mulVec, Function.comp, Finset.mul_sum, map_sum,
    map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe, hσ, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem linearIndependent_ratTup_of_det_ne_zero (R : Type) [CommRing R] [Algebra F R] {m : ℕ}
    (X : Fin m → Fin n → E) (hX : (gramE σ J X).det ≠ 0) :
    LinearIndependent (R ⊗[F] E) (ratTup (F := F) R X) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hcj : ∀ j, ∑ b, c b * inclR (F := F) R (X b j) = 0 := fun j => by
    simpa [Finset.sum_apply, ratTup] using congrFun hc j
  have hu : IsUnit ((gramE σ J X).map (inclR (F := F) R)).det := by
    have := (inclR (F := F) (E := E) R).map_det (gramE σ J X)
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]
    exact (IsUnit.mk0 _ hX).map _
  have h0 : ((gramE σ J X).map (inclR (F := F) R)).mulVec c = 0 := by
    funext a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, gramE, hE, Formalism.UG.hform, map_sum,
      map_mul, Finset.sum_mul, Pi.zero_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    have := congrArg (fun t => inclR (F := F) R ((σ : E →+* E) (X a i)) * inclR (F := F) R (J i j) * t)
      (hcj j)
    simp only [Finset.mul_sum, mul_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hinj := Matrix.mulVec_injective_of_isUnit
    ((Matrix.isUnit_iff_isUnit_det _).2 hu)
  have : c = 0 := hinj (by rw [h0, Matrix.mulVec_zero])
  exact fun b => congrFun this b

theorem det_gram_append_ne_zero (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) {r : ℕ}
    (y : Fin (r + 1) → Fin n → E) (f : Fin r → Fin n → E) (t : E) (ht : t ≠ 0)
    (hy : ∀ i j, gramE σ J y i j = if i = Fin.last r ∧ j = Fin.last r then t else 0)
    (hf : ∀ a b : Fin r, hE σ J (y a.castSucc) (f b) = if a = b then 1 else 0) :
    (gramE σ J (Fin.append y f)).det ≠ 0 := by
  intro h
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  have hy' : ∀ i j, hE σ J (y i) (y j) = if i = Fin.last r ∧ j = Fin.last r then t else 0 := hy
  have hf' : ∀ a b : Fin r, hE σ J (f a) (y b.castSucc) = if a = b then 1 else 0 := fun a b => by
    rw [← hE_swap hσ hJ, hf]
    by_cases hab : a = b
    · simp [hab]
    · simp [hab, Ne.symm hab]
  have row : ∀ k, ∑ b : Fin r, hE σ J (Fin.append y f k) (y b.castSucc) * c (Fin.castAdd r b.castSucc)
      + hE σ J (Fin.append y f k) (y (Fin.last r)) * c (Fin.castAdd r (Fin.last r))
      + ∑ b : Fin r, hE σ J (Fin.append y f k) (f b) * c (Fin.natAdd (r + 1) b) = 0 := fun k => by
    have := congrFun hc k
    simp only [Matrix.mulVec, dotProduct, gramE, Pi.zero_apply] at this
    rw [Fin.sum_univ_add, Fin.sum_univ_castSucc] at this
    simpa only [Fin.append_left, Fin.append_right] using this
  have h1 : ∀ a : Fin r, c (Fin.natAdd (r + 1) a) = 0 := fun a => by
    have := row (Fin.castAdd r a.castSucc)
    simpa [Fin.append_left, hy', hf, Fin.castSucc_ne_last] using this
  have h2 : c (Fin.castAdd r (Fin.last r)) = 0 := by
    have := row (Fin.castAdd r (Fin.last r))
    simpa [Fin.append_left, hy', h1, Fin.castSucc_ne_last, ht] using this
  have h3 : ∀ a : Fin r, c (Fin.castAdd r a.castSucc) = 0 := fun a => by
    have := row (Fin.natAdd (r + 1) a)
    simp only [Fin.append_right, hf', h1, h2] at this
    simpa using this
  apply hc0
  funext k
  refine Fin.addCases (fun i => ?_) (fun a => h1 a) k
  exact Fin.lastCases h2 h3 i

theorem gram_snoc (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) {r : ℕ}
    (e : Fin r → Fin n → E) (z : Fin n → E) (t : E) (he : ∀ a b, hE σ J (e a) (e b) = 0)
    (hez : ∀ a, hE σ J (e a) z = 0) (hz : hE σ J z z = t) (i j : Fin (r + 1)) :
    gramE σ J (Fin.snoc (α := fun _ => Fin n → E) e z) i j =
      if i = Fin.last r ∧ j = Fin.last r then t else 0 := by
  have hze : ∀ a, hE σ J z (e a) = 0 := fun a => by rw [← hE_swap hσ hJ, hez, map_zero]
  refine Fin.lastCases ?_ (fun a => ?_) i <;> refine Fin.lastCases ?_ (fun b => ?_) j <;>
    simp [gramE, he, hez, hze, hz, Fin.castSucc_ne_last]

end Alg

theorem _root_.GlobalTheory.FrameGram.conj_invol {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, hτ⟩ := h
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  apply τ.injective
  rw [hτ, hτ, star_star]

theorem frame_gram {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : IsHermND σ J) {r : ℕ} (y : Fin (r + 1) → Fin n → E) (f : Fin r → Fin n → E) (T : F)
    (hT : T ≠ 0)
    (hy : ∀ i j, gramE σ J y i j =
      if i = Fin.last r ∧ j = Fin.last r then algebraMap F E (-T) else 0)
    (hf : ∀ a b : Fin r, hE σ J (y a.castSucc) (f b) = if a = b then 1 else 0) :
    (gramE σ J (Fin.append y f)).det ≠ 0 ∧
      (∀ i j, σ (gramE σ J (Fin.append y f) j i) = gramE σ J (Fin.append y f) i j) ∧
      (∀ i j, σ (gramE σ J y j i) = gramE σ J y i j) ∧
      ∀ (R : Type) [CommRing R] [Algebra F R],
        LinearIndependent (R ⊗[F] E) (ratTup (F := F) R y) := by
  have hd := det_gram_append_ne_zero (conj_invol hσ) hJ.1 y f _
    ((map_ne_zero (algebraMap F E)).2 (neg_ne_zero.2 hT)) hy hf
  refine ⟨hd, fun i j => hE_swap (conj_invol hσ) hJ.1 _ _,
    fun i j => hE_swap (conj_invol hσ) hJ.1 _ _, fun R _ _ => ?_⟩
  have h := (linearIndependent_ratTup_of_det_ne_zero R _ hd).comp (Fin.castAdd r)
    (Fin.castAdd_injective _ _)
  have e : ratTup (F := F) R (Fin.append y f) ∘ Fin.castAdd r = ratTup (F := F) R y := by
    funext a i
    simp [ratTup, Fin.append_left]
  rwa [e] at h

theorem frame_gram_snoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : IsHermND σ J) {r : ℕ} (e f : Fin r → Fin n → E) (z : Fin n → E) (T : F) (hT : T ≠ 0)
    (he : ∀ a b, hE σ J (e a) (e b) = 0) (hez : ∀ a, hE σ J (e a) z = 0)
    (hz : hE σ J z z = algebraMap F E (-T))
    (hf : ∀ a b, hE σ J (e a) (f b) = if a = b then 1 else 0)
    (y : Fin (r + 1) → Fin n → E) (hy : y = Fin.snoc (α := fun _ => Fin n → E) e z)
    (w : Fin (r + 1 + r) → Fin n → E) (hw : w = Fin.append y f) :
    (gramE σ J w).det ≠ 0 ∧ (∀ i j, σ (gramE σ J w j i) = gramE σ J w i j) ∧
      (∀ i j, σ (gramE σ J y j i) = gramE σ J y i j) ∧
      (∀ i j, gramE σ J y i j =
        if i = Fin.last r ∧ j = Fin.last r then algebraMap F E (-T) else 0) ∧
      ∀ (R : Type) [CommRing R] [Algebra F R],
        LinearIndependent (R ⊗[F] E) (ratTup (F := F) R y) := by
  subst hw hy
  have hg := gram_snoc (conj_invol hσ) hJ.1 e z _ he hez hz
  obtain ⟨h1, h2, h3, h4⟩ := frame_gram hσ hJ _ f T hT hg (fun a b => by simpa using hf a b)
  exact ⟨h1, h2, h3, hg, h4⟩

end GlobalTheory.FrameGram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNondegenerateTupleComplementFixer
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNondegenerateTupleComplementFixer
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.FrameTuple

section Alg
variable {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {m : ℕ}

def tup (t : E) (g g' : Fin m → V) : Fin m ⊕ Fin m → V := Sum.elim g fun b => t • (g' b - g b)

theorem tup_indep {t θ : E} (h : θ * t = 1) {g g' : Fin m → V}
    (hli : LinearIndependent E (Sum.elim g g')) : LinearIndependent E (tup t g g') := by
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro c hc
  have key := hli (Sum.elim (fun a => c (Sum.inl a) - t * c (Sum.inr a)) fun b => t * c (Sum.inr b))
    (by
      rw [← hc]
      simp only [Fintype.sum_sum_type, tup, Sum.elim_inl, Sum.elim_inr, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [sub_smul, smul_sub, smul_smul, mul_comm t]
      abel)
  have h2 : ∀ b, c (Sum.inr b) = 0 := fun b => by
    have := key (Sum.inr b)
    simp only [Sum.elim_inr] at this
    linear_combination θ * this - c (Sum.inr b) * h
  rintro (a | b)
  · have := key (Sum.inl a)
    simpa [h2] using this
  · exact h2 b

theorem tup_span {t θ : E} (h : θ * t = 1) (g g' : Fin m → V) :
    Submodule.span E (Set.range (tup t g g')) = Submodule.span E (Set.range (Sum.elim g g')) := by
  apply le_antisymm <;> rw [Submodule.span_le]
  · rintro _ ⟨a | b, rfl⟩
    · exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩)
        (Submodule.subset_span ⟨Sum.inl b, rfl⟩))
  · rintro _ ⟨a | b, rfl⟩
    · exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    · have : Sum.elim g g' (Sum.inr b) = tup t g g' (Sum.inl b) + θ • tup t g g' (Sum.inr b) := by
        simp [tup, smul_smul, h]
      rw [this]
      exact Submodule.add_mem _ (Submodule.subset_span ⟨Sum.inl b, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩))

theorem tup_change (t : E) (g g' p p' : Fin m → V) (u u' : Matrix (Fin m) (Fin m) E)
    (hp : ∀ j, p j = ∑ i, u i j • g i) (hp' : ∀ j, p' j = ∑ i, u' i j • g' i) (j) :
    tup t p p' j = ∑ i, (Matrix.fromBlocks u (t • (u' - u)) 0 u') i j • tup t g g' i := by
  rcases j with j | j
  · simp [tup, Fintype.sum_sum_type, hp]
  · simp only [tup, Fintype.sum_sum_type, hp, hp', Sum.elim_inl, Sum.elim_inr,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, Finset.smul_sum, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    module

theorem det_uni (s : Matrix (Fin m) (Fin m) E) (h0 : ∀ i j, j < i → s i j = 0) (h1 : ∀ i, s i i = 1) :
    s.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => h0 i j hij)]
  simp [h1]

theorem comb_mul (g : Fin m → V) (s A : Matrix (Fin m) (Fin m) E) (j : Fin m) :
    ∑ i, A i j • ∑ l, s l i • g l = ∑ l, (s * A) l j • g l := by
  simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by rw [mul_comm]

end Alg

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem gram_unit (L : LocE F E) [IsArtinianRing E] {n m : ℕ} {H : Matrix (Fin n) (Fin n) E}
    (h : IsHerm L H) (x : Fin m → Fin n → E) (hli : LinearIndependent E x)
    (hd : Disjoint (Submodule.span E (Set.range x)) (perp L H (Submodule.span E (Set.range x)))) :
    IsUnit (gramT L H x).det := by
  have hinj : Function.Injective (Matrix.toLin' (gramT L H x)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro α hα
    have h1 : ∑ i, α i • x i = 0 := by
      refine Submodule.disjoint_def.1 hd _ ((Submodule.mem_span_range_iff_exists_fun E).2 ⟨α, rfl⟩) ?_
      rw [FrameBasic.mem_perp_span L h]
      intro j
      change FrameBasic.hfL L H (x j) _ = 0
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Eq.trans ?_ (congrFun hα j)
      simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, gramT, Matrix.of_apply, map_smul,
        smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    funext i
    exact Fintype.linearIndependent_iff.1 hli α h1 i
  have hb := IsArtinian.bijective_of_injective_endomorphism _ hinj
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.isUnit_toLin'_iff]
  exact (Module.End.isUnit_iff _).2 hb

theorem isLat_std (L : LocE F E) (n : ℕ) :
    IsLat L (Submodule.span L.O (Set.range fun i => (Pi.single i 1 : Fin n → E))) := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact Submodule.subset_span ⟨i, by simp⟩

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∃ x : Fin (2 * r + 2) → S.V, IsUnit (gramT L S.Hm x).det ∧ Submodule.span E (Set.range x) = S.ME ∧ S.H0 = fixG L S.Hm S.ME ∧ IsLat L (Submodule.span L.O (Set.range fun i => (Pi.single i 1 : S.V))) ∧ (∀ Mh, S.massSig Mh = sigMass L S.Hm S.ME (Submodule.span L.O (Set.range fun i => (Pi.single i 1 : S.V))) Mh) ∧ ∀ C, S.IsCls C → ∀ p ∈ C, ∃ (y : Fin (2 * r + 2) → S.V) (B : Matrix (Fin (2 * r + 2)) (Fin (2 * r + 2)) E), B.det * L.cj B.det = 1 ∧ y = rmul x B ∧ S.Mof p.1 p.2 = Submodule.span L.O (Set.range y) := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  obtain ⟨hli, hco, -, -, -, hth, -⟩ := FrameBasic.main L r k S
  obtain ⟨hN, hN', -⟩ := FrameOnto.unipotent_onto L r k S
  let e : Fin (r + 1) ⊕ Fin (r + 1) ≃ Fin (2 * r + 2) := finSumFinEquiv.trans (finCongr (by omega))
  have hθ : algebraMap F E S.th * algebraMap F E S.th⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hth, map_one]
  have hME : S.ME = Submodule.span E (Set.range (Sum.elim S.f S.f')) := by
    have hs : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := by
      ext i; simpa using i.2
    simp only [Frames.ME, Frames.spanTo, hs, Set.image_univ, Set.Sum.elim_range, Submodule.span_union]
  have hspan : Submodule.span E (Set.range (tup (algebraMap F E S.th⁻¹) S.f S.f' ∘ e.symm)) = S.ME := by
    rw [e.symm.surjective.range_comp, tup_span hθ, hME]
  refine ⟨tup (algebraMap F E S.th⁻¹) S.f S.f' ∘ e.symm, ?_, hspan, rfl, isLat_std L _, fun _ => rfl, ?_⟩
  · refine gram_unit L S.herm.1 _ ((tup_indep hθ hli).comp _ e.symm.injective) ?_
    rw [hspan]
    exact hco.disjoint
  · rintro C ⟨n, hn, n', hn', rfl⟩ p ⟨A, A', -, -, h0, h1, -, hp, hp'⟩
    obtain ⟨s, ⟨hs0, hs1⟩, hs⟩ := hN n hn
    obtain ⟨s', ⟨hs0', hs1'⟩, hs'⟩ := hN' n' hn'
    simp only [hs, hs', comb_mul] at hp hp'
    refine ⟨tup (algebraMap F E S.th⁻¹) p.1 p.2 ∘ e.symm,
      (Matrix.fromBlocks (s * A) (algebraMap F E S.th⁻¹ • (s' * A' - s * A)) 0 (s' * A')).submatrix
        e.symm e.symm, ?_, ?_, ?_⟩
    · rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul,
        det_uni s hs0 hs1, det_uni s' hs0' hs1', det_uni A (fun i j h => (h0 i j h).1) fun i => (h1 i).1,
        det_uni A' (fun i j h => (h0 i j h).2) fun i => (h1 i).2]
      simp
    · funext j
      rw [Function.comp_apply, tup_change _ S.f S.f' p.1 p.2 _ _ hp hp', rmul]
      exact (e.symm.sum_comp _).symm
    · rw [e.symm.surjective.range_comp, tup, Set.Sum.elim_range]
      rfl

end GlobalTheory.HL.FrameTuple
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNondegenerateTupleComplementFixerStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nondegenerate_tuple_complement_fixer : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∃ x : Fin (2 * r + 2) → S.V, IsUnit (gramT L S.Hm x).det ∧ Submodule.span E (Set.range x) = S.ME ∧ S.H0 = fixG L S.Hm S.ME ∧ IsLat L (Submodule.span L.O (Set.range fun i => (Pi.single i 1 : S.V))) ∧ (∀ Mh, S.massSig Mh = sigMass L S.Hm S.ME (Submodule.span L.O (Set.range fun i => (Pi.single i 1 : S.V))) Mh) ∧ ∀ C, S.IsCls C → ∀ p ∈ C, ∃ (y : Fin (2 * r + 2) → S.V) (B : Matrix (Fin (2 * r + 2)) (Fin (2 * r + 2)) E), B.det * L.cj B.det = 1 ∧ y = rmul x B ∧ S.Mof p.1 p.2 = Submodule.span L.O (Set.range y) := by
  first | exact @GlobalTheory.HL.FrameTuple.main | exact GlobalTheory.HL.FrameTuple.main | (intros; apply GlobalTheory.HL.FrameTuple.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalFrameStabilizerActsUnitriangular
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalFrameStabilizerActsUnitriangular
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section
namespace GlobalTheory.HL.StTri

theorem descend {E R : Type} [Field E] [CommRing R] [Nontrivial R] (ι : E →+* R) {n m : ℕ}
    (w : Fin m → Fin n → E) (s : Set (Fin m)) (v : Fin n → E)
    (h : (fun i => ι (v i)) ∈ Submodule.span R ((fun a i => ι (w a i)) '' s)) :
    v ∈ Submodule.span E (w '' s) := by
  letI : Algebra E R := ι.toAlgebra
  have hinj : Function.Injective (Algebra.linearMap E R) := ι.injective
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap E R)
    (LinearMap.ker_eq_bot.mpr hinj)
  have hg1 : ∀ c : E, g (ι c) = c := fun c => LinearMap.congr_fun hg c
  have hgm : ∀ (a : R) (c : E), g (a * ι c) = c * g a := by
    intro a c
    have : a * ι c = c • a := by rw [Algebra.smul_def, mul_comm]; rfl
    rw [this, map_smul, smul_eq_mul]
  rw [Finsupp.mem_span_image_iff_linearCombination] at h
  obtain ⟨l, hl, hv⟩ := h
  rw [Finsupp.mem_span_image_iff_linearCombination]
  refine ⟨Finsupp.mapRange g (map_zero g) l, ?_, ?_⟩
  · rw [Finsupp.mem_supported'] at hl ⊢
    intro i hi
    simp [hl i hi]
  · funext k
    have hk := congrFun hv k
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hk ⊢
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hk ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hg1 (v k), ← hk, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hgm, Finsupp.mapRange_apply, mul_comm]

theorem hf_smul_right {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (c : E) :
    hf L Hm x (c • y) = L.cj c * hf L Hm x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hf_add_right {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x y z : Fin n → E) :
    hf L Hm x (y + z) = hf L Hm x y + hf L Hm x z := by
  simp only [hf, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem loc_step {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g : Fin (r + 1) → S.V)
    (hg : ∀ b : Fin (r + 1), (b : ℕ) < r → hf L S.Hm (g (Fin.last r)) (g b) = 0)
    (x : S.GLV) (hx : x ∈ S.Nof g) (j : Fin (r + 1)) : x (g j) - g j ∈ S.spanTo g j := by
  unfold Frames.Nof at hx
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_iInf] at hx
  obtain ⟨⟨_, hU⟩, hP⟩ := hx
  by_cases hj : (j : ℕ) < r
  · have h1 := (hU ⟨j, hj⟩).2 (g j) (Submodule.subset_span ⟨j, by simp, rfl⟩)
    simpa using h1
  · have hjr : (j : ℕ) = r := by omega
    have hjl : j = Fin.last r := Fin.ext hjr
    have hmem : g (Fin.last r) ∈ perp L S.Hm (S.spanTo g r) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨b, hb, rfl⟩ := hy
        exact hg b hb
      | zero => simp [hf]
      | add y z _ _ hy hz => rw [hf_add_right, hy, hz, add_zero]
      | smul c y _ hy => rw [hf_smul_right, hy, mul_zero]
    have h2 := hP.2 _ hmem
    rw [hjl]
    simpa [Frames.spanTo] using h2

theorem frame_tri {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) {r n : ℕ} (p : HeightOneSpectrum (𝓞 F))
    (x : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (xp : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep)) (hext : A.Ext p x xp)
    (gG : Fin (r + 1) → Fin n → E) (gS : Fin (r + 1) → Fin n → (A.loc p).Ep)
    (u : Fin (r + 1) → (A.loc p).Ep) (hu : ∀ a, IsUnit (u a)) (heq : ∀ a, u a • gS a = A.bc p (gG a))
    (hstep : ∀ j : Fin (r + 1), xp (gS j) - gS j ∈ Submodule.span (A.loc p).Ep (gS '' {i | (i : ℕ) < j})) :
    ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧
      ∀ j, x (gG j) = ∑ i, s i j • gG i := by
  haveI : Nontrivial (A.loc p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (A.loc p).Fp) (by rw [(A.loc p).rank]; norm_num)
  have key : ∀ j : Fin (r + 1), x (gG j) - gG j ∈ Submodule.span E (gG '' {i | (i : ℕ) < j}) := by
    intro j
    apply descend (A.loc p).ιE gG
    have e1 : (fun i => (A.loc p).ιE ((x (gG j) - gG j) i)) = u j • (xp (gS j) - gS j) := by
      rw [smul_sub, ← map_smul, heq, hext]
      funext i
      simp [Places.bc]
    rw [e1]
    refine Submodule.smul_mem _ _ ?_
    refine (Submodule.span_le.mpr ?_) (hstep j)
    rintro _ ⟨i, hi, rfl⟩
    have h3 : gS i = ((hu i).unit⁻¹ : ((A.loc p).Ep)ˣ) • A.bc p (gG i) := by
      rw [← heq, Units.smul_def, smul_smul, (hu i).val_inv_mul, one_smul]
    rw [h3]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  have key2 : ∀ j : Fin (r + 1), ∃ l : Fin (r + 1) →₀ E,
      l ∈ Finsupp.supported E E {i : Fin (r + 1) | (i : ℕ) < j} ∧
      Finsupp.linearCombination E gG l = x (gG j) - gG j := fun j =>
    (Finsupp.mem_span_image_iff_linearCombination E).mp (key j)
  choose l hl hl' using key2
  have hz : ∀ i j : Fin (r + 1), ¬ ((i : ℕ) < j) → l j i = 0 := fun i j h =>
    (Finsupp.mem_supported' _ _).mp (hl j) i h
  refine ⟨Matrix.of fun i j => if i = j then 1 else l j i, ⟨fun i j hij => ?_, fun i => ?_⟩, fun j => ?_⟩
  · have hne : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
    simp only [Matrix.of_apply, if_neg hne]
    exact hz i j (by rw [Fin.lt_def] at hij; omega)
  · simp
  · have hjj : l j j = 0 := hz j j (lt_irrefl _)
    have hsplit : ∀ i, (if i = j then (1 : E) else l j i) = (if i = j then 1 else 0) + l j i := by
      intro i
      by_cases h : i = j
      · subst h; simp [hjj]
      · simp [h]
    have hlc := hl' j
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hlc
    simp only [Matrix.of_apply, hsplit, add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, hlc]
    abel

theorem stab_unitriangular : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ x ∈ G.St, ∃ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧ ((∀ i j, j < i → s' i j = 0) ∧ (∀ i, s' i i = 1)) ∧ (∀ j, x (G.f j) = ∑ i, s i j • G.f i) ∧ ∀ j, x (G.f' j) = ∑ i, s' i j • G.f' i := by
  intro F E _ _ _ _ _ sig A r k G x hx
  obtain ⟨p⟩ : Nonempty (HeightOneSpectrum (𝓞 F)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩⟩
  obtain ⟨xp, hxp, hext⟩ := (show ∀ p, ∃ g' ∈ (G.S p).St, A.Ext p x g' from hx) p
  have hxp' := Subgroup.mem_inf.mp hxp
  have hunit : ∀ a : Fin (r + 1), IsUnit (algebraMap (A.loc p).Fp (A.loc p).Ep
      (((G.c p : (A.loc p).Fp)) ^ (r - (a : ℕ)))) := fun a =>
    ((G.c p).isUnit.pow _).map _
  obtain ⟨s, hs, hsx⟩ := frame_tri A p x xp hext G.f (G.S p).f _ hunit (G.f_eq p)
    (loc_step (G.S p) (G.S p).f (fun b hb => by
      rw [(G.S p).gram]
      have : b ≠ Fin.last r := fun h => by subst h; simp at hb
      simp [this]) xp hxp'.1)
  obtain ⟨s', hs', hsx'⟩ := frame_tri A p x xp hext G.f' (G.S p).f' _ hunit (G.f'_eq p)
    (loc_step (G.S p) (G.S p).f' (fun b hb => by
      rw [(G.S p).gram']
      have : b ≠ Fin.last r := fun h => by subst h; simp at hb
      simp [this]) xp hxp'.2)
  exact ⟨s, s', hs, hs', hsx, hsx'⟩

end GlobalTheory.HL.StTri
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalFrameStabilizerActsUnitriangularStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalFrameStabilizer_acts_unitriangular : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ x ∈ G.St, ∃ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧ ((∀ i j, j < i → s' i j = 0) ∧ (∀ i, s' i i = 1)) ∧ (∀ j, x (G.f j) = ∑ i, s i j • G.f i) ∧ ∀ j, x (G.f' j) = ∑ i, s' i j • G.f' i := by
  first | exact @GlobalTheory.HL.StTri.stab_unitriangular | exact GlobalTheory.HL.StTri.stab_unitriangular | (intros; apply GlobalTheory.HL.StTri.stab_unitriangular <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryNearIdentityCloseTuples
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryNearIdentityCloseTuples
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CloseTuples

open GlobalTheory.HL.Eichler GlobalTheory.HL.DualInter

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}

theorem mem_jac [IsNonarchimedeanLocalField F] (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : ¬ IsUnit ϖ)
    (p : L.O) (hp : (p : E) = algebraMap F E ϖ) : p ∈ Ideal.jacobson (⊥ : Ideal L.O) := by
  have hm : ∀ c : 𝒪[F], algebraMap 𝒪[F] E c ∈ L.O := fun c =>
    (L.O_def _).2 isIntegral_algebraMap
  let f : 𝒪[F] →+* L.O := (algebraMap 𝒪[F] E).codRestrict L.O hm
  have hf : f.IsIntegral := fun x => by
    obtain ⟨p, hp, h⟩ := (L.O_def x).1 x.2
    refine ⟨p, hp, Subtype.ext ?_⟩
    change L.O.subtype _ = 0
    rw [Polynomial.hom_eval₂]
    exact h
  rw [Ideal.jacobson, Ideal.mem_sInf]
  rintro m ⟨-, hm⟩
  have h := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hf m
  have h2 : ϖ ∈ m.comap f := by
    rw [IsLocalRing.eq_maximalIdeal h]; exact hϖ
  have h3 : p = f ϖ := Subtype.ext hp
  rw [h3]
  exact h2

theorem exists_pow_denom [IsNonarchimedeanLocalField F] (L : LocE F E) {ϖ : 𝒪[F]}
    (hϖ : Irreducible ϖ) (x : E) : ∃ k : ℕ, algebraMap F E ϖ ^ k * x ∈ L.O := by
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; omega)
  have hx : IsAlgebraic 𝒪[F] x :=
    (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨d, hd0, hd⟩ := hx.exists_integral_multiple
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0 hϖ
  refine ⟨k, (L.O_def _).2 ?_⟩
  have h2 := hd.smul ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F])
  rw [smul_smul, Units.inv_mul_cancel_left, Algebra.smul_def, map_pow] at h2
  exact h2

theorem one_add_onto {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (p : L.O)
    (hp : p ∈ Ideal.jacobson (⊥ : Ideal L.O)) (A : (Fin n → E) →ₗ[E] (Fin n → E))
    (hA : ∀ v ∈ Λ, A v ∈ Λ) :
    Function.Bijective (LinearMap.id + (p : E) • A : (Fin n → E) →ₗ[E] (Fin n → E)) ∧
      ∀ v ∈ Λ, ∃ u ∈ Λ, u + (p : E) • A u = v := by
  set T : (Fin n → E) →ₗ[E] (Fin n → E) := LinearMap.id + (p : E) • A with hT
  have key : Λ ≤ Λ.map (T.restrictScalars L.O) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot hΛ.1 le_rfl fun z hz => ?_
    have hz' : z = T z + (-p) • A z := by
      change z = (z + (p : E) • A z) + (-(p : E)) • A z
      module
    rw [hz']
    exact Submodule.add_mem_sup ⟨z, hz, rfl⟩
      (Submodule.smul_mem_smul (Submodule.neg_mem _ hp) (hA z hz))
  have hs : Function.Surjective T := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hΛ.2, Submodule.span_le]
    intro v hv
    obtain ⟨u, -, hu⟩ := key hv
    exact ⟨u, hu⟩
  exact ⟨⟨OrzechProperty.injective_of_surjective_endomorphism T hs, hs⟩, fun v hv => key hv⟩

noncomputable def rk (L : LocE F E) (Hm : Matrix (Fin n) (Fin n) E) {m : ℕ}
    (t d : Fin m → Fin n → E) : (Fin n → E) →ₗ[E] (Fin n → E) :=
  ∑ a, (hfL L Hm (t a)).smulRight (d a)

theorem rk_apply {m : ℕ} (t d : Fin m → Fin n → E) (v : Fin n → E) :
    rk L Hm t d v = ∑ a, hf L Hm v (t a) • d a := by
  rw [rk, LinearMap.sum_apply]
  rfl

theorem rk_mem {Λ : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ) {m : ℕ}
    {t d : Fin m → Fin n → E} (ht : ∀ a, t a ∈ Λ) (hd : ∀ a, d a ∈ Λ) {v : Fin n → E}
    (hv : v ∈ Λ) : rk L Hm t d v ∈ Λ := by
  rw [rk_apply]
  exact Λ.sum_mem fun a _ => Λ.smul_mem ⟨_, (hΛ.2 _).2 (ht a) _ hv⟩ (hd a)

theorem rk_adj (h : IsHermND L Hm) {m : ℕ} (t d : Fin m → Fin n → E) (v w : Fin n → E) :
    hf L Hm (rk L Hm t d v) w = hf L Hm v (rk L Hm d t w) := by
  simp only [rk_apply, sum_l, sum_r, smul_l, smul_r, cj_hf h, mul_comm]

theorem rk_dual {m : ℕ} {s t : Fin m → Fin n → E} {q : E}
    (hst : ∀ a b, hf L Hm (s a) (t b) = if a = b then q else 0) (d : Fin m → Fin n → E)
    (c : Fin m) : rk L Hm t d (s c) = q • d c := by
  simp [rk_apply, hst]

theorem exists_skew (h : IsHermND L Hm) {Λ : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ) {m : ℕ}
    {s t d : Fin m → Fin n → E} (hs : ∀ a, s a ∈ Λ) (ht : ∀ a, t a ∈ Λ) (hd : ∀ a, d a ∈ Λ)
    {q : E} (hq : q ∈ L.O) (hq' : L.cj q = q)
    (hst : ∀ a b, hf L Hm (s a) (t b) = if a = b then q else 0)
    (hsk : ∀ a b, hf L Hm (s a) (d b) = - hf L Hm (d a) (s b)) :
    ∃ Z : (Fin n → E) →ₗ[E] (Fin n → E), (∀ v ∈ Λ, Z v ∈ Λ) ∧
      (∀ v w, hf L Hm (Z v) w = - hf L Hm v (Z w)) ∧ ∀ c, Z (s c) = (q * q) • d c := by
  have e1 : ∀ c, rk L Hm d t (s c) = - rk L Hm s t (d c) := fun c => by
    simp [rk_apply, hsk]
  have e3 : ∀ v w, hf L Hm (rk L Hm t d v) (rk L Hm t s w)
      = - hf L Hm (rk L Hm t s v) (rk L Hm t d w) := fun v w => by
    simp only [rk_apply, sum_l, sum_r, smul_l, smul_r, hsk, Finset.mul_sum, mul_neg,
      Finset.sum_neg_distrib, neg_neg]
  refine ⟨q • rk L Hm t d - q • rk L Hm d t - rk L Hm s t ∘ₗ rk L Hm t d, fun v hv => ?_,
    fun v w => ?_, fun c => ?_⟩
  · exact Λ.sub_mem (Λ.sub_mem (Λ.smul_mem ⟨q, hq⟩ (rk_mem hΛ ht hd hv))
      (Λ.smul_mem ⟨q, hq⟩ (rk_mem hΛ hd ht hv))) (rk_mem hΛ hs ht (rk_mem hΛ ht hd hv))
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, sub_l, sub_r,
      smul_l, smul_r, hq']
    rw [rk_adj h s t, e3, ← rk_adj h t s v, rk_adj h t d v w, rk_adj h d t v w]
    ring
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, rk_dual hst, e1,
      map_smul]
    module

theorem exists_cayley {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (p : L.O)
    (hp : p ∈ Ideal.jacobson (⊥ : Ideal L.O)) (hp' : L.cj p = p)
    (Z : (Fin n → E) →ₗ[E] (Fin n → E)) (hZ : ∀ v ∈ Λ, Z v ∈ Λ)
    (hsk : ∀ v w, hf L Hm (Z v) w = - hf L Hm v (Z w)) :
    ∃ g ∈ isomG L Hm, (∀ v ∈ Λ, ∃ w ∈ Λ, g v - v = (p : E) • w) ∧
      ∀ x y, (p : E) • Z (x + y) = y - x → g x = y := by
  obtain ⟨b1, -⟩ := one_add_onto hΛ p hp Z hZ
  obtain ⟨b2, o2⟩ := one_add_onto hΛ p hp (-Z) fun v hv => Λ.neg_mem (hZ v hv)
  let g := (LinearEquiv.ofBijective _ b1).trans (LinearEquiv.ofBijective _ b2).symm
  have hg : ∀ x y, x + (p : E) • Z x = y - (p : E) • Z y → g x = y := fun x y e => by
    refine (LinearEquiv.symm_apply_eq _).2 ?_
    change x + (p : E) • Z x = y + (p : E) • (-Z y)
    rw [e]; module
  have hg' : ∀ u, g (u + (p : E) • (-Z u)) = u + (p : E) • Z u := fun u => hg _ _ (by
    simp only [map_add (f := _), map_smul, map_neg]; module)
  refine ⟨g, fun v w => ?_, fun v hv => ?_, fun x y e => hg x y ?_⟩
  · obtain ⟨v, rfl⟩ := b2.2 v
    obtain ⟨w, rfl⟩ := b2.2 w
    change hf L Hm (g (v + (p : E) • (-Z v))) (g (w + (p : E) • (-Z w)))
      = hf L Hm (v + (p : E) • (-Z v)) (w + (p : E) • (-Z w))
    rw [hg', hg']
    simp only [hf_add_l, hf_add_r, hf_smul_l, hf_smul_r, hf_neg_l, hf_neg_r, hp', hsk v w]
    ring
  · obtain ⟨u, hu, rfl⟩ := o2 v hv
    refine ⟨Z u + Z u, Λ.add_mem (hZ u hu) (hZ u hu), ?_⟩
    change g (u + (p : E) • (-Z u)) - (u + (p : E) • (-Z u)) = _
    rw [hg']; module
  · rw [map_add (f := _), smul_add] at e
    linear_combination (exp := 1) e

theorem exists_isometry_close : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ, IsSD L Hm Λ → ∀ (m : ℕ) (Γ : Matrix (Fin m) (Fin m) E), IsUnit Γ.det → ∀ N : ℕ, ∃ N' : ℕ, ∀ x y : Fin m → Fin n → E, (∀ a, x a ∈ Λ) → gramT L Hm x = Γ → gramT L Hm y = Γ → (∀ a, ∃ w ∈ Λ, y a - x a = algebraMap F E ((ϖ : F) ^ N') • w) → ∃ g ∈ isomG L Hm, CongId L ϖ Λ N g ∧ ∀ a, g (x a) = y a := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm h Λ hΛ m Γ hΓ N
  set π : E := algebraMap F E ϖ with hπ
  have hπO : π ∈ L.O := (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 ϖ.2
  have hπc : L.cj π = π := L.cj.commutes _
  have hπu : IsUnit π :=
    (IsUnit.mk0 (ϖ : F) fun e => hϖ.ne_zero (Subtype.ext e)).map _
  have hπj := mem_jac L hϖ.not_isUnit ⟨π, hπO⟩ rfl
  set hf2 : E := algebraMap F E 2⁻¹ with hhf2
  have h2 : hf2 * 2 = 1 := by
    rw [hhf2, ← map_ofNat (algebraMap F E) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  choose k hk using fun ab : Fin m × Fin m => exists_pow_denom L hϖ (hf2 * Γ⁻¹ ab.1 ab.2)
  obtain ⟨c, hc⟩ : ∃ c, ∀ ab, k ab ≤ c := ⟨Finset.univ.sup k, fun ab => Finset.le_sup (Finset.mem_univ ab)⟩
  set q : E := π ^ c with hq
  have hqO : q ∈ L.O := L.O.pow_mem hπO c
  have hqc : L.cj q = q := by rw [hq, map_pow, hπc]
  have hqΓ : ∀ a b, q * (hf2 * Γ⁻¹ a b) ∈ L.O := fun a b => by
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le' (hc (a, b))
    rw [hq, hj, pow_add, mul_assoc]
    exact L.O.mul_mem (L.O.pow_mem hπO j) (hk (a, b))
  let p : L.O := ⟨π, hπO⟩ ^ (N + 1)
  have hpe : (p : E) = π ^ (N + 1) := rfl
  have hpj : p ∈ Ideal.jacobson (⊥ : Ideal L.O) := Ideal.pow_mem_of_mem _ hπj _ (Nat.succ_pos N)
  have hpc : L.cj p = p := by rw [hpe, map_pow, hπc]
  refine ⟨N + 1 + (c + c), fun x y hx gx gy hxy => ?_⟩
  choose d hd hxy using hxy
  have hxy' : ∀ a, y a = x a + ((p : E) * (q * q)) • d a := fun a => by
    rw [← sub_eq_iff_eq_add', hxy, map_pow, pow_add, pow_add _ c c]; rfl
  have hu : IsUnit ((p : E) * (q * q)) := (hπu.pow _).mul ((hπu.pow _).mul (hπu.pow _))
  have huc : L.cj ((p : E) * (q * q)) = p * (q * q) := by simp only [map_mul, hpc, hqc]
  have hy : ∀ a, y a ∈ Λ := fun a => by
    rw [hxy']
    exact Λ.add_mem (hx a) (Λ.smul_mem ⟨_, L.O.mul_mem p.2 (L.O.mul_mem hqO hqO)⟩ (hd a))
  have gx' : ∀ a b, hf L Hm (x b) (x a) = Γ a b := fun a b => congrFun (congrFun gx a) b
  have gy' : ∀ a b, hf L Hm (y b) (y a) = Γ a b := fun a b => congrFun (congrFun gy a) b
  have hsk : ∀ a b, hf L Hm (x a + y a) (d b) = - hf L Hm (d a) (x b + y b) := fun a b => by
    refine hu.mul_left_cancel ?_
    have e : ∀ a, ((p : E) * (q * q)) • d a = y a - x a := fun a => by rw [hxy' a]; abel
    rw [mul_neg, ← smul_l L Hm _ (d a), e]
    conv_lhs => rw [← huc, ← smul_r, e]
    simp only [hf_add_l, hf_add_r, sub_l, sub_r, gx', gy']
    ring
  let t0 : Fin m → Fin n → E := fun b => ∑ a, L.cj (q * (hf2 * Γ⁻¹ b a)) • x a
  have ht0 : ∀ b, t0 b ∈ Λ := fun b => Λ.sum_mem fun a _ =>
    Λ.smul_mem ⟨_, GlobalTheory.UnramOrder.cj_mem L (hqΓ b a)⟩ (hx a)
  have hxt : ∀ a b, hf L Hm (x a + x a) (t0 b) = if a = b then q else 0 := fun a b => by
    have e : ∑ j, Γ⁻¹ b j * Γ j a = if a = b then 1 else 0 := by
      rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ hΓ, Matrix.one_apply]
      simp only [eq_comm]
    have e' : hf L Hm (x a) (t0 b) = q * hf2 * ∑ j, Γ⁻¹ b j * Γ j a := by
      simp only [t0, sum_r, smul_r, L.cj_cj, gx', Finset.mul_sum, mul_assoc]
    rw [hf_add_l, e', e]
    split_ifs
    · linear_combination q * h2
    · ring
  obtain ⟨-, o⟩ := one_add_onto hΛ.1 p hpj (q • rk L Hm d t0) fun v hv =>
    Λ.smul_mem ⟨q, hqO⟩ (rk_mem hΛ hd ht0 hv)
  choose t ht et using fun b => o _ (ht0 b)
  have hst : ∀ a b, hf L Hm (x a + y a) (t b) = if a = b then q else 0 := fun a b => by
    rw [← hxt, ← et b, hf_add_r, LinearMap.smul_apply, smul_r, smul_r, ← rk_adj h,
      rk_dual (s := fun a => x a + x a) hxt, hxy', ← add_assoc, hf_add_l _ _ (x a + x a), smul_l,
      smul_l, hpc, hqc]
    ring
  obtain ⟨Z, hZ, hZs, hZd⟩ := exists_skew h hΛ (s := fun a => x a + y a)
    (fun a => Λ.add_mem (hx a) (hy a)) ht hd hqO hqc hst hsk
  obtain ⟨g, hg, hgΛ, hgx⟩ := exists_cayley (Hm := Hm) hΛ.1 p hpj hpc Z hZ hZs
  refine ⟨g, hg, fun v hv => ?_, fun a => hgx _ _ ?_⟩
  · obtain ⟨w, hw, e⟩ := hgΛ v hv
    refine ⟨π • w, Λ.smul_mem ⟨π, hπO⟩ hw, ?_⟩
    rw [e, hpe, map_pow, smul_smul, pow_succ]
  · rw [hZd a, smul_smul, eq_sub_iff_add_eq', ← hxy']

end GlobalTheory.HL.CloseTuples
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryNearIdentityCloseTuplesStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isometry_near_identity_close_tuples : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ, IsSD L Hm Λ → ∀ (m : ℕ) (Γ : Matrix (Fin m) (Fin m) E), IsUnit Γ.det → ∀ N : ℕ, ∃ N' : ℕ, ∀ x y : Fin m → Fin n → E, (∀ a, x a ∈ Λ) → gramT L Hm x = Γ → gramT L Hm y = Γ → (∀ a, ∃ w ∈ Λ, y a - x a = algebraMap F E ((ϖ : F) ^ N') • w) → ∃ g ∈ isomG L Hm, CongId L ϖ Λ N g ∧ ∀ a, g (x a) = y a := by
  first | exact @GlobalTheory.HL.CloseTuples.exists_isometry_close | exact GlobalTheory.HL.CloseTuples.exists_isometry_close | (intros; apply GlobalTheory.HL.CloseTuples.exists_isometry_close <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LoweringDifferenceOfIsometries
open Matrix

namespace GlobalTheory

theorem hform_sub_left_flag {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (x x' y : n → A) :
    Formalism.UG.hform σ J (x - x') y = Formalism.UG.hform σ J x y - Formalism.UG.hform σ J x' y := by
  unfold Formalism.UG.hform
  simp only [Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem hform_sub_right_flag {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (x y y' : n → A) :
    Formalism.UG.hform σ J x (y - y') = Formalism.UG.hform σ J x y - Formalism.UG.hform σ J x y' := by
  unfold Formalism.UG.hform
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private theorem hform_eq_dotProduct_mulVec {K : Type} [CommRing K] {n : ℕ} (σ : K →+* K)
    (J : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  unfold Formalism.UG.hform
  simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

private theorem hform_mulVec_eq_of_unitary {K : Type} [CommRing K] {n : ℕ} (σ : K →+* K)
    (J γ : Matrix (Fin n) (Fin n) K) (hγ : Formalism.UG.cT σ γ * J * γ = J) (x y : Fin n → K) :
    Formalism.UG.hform σ J (γ *ᵥ x) (γ *ᵥ y) = Formalism.UG.hform σ J x y := by
  rw [hform_eq_dotProduct_mulVec, hform_eq_dotProduct_mulVec]
  have h1 : (fun i => σ ((γ *ᵥ x) i)) = γ.map σ *ᵥ (fun i => σ (x i)) := by
    funext i
    exact RingHom.map_mulVec σ γ x i
  unfold Formalism.UG.cT at hγ
  rw [Matrix.mul_assoc] at hγ
  rw [h1, ← vecMul_transpose (γ.map σ), ← dotProduct_mulVec]
  simp only [mulVec_mulVec, hγ]

theorem lowering_difference_of_isometries :
    ∀ (K R : Type) [Field K] [StarRing K] [CommRing R] [Algebra R K] (n : ℕ) (J : Matrix (Fin n) (Fin n) K), Formalism.UG.IsHerm (starRingEnd K) J → ∀ (a : ℕ) (G : ℕ → Submodule R (Fin n → K)), G 0 = ⊥ → Monotone G → (∀ p ≤ 2 * a + 1, ∀ y, y ∈ G (2 * a + 1 - p) ↔ y ∈ G (2 * a + 1) ∧ ∀ s ∈ G p, Formalism.UG.hform (starRingEnd K) J s y = 0) → ∀ γ γ' : Matrix (Fin n) (Fin n) K, Formalism.UG.cT (starRingEnd K) γ * J * γ = J → Formalism.UG.cT (starRingEnd K) γ' * J * γ' = J → (∀ p ≤ 2 * a, ∀ y ∈ G (p + 1), (γ - 1) *ᵥ y ∈ G p) → (∀ p ≤ 2 * a, ∀ y ∈ G (p + 1), (γ' - 1) *ᵥ y ∈ G p) → ∀ c : ℕ, 1 ≤ c → (∀ q p : ℕ, q < p → q + p ≤ 2 * a → p - q < c → ∀ y ∈ G (p + 1), (γ - γ') *ᵥ y ∈ G q) → (∀ p ≤ 2 * a + 1, ∀ y ∈ G p, (γ - γ') *ᵥ y ∈ G (p - c)) ∧ ∀ p p' : ℕ, p ≤ 2 * a → p' ≤ 2 * a → p + p' ≤ 2 * a + c → ∀ x ∈ G (p + 1), ∀ y ∈ G (p' + 1), Formalism.UG.hform (starRingEnd K) J ((γ - γ') *ᵥ x) y + Formalism.UG.hform (starRingEnd K) J x ((γ - γ') *ᵥ y) = 0 := by
  intro K R _ _ _ _ n J _ a G hG0 hGm hdual γ γ' hγ hγ' hl hl' c hc hlow
  set hf := Formalism.UG.hform (starRingEnd K) J with hhf
  have hL : ∀ x x' y, hf (x - x') y = hf x y - hf x' y := fun x x' y => hform_sub_left_flag _ J x x' y
  have hR : ∀ x y y', hf x (y - y') = hf x y - hf x y' := fun x y y' => hform_sub_right_flag _ J x y y'
  have iso : ∀ x y, hf (γ *ᵥ x) (γ *ᵥ y) = hf x y := hform_mulVec_eq_of_unitary _ J γ hγ
  have iso' : ∀ x y, hf (γ' *ᵥ x) (γ' *ᵥ y) = hf x y := hform_mulVec_eq_of_unitary _ J γ' hγ'
  have h0 : ∀ v, hf 0 v = 0 := fun v => by simp [hhf, Formalism.UG.hform]
  have mem0 : ∀ y ∈ G 0, y = 0 := fun y hy => by
    rw [hG0] at hy
    exact (Submodule.mem_bot R).1 hy
  have orth : ∀ m m', m + m' ≤ 2 * a + 1 → ∀ u ∈ G m, ∀ v ∈ G m', hf u v = 0 := by
    intro m m' hmm u hu v hv
    exact ((hdual m (by omega) v).1 (hGm (by omega) hv)).2 u hu
  have key : ∀ x y, hf ((γ - γ') *ᵥ x) (γ *ᵥ y) + hf (γ' *ᵥ x) ((γ - γ') *ᵥ y) = 0 := by
    intro x y
    rw [sub_mulVec, sub_mulVec, hL, hR, iso, iso']
    ring
  have base : ∀ p ≤ 2 * a + 1, ∀ y ∈ G p, (γ - γ') *ᵥ y ∈ G (p - 1) := by
    intro p hp y hy
    rcases Nat.eq_zero_or_pos p with rfl | hp0
    · rw [mem0 y hy, mulVec_zero]
      exact zero_mem _
    · obtain ⟨p0, rfl⟩ : ∃ p0, p = p0 + 1 := ⟨p - 1, by omega⟩
      have e : (γ - γ') *ᵥ y = (γ - 1) *ᵥ y - (γ' - 1) *ᵥ y := by
        simp only [sub_mulVec, one_mulVec]
        abel
      rw [e, Nat.add_sub_cancel]
      exact sub_mem (hl p0 (by omega) y hy) (hl' p0 (by omega) y hy)
  have main1 : ∀ p, p ≤ 2 * a + 1 → ∀ y ∈ G p, (γ - γ') *ᵥ y ∈ G (p - c) := by
    intro p
    induction p using Nat.strong_induction_on with
    | _ p ih =>
      intro hp y hy
      by_cases hA : c = 1 ∨ p ≤ 1
      · exact hGm (by omega) (base p hp y hy)
      by_cases hB : 2 * p ≤ 2 * a + 1 + c ∨ p < c
      · obtain ⟨p0, rfl⟩ : ∃ p0, p = p0 + 1 := ⟨p - 1, by omega⟩
        exact hlow (p0 + 1 - c) p0 (by omega) (by omega) (by omega) y hy
      have hγy : γ *ᵥ y ∈ G p := by
        have e1 : γ *ᵥ y = (γ - 1) *ᵥ y + y := by
          simp only [sub_mulVec, one_mulVec]
          abel
        rw [e1]
        refine add_mem (hGm (Nat.sub_le p 1) (hl (p - 1) (by omega) y ?_)) hy
        rwa [Nat.sub_add_cancel (by omega : 1 ≤ p)]
      have inner : ∀ j, j ≤ 2 * a + 1 - (p - c) → ∀ s ∈ G j, hf s ((γ - γ') *ᵥ y) = 0 := by
        intro j
        induction j with
        | zero =>
          intro _ s hs
          rw [mem0 s hs, h0]
        | succ j ihj =>
          intro hj s hs
          have k := key s y
          have ha : hf ((γ' - 1) *ᵥ s) ((γ - γ') *ᵥ y) =
              hf (γ' *ᵥ s) ((γ - γ') *ᵥ y) - hf s ((γ - γ') *ᵥ y) := by
            rw [sub_mulVec γ' 1, one_mulVec, hL]
          have hz1 := ihj (by omega) _ (hl' j (by omega) s hs)
          have hz2 := orth (j + 1 - c) p (by omega) _ (ih (j + 1) (by omega) (by omega) s hs) _ hγy
          linear_combination k + ha - hz1 - hz2
      have hd := (hdual (2 * a + 1 - (p - c)) (by omega) ((γ - γ') *ᵥ y)).2
        ⟨hGm (by omega) (base p hp y hy), fun s hs => inner _ le_rfl s hs⟩
      have e2 : 2 * a + 1 - (2 * a + 1 - (p - c)) = p - c := by omega
      rwa [e2] at hd
  refine ⟨main1, ?_⟩
  intro p p' hp hp' hpp x hx y hy
  have e3 : hf ((γ - γ') *ᵥ x) ((γ - 1) *ᵥ y) = 0 :=
    orth (p + 1 - c) p' (by omega) _ (main1 (p + 1) (by omega) x hx) _ (hl p' hp' y hy)
  have e4 : hf ((γ' - 1) *ᵥ x) ((γ - γ') *ᵥ y) = 0 :=
    orth p (p' + 1 - c) (by omega) _ (hl' p hp x hx) _ (main1 (p' + 1) (by omega) y hy)
  rw [sub_mulVec γ 1, one_mulVec, hR] at e3
  rw [sub_mulVec γ' 1, one_mulVec, hL] at e4
  linear_combination key x y - e3 - e4

end GlobalTheory
end
