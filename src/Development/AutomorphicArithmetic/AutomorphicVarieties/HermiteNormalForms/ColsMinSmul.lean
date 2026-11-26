module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Nearvec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.SimpSpan

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Nearvx
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.FiniteSubfamilySpansDual
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Rankhs
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.rankhs :
    ∀ (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N : ℕ), Module.finrank ℝ (HS L N) ≤ dd L N * N := by
  intro L _ _ _ N
  refine (Submodule.finrank_le (HSsub L N)).trans (le_of_eq ?_)
  have h1 := IsTotallyComplex.finrank L
  have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces L
  have h3 := IsTotallyComplex.nrRealPlaces_eq_zero L
  simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, dd]
  rw [h1, h2, h3]
  ring
end

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

private theorem UpperTheory.V.KT.finite_subfamily_spans_dual {E Y : Type*} [AddCommGroup E] [Module ℝ E]
    [Module.Finite ℝ E] (f : Y → Module.Dual ℝ E) (S : Set Y) :
    ∃ M : Finset Y, M.card ≤ Module.finrank ℝ E ∧ (∀ y ∈ M, y ∈ S) ∧
      ∀ k : E, (∀ y ∈ M, f y k = 0) → ∀ y ∈ S, f y k = 0 := by
  classical
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent ℝ (f '' S)
  have hbfin : b.Finite := hli.setFinite
  have hch : ∀ φ ∈ b, ∃ y, y ∈ S ∧ f y = φ := fun φ hφ => hbs hφ
  choose g hgS hgf using hch
  refine ⟨hbfin.toFinset.attach.image (fun φ => g φ.1 (hbfin.mem_toFinset.mp φ.2)), ?_, ?_, ?_⟩
  · haveI : Fintype b := hbfin.fintype
    calc (hbfin.toFinset.attach.image (fun φ => g φ.1 (hbfin.mem_toFinset.mp φ.2))).card
        ≤ hbfin.toFinset.attach.card := Finset.card_image_le
      _ = hbfin.toFinset.card := Finset.card_attach
      _ = Fintype.card b := hbfin.card_toFinset
      _ ≤ Module.finrank ℝ (Module.Dual ℝ E) := hli.fintype_card_le_finrank
      _ = Module.finrank ℝ E := Subspace.dual_finrank_eq
  · intro y hy
    obtain ⟨φ, _, rfl⟩ := Finset.mem_image.mp hy
    exact hgS _ _
  · intro k hk y hy
    have hsub : b ⊆ LinearMap.ker (Module.Dual.eval ℝ E k) := by
      intro φ hφ
      rw [SetLike.mem_coe, LinearMap.mem_ker, Module.Dual.eval_apply, ← hgf φ hφ]
      exact hk _ (Finset.mem_image.mpr ⟨⟨φ, hbfin.mem_toFinset.mpr hφ⟩, Finset.mem_attach _ _, rfl⟩)
    have hle := Submodule.span_le.mpr hsub
    rw [hspan] at hle
    have hm := hle (Submodule.subset_span ⟨y, hy, rfl⟩)
    rwa [LinearMap.mem_ker, Module.Dual.eval_apply] at hm

theorem UpperTheory.V.KT.vxdet :
    ∀ (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N : ℕ) (v : Vx L N),
    ∃ M : Finset (Lat L N), M.card ≤ dd L N * N ∧ (∀ y ∈ M, q v.1 y = 1) ∧
      ∀ h : HS L N, (∀ y ∈ M, q h y = 1) → h = v.1 := by
  intro L _ _ _ N v
  obtain ⟨M, hMc, hMS, hMk⟩ := UpperTheory.V.KT.finite_subfamily_spans_dual (E := HS L N)
    (fun y : Lat L N => (ev y : Module.Dual ℝ (HS L N))) {y | y ≠ 0 ∧ q v.1 y = 1}
  refine ⟨M, hMc.trans (rankhs L N), fun y hy => (hMS y hy).2, ?_⟩
  intro h hh
  have hk : ∀ y ∈ M, ev y (h - v.1) = 0 := by
    intro y hy
    rw [map_sub, ev_apply, ev_apply, hh y hy, (hMS y hy).2, sub_self]
  have hall := hMk (h - v.1) hk
  have h0 : h - v.1 = 0 := by
    apply v.2.2
    intro y hy
    have hy' : q v.1 y.1 = 1 := by
      rw [← ev_apply]
      exact hy
    exact hall y.1 ⟨y.2, hy'⟩
  exact sub_eq_zero.mp h0
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Cardsub
open Matrix
open scoped ComplexOrder

theorem UpperTheory.V.KT.cardsub :
    ∀ (α : Type) (S : Set α) (k : ℕ), S.Finite →
    {M : Finset α | (↑M : Set α) ⊆ S ∧ M.card ≤ k}.Finite ∧
      {M : Finset α | (↑M : Set α) ⊆ S ∧ M.card ≤ k}.ncard ≤ (S.ncard + 1) ^ k := by
  intro α S k hS
  classical
  set T := hS.toFinset with hT
  let F : Finset (Finset α) := (Finset.range (k + 1)).biUnion fun j => T.powersetCard j
  have hsub : {M : Finset α | (↑M : Set α) ⊆ S ∧ M.card ≤ k} ⊆ (↑F : Set (Finset α)) := by
    rintro M ⟨hM, hk⟩
    rw [Finset.mem_coe, Finset.mem_biUnion]
    refine ⟨M.card, Finset.mem_range.2 (by omega), Finset.mem_powersetCard.2 ⟨?_, rfl⟩⟩
    intro x hx
    simpa [T] using hM hx
  have hfin := F.finite_toSet.subset hsub
  refine ⟨hfin, ?_⟩
  calc _ ≤ (↑F : Set (Finset α)).ncard := Set.ncard_le_ncard hsub F.finite_toSet
    _ = F.card := Set.ncard_coe_finset F
    _ ≤ ∑ j ∈ Finset.range (k + 1), (T.powersetCard j).card := Finset.card_biUnion_le
    _ = ∑ j ∈ Finset.range (k + 1), T.card.choose j := by simp [Finset.card_powersetCard]
    _ ≤ ∑ j ∈ Finset.range (k + 1), T.card ^ j * 1 ^ (k - j) * k.choose j := by
      apply Finset.sum_le_sum
      intro j hj
      have h1 : T.card.choose j ≤ T.card ^ j := Nat.choose_le_pow _ _
      have h2 : 1 ≤ k.choose j := Nat.choose_pos (by simp at hj; omega)
      rw [one_pow, mul_one]
      calc T.card.choose j ≤ T.card ^ j := h1
        _ = T.card ^ j * 1 := (mul_one _).symm
        _ ≤ T.card ^ j * k.choose j := Nat.mul_le_mul_left _ h2
    _ = (T.card + 1) ^ k := (add_pow _ _ _).symm
    _ = (S.ncard + 1) ^ k := by rw [Set.ncard_eq_toFinset_card S hS]
end

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.nearvx :
    ∀ (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N : ℕ) (A : Matrix (Fin N) (Fin N) (𝓞 L)), A.det ≠ 0 →
    (nearVx A).Finite ∧ (nearVx A).ncard ≤ ((2 * RR L N + 1) ^ dd L N + 1) ^ (dd L N * N) := by
  intro L _ _ _ N A hA
  choose f hf1 hf2 hf3 using vxdet L N
  obtain ⟨hfin, hcard⟩ := nearvec L N A hA
  obtain ⟨h1, h2⟩ := cardsub (Lat L N) (nearVec A) (dd L N * N) hfin
  have hinj : Function.Injective f := fun v w e =>
    Subtype.ext (hf3 w v.1 (fun y hy => hf2 v y (e ▸ hy)))
  have hmap : ∀ v ∈ nearVx A, f v ∈
      {M : Finset (Lat L N) | (↑M : Set (Lat L N)) ⊆ nearVec A ∧ M.card ≤ dd L N * N} := by
    intro v hv
    refine ⟨fun y hy => ⟨v.1, ?_, hv, hf2 v y hy⟩, hf1 v⟩
    have := v.2.1
    rwa [poly_qc] at this
  refine ⟨Set.Finite.of_injOn hmap hinj.injOn h1, ?_⟩
  refine (Set.ncard_le_ncard_of_injOn f hmap hinj.injOn h1).trans (h2.trans ?_)
  exact Nat.pow_le_pow_left (Nat.succ_le_succ hcard) _
end

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

private theorem sx_basis (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N p : ℕ)
    (t : Sx L N p) :
    ∃ A : Matrix (Fin N) (Fin N) (𝓞 L), A.det ≠ 0 ∧ ∀ j, ColsMin A (t.1 j).1 := by
  have hs : Spans {y : Lat L N | ∀ j, q (t.1 j).1 y = 1} := by
    refine spanpsd L N _ fun k hk H => ?_
    refine ConeExtensionAcyclic.simp_span (good L N).locFin p t.1 t.2 k hk fun y hy => ?_
    exact H y.1 hy
  obtain ⟨A, hA, hc⟩ := exbasis L N _ hs
  exact ⟨A, hA, fun j a => hc a j⟩

private theorem colsMin_smul {L : Type} [Field L] [NumberField L] {N : ℕ} (g : Gm L N)
    {A : Matrix (Fin N) (Fin N) (𝓞 L)} {h : HS L N} (H : ColsMin A h) :
    ColsMin ((g : Matrix (Fin N) (Fin N) (𝓞 L)) * A) (g • h) := by
  intro a
  have e : (fun i => ((g : Matrix (Fin N) (Fin N) (𝓞 L)) * A) i a) =
      g • (fun i => A i a : Lat L N) := by
    ext i
    simp [smul_lat, Matrix.mul_apply, mulVec, dotProduct]
  rw [e, q_smul, inv_smul_smul]
  exact H a

theorem UpperTheory.V.KT.orb :
    ∀ (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N : ℕ) (p : ℕ),
    KH.OrbLe (Gm L N) (Sx L N p) (orbBound L N p) := by
  intro L _ _ _ N p
  classical
  obtain ⟨S, hS, hrep⟩ := hnf L N (I0 L N)
  let S' := S.filter fun A => A.det ≠ 0
  have hdet : ∀ A : S', A.1.det ≠ 0 := fun A => (Finset.mem_filter.1 A.2).2
  haveI : ∀ A : S', Finite (nearVx A.1) := fun A => (nearvx L N A.1 (hdet A)).1.to_subtype
  have key : ∀ c : MulAction.orbitRel.Quotient (Gm L N) (Sx L N p),
      ∃ s : (Σ A : S', (Fin (p + 1) → nearVx A.1)), ∃ t : Sx L N p,
        Quotient.mk _ t = c ∧ ∀ j, t.1 j = (s.2 j).1 := by
    intro c
    induction c using Quotient.inductionOn with
    | h t =>
      obtain ⟨A, hA, hc⟩ := sx_basis L N p t
      have hR : (t.1 0).1 ∈ Ry L N := by
        rw [← poly_qc]; exact (t.1 0).2.1
      obtain ⟨g, hg⟩ := hrep A hA (nrmle L N _ A hR (hc 0) hA).1
      have hd : ((g : Matrix (Fin N) (Fin N) (𝓞 L)) * A).det ≠ 0 := by
        rw [Matrix.det_mul]
        exact mul_ne_zero (Matrix.isUnits_det_units g).ne_zero hA
      refine ⟨⟨⟨_, Finset.mem_filter.2 ⟨hg, hd⟩⟩,
        fun j => ⟨g • t.1 j, colsMin_smul g (hc j)⟩⟩, g • t, ?_, fun j => rfl⟩
      exact Quotient.sound (MulAction.orbitRel_apply.2 ⟨g, rfl⟩)
  choose f t ht hf using key
  have hinj : Function.Injective f := by
    intro c c' e
    rw [← ht c, ← ht c']
    congr 1
    refine Subtype.ext (funext fun j => ?_)
    rw [hf, hf, e]
  refine ⟨Finite.of_injective f hinj, (Nat.card_le_card_of_injective f hinj).trans ?_⟩
  rw [Nat.card_sigma]
  have hb : ∀ A : S', Nat.card (Fin (p + 1) → nearVx A.1) ≤
      ((2 * RR L N + 1) ^ dd L N + 1) ^ (dd L N * N * (p + 1)) := by
    intro A
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin (p + 1)), Fintype.card_fin, pow_mul _ _ (p + 1)]
    exact Nat.pow_le_pow_left (nearvx L N A.1 (hdet A)).2 _
  refine (Finset.sum_le_card_nsmul _ _ _ fun A _ => hb A).trans ?_
  rw [smul_eq_mul, Finset.card_univ, Fintype.card_coe]
  exact Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans hS)
