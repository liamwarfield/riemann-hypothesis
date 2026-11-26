module

public import Development.WeilBound.CoreStatements.BranchingTraces.HeBranching
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSliceCut
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.BranchingTraces.BranchingComatrices.ContDiffEmb
noncomputable section

open Matrix
open scoped ContDiff

namespace PositivityTheory.UnitaryDecomposition.Com

open Formalism.REAL PI.DSInfCharCap CompanionTheory.D.Upq.Sm

variable {n : ℕ} (e : Fin n ⊕ Unit ≃ Fin (n + 1))

def blk : Matrix (Fin n) (Fin n) ℂ × ℂ →ₐ[ℂ] Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ where
  toFun p := Matrix.reindex e e (Matrix.fromBlocks p.1 0 0 (p.2 • 1))
  map_one' := by simp [Matrix.fromBlocks_one]
  map_mul' p q := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Prod.fst_mul, Prod.snd_mul]
    simp [smul_smul, mul_comm]
  map_zero' := by simp
  map_add' p q := by
    ext i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    rcases i with i | i <;> rcases j with j | j <;> simp [add_smul]
  commutes' c := by
    ext i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    rcases i with i | i <;> rcases j with j | j <;> simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply]

theorem blk_apply (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    blk e (A, c) = Matrix.reindex e e (Matrix.fromBlocks A 0 0 (c • 1)) := rfl

theorem emb_eq (A : Matrix (Fin n) (Fin n) ℂ) : emb e A = blk e (A, 1) := by simp [emb, blk_apply]

theorem blk_ct (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) : (blk e (A, c))ᴴ = blk e (Aᴴ, star c) := by
  simp [blk_apply, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]

theorem blk_single (a b : Fin n) :
    blk e (Matrix.single a b 1, 0) = Matrix.single (e (Sum.inl a)) (e (Sum.inl b)) 1 := by
  ext i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp [blk_apply, Matrix.single_apply]

variable {e} {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool}

theorem blk_J (hF : Fits ε ε' e) : Jm ε = blk e (Jm ε', 1) := by
  ext i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  have h1 : ε (e (Sum.inr ())) = true := hF.1
  rcases i with i | i <;> rcases j with j | j <;> simp [blk_apply, Jm, Matrix.diagonal_apply, hF.2, h1]

theorem emb_mem (hF : Fits ε ε' e) {h : Matrix (Fin n) (Fin n) ℂ} (hh : hᴴ * Jm ε' * h = Jm ε') :
    (emb e h)ᴴ * Jm ε * emb e h = Jm ε := by
  rw [emb_eq, blk_ct, blk_J hF, ← map_mul, ← map_mul]
  simp [hh]

theorem blk_theta (hF : Fits ε ε' e) (Y : Matrix (Fin n) (Fin n) ℂ) : thetaJ ε (blk e (Y, 0)) = blk e (thetaJ ε' Y, 0) := by
  unfold thetaJ
  rw [blk_ct, blk_J hF, ← map_mul, ← map_mul, ← map_neg]
  simp

theorem exp_blk (X : Matrix (Fin n) (Fin n) ℂ) : NormedSpace.exp (blk e (X, 0)) = emb e (NormedSpace.exp X) := by
  rw [blk_apply, Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential.exp_reindex, Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential.exp_fromBlocks, zero_smul, NormedSpace.exp_zero]
  rfl

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_emb : ContDiff ℝ ∞ (emb e) := by
  have h : emb e = fun A => (LinearMap.toContinuousLinearMap
      (((blk e).toLinearMap ∘ₗ LinearMap.inl ℂ _ ℂ).restrictScalars ℝ)) A + blk e (0, 1) := by
    funext A
    show _ = blk e (A, 0) + blk e (0, 1)
    rw [← map_add (f := _), emb_eq]; simp
  rw [h]
  exact (ContinuousLinearMap.contDiff _).add contDiff_const

variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {π : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (H →L[ℂ] H)} {σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')} {P : H →L[ℂ] H'}

theorem intertw_mat (hP : Intertw ε' e π σ P) {h : Matrix (Fin n) (Fin n) ℂ} (hh : hᴴ * Jm ε' * h = Jm ε') (x : H) :
    P (π (emb e h) x) = σ h (P x) := by
  have h1 : (Jm ε' * hᴴ * Jm ε') * h = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc hᴴ, hh, Jm_mul_self]
  exact hP.2 ⟨⟨h, _, mul_eq_one_comm.1 h1, h1⟩, hh⟩ x

theorem smooth_map (hF : Fits ε ε' e) (hP : Intertw ε' e π σ P) {η : H} (hη : η ∈ PI.PhMeasCore.smoothVecs (Jm ε) π) :
    P η ∈ PI.PhMeasCore.smoothVecs (Jm ε') σ := by
  have h1 : IsSm (PI.PhMeasCore.UH (Jm ε)) π η := hη
  have h2 := (SmOn.comp h1 (contDiff_emb (e := e)) (B := PI.PhMeasCore.UH (Jm ε')) fun h hh => emb_mem hF hh).clm
    (P.restrictScalars ℝ)
  exact SmOn.congr h2 fun h hh => (intertw_mat hP hh η).symm

theorem dsig_map (hP : Intertw ε' e π σ P) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε' X) {η : H}
    (hd : DifferentiableAt ℝ (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • blk e (X, 0))) η) 0) :
    P (PI.PhMeasCore.dsig π (blk e (X, 0)) η) = PI.PhMeasCore.dsig σ X (P η) := by
  have h1 := (P.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd.hasDerivAt
  have h2 : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (P η)) =
      (P.restrictScalars ℝ) ∘ fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • blk e (X, 0))) η := by
    funext t
    have e1 : (t : ℂ) • blk e (X, 0) = blk e ((t : ℂ) • X, 0) := by rw [← map_smul]; simp
    show _ = P (π (NormedSpace.exp ((t : ℂ) • blk e (X, 0))) η)
    rw [e1, exp_blk]
    exact (intertw_mat hP (ex_mem_of_lie hX t) η).symm
  unfold PI.PhMeasCore.dsig
  rw [h2, h1.deriv]
  rfl

theorem blk_inG (hF : Fits ε ε' e) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε' X) : inG ε (blk e (X, 0)) := by
  unfold inG at hX ⊢
  rw [blk_ct, blk_J hF, ← map_mul, ← map_mul, ← map_add (f := _)]
  simp [hX, ← Prod.zero_eq_mk]

theorem inG_parts (Y : Matrix (Fin n) (Fin n) ℂ) :
    inG ε' ((1 / 2 : ℂ) • (Y + thetaJ ε' Y)) ∧ inG ε' ((1 / (2 * Complex.I)) • (Y - thetaJ ε' Y)) := by
  have hJ : (Jm ε')ᴴ = Jm ε' := by
    unfold Jm
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    by_cases h : ε' a <;> simp [h]
  have a1 : Jm ε' * Y * Jm ε' * Jm ε' = Jm ε' * Y := by rw [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]
  have a2 : Jm ε' * (Jm ε' * Yᴴ * Jm ε') = Yᴴ * Jm ε' := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]
  have hθ : (thetaJ ε' Y)ᴴ * Jm ε' = -(Jm ε' * Y) := by
    unfold thetaJ
    rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJ, Matrix.conjTranspose_conjTranspose,
      Matrix.neg_mul, ← Matrix.mul_assoc, a1]
  have hθ' : Jm ε' * thetaJ ε' Y = -(Yᴴ * Jm ε') := by
    unfold thetaJ
    rw [Matrix.mul_neg, a2]
  unfold inG
  constructor
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
      Matrix.mul_add, hθ, hθ', show star (1 / 2 : ℂ) = 1 / 2 by simp, ← smul_add]
    simp
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,
      Matrix.mul_sub, hθ, hθ', show star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) by simp, neg_smul, ← sub_eq_neg_add,
      ← smul_sub]
    simp [add_comm]

theorem dsigC_map (hF : Fits ε ε' e) (hP : Intertw ε' e π σ P) {η : H}
    (hd : ∀ X, inG ε X → DifferentiableAt ℝ (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) η) 0)
    (Y : Matrix (Fin n) (Fin n) ℂ) : P (dsigC ε π (blk e (Y, 0)) η) = dsigC ε' σ Y (P η) := by
  have e1 : (1 / 2 : ℂ) • (blk e (Y, 0) + thetaJ ε (blk e (Y, 0))) = blk e ((1 / 2 : ℂ) • (Y + thetaJ ε' Y), 0) := by
    rw [blk_theta hF, ← map_add (f := _), ← map_smul]; simp
  have e2 : (1 / (2 * Complex.I)) • (blk e (Y, 0) - thetaJ ε (blk e (Y, 0))) =
      blk e ((1 / (2 * Complex.I)) • (Y - thetaJ ε' Y), 0) := by
    rw [blk_theta hF, ← map_sub, ← map_smul]; simp
  unfold dsigC
  rw [e1, e2, map_add (f := _), map_smul, dsig_map hP (inG_parts Y).1 (hd _ (blk_inG hF (inG_parts Y).1)),
    dsig_map hP (inG_parts Y).2 (hd _ (blk_inG hF (inG_parts Y).2))]

end PositivityTheory.UnitaryDecomposition.Com
end
end

section -- merged from Development.WeilBound.CoreStatements.BranchingTraces.BranchingComatrices.RootOfNe
open Finset Polynomial

noncomputable section

namespace PositivityTheory.UnitaryDecomposition.Com

open Formalism.REAL Formalism.FourierDecayAlt.P.CapelliAbstractCharacter

section Alg

variable {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} {E : Fin (N + 1) → Fin (N + 1) → Module.End ℂ V}
  {m : Fin (N + 1) → ℂ}

theorem th_mul (hE : GlRel E) (hq : ∀ u v, qdet E u v = (∏ j, (u + m j)) • v) {Y : Fin (N + 1) → V} {κ : ℂ}
    (hY : EE E Y = κ • Y) (u : ℂ) : (u - N + κ) • Th E u Y = (∏ j, (u + m j)) • Y := by
  funext i
  have h := comat E hE u Y i
  rw [hY, ← add_smul, map_smul, hq] at h
  exact h

theorem root_of_ne (hE : GlRel E) (hq : ∀ u v, qdet E u v = (∏ j, (u + m j)) • v) {Y : Fin (N + 1) → V} {κ : ℂ}
    (hY : EE E Y = κ • Y) (h0 : Y ≠ 0) : ∃ i, κ = N + m i := by
  have h := th_mul hE hq hY (N - κ)
  rw [show (N : ℂ) - κ - N + κ = 0 by ring, zero_smul, eq_comm, smul_eq_zero, or_iff_left h0, Finset.prod_eq_zero_iff] at h
  obtain ⟨i, -, hi⟩ := h
  exact ⟨i, by linear_combination -hi⟩

theorem th_eig (hE : GlRel E) (hq : ∀ u v, qdet E u v = (∏ j, (u + m j)) • v) {Y : Fin (N + 1) → V} (i : Fin (N + 1))
    (hY : EE E Y = (N + m i) • Y) (u : ℂ) : Th E u Y = (∏ j ∈ univ.erase i, (u + m j)) • Y := by
  obtain ⟨A, hA⟩ := Th_pol E
  have hQ : (∏ j ∈ univ.erase i, ((X : ℂ[X]) + C (m j))).natDegree < N + 1 :=
    lt_of_le_of_lt (deg_prod_lin _ _) (by simp [Finset.card_erase_of_mem])
  have hdiff : ∀ u : ℂ, Th E u Y - (∏ j ∈ univ.erase i, (u + m j)) • Y =
      ∑ s ∈ range (N + 1), u ^ s • (A s Y - (∏ j ∈ univ.erase i, ((X : ℂ[X]) + C (m j))).coeff s • Y) := by
    intro u
    rw [hA, ← eval_prod_lin, Polynomial.eval_eq_sum_range' hQ, Finset.sum_smul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by rw [smul_sub, smul_smul, mul_comm]
  have hz := polyVanish (N + 1)
    (fun s => A s Y - (∏ j ∈ univ.erase i, ((X : ℂ[X]) + C (m j))).coeff s • Y) {-m i}
    (fun u hu => by
      rw [← hdiff]
      have hne : u + m i ≠ 0 := fun h => hu (by simp [eq_neg_of_add_eq_zero_left h])
      have hs := th_mul hE hq hY u
      rw [show u - N + (N + m i) = u + m i by ring] at hs
      have h0 : (u + m i) • (Th E u Y - (∏ j ∈ univ.erase i, (u + m j)) • Y) = 0 := by
        rw [smul_sub, smul_smul, Finset.mul_prod_erase univ (fun j => u + m j) (mem_univ i), hs, sub_self]
      exact (smul_eq_zero.1 h0).resolve_left hne)
  rw [← sub_eq_zero, hdiff]
  exact Finset.sum_eq_zero fun s hs => by rw [hz s hs, smul_zero]

theorem th_proj (hE : GlRel E) (hq : ∀ u v, qdet E u v = (∏ j, (u + m j)) • v) {ι : Type} (S : Finset ι)
    (Y : ι → Fin (N + 1) → V) (κ : ι → ℂ) (hκ : Set.InjOn κ S) (hY : ∀ t ∈ S, EE E (Y t) = κ t • Y t) {s : ι} (hs : s ∈ S)
    (i : Fin (N + 1)) (hi : κ s = N + m i) :
    Th E (-m i) (∑ t ∈ S, Y t) = (∏ j ∈ univ.erase i, (-m i + m j)) • Y s := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single_of_mem s hs fun t ht hts => ?_]
  · exact th_eig hE hq i (hi ▸ hY s hs) _
  · have h := th_mul hE hq (hY t ht) (-m i)
    rw [Finset.prod_eq_zero (mem_univ i) (by ring), zero_smul, smul_eq_zero] at h
    refine h.resolve_left fun h0 => hts (hκ ht hs ?_)
    rw [hi]; linear_combination h0

theorem th_single (u : ℂ) (l c : Fin (N + 1)) (v : V) :
    Th E u (Pi.single l v) c = ((-1 : ℂ) ^ ((l : ℕ) + (c : ℕ))) • qminor E l.succAbove c.succAbove u v := by
  rw [Th_apply, Finset.sum_eq_single l (fun a _ ha => by simp [Pi.single_eq_of_ne ha]) (by simp), Pi.single_eq_same]

theorem corner (hE : GlRel E) (z : Fin (N + 1)) (ι : Fin N → Fin (N + 1)) (hι : Function.Injective ι) (hz : ∀ a, ι a ≠ z)
    (u : ℂ) : qminor E z.succAbove z.succAbove u = qdet (fun a b => E (ι a) (ι b)) u := by
  choose f hf using fun a => Fin.exists_succAbove_eq (hz a)
  have hfi : Function.Injective f := fun a b h => hι (by rw [← hf a, ← hf b, h])
  let τ : Equiv.Perm (Fin N) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hfi)
  have e : ι = z.succAbove ∘ τ := funext fun a => (hf a).symm
  have h1 : qdet (fun a b => E (ι a) (ι b)) u = qminor E ι ι u := by
    unfold qdet qminor Tm
    simp only [id, hι.eq_iff]
  rw [h1, e, quantumMinorRowSkew_holds, quantumMinorColSkew_holds _ _ _ _ hE, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

end Alg

theorem qdet_int {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {n : ℕ}
    {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ V'} (f : V →ₗ[ℂ] V')
    (hf : ∀ a b x, f (E a b x) = E' a b (f x)) (u : ℂ) (x : V) : f (qdet E u x) = qdet E' u (f x) := by
  have tm : ∀ w a b y, f (Tm E w a b y) = Tm E' w a b (f y) := fun w a b y => by
    unfold Tm
    split_ifs <;> simp [Module.algebraMap_end_apply, hf]
  have hl : ∀ (L : List (ℂ × Fin n × Fin n)) y, f ((L.map fun p => Tm E p.1 p.2.1 p.2.2).prod y) =
      (L.map fun p => Tm E' p.1 p.2.1 p.2.2).prod (f y) := fun L y => by
    induction L with
    | nil => simp
    | cons p L ih => simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp, tm, ih]
  unfold qdet qminor
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_apply_eq_comp, mul_apply_eq_comp, intCast_apply_eq_smul, intCast_apply_eq_smul, map_zsmul]
  have := hl (List.ofFn fun k : Fin n => (u - (k : ℂ), σ k, k)) x
  simp only [List.map_ofFn] at this
  exact congrArg _ this

section Norm

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V}

theorem prod_bd {v : V} {S : ℕ} {M R : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hW : ∀ W : List (Fin n × Fin n), W.length ≤ S → ‖(W.map fun p => E p.1 p.2).prod v‖ ≤ M ^ W.length * ‖v‖) :
    ∀ (L : List (ℂ × Fin n × Fin n)), (∀ p ∈ L, ‖p.1‖ ≤ R) → ∀ W : List (Fin n × Fin n), W.length + L.length ≤ S →
      ‖(W.map fun p => E p.1 p.2).prod ((L.map fun p => Tm E p.1 p.2.1 p.2.2).prod v)‖ ≤
        (R + M) ^ L.length * M ^ W.length * ‖v‖ := by
  intro L
  induction L with
  | nil =>
    intro _ W h
    simpa using hW W (by simpa using h)
  | cons p L ih =>
    intro hL W h
    have hL' : ∀ q ∈ L, ‖q.1‖ ≤ R := fun q hq => hL q (List.mem_cons_of_mem _ hq)
    have h1 := ih hL' W (by simp at h; omega)
    have h2 := ih hL' (W ++ [p.2]) (by simp at h ⊢; omega)
    set y := (L.map fun p => Tm E p.1 p.2.1 p.2.2).prod v with hy
    have e : (((p :: L).map fun p => Tm E p.1 p.2.1 p.2.2).prod v) = (if p.2.1 = p.2.2 then p.1 else 0) • y + E p.2.1 p.2.2 y := by
      rw [List.map_cons, List.prod_cons, mul_apply_eq_comp, ← hy]
      unfold Tm
      split_ifs <;> simp [Module.algebraMap_end_apply]
    have hc : ‖(if p.2.1 = p.2.2 then p.1 else 0)‖ ≤ R := by
      split_ifs
      · exact hL p List.mem_cons_self
      · simpa [Function.comp_def] using hR
    simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      mul_apply_eq_comp, List.length_append, List.length_cons, List.length_nil, zero_add] at h2
    rw [e, map_add (f := _), map_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, List.length_cons]
    have hRM : 0 ≤ R + M := add_nonneg hR hM
    calc _ ≤ R * ((R + M) ^ L.length * M ^ W.length * ‖v‖) + (R + M) ^ L.length * M ^ (W.length + 1) * ‖v‖ :=
          add_le_add (mul_le_mul_of_nonneg hc h1 (norm_nonneg _) (by positivity)) h2
      _ = _ := by ring

theorem qminor_bd {t : ℕ} {v : V} {M R : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hW : ∀ W : List (Fin n × Fin n), W.length ≤ t → ‖(W.map fun p => E p.1 p.2).prod v‖ ≤ M ^ W.length * ‖v‖)
    (a b : Fin t → Fin n) (u : ℂ) (hu : ∀ k : Fin t, ‖u - (k : ℂ)‖ ≤ R) :
    ‖qminor E a b u v‖ ≤ t.factorial * ((R + M) ^ t * ‖v‖) := by
  unfold qminor
  rw [LinearMap.sum_apply]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ ((R + M) ^ t * ‖v‖) fun σ _ => ?_).trans ?_)
  · have h := prod_bd hR hM hW (List.ofFn fun k : Fin t => (u - (k : ℂ), a (σ k), b k))
      (fun p hp => by obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hp; exact hu k) [] (by simp)
    simp only [List.map_ofFn, List.map_nil, List.prod_nil, List.length_ofFn, List.length_nil, pow_zero, mul_one,
      one_apply_eq_self] at h
    rw [mul_apply_eq_comp, intCast_apply_eq_smul]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> rw [e]
    · simpa [Function.comp_def] using h
    · simpa [Function.comp_def] using h
  · simp [Fintype.card_perm]

end Norm

end PositivityTheory.UnitaryDecomposition.Com
end
end

noncomputable section

open Matrix Finset

namespace PositivityTheory.UnitaryDecomposition.Com

open Formalism.REAL PI.DSInfCharCap CompanionTheory.D.DSIC Formalism.FourierDecayAlt.P.CapelliAbstractCharacter

theorem cap_of {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hπ : Formalism.MainNotions.S.IsDS ε lam π)
    {S : Submodule ℂ H} {E : Fin m → Fin m → Module.End ℂ S} (hS : IsSmMod ε π S E) (u : ℂ) (v : S) :
    qdet E u v = (∏ j, (u + ((lam j : ℂ) - ((m : ℂ) - 1) / 2))) • v := by
  have h := discrete_series_infinitesimal_character m ε lam H π hl hπ v ((hS.mem _).1 v.2) (u - ((m : ℂ) - 1) / 2)
  rw [sub_add_cancel, hActQ m ε H π S E hS] at h
  refine Subtype.ext (h.trans ?_)
  rw [Submodule.coe_smul, Formalism.QuantumDeterminants.capP]
  congr 1
  exact Finset.prod_congr rfl fun j _ => by ring

theorem one_le_diff {m : ℕ} {lam : Fin m → ℝ} (hl : Formalism.QuantumDeterminants.IsHCParam lam) {i j : Fin m} (h : j ≠ i) :
    1 ≤ |lam j - lam i| := by
  obtain ⟨a, ha⟩ := hl.2 i
  obtain ⟨b, hb⟩ := hl.2 j
  have e : lam j - lam i = ((b - a : ℤ) : ℝ) := by push_cast; linarith
  have h0 : b - a ≠ 0 := fun h0 => h (hl.1.injective (by rw [h0] at e; simpa [sub_eq_zero] using e))
  rw [e, ← Int.cast_abs]
  exact_mod_cast Int.one_le_abs h0

theorem spread {n : ℕ} {lam : Fin (n + 1) → ℝ} (hl : Formalism.QuantumDeterminants.IsHCParam lam) {B : ℝ} (hB : ∀ a, |lam a| ≤ B) :
    (n : ℝ) ≤ 2 * B := by
  have hA := hl.1
  have key : ∀ k : ℕ, ∀ hk : k ≤ n, (k : ℝ) ≤ lam 0 - lam ⟨k, by omega⟩ := by
    intro k
    induction k with
    | zero => intro hk; simp
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have hlt : lam ⟨k + 1, by omega⟩ < lam ⟨k, by omega⟩ := hA (by simp [Fin.lt_def])
      have hne : (⟨k + 1, by omega⟩ : Fin (n + 1)) ≠ ⟨k, by omega⟩ := by simp [Fin.ext_iff]
      have h2 := one_le_diff hl hne
      rw [abs_of_neg (by linarith)] at h2
      push_cast
      linarith
  have h := key n le_rfl
  have h0 := (abs_le.mp (hB 0)).2
  have hn := (abs_le.mp (hB ⟨n, by omega⟩)).1
  linarith

private theorem exists_norm_le_one_p_eq_smul_Th {n : ℕ} {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → H →L[ℂ] H}
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hπ : Formalism.MainNotions.S.IsDS ε lam π) {S : Submodule ℂ H}
    {E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ S} (hS : IsSmMod ε π S E) (X : Dec ε lam π)
    {s : Fin (n + 1)} (hs : s ∈ X.S) :
    ∃ (i : Fin (n + 1)) (c0 : ℂ), ‖c0‖ ≤ 1 ∧ ∀ (x : Fin (n + 1) → S) (c : Fin (n + 1)),
      X.p s (fun l => (x l : H)) c =
        c0 • ((Th E (-((lam i : ℂ) - (((n + 1 : ℕ) : ℂ) - 1) / 2)) x c : S) : H) := by
  classical
  set mm : Fin (n + 1) → ℂ := fun j => (lam j : ℂ) - (((n + 1 : ℕ) : ℂ) - 1) / 2 with hmm
  have hq : ∀ (u : ℂ) (v : S), qdet E u v = (∏ j, (u + mm j)) • v := fun u v => cap_of hl hπ hS u v
  have hgl : GlRel E := hS.gl
  have hxs : ∀ x : Fin (n + 1) → S, (fun l => (x l : H)) ∈ SmT ε π := fun x l => (hS.mem _).1 (x l).2
  let Y : (Fin (n + 1) → S) → Fin (n + 1) → Fin (n + 1) → S := fun x t c =>
    if ht : t ∈ X.S then ⟨X.p t (fun l => (x l : H)) c, (hS.mem _).2 (X.p_sm t ht _ (hxs x) c)⟩ else 0
  have hYs : ∀ x t, t ∈ X.S → ∀ c, ((Y x t c : S) : H) = X.p t (fun l => (x l : H)) c := by
    intro x t ht c
    simp [Y, ht]
  have hEig : ∀ x t, t ∈ X.S → EE E (Y x t) = X.κ t • Y x t := by
    intro x t ht
    funext c
    apply Subtype.ext
    rw [EE_apply]
    simp only [Submodule.coe_sum, hS.act, Pi.smul_apply, Submodule.coe_smul, hYs x t ht]
    have h2 := congrFun (X.cas t ht _ (hxs x)) c
    simpa [casT] using h2
  have hSum : ∀ x, ∑ t ∈ X.S, Y x t = x := by
    intro x
    funext c
    apply Subtype.ext
    rw [Finset.sum_apply, Submodule.coe_sum, Finset.sum_congr rfl fun t ht => hYs x t ht c,
      ← Finset.sum_apply, X.sum _ (hxs x)]
  by_cases h0 : ∀ x : Fin (n + 1) → S, Y x s = 0
  · refine ⟨0, 0, by simp, fun x c => ?_⟩
    rw [← hYs x s hs c, h0 x]
    simp
  · push_neg at h0
    obtain ⟨x0, hx0⟩ := h0
    obtain ⟨i, hi⟩ := root_of_ne hgl hq (hEig x0 s hs) hx0
    set D := ∏ j ∈ univ.erase i, (-mm i + mm j) with hD
    have hD1 : 1 ≤ ‖D‖ := by
      rw [hD, norm_prod]
      calc (1 : ℝ) = ∏ j ∈ univ.erase i, (1 : ℝ) := by simp
        _ ≤ ∏ j ∈ univ.erase i, ‖-mm i + mm j‖ := by
          apply Finset.prod_le_prod₀ (fun _ _ => zero_le_one)
          intro j hj
          have hji : j ≠ i := Finset.ne_of_mem_erase hj
          have he : -mm i + mm j = ((lam j - lam i : ℝ) : ℂ) := by
            simp only [hmm]
            push_cast
            ring
          rw [he, Complex.norm_real, Real.norm_eq_abs]
          exact one_le_diff hl hji
    have hDne : D ≠ 0 := by
      intro h
      rw [h, norm_zero] at hD1
      linarith
    refine ⟨i, D⁻¹, ?_, fun x c => ?_⟩
    · rw [norm_inv]
      exact inv_le_one_of_one_le₀ hD1
    · have hT := th_proj hgl hq X.S (Y x) X.κ X.κ_inj (fun t ht => hEig x t ht) hs i hi
      rw [hSum x] at hT
      rw [hT, Pi.smul_apply, Submodule.coe_smul, smul_smul, inv_mul_cancel₀ hDne, one_smul, hYs x s hs c]

private theorem list_prod_E_apply_eq_dsigCW {m : ℕ} {ε : Fin m → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {π : Matrix (Fin m) (Fin m) ℂ → H →L[ℂ] H} {S : Submodule ℂ H} {E : Fin m → Fin m → Module.End ℂ S}
    (hS : IsSmMod ε π S E) (W : List (Fin m × Fin m)) (w : S) :
    (((W.map (fun p => E p.1 p.2)).prod w : S) : H) =
      dsigCW ε π (W.map (fun p => single p.1 p.2 (1 : ℂ))) (w : H) := by
  induction W with
  | nil => rfl
  | cons p W ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [hS.act, ih]
    rfl

private theorem hs_single_one_le_one {m : ℕ} (a b : Fin m) : hs (single a b (1 : ℂ)) ≤ 1 := by
  simp only [hs, Matrix.single_apply]
  rw [Finset.sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  rw [Finset.sum_eq_single b (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  simp

theorem comat_of (hW : WordBd) : Comat := by
  unfold Comat ForPairs
  intro n ε lam ε' mu B e H H' _ _ _ _ _ _ π σ ν hν hF hP hπ hσ X s hs
  obtain ⟨S, E, hS⟩ := hSmMod (n + 1) ε H π (show PI.UpqRep.IsDS ε lam π from hπ).2.2.1
  obtain ⟨S', E', hS'⟩ := hSmMod n ε' H' σ (show PI.UpqRep.IsDS ε' mu σ from hσ).2.2.1
  obtain ⟨i, c0, hc0, hform⟩ := exists_norm_le_one_p_eq_smul_Th hP.hc hπ hS X hs
  have hn2 := hP.two
  have hB : (n : ℝ) ≤ 2 * B := spread hP.hc hP.bd
  have hn2r : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hB1 : 1 ≤ B := by linarith
  have hK1 : (1 : ℝ) ≤ 8 * ((n : ℝ) + 1) * B := by nlinarith
  refine ⟨?_, ?_⟩
  · intro v hv l c
    have hGap : Formalism.QuantumDeterminants.GapAtLeast ε lam (100 * ((n + 1 : ℕ) : ℝ) ^ 3) := by
      intro a b hab
      refine le_trans ?_ (hP.gap a b hab)
      have : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := by positivity
      push_cast
      linarith
    obtain ⟨hsm, hwb⟩ := hW (n + 1) ε lam B H π (by omega) hP.hc hπ hP.bd hGap v hv
    let vs : S := ⟨v, (hS.mem v).2 hsm⟩
    have hx : (fun l' => ((Pi.single l vs : Fin (n + 1) → S) l' : H)) = Pi.single l v := by
      funext l'
      by_cases h : l' = l
      · subst h
        simp [vs]
      · simp [h]
    have h1 := hform (Pi.single l vs) c
    rw [hx, th_single] at h1
    rw [h1, norm_smul, Submodule.coe_smul, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    set M : ℝ := 8 * √((n + 1 : ℕ) : ℝ) * (B + n) with hMdef
    have hM : ∀ W : List (Fin (n + 1) × Fin (n + 1)), W.length ≤ n →
        ‖(W.map (fun p => E p.1 p.2)).prod vs‖ ≤ M ^ W.length * ‖vs‖ := by
      intro W hWl
      have h3 := hwb n (W.map (fun p => single p.1 p.2 (1 : ℂ))) (by simpa using hWl)
        (by
          simp only [List.mem_map]
          rintro _ ⟨p, _, rfl⟩
          exact hs_single_one_le_one p.1 p.2)
      rw [List.length_map] at h3
      show ‖(((W.map (fun p => E p.1 p.2)).prod vs : S) : H)‖ ≤ M ^ W.length * ‖v‖
      rw [list_prod_E_apply_eq_dsigCW hS W vs]
      exact h3
    have hR : ∀ k : Fin n, ‖-((lam i : ℂ) - (((n + 1 : ℕ) : ℂ) - 1) / 2) - ((k : ℕ) : ℂ)‖ ≤ 4 * B := by
      intro k
      have he : -((lam i : ℂ) - (((n + 1 : ℕ) : ℂ) - 1) / 2) - ((k : ℕ) : ℂ)
          = ((-lam i + (n : ℝ) / 2 - (k : ℕ) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [he, Complex.norm_real, Real.norm_eq_abs]
      have hk : ((k : ℕ) : ℝ) ≤ n := by exact_mod_cast k.2.le
      have hk0 : (0 : ℝ) ≤ (k : ℕ) := by positivity
      have h2 := hP.bd i
      rw [abs_le] at h2 ⊢
      constructor <;> nlinarith
    have hq : ‖((qminor E l.succAbove c.succAbove (-((lam i : ℂ) - (((n + 1 : ℕ) : ℂ) - 1) / 2)) vs : S) : H)‖
        ≤ (n.factorial : ℝ) * ((4 * B + M) ^ n * ‖v‖) :=
      qminor_bd (t := n) (by linarith) (by positivity) hM l.succAbove c.succAbove _ hR
    set K : ℝ := 8 * ((n : ℝ) + 1) * B with hKdef
    have hsq : √((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 1 :=
      Real.sqrt_le_iff.mpr ⟨by positivity, by push_cast; nlinarith⟩
    have hM3 : M ≤ 3 * K := by
      rw [hMdef, hKdef]
      have h0 : (0 : ℝ) ≤ B + n := by positivity
      have h5 : B + n ≤ 3 * B := by linarith
      calc 8 * √((n + 1 : ℕ) : ℝ) * (B + n) ≤ 8 * ((n : ℝ) + 1) * (3 * B) := by
            apply mul_le_mul (by linarith) h5 h0 (by positivity)
        _ = 3 * (8 * ((n : ℝ) + 1) * B) := by ring
    have hK24 : 24 * B ≤ K := by rw [hKdef]; nlinarith
    have h4 : 4 * B + M ≤ K ^ 2 := by nlinarith
    have hfact : (n.factorial : ℝ) ≤ K ^ n := by
      calc (n.factorial : ℝ) ≤ ((n ^ n : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_le_pow n
        _ = (n : ℝ) ^ n := by push_cast; ring
        _ ≤ K ^ n := pow_le_pow_left₀ (by positivity) (by nlinarith) n
    calc ‖c0‖ * _ ≤ 1 * ((n.factorial : ℝ) * ((4 * B + M) ^ n * ‖v‖)) :=
          mul_le_mul hc0 hq (norm_nonneg _) zero_le_one
      _ = ((n.factorial : ℝ) * (4 * B + M) ^ n) * ‖v‖ := by ring
      _ ≤ K ^ (4 * (n + 1)) * ‖v‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
        have hM0 : 0 ≤ M := by positivity
        calc (n.factorial : ℝ) * (4 * B + M) ^ n ≤ K ^ n * (K ^ 2) ^ n :=
              mul_le_mul hfact (pow_le_pow_left₀ (by positivity) h4 n) (by positivity) (by positivity)
          _ = K ^ (3 * n) := by rw [← pow_mul, ← pow_add]; ring_nf
          _ ≤ K ^ (4 * (n + 1)) := pow_le_pow_right₀ hK1 (by omega)
  · refine ⟨c0 * ∏ j : Fin n, (-((lam i : ℂ) - (((n + 1 : ℕ) : ℂ) - 1) / 2) + ((mu j : ℂ) - ((n : ℂ) - 1) / 2)), ?_, ?_⟩
    · rw [norm_mul, norm_prod]
      have hprod : ∏ j : Fin n, ‖-((lam i : ℂ) - (((n + 1 : ℕ) : ℂ) - 1) / 2) + ((mu j : ℂ) - ((n : ℂ) - 1) / 2)‖
          ≤ (8 * ((n : ℝ) + 1) * B) ^ n := by
        calc _ ≤ ∏ j : Fin n, (8 * ((n : ℝ) + 1) * B) := by
              apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
              intro j _
              have he : -((lam i : ℂ) - (((n + 1 : ℕ) : ℂ) - 1) / 2) + ((mu j : ℂ) - ((n : ℂ) - 1) / 2)
                  = ((mu j - lam i + 1 / 2 : ℝ) : ℂ) := by
                push_cast
                ring
              rw [he, Complex.norm_real, Real.norm_eq_abs]
              have h1 := hP.bd i
              have h2 := hP.bd' j
              rw [abs_le] at h1 h2 ⊢
              constructor <;> nlinarith
          _ = _ := by simp
      calc ‖c0‖ * _ ≤ 1 * (8 * ((n : ℝ) + 1) * B) ^ n :=
            mul_le_mul hc0 hprod (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one
        _ ≤ _ := by
          rw [one_mul]
          exact pow_le_pow_right₀ hK1 (Nat.le_succ n)
    · intro P hPI η hη
      have hηS : η ∈ S := (hS.mem η).2 hη
      let ηs : S := ⟨η, hηS⟩
      have hx : (fun l => ((Pi.single (zi e) ηs : Fin (n + 1) → S) l : H)) = Pi.single (zi e) η := by
        funext l
        by_cases h : l = zi e
        · subst h
          simp [ηs]
        · simp [h]
      have h1 := hform (Pi.single (zi e) ηs) (zi e)
      rw [hx, th_single] at h1
      rw [h1]
      have hpow : ((-1 : ℂ) ^ ((zi e : ℕ) + (zi e : ℕ))) = 1 := by
        rw [← two_mul, pow_mul]
        simp
      rw [hpow, one_smul]
      have hι : Function.Injective (fun a : Fin n => e (Sum.inl a)) :=
        fun a b h => Sum.inl_injective (e.injective h)
      have hιz : ∀ a : Fin n, e (Sum.inl a) ≠ zi e := fun a h => by
        have := e.injective h
        simp at this
      rw [corner hS.gl (zi e) _ hι hιz]
      have hPS : ∀ w : S, P w ∈ S' := fun w => (hS'.mem _).2 (smooth_map hF hPI ((hS.mem _).1 w.2))
      let f : S →ₗ[ℂ] S' := LinearMap.codRestrict S' (P.toLinearMap ∘ₗ S.subtype) hPS
      have hf : ∀ w : S, ((f w : S') : H') = P w := fun w => rfl
      have hcomm : ∀ (a b : Fin n) (w : S),
          f (E (e (Sum.inl a)) (e (Sum.inl b)) w) = E' a b (f w) := by
        intro a b w
        apply Subtype.ext
        rw [hf, hS'.act, hf, hS.act, ← blk_single]
        exact dsigC_map hF hPI (fun Xm hXm => (hS.real Xm hXm w).differentiableAt) (single a b 1)
      have hqi := qdet_int (E := fun a b => E (e (Sum.inl a)) (e (Sum.inl b))) f hcomm
        (-((lam i : ℂ) - (((n + 1 : ℕ) : ℂ) - 1) / 2)) ηs
      rw [cap_of hP.hc' hσ hS'] at hqi
      rw [map_smul, ← hf, hqi, Submodule.coe_smul, hf, smul_smul]

end PositivityTheory.UnitaryDecomposition.Com
