module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSpan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem co_mvps_equiv {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (e : A ≃+* B) (h : IsAdicComplete (maximalIdeal A) A) :
    IsAdicComplete (maximalIdeal B) B := by
  rw [← map_ringEquiv_maximalIdeal e, IsAdicComplete.congr_ringEquiv]
  exact h

private theorem co_mvps_fin (R : Type) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] (n : ℕ) :
    IsAdicComplete (maximalIdeal (MvPowerSeries (Fin n) R)) (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero => exact co_mvps_equiv (isEmptyEquiv (Fin 0) R).toRingEquiv.symm inferInstance
  | succ n ih =>
    exact co_mvps_equiv (finSuccEquiv R n).toRingEquiv.symm
      (UpperTheory.V.abelian₂.adicComplete (MvPowerSeries (Fin n) R))

theorem UpperTheory.V.Alg.co_mvps :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : Type) [Finite σ], IsCO O (MvPowerSeries σ R) := by
  intro O _ _ R _ _ hR σ _
  have hc : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  have hl : IsLocalHom (algebraMap O R) := IsCO.isLocalHom
  have hn : IsNoetherianRing R := hR.toIsNoetherian
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  refine
    { toIsLocalRing := inferInstance
      toIsNoetherian := MvPowerSeries.isNoetherianRing R
      complete := co_mvps_equiv (renameEquiv R e.symm).toRingEquiv (co_mvps_fin R n)
      isLocalHom := ⟨fun a ha => ?_⟩
      res_surj := fun x => ?_ }
  · have h := isUnit_constantCoeff _ ha
    rw [MvPowerSeries.algebraMap_apply, constantCoeff_C] at h
    exact IsLocalHom.map_nonunit a h
  · obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) (constantCoeff x)
    refine ⟨a, fun h => ha ?_⟩
    have h2 := isUnit_constantCoeff _ h
    rwa [map_sub, MvPowerSeries.algebraMap_apply, constantCoeff_C] at h2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
noncomputable section

namespace UpperTheory.V.Alg.WPres

variable {O X R : Type} [CommRing O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R] (W : WPres O X R)

instance gradedAlgebra : GradedAlgebra W.gr :=
  { (inferInstance : SetLike.GradedMonoid W.gr), (UpperTheory.V.Alg.gr_internal O X R W).chooseDecomposition with }

def originA (h : W.HasOrigin) : W.A →ₐ[O] O := (W.origin h).comp W.A.val


omit [DecidableEq X] in
def quot {R' : Type} [CommRing R'] [Algebra O R'] (p : R →ₐ[O] R') (hp : Function.Surjective p)
    (h : IsHomog O W.wt (RingHom.ker (p.comp W.π))) : WPres O X R' where
  σ := W.σ
  wt := W.wt
  π := p.comp W.π
  surj := hp.comp W.surj
  homog := h

end UpperTheory.V.Alg.WPres
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSqz
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.co_sqz :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (M : Type) [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] [Module O M] [IsScalarTower O R M] [Module.Finite R M] [Algebra O (TrivSqZeroExt R M)],
      (∀ c : O, algebraMap O (TrivSqZeroExt R M) c = TrivSqZeroExt.inl (algebraMap O R c)) → IsCO O (TrivSqZeroExt R M) := by
  intro O _ _ R _ _ _ M _ _ _ _ _ _ _ _ hO
  haveI : IsLocalRing (TrivSqZeroExt R M) :=
    IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
      simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
      exact IsLocalRing.isUnit_or_isUnit_one_sub_self a.fst
  haveI hST := IsScalarTower.of_algebraMap_eq (R := O) (S := R) (A := TrivSqZeroExt R M) fun c => by
    rw [hO, TrivSqZeroExt.algebraMap_eq_inl]
  haveI : Module.Finite R (TrivSqZeroExt R M) := inferInstanceAs (Module.Finite R (R × M))
  refine co_finite O R (TrivSqZeroExt R M) ?_
  intro x
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x.fst
  refine ⟨a, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, hO,
    TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inl]
  rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KerGen
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem ker_gen_closed {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (I : Ideal A)
    (f : A) (h : ∀ N : ℕ, ∃ g ∈ I, f - g ∈ maximalIdeal A ^ N) : f ∈ I := by
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := A ⧸ I) (maximalIdeal A) (maximalIdeal.isMaximal A).ne_top
  have hmem : Ideal.Quotient.mk I f ∈ ⨅ i, (maximalIdeal A) ^ i • (⊤ : Submodule A (A ⧸ I)) := by
    rw [Submodule.mem_iInf]
    intro N
    obtain ⟨g, hg, hfg⟩ := h N
    have heq : Ideal.Quotient.mk I f = (f - g) • (1 : A ⧸ I) := by
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one, map_sub,
        Ideal.Quotient.eq_zero_iff_mem.mpr hg, sub_zero]
    rw [heq]
    exact Submodule.smul_mem_smul hfg Submodule.mem_top
  rw [hbot, Submodule.mem_bot] at hmem
  exact Ideal.Quotient.eq_zero_iff_mem.mp hmem

private theorem ker_gen_approx {O : Type} [CommRing O] [IsLocalRing O] {X : Type} [AddCommGroup X]
    {σ : Type} [Finite σ] (wt : σ → X) (f : MvPowerSeries σ O) (N : ℕ) :
    ∃ T : Finset X, f - ∑ j ∈ T, wcomp O wt j f ∈ maximalIdeal (MvPowerSeries σ O) ^ N := by
  classical
  set D := (Finsupp.finite_of_degree_lt (σ := σ) N).toFinset with hD
  refine ⟨D.image (Finsupp.weight wt), ?_⟩
  have hX : ∀ i : σ, (AlgHom.id O (MvPowerSeries σ O)) (MvPowerSeries.X i) ∈ maximalIdeal (MvPowerSeries σ O) := by
    intro i
    rw [AlgHom.id_apply, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  have hord : ((N : ℕ) : ℕ∞) ≤ (f - ∑ j ∈ D.image (Finsupp.weight wt), wcomp O wt j f).order := by
    apply MvPowerSeries.nat_le_order
    intro d hd
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum]
    simp only [coeff_wcomp]
    rw [Finset.sum_ite_eq, if_pos, sub_self]
    exact Finset.mem_image_of_mem _ (by simpa [hD] using hd)
  have key := GlobalTheory.algHom_mem_pow_of_le_order (AlgHom.id O (MvPowerSeries σ O)) hX hord
  simpa using key

theorem UpperTheory.V.Alg.ker_gen :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] (σ : Type) [Finite σ] (wt : σ → X) (J : Ideal (MvPowerSeries σ O)), IsHomog O wt J →
      ∃ (n : ℕ) (f : Fin n → MvPowerSeries σ O) (c : Fin n → X), (∀ i, f i ∈ wtPart O wt (c i)) ∧ J = Ideal.span (Set.range f) := by
  intro O _ _ _ _ X _ σ _ wt J hJ
  classical
  set G : Set (MvPowerSeries σ O) := {g | ∃ f ∈ J, ∃ j : X, g = wcomp O wt j f} with hG
  have hGJ : Ideal.span G ≤ J := by
    rw [Ideal.span_le]
    rintro g ⟨f, hf, j, rfl⟩
    exact hJ f hf j
  have hJG : J ≤ Ideal.span G := by
    intro f hf
    apply ker_gen_closed (Ideal.span G) f
    intro N
    obtain ⟨T, hT⟩ := ker_gen_approx wt f N
    exact ⟨_, Ideal.sum_mem _ (fun j _ => Ideal.subset_span ⟨f, hf, j, rfl⟩), hT⟩
  have hfg : (Submodule.span (MvPowerSeries σ O) G).FG := IsNoetherian.noetherian _
  obtain ⟨s, hsG, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset G).mp hfg
  have hchoice : ∀ g : s, ∃ j : X, g.1 ∈ wtPart O wt j := by
    rintro ⟨g, hg⟩
    obtain ⟨f, _, j, rfl⟩ := hsG hg
    exact ⟨j, wcomp_mem O wt j f⟩
  choose c hc using hchoice
  refine ⟨s.card, fun i => (s.equivFin.symm i).1, fun i => c (s.equivFin.symm i), fun i => hc _, ?_⟩
  have hrange : Set.range (fun i => (s.equivFin.symm i).1) = (s : Set (MvPowerSeries σ O)) := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i).2
    · intro hg
      exact ⟨s.equivFin ⟨g, hg⟩, by simp⟩
  rw [hrange]
  calc J = Ideal.span G := le_antisymm hJG hGJ
    _ = Ideal.span (s : Set (MvPowerSeries σ O)) := hspan
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HhGroup
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TripleNe
theorem UpperTheory.Reformulated.B.Qk1.triple_ne :
    ∀ {R ι : Type} [inst : CommRing R] [inst_1 : Fintype ι]
    {A Y B : Matrix ι ι R} {a b : ι},
    (A * Y * B) a b ≠ (0 : R) → ∃ (c : ι) (d : ι), A a c ≠ (0 : R) ∧ Y c d ≠ (0 : R) ∧ B d b ≠ (0 : R) := by
  intro R ι _ _ A Y B a b h
  rw [Matrix.mul_apply] at h
  obtain ⟨d, -, hd⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h1 := left_ne_zero_of_mul hd
  rw [Matrix.mul_apply] at h1
  obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  exact ⟨c, d, left_ne_zero_of_mul hc, right_ne_zero_of_mul hc, right_ne_zero_of_mul hd⟩
end

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

open Matrix in
private theorem conj_form {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] {J A A' h : Matrix ι ι R} {ν : R}
    (e1 : A * A' = 1) (hA : Aᵀ * J * A = ν • J) (hh : hᵀ * J * h = J) :
    (A * h * A')ᵀ * J * (A * h * A') = J := by
  have e2 : A'ᵀ * Aᵀ = 1 := by rw [← transpose_mul, e1, transpose_one]
  calc (A * h * A')ᵀ * J * (A * h * A') = A'ᵀ * (hᵀ * (Aᵀ * J * A) * h) * A' := by
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = A'ᵀ * (Aᵀ * J * A) * A' := by
        rw [hA, mul_smul_comm, smul_mul_assoc, hh]
    _ = (A'ᵀ * Aᵀ) * J * (A * A') := by simp only [Matrix.mul_assoc]
    _ = J := by rw [e1, e2, one_mul, mul_one]

private theorem triple_ne {R ι : Type} [CommRing R] [Fintype ι] {A Y B : Matrix ι ι R} {a b : ι}
    (hab : (A * Y * B) a b ≠ 0) : ∃ c d, A a c ≠ 0 ∧ Y c d ≠ 0 ∧ B d b ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.Qk1.triple_ne hab

private theorem blk_inv {R ι κ : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (blk : ι → κ) {h h' : Matrix ι ι R}
    (e1 : h * h' = 1) (e2 : h' * h = 1) (hb : ∀ a b, blk a ≠ blk b → h a b = 0) :
    ∀ a b, blk a ≠ blk b → h' a b = 0 := by
  classical
  intro a b hab
  set E : Matrix ι ι R := Matrix.diagonal fun x => if blk x = blk a then 1 else 0 with hE
  have h1 : E * h = h * E := by
    ext x y
    rw [hE, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hxy : blk x = blk y
    · rw [hxy, mul_comm]
    · rw [hb x y hxy, mul_zero, zero_mul]
  have h2 : h' * E = E * h' := by
    calc h' * E = h' * (E * h) * h' := by rw [mul_assoc, mul_assoc, e1, mul_one]
      _ = E * h' := by rw [h1, ← mul_assoc, e2, one_mul]
  have h3 := congrFun (congrFun h2 a) b
  rw [hE, Matrix.diagonal_mul, Matrix.mul_diagonal, if_neg (Ne.symm hab), if_pos rfl, mul_zero, one_mul] at h3
  exact h3.symm

private theorem map_mul_alg {O R S ι : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    [Fintype ι] [DecidableEq ι] (f : R →ₐ[O] S) (A B : Matrix ι ι R) : (A * B).map f = A.map f * B.map f :=
  Matrix.map_mul (f := (f : R →+* S))

theorem UpperTheory.V.Alg.hh_group :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X) (Φ : FormData O w) (R : Type) [CommRing R] [Algebra O R] [IsCO O R],
      Φ.HH (1 : Matrix ι ι R) ∧ (∀ h h' : Matrix ι ι R, Φ.HH h → Φ.HH h' → Φ.HH (h * h')) ∧ (∀ h : Matrix ι ι R, Φ.HH h → ∃ h', Φ.HH h' ∧ h * h' = 1 ∧ h' * h = 1) ∧
      (∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (h : Matrix ι ι R), Φ.HH h → Φ.HH (h.map f)) ∧
      (∀ (Γ : Type) [Group Γ] (r0 : Γ →* Matrix ι ι O), Φ.Normalises r0 → ∀ (s : Γ) (h : Matrix ι ι R), Φ.HH h → Φ.HH ((r0 s).map (algebraMap O R) * h * (r0 s⁻¹).map (algebraMap O R))) ∧
      ∀ (t : Multiplicative X →* Rˣ) (h : Matrix ι ι R), Φ.HH h → Φ.HH (Matrix.of fun a b => (t (Multiplicative.ofAdd (w a - w b)) : R) * h a b) := by
  intro O _ _ ι X _ _ _ w Φ R _ _ _
  refine ⟨⟨by simp, fun a b hab => Matrix.one_apply_ne fun e => hab (by rw [e]), by simp⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rintro h h' ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
    refine ⟨?_, fun a b hab => ?_, by rw [map_mul_alg, a3, b3, one_mul]⟩
    · calc (h * h').transpose * Φ.JR R * (h * h') = h'.transpose * (h.transpose * Φ.JR R * h) * h' := by
            simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = Φ.JR R := by rw [a1, b1]
    · rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : Φ.blk a = Φ.blk c
      · rw [b2 c b (hc ▸ hab), mul_zero]
      · rw [a2 a c hc, zero_mul]
  · rintro h ⟨a1, a2, a3⟩
    have hJ : IsUnit (Φ.JR R) := Φ.unit.map (algebraMap O R).mapMatrix
    obtain ⟨K, hK⟩ := hJ.exists_left_inv
    have e2 : (K * h.transpose * Φ.JR R) * h = 1 := by
      rw [mul_assoc K, mul_assoc K, a1, hK]
    generalize K * h.transpose * Φ.JR R = h' at e2
    have e1 : h * h' = 1 := mul_eq_one_comm.1 e2
    refine ⟨h', ⟨?_, blk_inv Φ.blk e1 e2 a2, ?_⟩, e1, e2⟩
    · have := conj_form (h := h) (ν := (1 : R)) e1 (by rw [a1, one_smul]) a1
      calc h'.transpose * Φ.JR R * h' = h'.transpose * (h.transpose * Φ.JR R * h) * h' := by rw [a1]
        _ = (h * h').transpose * Φ.JR R * (h * h') := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = Φ.JR R := by rw [e1]; simp
    · have := congrArg (fun A : Matrix ι ι R => A.map (res O R)) e1
      simp only [map_mul_alg, a3, one_mul] at this
      rw [this]; simp
  · rintro R' _ _ _ f h ⟨a1, a2, a3⟩
    have hJ : Φ.JR R' = (Φ.JR R).map f := by
      ext a b; simp [FormData.JR]
    refine ⟨?_, fun a b hab => by simp [a2 a b hab], ?_⟩
    · rw [hJ, ← Matrix.transpose_map, ← map_mul_alg, ← map_mul_alg, a1]
    · rw [← a3]
      ext a b
      simp only [Matrix.map_apply, res_map]
  · rintro Γ _ r0 ⟨h1, ⟨π, h2⟩, -⟩ s h ⟨a1, a2, a3⟩
    have e1 : (r0 s).map (algebraMap O R) * (r0 s⁻¹).map (algebraMap O R) = 1 := by
      rw [← Matrix.map_mul, ← map_mul, mul_inv_cancel, map_one]; simp
    refine ⟨?_, fun a b hab => ?_, ?_⟩
    · obtain ⟨ν, hν⟩ := h1 s
      refine conj_form (ν := algebraMap O R ν) e1 ?_ a1
      have hO : Φ.JR O = Φ.J := by ext a b; simp [FormData.JR]
      rw [hO] at hν
      rw [FormData.JR, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hν]
      ext a b; simp
    · by_contra hne
      obtain ⟨c, d, k1, k2, k3⟩ := triple_ne hne
      have k1' : r0 s a c ≠ 0 := fun e => k1 (by simp [e])
      have k3' : r0 s⁻¹ d b ≠ 0 := fun e => k3 (by simp [e])
      have k4 : Φ.blk c = Φ.blk d := by_contra fun n => k2 (a2 c d n)
      apply hab
      rw [h2 s a c k1', k4, h2 s⁻¹ d b k3', map_inv]
      simp
    · rw [map_mul_alg, map_mul_alg, a3, mul_one, ← map_mul_alg, e1]; simp
  · rintro t h ⟨a1, a2, a3⟩
    refine ⟨?_, fun a b hab => by simp [a2 a b hab], ?_⟩
    · have e : (Matrix.of fun a b => (t (Multiplicative.ofAdd (w a - w b)) : R) * h a b) =
          Matrix.diagonal (fun a => (t (Multiplicative.ofAdd (w a)) : R)) * h *
            Matrix.diagonal (fun a => (t (Multiplicative.ofAdd (-w a)) : R)) := by
        ext a b
        rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply, sub_eq_add_neg, ofAdd_add, map_mul,
          Units.val_mul]
        ring
      rw [e]
      refine conj_form (ν := (t (Multiplicative.ofAdd Φ.c) : R)) ?_ ?_ a1
      · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1
        funext a
        rw [← Units.val_mul, ← map_mul, ← ofAdd_add, add_neg_cancel, ofAdd_zero, map_one, Units.val_one]
      · ext a b
        rw [Matrix.diagonal_transpose, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
        by_cases hJ : Φ.J a b = 0
        · simp [FormData.JR, hJ]
        · rw [← Φ.hw a b hJ, ofAdd_add, map_mul, Units.val_mul]
          ring
    · ext a b
      have k := congrFun (congrFun a3 a) b
      rw [Matrix.map_apply] at k
      rw [Matrix.map_apply, Matrix.of_apply, map_mul, k]
      by_cases hab : a = b
      · subst hab; simp
      · simp [Matrix.one_apply_ne hab]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.UnivCond
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem lift_map_map' {O : Type} [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ]
    [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)}
    {R R' R'' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R']
    [CommRing R''] [Algebra O R''] [IsCO O R''] (f : R →ₐ[O] R') (g : R' →ₐ[O] R'')
    (r : Lift O rbar R) : Lift.map g (Lift.map f r) = Lift.map (g.comp f) r := by
  apply Lift.ext
  ext x a b
  rfl

theorem UpperTheory.V.Alg.univ_cond :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (Γ ι : Type) [Group Γ] [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (r : Lift O rbar R) (P₀ P : Cond O rbar), Represents P₀ r → P.IsClosed → (∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra O R₁) (_ : IsCO O R₁) (r₁ : Lift O rbar R₁), P₀ R₁ r₁ ∧ P R₁ r₁) →
      ∃ (R' : Type) (_ : CommRing R') (_ : Algebra O R') (_ : IsCO O R') (p : R →ₐ[O] R'), Function.Surjective p ∧ Represents (fun C _ _ _ s => P₀ C s ∧ P C s) (r.map p) := by
  intro O _ _ Γ ι _ _ _ _ rbar R _ _ _ r P₀ P hrep hcl hex
  obtain ⟨I, hI⟩ := hcl R r
  obtain ⟨R₁, _, _, _, r₁, h0, h1⟩ := hex
  obtain ⟨f, hf, -⟩ := (hrep R₁).2 r₁ h0
  have hf1 : P R₁ (Lift.map f r) := hf ▸ h1
  have hfI : ∀ x ∈ I, f x = 0 := (hI R₁ f).1 hf1
  set J : Ideal R := Ideal.span I
  have hJf : ∀ x ∈ J, f x = 0 := by
    intro x hx
    have hle : J ≤ RingHom.ker f.toRingHom := Ideal.span_le.2 (fun y hy => hfI y hy)
    exact hle hx
  have hJ : J ≠ ⊤ := by
    intro htop
    have h1mem : (1 : R) ∈ J := htop ▸ Submodule.mem_top
    have := hJf 1 h1mem
    simp at this
  haveI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  haveI hco : IsCO O (R ⧸ J) := co_quot O R (R ⧸ J) (Ideal.Quotient.mkₐ O J) (Ideal.Quotient.mkₐ_surjective O J)
  have hpI : ∀ x ∈ I, Ideal.Quotient.mkₐ O J x = 0 := by
    intro x hx
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span hx
  refine ⟨R ⧸ J, inferInstance, inferInstance, hco, Ideal.Quotient.mkₐ O J, Ideal.Quotient.mkₐ_surjective O J, ?_⟩
  intro R'' _ _ _
  refine ⟨fun g => ?_, fun r' hr' => ?_⟩
  · rw [lift_map_map']
    refine ⟨(hrep R'').1 _, (hI R'' _).2 ?_⟩
    intro x hx
    rw [AlgHom.comp_apply, hpI x hx, map_zero]
  · obtain ⟨f', hf', huniq⟩ := (hrep R'').2 r' hr'.1
    have hf'I : ∀ x ∈ I, f' x = 0 := (hI R'' f').1 (hf' ▸ hr'.2)
    have hf'J : ∀ x ∈ J, f' x = 0 := by
      intro x hx
      have hle : J ≤ RingHom.ker f'.toRingHom := Ideal.span_le.2 (fun y hy => hf'I y hy)
      exact hle hx
    refine ⟨Ideal.Quotient.liftₐ J f' hf'J, ?_, ?_⟩
    · show Lift.map _ (Lift.map _ r) = r'
      rw [lift_map_map', Ideal.Quotient.liftₐ_comp]
      exact hf'
    · intro g hg
      apply Ideal.Quotient.algHom_ext O
      rw [Ideal.Quotient.liftₐ_comp]
      apply huniq
      show Lift.map _ r = r'
      rw [← lift_map_map']
      exact hg
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.TactVanish
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem tact_prod {X σ S : Type} [AddCommGroup X] [CommRing S] (wt : σ → X)
    (t : Multiplicative X →* Sˣ) (x : σ → S) (d : σ →₀ ℕ) :
    (d.prod fun i k => ((t (Multiplicative.ofAdd (wt i)) : S) * x i) ^ k) =
      (t (Multiplicative.ofAdd (Finsupp.weight wt d)) : S) * d.prod fun i k => x i ^ k := by
  simp_rw [mul_pow]
  rw [Finsupp.prod_mul]
  congr 1
  rw [Finsupp.weight_apply, Finsupp.sum, ofAdd_sum, map_prod, Units.coe_prod, Finsupp.prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ofAdd_nsmul, map_pow, Units.val_pow_eq_pow_val]

private theorem tact_aeval {O X σ S : Type} [CommRing O] [AddCommGroup X] [CommRing S] [Algebra O S]
    (wt : σ → X) (t : Multiplicative X →* Sˣ) (x : σ → S) (j : X) (p : MvPolynomial σ O)
    (hp : ∀ d, Finsupp.weight wt d ≠ j → AddMonoidAlgebra.coeff p d = 0) :
    MvPolynomial.aeval (fun i => (t (Multiplicative.ofAdd (wt i)) : S) * x i) p =
      (t (Multiplicative.ofAdd j) : S) * MvPolynomial.aeval x p := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [p.as_sum, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' : Finsupp.weight wt d = j := by
    by_contra h
    exact MvPolynomial.mem_support_iff.1 hd (hp d h)
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, tact_prod, hd']
  ring

private theorem tact_approx {O X σ : Type} [CommRing O] [AddCommGroup X] [Finite σ] (wt : σ → X)
    (F : MvPowerSeries σ O) (n : ℕ) :
    ∃ s : Finset X, (n : ℕ∞) ≤ (F - ∑ j ∈ s, wcomp O wt j F).order := by
  classical
  refine ⟨(truncTotal n F).support.image (Finsupp.weight wt), nat_le_order fun d hd => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum]
  simp only [coeff_wcomp]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · exact sub_self _
  · rw [sub_zero]
    by_contra h0
    refine h (Finset.mem_image_of_mem _ (MvPolynomial.mem_support_iff.2 ?_))
    rwa [coeff_truncTotal _ hd]

private theorem tact_vanish {O X σ S : Type} [CommRing O] [AddCommGroup X] [Finite σ] [CommRing S]
    [Algebra O S] (wt : σ → X) (J : Ideal S) [IsHausdorff J S] (φ : MvPowerSeries σ O →ₐ[O] S)
    (hφ : ∀ i, φ (MvPowerSeries.X i) ∈ J) (F : MvPowerSeries σ O) (h : ∀ j, φ (wcomp O wt j F) = 0) :
    φ F = 0 := by
  apply GlobalTheory.eq_of_forall_sub_mem_ideal_pow J
  intro n
  obtain ⟨s, hs⟩ := tact_approx wt F n
  have hm := GlobalTheory.algHom_mem_pow_of_le_order φ hφ hs
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum] at hm
  simpa [h] using hm

theorem UpperTheory.V.Alg.tact :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (X : Type) [AddCommGroup X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (t : Multiplicative X →* R'ˣ),
      ∃! f' : R →ₐ[O] R', ∀ j, ∀ x ∈ W.part j, f' x = t (Multiplicative.ofAdd j) * f x := by
  intro O _ _ X _ R _ _ _ W hz R' _ _ _ f t
  classical
  haveI : Fintype W.σ := W.fin
  haveI : IsAdicComplete (maximalIdeal R') R' := IsCO.complete (O := O)
  have hf_max : ∀ x ∈ maximalIdeal R, f x ∈ maximalIdeal R' := by
    intro x hx
    rw [← res_eq_zero_iff O R' (f x), UpperTheory.V.Alg.res_map f x, res_eq_zero_iff O R x]
    exact hx
  let xs : W.σ → R' := fun i =>
    (t (Multiplicative.ofAdd (W.wt i)) : R') * f (W.π (MvPowerSeries.X i))
  have hxs : ∀ i, xs i ∈ maximalIdeal R' := fun i => Ideal.mul_mem_left _ _ (hf_max _ (hz i))
  obtain ⟨Ψ, hΨX, hΨtr⟩ : ∃ Ψ : MvPowerSeries W.σ O →ₐ[O] R', (∀ i, Ψ (MvPowerSeries.X i) = xs i) ∧
      ∀ (n : ℕ) (G : MvPowerSeries W.σ O),
        Ψ G - MvPolynomial.aeval xs (truncTotal n G) ∈ maximalIdeal R' ^ n :=
    ⟨_, GlobalTheory.mvEvalAdic_X _ xs hxs, GlobalTheory.mvEvalAdic_sub_aeval_truncTotal_mem _ xs hxs⟩
  have key : ∀ j, ∀ G ∈ wtPart O W.wt j,
      Ψ G = (t (Multiplicative.ofAdd j) : R') * f (W.π G) := by
    intro j G hG
    apply GlobalTheory.eq_of_forall_sub_mem_ideal_pow (maximalIdeal R')
    intro n
    have h1 := hΨtr n G
    have h2 := GlobalTheory.algHom_sub_aeval_truncTotal_mem (f.comp W.π) (J := maximalIdeal R')
      (fun i => hf_max _ (hz i)) n G
    simp only [AlgHom.coe_comp, Function.comp_apply] at h2
    have h3 : MvPolynomial.aeval xs (truncTotal n G) =
        (t (Multiplicative.ofAdd j) : R') *
          MvPolynomial.aeval (fun i => f (W.π (MvPowerSeries.X i))) (truncTotal n G) := by
      refine tact_aeval W.wt t (fun i => f (W.π (MvPowerSeries.X i))) j _ fun d hd => ?_
      rw [coeff_truncTotal_eq_ite]
      split_ifs
      · exact hG d hd
      · rfl
    have he : Ψ G - (t (Multiplicative.ofAdd j) : R') * f (W.π G) =
        (Ψ G - MvPolynomial.aeval xs (truncTotal n G)) -
          (t (Multiplicative.ofAdd j) : R') *
            (f (W.π G) - MvPolynomial.aeval (fun i => f (W.π (MvPowerSeries.X i))) (truncTotal n G)) := by
      rw [h3]
      ring
    rw [he]
    exact Ideal.sub_mem _ h1 (Ideal.mul_mem_left _ _ h2)
  have hker : ∀ F ∈ RingHom.ker W.π, Ψ F = 0 := by
    intro F hF
    refine tact_vanish W.wt (maximalIdeal R') Ψ (fun i => by rw [hΨX]; exact hxs i) F fun j => ?_
    rw [key j _ (wcomp_mem O W.wt j F)]
    have h0 : W.π (wcomp O W.wt j F) = 0 := RingHom.mem_ker.mp (W.homog F hF j)
    rw [h0, map_zero, mul_zero]
  let f' : R →ₐ[O] R' := (Ideal.Quotient.liftₐ (RingHom.ker W.π) Ψ hker).comp
    (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm.toAlgHom
  have hf'π : ∀ G, f' (W.π G) = Ψ G := by
    intro G
    have hs : (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm (W.π G) =
        Ideal.Quotient.mk (RingHom.ker W.π) G := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    show Ideal.Quotient.liftₐ (RingHom.ker W.π) Ψ hker
      ((Ideal.quotientKerAlgEquivOfSurjective W.surj).symm (W.π G)) = Ψ G
    rw [hs]
    rfl
  refine ⟨f', ?_, ?_⟩
  · intro j x hx
    obtain ⟨G, hG, rfl⟩ := Submodule.mem_map.mp hx
    simp only [AlgHom.toLinearMap_apply]
    rw [hf'π, key j G hG]
  · intro g hg
    have hgz : ∀ i, g (W.π (MvPowerSeries.X i)) = xs i := fun i => hg (W.wt i) (W.z i) (W.z_mem i)
    have hcomp : g.comp W.π = Ψ := by
      apply GlobalTheory.mvPowerSeries_algHom_ext_of_isHausdorff (maximalIdeal R')
      · intro i
        rw [AlgHom.comp_apply, hgz]
        exact hxs i
      · intro i
        rw [AlgHom.comp_apply, hgz, hΨX]
    ext x
    obtain ⟨G, rfl⟩ := W.surj x
    rw [hf'π, ← AlgHom.comp_apply, hcomp]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.MapPart
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.map_part :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (W' : WPres O X R'), (∀ s, W'.z s ∈ maximalIdeal R') → ∀ f : R →ₐ[O] R', (∀ s, f (W.z s) ∈ W'.part (W.wt s)) → ∀ j, ∀ x ∈ W.part j, f x ∈ W'.part j := by
  intro O _ _ _ _ X _ _ _ _ R _ _ _ W hW R' _ _ _ W' hW' f hf j x hx
  classical
  obtain ⟨g, hg, rfl⟩ := hx
  have hm : ∀ s, (f.comp W.π) (MvPowerSeries.X s) ∈ maximalIdeal R' := fun s => by
    show f (W.z s) ∈ maximalIdeal R'
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hW s
  refine part_closed O X R' W' hW' j _ fun N => ⟨_, ?_, GlobalTheory.algHom_sub_aeval_truncTotal_mem (f.comp W.π) hm N g⟩
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hw : Finsupp.weight W.wt d = j := by
    by_contra hne
    apply MvPolynomial.mem_support_iff.1 hd
    rw [coeff_truncTotal_eq_ite, hg d hne, ite_self]
  rw [← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  rw [← hw, Finsupp.weight_apply, Finsupp.sum]
  exact SetLike.prod_pow_mem_graded W'.part W.wt (fun s => f (W.z s)) d (fun s _ => hf s)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ExistsLimitOfSuccessiveDiffMemFiltration
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.exists_limit_of_successive_diff_mem_filtration :
    ∀ (P : Type) [CommRing P] (m : Ideal P) [IsPrecomplete m P] (J : ℕ → Ideal P), (∀ N, m ^ (N + 1) ≤ J N) → (∀ N, J N ≤ J (N + 1) ⊔ m ^ (N + 1)) → ∀ (N₀ : ℕ) (p : ℕ → P), (∀ N, N₀ ≤ N → p (N + 1) - p N ∈ J N) → ∃ x : P, (∀ N, N₀ ≤ N → x - p N ∈ J N) ∧ x - p N₀ ∈ m ^ (N₀ + 1) := by
  intro P _ m _ J hmJ hJ N₀ p hp
  classical
  have hsm : ∀ n, (m ^ n • ⊤ : Submodule P P) = m ^ n := by
    intro n
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have step : ∀ (k : ℕ) (y : P), ∃ y' : P,
      y - p (N₀ + k) ∈ J (N₀ + k) →
        y' - p (N₀ + k + 1) ∈ J (N₀ + k + 1) ∧ y' - y ∈ m ^ (N₀ + k + 1) := by
    intro k y
    by_cases hy : y - p (N₀ + k) ∈ J (N₀ + k)
    · have h1 : y - p (N₀ + k + 1) ∈ J (N₀ + k) := by
        have h := sub_mem hy (hp (N₀ + k) (Nat.le_add_right _ _))
        have e : y - p (N₀ + k + 1) = y - p (N₀ + k) - (p (N₀ + k + 1) - p (N₀ + k)) := by ring
        rw [e]
        exact h
      obtain ⟨j, hj, t, ht, hjt⟩ := Submodule.mem_sup.1 (hJ (N₀ + k) h1)
      refine ⟨y - t, fun _ => ⟨?_, ?_⟩⟩
      · have e : y - t - p (N₀ + k + 1) = j := by
          rw [sub_right_comm, ← hjt]
          ring
        rw [e]
        exact hj
      · rw [sub_sub_cancel_left]
        exact neg_mem ht
    · exact ⟨y, fun h => absurd h hy⟩
  choose g hg using step
  let q : ℕ → P := fun k => Nat.rec (p N₀) (fun k y => g k y) k
  have hq0 : q 0 = p N₀ := rfl
  have hqs : ∀ k, q (k + 1) = g k (q k) := fun k => rfl
  have hqJ : ∀ k, q k - p (N₀ + k) ∈ J (N₀ + k) ∧ q (k + 1) - q k ∈ m ^ (N₀ + k + 1) := by
    intro k
    induction k with
    | zero =>
      have h0 : q 0 - p (N₀ + 0) ∈ J (N₀ + 0) := by simp [hq0]
      exact ⟨h0, by rw [hqs]; exact (hg 0 (q 0) h0).2⟩
    | succ k ih =>
      have h0 : q (k + 1) - p (N₀ + (k + 1)) ∈ J (N₀ + (k + 1)) := by
        rw [hqs]
        exact (hg k (q k) ih.1).1
      exact ⟨h0, by rw [hqs (k + 1)]; exact (hg (k + 1) (q (k + 1)) h0).2⟩
  have hcau : ∀ a b, a ≤ b → q b - q a ∈ m ^ (N₀ + a + 1) := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ b hab ih =>
      have h := add_mem (Ideal.pow_le_pow_right (by omega) (hqJ b).2) ih
      rwa [sub_add_sub_cancel] at h
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := m) q (fun {a b} hab => by
    rw [hsm, SModEq.sub_mem, ← neg_sub]
    exact neg_mem (Ideal.pow_le_pow_right (by omega) (hcau a b hab)))
  have hx : ∀ k, L - q k ∈ m ^ (N₀ + k + 1) := by
    intro k
    have h1 := hL (N₀ + k + 1)
    rw [hsm, SModEq.sub_mem] at h1
    have h2 := hcau k (N₀ + k + 1) (by omega)
    have e : L - q k = -(q (N₀ + k + 1) - L) + (q (N₀ + k + 1) - q k) := by ring
    rw [e]
    exact add_mem (neg_mem h1) h2
  refine ⟨L, fun N hN => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
    have e : L - p (N₀ + k) = (L - q k) + (q k - p (N₀ + k)) := by ring
    rw [e]
    exact add_mem (hmJ (N₀ + k) (hx k)) (hqJ k).1
  · simpa [hq0] using hx 0
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HhSmall
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

open Matrix in
private theorem expand_small {O : Type} [CommRing O] [IsLocalRing O] {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : Type} [CommRing R] [Algebra O R] [IsCO O R] {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R']
    (p : R →ₐ[O] R') (hs : maximalIdeal R * RingHom.ker p = ⊥) (J h Z : Matrix ι ι R)
    (hh : h.map (res O R) = 1) (hZ : Z.map p = 0) :
    (h + Z)ᵀ * J * (h + Z) = hᵀ * J * h + (Zᵀ * J + J * Z) ∧ (h + Z).map (res O R) = 1 := by
  have k : ∀ x y : R, res O R x = 0 → p y = 0 → x * y = 0 := fun x y hx hy => by
    have : x * y ∈ maximalIdeal R * RingHom.ker p :=
      Ideal.mul_mem_mul ((res_eq_zero_iff O R x).1 hx) hy
    rwa [hs, Ideal.mem_bot] at this
  have z1 : ∀ a b, p (Z a b) = 0 := fun a b => congrFun (congrFun hZ a) b
  have z2 : ∀ a b, res O R (Z a b) = 0 := fun a b => by rw [← res_map p, z1, map_zero]
  have h1 : ∀ a b, res O R ((h - 1) a b) = 0 := fun a b => by
    have := congrFun (congrFun hh a) b
    simp only [map_apply] at this
    rw [Matrix.sub_apply, map_sub, this]
    by_cases e : a = b
    · subst e; simp
    · simp [one_apply_ne e]
  have K : ∀ A B : Matrix ι ι R, (∀ a b, res O R (A a b) = 0) → (∀ a b, p (B a b) = 0) →
      Aᵀ * J * B = 0 ∧ Bᵀ * J * A = 0 := fun A B hA hB => by
    constructor
    · ext a b
      simp only [Matrix.mul_apply, transpose_apply, Matrix.zero_apply, Finset.sum_mul]
      refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
      rw [mul_right_comm, k _ _ (hA _ _) (hB _ _), zero_mul]
    · ext a b
      simp only [Matrix.mul_apply, transpose_apply, Matrix.zero_apply, Finset.sum_mul]
      refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
      rw [mul_right_comm, mul_comm (B _ _), k _ _ (hA _ _) (hB _ _), zero_mul]
  constructor
  · obtain ⟨e1, e2⟩ := K (h - 1) Z h1 z1
    obtain ⟨e3, -⟩ := K Z Z z2 z1
    rw [transpose_sub, transpose_one, sub_mul, sub_mul, one_mul, sub_eq_zero] at e1
    rw [mul_sub, mul_one, sub_eq_zero] at e2
    rw [transpose_add, add_mul, add_mul, mul_add, mul_add, e1, e2, e3]
    abel
  · ext a b
    have := congrFun (congrFun hh a) b
    simp only [map_apply] at this
    rw [map_apply, Matrix.add_apply, map_add (f := _), z2, add_zero, this]

open Matrix in
theorem UpperTheory.V.Alg.hh_small :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X) (Φ : FormData O w), IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (p : R →ₐ[O] R'), Function.Surjective p → maximalIdeal R * RingHom.ker p = ⊥ →
      (∀ h' : Matrix ι ι R', Φ.HH h' → ∃ h : Matrix ι ι R, Φ.HH h ∧ h.map p = h') ∧
      (∀ h₁ h₂ : Matrix ι ι R, Φ.HH h₁ → Φ.HH h₂ → h₁.map p = h₂.map p → h₂ - h₁ ∈ Φ.g R) ∧
      ∀ h Y : Matrix ι ι R, Φ.HH h → Y ∈ Φ.g R → Y.map p = 0 → Φ.HH (h + Y) := by
  intro O _ _ _ _ ι X _ _ _ w Φ h2 R _ _ _ R' _ _ _ p hp hs
  refine ⟨?_, ?_, ?_⟩
  · classical
    rintro h' ⟨a1, a2, a3⟩
    choose s hs' using hp
    obtain ⟨h0, b1, b2⟩ : ∃ h0 : Matrix ι ι R, h0.map p = h' ∧ ∀ a b, Φ.blk a ≠ Φ.blk b → h0 a b = 0 := by
      refine ⟨Matrix.of fun a b => if Φ.blk a = Φ.blk b then s (h' a b) else 0, ?_, fun a b e => by simp [e]⟩
      ext a b
      by_cases e : Φ.blk a = Φ.blk b
      · simp [e, hs']
      · simp [e, a2 a b e]
    have b3 : h0.map (res O R) = 1 := by
      rw [← a3, ← b1]
      ext a b
      simp [res_map]
    have jp : (Φ.JR R).map p = Φ.JR R' := by
      ext a b
      simp [FormData.JR]
    have jb : ∀ a b, Φ.JR R a b ≠ 0 → Φ.blk b = Φ.σ (Φ.blk a) := fun a b e =>
      Φ.hblk a b fun n => e (by simp [FormData.JR, n])
    obtain ⟨K, hK⟩ : ∃ K : Matrix ι ι R, Φ.JR R * K = 1 :=
      (Φ.unit.map (algebraMap O R).mapMatrix).exists_right_inv
    obtain ⟨u, hu⟩ : ∃ u : R, 2 * u = 1 := by
      have := (h2.map (algebraMap O R)).exists_right_inv
      rwa [map_ofNat] at this
    obtain ⟨ε, hε, hε2⟩ : ∃ ε : R, (Φ.JR R)ᵀ = ε • Φ.JR R ∧ ε * ε = 1 := by
      rcases Φ.sym with e | e
      · refine ⟨1, ?_, by simp⟩
        ext a b
        have := congrFun (congrFun e a) b
        simp only [transpose_apply] at this
        simp [FormData.JR, this]
      · refine ⟨-1, ?_, by simp⟩
        ext a b
        have := congrFun (congrFun e a) b
        simp only [transpose_apply] at this
        simp [FormData.JR, this]
    set E := h0ᵀ * Φ.JR R * h0 - Φ.JR R with hE
    have E1 : E.map p = 0 := by
      rw [hE, Matrix.map_sub _ (map_sub p), Matrix.map_mul, Matrix.map_mul, transpose_map, b1, jp, a1, sub_self]
    have E2 : Eᵀ = ε • E := by
      rw [hE, transpose_sub, transpose_mul, transpose_mul, transpose_transpose, hε, smul_sub]
      simp [mul_assoc]
    have E3 : ∀ a b, Φ.blk b ≠ Φ.σ (Φ.blk a) → E a b = 0 := fun a b e => by
      have : Φ.JR R a b = 0 := by_contra fun n => e (jb a b n)
      rw [hE, Matrix.sub_apply, this, sub_zero]
      simp only [Matrix.mul_apply, transpose_apply, Finset.sum_mul]
      refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
      by_cases e1 : Φ.blk d = Φ.blk a
      · by_cases e2 : Φ.blk c = Φ.blk b
        · have : Φ.JR R d c = 0 := by_contra fun n => e (by rw [← e2, ← e1]; exact jb d c n)
          simp [this]
        · simp [b2 _ _ e2]
      · simp [b2 _ _ e1]
    set Z0 : Matrix ι ι R := K * ((-u) • E) with hZ0
    have Z1 : Φ.JR R * Z0 = (-u) • E := by rw [hZ0, ← mul_assoc, hK, one_mul]
    have Z2 : ∀ a b, p (Z0 a b) = 0 := fun a b => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hZ0, Matrix.mul_apply, map_sum]
      refine Finset.sum_eq_zero fun c _ => ?_
      have : p (E c b) = 0 := congrFun (congrFun E1 c) b
      simp [this]
    let Z : Matrix ι ι R := Matrix.of fun a b => if Φ.blk a = Φ.blk b then Z0 a b else 0
    have Z3 : Z.map p = 0 := by
      ext a b
      by_cases e : Φ.blk a = Φ.blk b <;> simp [Z, e, Z2]
    have Z4 : Φ.JR R * Z = (-u) • E := by
      ext a b
      by_cases e : Φ.blk b = Φ.σ (Φ.blk a)
      · rw [← Z1, Matrix.mul_apply, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun c _ => ?_
        by_cases n : Φ.JR R a c = 0
        · simp [n]
        · have : Φ.blk c = Φ.blk b := by rw [e]; exact jb a c n
          simp [Z, this]
      · rw [Matrix.smul_apply, E3 a b e, smul_zero, Matrix.mul_apply]
        refine Finset.sum_eq_zero fun c _ => ?_
        by_cases n : Φ.JR R a c = 0
        · simp [n]
        · have : ¬ Φ.blk c = Φ.blk b := fun m => e (by rw [← m]; exact jb a c n)
          simp [Z, this]
    have Z5 : Zᵀ * Φ.JR R = (-u) • E := by
      have := congrArg (fun M => ε • Mᵀ) Z4
      simp only [transpose_mul, transpose_smul, hε, E2, Matrix.mul_smul, smul_smul] at this
      rw [hε2, one_smul, mul_left_comm, hε2, mul_one] at this
      exact this
    obtain ⟨c1, c2⟩ := expand_small p hs (Φ.JR R) h0 Z b3 Z3
    refine ⟨h0 + Z, ⟨?_, fun a b e => by simp [Z, e, b2 a b e], c2⟩, ?_⟩
    · rw [c1, Z4, Z5, ← add_smul, show -u + -u = -1 by rw [← hu]; ring, neg_one_smul, hE]
      abel
    · rw [Matrix.map_add _ (map_add p), b1, Z3, add_zero]
  · rintro h₁ h₂ ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ e
    have hZ : (h₂ - h₁).map p = 0 := by rw [Matrix.map_sub _ (map_sub p), e, sub_self]
    obtain ⟨c1, -⟩ := expand_small p hs (Φ.JR R) h₁ (h₂ - h₁) a3 hZ
    rw [add_sub_cancel, a1, b1, left_eq_add] at c1
    exact ⟨c1, fun a b n => by simp [a2 a b n, b2 a b n]⟩
  · rintro h Y ⟨a1, a2, a3⟩ ⟨b1, b2⟩ e
    obtain ⟨c1, c2⟩ := expand_small p hs (Φ.JR R) h Y a3 e
    exact ⟨by rw [c1, a1, b1, add_zero], fun a b n => by simp [a2 a b n, b2 a b n], c2⟩
end
