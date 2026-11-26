module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.PrAdd

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.TrLatRange
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.AdjoinNilFinite
open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.adjoin_nil_finite :
    ∀ {A G : Type} [CommRing A] [IsLocalRing A] [CommRing G] [Algebra A G] [Nontrivial G] (P : Submodule A G), P.FG → (∀ y ∈ P, ∃ a : A, IsNilpotent (y - algebraMap A G a)) → Module.Finite A (Algebra.adjoin A (P : Set G)) ∧ IsLocalRing (Algebra.adjoin A (P : Set G)) ∧ ∀ y ∈ Algebra.adjoin A (P : Set G), ∃ a : A, IsNilpotent (y - algebraMap A G a) := by
  intro A G _ _ _ _ _ P hP hnil
  let N : Subalgebra A G :=
    { carrier := {y | ∃ a : A, IsNilpotent (y - algebraMap A G a)}
      mul_mem' := by
        rintro x y ⟨a, ha⟩ ⟨b, hb⟩
        refine ⟨a * b, ?_⟩
        have e : x * y - algebraMap A G (a * b) =
            (x - algebraMap A G a) * y + algebraMap A G a * (y - algebraMap A G b) := by
          rw [map_mul]; ring
        rw [e]
        obtain ⟨k, hk⟩ := ha
        obtain ⟨m, hm⟩ := hb
        exact (Commute.all _ _).isNilpotent_add ⟨k, by rw [mul_pow, hk, zero_mul]⟩
          ⟨m, by rw [mul_pow, hm, mul_zero]⟩
      add_mem' := by
        rintro x y ⟨a, ha⟩ ⟨b, hb⟩
        refine ⟨a + b, ?_⟩
        have e : x + y - algebraMap A G (a + b) =
            (x - algebraMap A G a) + (y - algebraMap A G b) := by
          rw [map_add (f := _)]; ring
        rw [e]
        exact (Commute.all _ _).isNilpotent_add ha hb
      algebraMap_mem' := fun r => ⟨r, by simp⟩ }
  have hS : Algebra.adjoin A (P : Set G) ≤ N := Algebra.adjoin_le (fun y hy => hnil y hy)
  have hint : ∀ y, (∃ a : A, IsNilpotent (y - algebraMap A G a)) → IsIntegral A y := by
    rintro y ⟨a, k, hk⟩
    have hn : IsIntegral A (y - algebraMap A G a) :=
      ⟨X ^ k, monic_X_pow k, by simp [hk]⟩
    have := hn.add (isIntegral_algebraMap (x := a))
    simpa using this
  refine ⟨?_, ?_, fun y hy => hS hy⟩
  · obtain ⟨s, hs⟩ := hP
    rw [← hs, Algebra.adjoin_span]
    exact Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet
      (fun y hy => hint y (hnil y (hs ▸ Submodule.subset_span hy)))
  · apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
    intro y
    obtain ⟨a, ha⟩ := hS y.2
    let n : Algebra.adjoin A (P : Set G) :=
      ⟨(y : G) - algebraMap A G a, Subalgebra.sub_mem _ y.2 (Subalgebra.algebraMap_mem _ a)⟩
    have hn : IsNilpotent n := by
      obtain ⟨k, hk⟩ := ha
      exact ⟨k, Subtype.ext (by simpa [n] using hk)⟩
    have hy : y = algebraMap A _ a + n := Subtype.ext (by simp [n])
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with hu | hu
    · left
      rw [hy, add_comm]
      exact hn.isUnit_add_right_of_commute (hu.map _) (Commute.all _ _)
    · right
      have e : 1 - y = algebraMap A _ (1 - a) + (-n) := by
        rw [hy, map_sub, map_one]; ring
      rw [e, add_comm]
      exact hn.neg.isUnit_add_right_of_commute (hu.map _) (Commute.all _ _)
end

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem trLat_range {A B R : Type} [CommRing A] [CommRing B] [CommRing R] [Algebra A R] [IsNoetherianRing B]
    (φ : B →+* R) (f : B →+* A) (J : Ideal R) (N : ℕ) (hJ : J ^ N = ⊥)
    (h1 : ∀ a, ∃ b, φ b = algebraMap A R a ∧ f b = a) (h2 : ∀ b, φ b - algebraMap A R (f b) ∈ J) :
    ∃ M : Subalgebra A R, (Subalgebra.toSubmodule M).FG ∧ ∀ b, φ b ∈ M := by
  classical
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian (RingHom.ker f))
  have hgJ : ∀ i, φ (g i) ∈ J := by
    intro i
    have : g i ∈ RingHom.ker f := hg ▸ Submodule.subset_span ⟨i, rfl⟩
    have h := h2 (g i)
    rwa [(RingHom.mem_ker.1 this), map_zero, sub_zero] at h
  refine ⟨Algebra.adjoin A (Set.range fun i => φ (g i)), ?_, ?_⟩
  · refine fg_adjoin_of_finite (Set.finite_range _) ?_
    rintro _ ⟨i, rfl⟩
    have : φ (g i) ^ N = 0 := by
      have := Ideal.pow_mem_pow (hgJ i) N
      rwa [hJ, Ideal.mem_bot] at this
    exact ⟨Polynomial.X ^ N, Polynomial.monic_X_pow N, by simpa using this⟩
  · have key : ∀ k : ℕ, ∀ b, ∃ m ∈ Algebra.adjoin A (Set.range fun i => φ (g i)), φ b - m ∈ J ^ k := by
      intro k
      induction k with
      | zero => intro b; exact ⟨0, zero_mem _, by simp⟩
      | succ k ih =>
        intro b
        obtain ⟨b', hb', hf⟩ := h1 (f b)
        have hq : b - b' ∈ Submodule.span B (Set.range g) := by
          rw [hg, RingHom.mem_ker, map_sub, hf, sub_self]
        obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun B).1 hq
        choose m hm hm' using ih
        refine ⟨algebraMap A R (f b) + ∑ i, m (c i) * φ (g i), ?_, ?_⟩
        · refine add_mem (Subalgebra.algebraMap_mem _ _) (sum_mem fun i _ => mul_mem (hm _) ?_)
          exact Algebra.subset_adjoin ⟨i, rfl⟩
        · have e : φ b - (algebraMap A R (f b) + ∑ i, m (c i) * φ (g i)) = ∑ i, (φ (c i) - m (c i)) * φ (g i) := by
            have := congrArg φ hc
            set_option synthInstance.maxHeartbeats 100000 in
              rw [map_sub, map_sum, hb'] at this
            simp only [smul_eq_mul, map_mul] at this
            simp only [sub_mul, Finset.sum_sub_distrib]
            linear_combination -this
          rw [e, pow_succ]
          exact sum_mem fun i _ => Ideal.mul_mem_mul (hm' _) (hgJ i)
    intro b
    obtain ⟨m, hm, h⟩ := key N b
    rw [hJ, Ideal.mem_bot, sub_eq_zero] at h
    rwa [h]

private theorem trLat_pow {A B R : Type} [CommRing A] [CommRing B] [CommRing R] [Algebra A R] [IsLocalRing A]
    [IsLocalRing B] (t : A) (ht : maximalIdeal A ≤ Ideal.span {t})
    (φ : B →+* R) (f : B →+* A) (J : Ideal R) (N : ℕ) (hJ : J ^ N = ⊥)
    (h1 : Function.Surjective f) (h2 : ∀ b, φ b - algebraMap A R (f b) ∈ J) (M : Subalgebra A R) (hM : ∀ b, φ b ∈ M) (j : ℕ) :
    ∀ b ∈ maximalIdeal B ^ (j + N), ∃ y ∈ M, φ b = t ^ j • y := by
  haveI : IsLocalHom f := IsLocalHom.of_surjective f h1
  let φ' : B →+* M := φ.codRestrict M hM
  let J' : Ideal M := J.comap M.val.toRingHom
  have hJ' : J' ^ N = ⊥ := by
    refine le_bot_iff.1 ((Ideal.le_comap_pow _ N).trans ?_)
    rw [hJ]
    intro y hy
    rw [Ideal.mem_comap, Ideal.mem_bot] at hy
    exact Ideal.mem_bot.2 (Subtype.ext hy)
  have hle : (maximalIdeal B).map φ' ≤ Ideal.span {algebraMap A M t} ⊔ J' := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (ht (map_nonunit f b hb))
    rw [Ideal.mem_comap]
    have e : φ' b = algebraMap A M a * algebraMap A M t + (φ' b - algebraMap A M (f b)) := by
      rw [← map_mul, ha]; ring
    rw [e]
    exact add_mem (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
      (Ideal.mem_sup_right (h2 b))
  intro b hb
  have h3 : φ' b ∈ ((maximalIdeal B).map φ') ^ (j + N) := by
    rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hb
  have h4 := Ideal.sup_pow_add_le_pow_sup_pow (Ideal.pow_right_mono hle _ h3)
  rw [hJ', sup_bot_eq, Ideal.span_singleton_pow] at h4
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h4
  refine ⟨y, y.2, ?_⟩
  have := congrArg Subtype.val hy
  rw [Algebra.smul_def, map_pow, mul_comm]
  simpa [φ'] using this.symm

private theorem trLat_mul {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (M : Subalgebra A R) (E : Submodule A R) :
    (∀ y ∈ M, ∀ z ∈ Subalgebra.toSubmodule M * E, y * z ∈ Subalgebra.toSubmodule M * E) ∧
      E ≤ Subalgebra.toSubmodule M * E := by
  refine ⟨fun y hy z hz => ?_, fun z hz => ?_⟩
  · have : y * z ∈ Subalgebra.toSubmodule M * (Subalgebra.toSubmodule M * E) := Submodule.mul_mem_mul hy hz
    rwa [← mul_assoc, M.isIdempotentElem_toSubmodule.eq] at this
  · have : 1 * z ∈ Subalgebra.toSubmodule M * E := Submodule.mul_mem_mul M.one_mem hz
    rwa [one_mul] at this

theorem UpperTheory.V.Pa.trLat :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ (R : Type) [CommRing R] [Algebra S.F R] [Algebra S.x.A R] [IsScalarTower S.x.A S.F R] (e : R →ₐ[S.F] S.F) (θ : S.U.AA →+* R), S.Test R e θ → ∃ M : Subalgebra S.x.A R, Module.Finite S.x.A M ∧ (∀ b : S.B, θ (algebraMap S.B S.U.AA b) ∈ M) ∧ (∀ g i j, θ (S.U.vr g i j) ∈ M) ∧ (∀ j : ℕ, ∃ j' : ℕ, ∀ b ∈ maximalIdeal S.B ^ j', ∃ y ∈ M, θ (algebraMap S.B S.U.AA b) = S.x.t ^ j • y) ∧ ∃ P : Submodule S.x.A R, P.FG ∧ (∀ p ∈ S.U.P, ∀ i j, θ (p i j) ∈ P) ∧ ∀ y ∈ M, ∀ z ∈ P, y * z ∈ P := by
  intro l _ S R _ _ _ _ e θ T
  classical
  obtain ⟨N, hN⟩ := T.nil
  haveI : Nontrivial R := e.toRingHom.domain_nontrivial
  haveI : IsNoetherianRing S.B := inferInstance
  let φ : S.B →+* R := θ.comp (algebraMap S.B S.U.AA)
  have hφ : ∀ b, φ b = θ (algebraMap S.Bh S.U.AA (algebraMap S.B S.Bh b)) := fun b => by
    rw [← IsScalarTower.algebraMap_apply]; rfl
  have heA : ∀ a : S.x.A, e (algebraMap S.x.A R a) = algebraMap S.x.A S.F a := fun a => by
    rw [IsScalarTower.algebraMap_apply S.x.A S.F R, AlgHom.commutes]; rfl
  have h1 : ∀ a, ∃ b, φ b = algebraMap S.x.A R a ∧ S.P.f.toRingHom b = a := by
    intro a
    obtain ⟨o, b, ho, hb⟩ := S.oo_A a
    refine ⟨b, ?_, hb⟩
    rw [hφ, ← ho, T.oo, ho, S.rF_f, hb, ← IsScalarTower.algebraMap_apply]
  have h2 : ∀ b, φ b - algebraMap S.x.A R (S.P.f.toRingHom b) ∈ RingHom.ker e := by
    intro b
    have this : S.pr0 (algebraMap S.Bh S.U.AA (algebraMap S.B S.Bh b)) = algebraMap S.B S.Bh b := by
      have e : algebraMap S.Bh S.U.AA (S.pr0 (algebraMap S.Bh S.U.AA (algebraMap S.B S.Bh b)) - algebraMap S.B S.Bh b) ∈ S.U.N := by
        have h := (S.pr1 (algebraMap S.Bh S.U.AA (algebraMap S.B S.Bh b))).2
        rw [map_sub]
        convert S.U.N.neg_mem h using 1 <;> simp [Ctx.pr1] <;> ring
      have hz := Submodule.disjoint_def.1 S.U.compl.disjoint _ (Submodule.mem_one.2 ⟨_, rfl⟩) e
      exact sub_eq_zero.1 (S.U.inj (by rw [hz, map_zero]))
    rw [RingHom.mem_ker, map_sub, heA, hφ, T.res, this, S.rF_f, sub_eq_zero]
    rfl
  obtain ⟨M0, hM0, hM0'⟩ := trLat_range φ S.P.f.toRingHom (RingHom.ker e) N hN h1 h2
  obtain ⟨r, p, hp⟩ := Submodule.fg_iff_exists_fin_generating_family.1 S.U.ker_le_span_sub_sup_map
  let E : Submodule S.x.A R := Submodule.span S.x.A (Set.range fun q : Fin r × Fin S.n × Fin S.n => θ (p q.1 q.2.1 q.2.2))
  have hE : E.FG := Submodule.fg_span (Set.finite_range _)
  have hP : ∀ M : Subalgebra S.x.A R, (∀ b, φ b ∈ M) → ∀ z ∈ S.U.P, ∀ i j, θ (z i j) ∈ Subalgebra.toSubmodule M * E := by
    intro M hM z hz i j
    rw [← hp] at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨k, rfl⟩ := hz
      exact (trLat_mul M E).2 (Submodule.subset_span ⟨(k, i, j), rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_apply, map_add (f := _)]; exact add_mem hx hy
    | smul b x _ hx =>
      rw [Matrix.smul_apply, Algebra.smul_def, map_mul]
      exact (trLat_mul M E).1 _ (hM b) _ hx
  let Q : Submodule S.x.A R := Subalgebra.toSubmodule M0 ⊔ Subalgebra.toSubmodule M0 * E
  have hQ : Q.FG := hM0.sup (hM0.mul hE)
  let P0 : Submodule S.x.A R := Q ⊓ ((1 : Submodule S.x.A R) ⊔ (RingHom.ker e).restrictScalars S.x.A)
  have hP0 : P0.FG := hQ.of_le inf_le_left
  have hmem : ∀ y ∈ Q, ∀ a : S.x.A, y - algebraMap S.x.A R a ∈ RingHom.ker e → y ∈ P0 := by
    intro y hy a ha
    refine ⟨hy, Submodule.mem_sup.2 ⟨algebraMap S.x.A R a, Submodule.mem_one.2 ⟨a, rfl⟩, _, ha, by ring⟩⟩
  have hnil : ∀ y ∈ P0, ∃ a : S.x.A, IsNilpotent (y - algebraMap S.x.A R a) := by
    intro y hy
    obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.1 hy.2
    obtain ⟨a, rfl⟩ := Submodule.mem_one.1 hu
    refine ⟨a, N, ?_⟩
    have := Ideal.pow_mem_pow (I := RingHom.ker e) hz N
    rw [hN, Ideal.mem_bot] at this
    rwa [add_sub_cancel_left]
  have hfin := (adjoin_nil_finite P0 hP0 hnil).1
  have hB : ∀ b, φ b ∈ Algebra.adjoin S.x.A (P0 : Set R) := fun b =>
    Algebra.subset_adjoin (hmem _ (Submodule.mem_sup_left (hM0' b)) _ (h2 b))
  refine ⟨Algebra.adjoin S.x.A (P0 : Set R), hfin, hB, fun g i j => ?_, fun j => ⟨j + N, ?_⟩,
    Subalgebra.toSubmodule (Algebra.adjoin S.x.A (P0 : Set R)) * E, (Module.Finite.iff_fg.1 hfin).mul hE, hP _ hB,
    (trLat_mul _ E).1⟩
  · refine Algebra.subset_adjoin (hmem _ (Submodule.mem_sup_right (hP M0 hM0' _ (S.U.vr_mem g) i j))
      (mat S.x.ρ (S.h.p₀ g) i j) ?_)
    have hvr := S.U.red g i j _ (S.pr1 (S.U.vr g i j)).2
    rw [RingHom.mem_ker, map_sub, heA, T.res, hvr, sub_eq_zero]
  · exact trLat_pow S.x.t PowerSeries.maximalIdeal_eq_span_X.le φ S.P.f.toRingHom (RingHom.ker e) N hN
      (fun a => (h1 a).imp fun _ h => h.2) h2 _ hB j
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.SelmerRankBoundLaurent
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.SelScale1
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

namespace UpperTheory.V.Pa

private theorem adicDD {A Γ : Type} [CommRing A] [TopologicalSpace Γ] {e : ℕ} (t : A) (d : Γ → DD A e)
    (h1 : AdicCont (Ideal.span {t}) fun g => (d g).a)
    (h2 : ∀ k, AdicCont (Ideal.span {t}) fun g => (d g).ep k)
    (h3 : ∀ k, AdicCont (Ideal.span {t}) fun g => (d g).ep' k)
    (h4 : AdicCont (Ideal.span {t}) fun g => (d g).eta) :
    AdicCont (Ideal.span {algebraMap A (DD A e) t}) d := by
  intro N
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have e1 := (h1 N).eventually_eq x
  have e2 := Filter.eventually_all.2 fun k => (h2 k N).eventually_eq x
  have e3 := Filter.eventually_all.2 fun k => (h3 k N).eventually_eq x
  have e4 := (h4 N).eventually_eq x
  filter_upwards [e1, e2, e3, e4] with y a1 a2 a3 a4
  simp only [Ideal.Quotient.eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at a1 a2 a3 a4 ⊢
  obtain ⟨b1, a1⟩ := a1
  obtain ⟨b4, a4⟩ := a4
  choose b2 a2 using a2
  choose b3 a3 using a3
  refine ⟨⟨b1, b2, b3, b4⟩, ?_⟩
  rw [← map_pow]
  have : algebraMap A (DD A e) (t ^ N) = DD.C (t ^ N) := rfl
  rw [this, sub_eq_add_neg]
  ext <;> simp [-map_pow, a1, a2, a3, a4, sub_eq_add_neg]

private theorem mapInj {X Y : Type} [CommRing X] [CommRing Y] {e : ℕ} (f : X →+* Y) (hf : Function.Injective f) :
    Function.Injective (DD.map (g := e) f) := by
  intro u v h
  have h1 := congrArg DD.a h
  have h2 := congrArg DD.ep h
  have h3 := congrArg DD.ep' h
  have h4 := congrArg DD.eta h
  ext k
  · exact hf h1
  · exact hf (congrFun h2 k)
  · exact hf (congrFun h3 k)
  · exact hf h4

private theorem selLift {l : ℕ} [Fact l.Prime] (F : GFrame l) {n : ℕ} {A R R' : Type} [CommRing A] [CommRing R] [CommRing R']
    [Algebra A R] [Algebra A R'] (t : A) (f : R →+* R') (hf : Function.Injective f)
    (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (w wi : F.Vl → Matrix (Fin n) (Fin n) R)
    (ρ' : F.G₀ → Matrix (Fin n) (Fin n) R') (w' wi' : F.Vl → Matrix (Fin n) (Fin n) R')
    (hρ : ∀ g, (ρ g).map f = ρ' g) (hw : ∀ g, (w g).map f = w' g) (hwi : ∀ g, (wi g).map f = wi' g)
    (V : Submodule A (Matrix (Fin n) (Fin n) R)) (V' : Submodule A (Matrix (Fin n) (Fin n) R'))
    (c : R') (hV : ∀ Z : Matrix (Fin n) (Fin n) R, ∀ Z' ∈ V', Z.map f = c • Z' → Z ∈ V)
    (z' : F.G₀ → Matrix (Fin n) (Fin n) R') (hz' : z' ∈ SelZ F t ρ' w' wi' V')
    (Y' : F.Vl → Matrix (Fin n) (Fin n) R') (hY' : ∀ v, Y' v ∈ V' ∧ LocAt F ρ' w' wi' z' v (Y' v))
    (z : F.G₀ → Matrix (Fin n) (Fin n) R) (hc : ∀ i j, AdicCont (Ideal.span {algebraMap A R t}) fun g => z g i j)
    (hz : ∀ g, (z g).map f = c • z' g) (Y : F.Vl → Matrix (Fin n) (Fin n) R) (hY : ∀ v, (Y v).map f = c • Y' v) :
    z ∈ SelZ F t ρ w wi V := by
  obtain ⟨h1, -, h3, h4, h5, -⟩ := hz'
  have inj : Function.Injective fun Z : Matrix (Fin n) (Fin n) R => Z.map f := Matrix.map_injective hf
  refine ⟨fun g => hV _ _ (h1 g) (hz g), hc, fun g g' => inj ?_, fun g => inj ?_, fun u g hg => inj ?_,
    fun v => ⟨Y v, hV _ _ (hY' v).1 (hY v), fun g => ?_⟩⟩
  · simp only [Matrix.map_add f (map_add f), Matrix.map_mul, hz, hρ, h3, smul_add, Matrix.mul_smul, Matrix.smul_mul]
  · simp only [Matrix.map_neg f (map_neg f), Matrix.transpose_map, hz, h4, smul_neg, Matrix.transpose_smul]
  · simp only [hz, h5 u g hg, smul_zero, Matrix.map_zero f (map_zero f)]
  · have key : (wi v * (z (F.φ v g) - dY F ρ (Y v) (F.φ v g)) * w v).map f =
        c • (wi' v * (z' (F.φ v g) - dY F ρ' (Y' v) (F.φ v g)) * w' v) := by
      simp only [dY, Matrix.map_sub f (map_sub f), Matrix.map_mul, hz, hρ, hw, hwi, hY, ← smul_sub, Matrix.mul_smul,
        Matrix.smul_mul]
    have k2 : ∀ i j, (wi' v * (z' (F.φ v g) - dY F ρ' (Y' v) (F.φ v g)) * w' v) i j = 0 →
        (wi v * (z (F.φ v g) - dY F ρ (Y v) (F.φ v g)) * w v) i j = 0 := by
      intro i j h0
      apply hf
      have := congrFun (congrFun key i) j
      rw [Matrix.map_apply, Matrix.smul_apply, h0, smul_zero] at this
      rw [this, map_zero]
    exact ⟨fun i j hij => k2 i j (((hY' v).2 g).1 i j hij), fun hg i => k2 i i (((hY' v).2 g).2 hg i)⟩

private theorem liftM {K Γ : Type} [Field K] [TopologicalSpace Γ] [Group Γ] [IsTopologicalGroup Γ] {n e : ℕ}
    (z : Γ → Matrix (Fin n) (Fin n) (DD (FractionRing (PowerSeries K)) e)) (hz : BndD (PowerSeries.X : PowerSeries K) z) :
    ∀ᶠ s : ℕ in Filter.atTop, ∃ z' : Γ → Matrix (Fin n) (Fin n) (DD (PowerSeries K) e),
      (∀ i j, AdicCont (Ideal.span {algebraMap (PowerSeries K) (DD (PowerSeries K) e) PowerSeries.X}) fun g => z' g i j) ∧
      ∀ g, (z' g).map (DD.map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))) =
        (DD.C (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) PowerSeries.X ^ s) : DD (FractionRing (PowerSeries K)) e) • z g := by
  have B := fun φ hφ => Filter.eventually_atTop.2 ((bndOps K Γ).2.2.2.2 φ hφ)
  have e1 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => B _ (hz i j).1
  have e2 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
    Filter.eventually_all.2 fun k => B _ ((hz i j).2.1 k)
  have e3 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
    Filter.eventually_all.2 fun k => B _ ((hz i j).2.2.1 k)
  have e4 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => B _ (hz i j).2.2.2
  filter_upwards [e1, e2, e3, e4] with s a1 a2 a3 a4
  choose b1 c1 a1 using a1
  choose b2 c2 a2 using a2
  choose b3 c3 a3 using a3
  choose b4 c4 a4 using a4
  refine ⟨fun g => Matrix.of fun i j => ⟨b1 i j g, fun k => b2 i j k g, fun k => b3 i j k g, b4 i j g⟩,
    fun i j => adicDD _ _ (c1 i j) (c2 i j) (c3 i j) (c4 i j), fun g => ?_⟩
  ext i j <;> simp [-map_pow, DD.map, a1, a2, a3, a4]

end UpperTheory.V.Pa

theorem UpperTheory.V.Pa.selScale1 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), ∀ z ∈ Sel1 h x.Fr k, BndD x.t z → ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → ∃ z' ∈ Sel1 h x.A k, ∀ g, (z' g).map (DD.map (algebraMap x.A x.Fr)) = algebraMap x.A x.Fr x.t ^ s • z g := by
  intro l _ L G G0 h n x k z hz hb
  choose Y hY using hz.2.2.2.2.2
  have c0 := (bndOps x.K G.G₀).1
  have e1 := liftM z hb
  have e2 := Filter.eventually_all.2 fun v => liftM (K := x.K) (fun _ : G.G₀ => Y v)
    fun i j => ⟨c0 _, fun _ => c0 _, fun _ => c0 _, c0 _⟩
  apply Filter.eventually_atTop.1
  filter_upwards [e1, e2] with s a1 a2
  obtain ⟨z', hc, hz'⟩ := a1
  choose Y' _ hY' using a2
  have hf : Function.Injective (algebraMap x.A x.Fr) := IsFractionRing.injective _ _
  have m1 : ∀ M : Matrix (Fin n) (Fin n) x.A, (M.map (algebraMap x.A (DD x.A k.g))).map (DD.map (algebraMap x.A x.Fr)) =
      M.map (algebraMap x.A (DD x.Fr k.g)) := by
    intro M
    ext i j <;> first | rfl | exact map_zero (algebraMap x.A x.Fr)
  have m2 : ∀ Z : Fin k.g → Matrix (Fin n) (Fin n) x.A,
      (DD.epM fun j => (Z j).map (algebraMap x.A x.A)).map (DD.map (algebraMap x.A x.Fr)) =
      DD.epM fun j => (Z j).map (algebraMap x.A x.Fr) := by
    intro Z
    ext i j <;> first | rfl | exact map_zero (algebraMap x.A x.Fr)
  have m0 : (1 : Matrix (Fin n) (Fin n) (DD x.A k.g)).map (DD.map (algebraMap x.A x.Fr)) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have p : ∀ (b1 b2 b3 b4 : Bool) (u : DD x.A k.g), ∀ u' ∈ ddPart x.A x.Fr k.g b1 b2 b3 b4,
      DD.map (algebraMap x.A x.Fr) u = DD.C (algebraMap x.A x.Fr x.t ^ s) * u' → u ∈ ddPart x.A x.A k.g b1 b2 b3 b4 := by
    rintro b1 b2 b3 b4 u u' ⟨q1, q2, q3, q4⟩ hu
    refine ⟨fun e => hf ?_, fun e => funext fun j => hf ?_, fun e => funext fun j => hf ?_, fun e => hf ?_⟩
    · simpa [-map_pow, DD.map, q1 e] using congrArg DD.a hu
    · simpa [-map_pow, DD.map, q2 e] using congrFun (congrArg DD.ep hu) j
    · simpa [-map_pow, DD.map, q3 e] using congrFun (congrArg DD.ep' hu) j
    · simpa [-map_pow, DD.map, q4 e] using congrArg DD.eta hu
  refine ⟨z', selLift G.frame x.t (DD.map (algebraMap x.A x.Fr)) (mapInj _ hf) _ _ _ _ _ _ (fun g => ?_) (fun v => ?_) (fun v => ?_)
    _ _ (DD.C (algebraMap x.A x.Fr x.t ^ s)) (fun Z Z' hZ' hZ i j => ?_) z hz Y hY z' hc hz' (fun v => Y' v 1) (fun v => hY' v 1), hz'⟩
  · simp only [Kap.ρ1, NP.ρX, Matrix.map_mul, Matrix.map_add _ (map_add (DD.map (algebraMap x.A x.Fr))), m0, m1, m2]
  · simp only [Kap.w1, NP.wX, Matrix.map_mul, Matrix.map_sub _ (map_sub (DD.map (algebraMap x.A x.Fr))), m0, m1, m2]
  · simp only [Kap.wi1, NP.wiX, Matrix.map_mul, Matrix.map_add _ (map_add (DD.map (algebraMap x.A x.Fr))), m0, m1, m2]
  · have := congrFun (congrFun hZ i) j
    exact ⟨fun e => p _ _ _ _ _ _ ((hZ' i j).1 e) this, fun e => p _ _ _ _ _ _ ((hZ' i j).2 e) this⟩
end

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem dual_numbers_map_smul {X Y : Type} [CommRing X] [CommRing Y] {g : ℕ} (f : X →+* Y) (c : X) (u : DD X g) :
    DD.map f (c • u) = f c • DD.map f u := by
  show DD.map f (DD.C c * u) = DD.C (f c) * DD.map f u
  rw [map_mul]
  congr 1
  apply DD.ext
  · rfl
  · funext j
    exact map_zero f
  · funext j
    exact map_zero f
  · exact map_zero f

private theorem map_first_order_lift_residue_field {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (g : F.G₀) :
    (DD.map (algebraMap x.A x.Fr)).mapMatrix (k.ρ1 x.A g) = k.ρ1 x.Fr g := by
  have hE : (DD.map (algebraMap x.A x.Fr)).mapMatrix (DD.epM fun j => (k.κ j g).map (algebraMap x.A x.A))
      = DD.epM fun j => (k.κ j g).map (algebraMap x.A x.Fr) := by
    ext a b <;> simp [DD.epM, DD.map, RingHom.mapMatrix_apply]
  have hR : (DD.map (algebraMap x.A x.Fr)).mapMatrix (x.ρX (DD x.A k.g) g) = x.ρX (DD x.Fr k.g) g := by
    ext a b <;> simp [NP.ρX, DD.map, RingHom.mapMatrix_apply]
    all_goals first | rfl | exact map_zero _
  unfold Kap.ρ1
  rw [map_mul, map_add (f := _), map_one, hE, hR]

private theorem map_mem_dual_numbers_part {A Y : Type} [CommRing A] [CommRing Y] [Algebra A Y] {g : ℕ} {b1 b2 b3 b4 : Bool} {u : DD A g}
    (hu : u ∈ ddPart A A g b1 b2 b3 b4) : DD.map (algebraMap A Y) u ∈ ddPart A Y g b1 b2 b3 b4 := by
  obtain ⟨h1, h2, h3, h4⟩ := hu
  refine ⟨fun hb => ?_, fun hb => ?_, fun hb => ?_, fun hb => ?_⟩
  · show algebraMap A Y u.a = 0
    rw [h1 hb, map_zero]
  · show (fun j => algebraMap A Y (u.ep j)) = 0
    rw [h2 hb]
    funext j
    simp
  · show (fun j => algebraMap A Y (u.ep' j)) = 0
    rw [h3 hb]
    funext j
    simp
  · show algebraMap A Y u.eta = 0
    rw [h4 hb, map_zero]

theorem UpperTheory.V.Pa.k1F :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), ∀ D0, K1 h k D0 → SelmerRankBoundLaurent h k D0 := by
  intro l _ L G G0 h n x k D0 hK e z hz hind
  classical
  choose s₀ hs₀ using fun i => selScale1 l L G G0 h n x k (z i) (hz i).1 (hz i).2
  obtain ⟨z', hz'S, hz'map⟩ : ∃ z' : Fin e → G.frame.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g),
      (∀ i, z' i ∈ Sel1 h x.A k) ∧ ∀ i g, (z' i g).map (DD.map (algebraMap x.A x.Fr))
        = (algebraMap x.A x.Fr) x.t ^ (Finset.univ.sup s₀) • z i g := by
    choose z' hz'S hz'map using fun i => hs₀ i (Finset.univ.sup s₀) (Finset.le_sup (Finset.mem_univ i))
    exact ⟨z', hz'S, hz'map⟩
  apply hK e z' hz'S
  intro c hc
  obtain ⟨Y, hY, hYt, hYeq⟩ := hc
  have hmapSmul : ∀ (c0 : x.A) (M : Matrix (Fin n) (Fin n) (DD x.A k.g)),
      (DD.map (algebraMap x.A x.Fr)).mapMatrix (c0 • M)
        = algebraMap x.A x.Fr c0 • (DD.map (algebraMap x.A x.Fr)).mapMatrix M := by
    intro c0 M
    exact Matrix.ext fun a b => dual_numbers_map_smul (algebraMap x.A x.Fr) c0 (M a b)
  have key : ∑ i, (algebraMap x.A x.Fr (c i) * algebraMap x.A x.Fr x.t ^ (Finset.univ.sup s₀)) • z i
      ∈ Bd1 h x.Fr k := by
    simp only [Bd1, Bd, Set.mem_setOf_eq]
    refine ⟨(DD.map (algebraMap x.A x.Fr)).mapMatrix Y, ?_, ?_, ?_⟩
    · intro a b
      exact ⟨fun hab => map_mem_dual_numbers_part ((hY a b).1 hab), fun hab => map_mem_dual_numbers_part ((hY a b).2 hab)⟩
    · refine Matrix.ext fun a b => ?_
      show DD.map (algebraMap x.A x.Fr) (Y b a) = -(DD.map (algebraMap x.A x.Fr) (Y a b))
      rw [← map_neg]
      congr 1
      exact congrFun (congrFun hYt a) b
    · funext g
      have h1 := congrFun hYeq g
      have hsum : (DD.map (algebraMap x.A x.Fr)).mapMatrix (∑ i, c i • z' i g)
          = ∑ i, (algebraMap x.A x.Fr (c i) * algebraMap x.A x.Fr x.t ^ (Finset.univ.sup s₀)) • z i g := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hmapSmul, show (DD.map (algebraMap x.A x.Fr)).mapMatrix (z' i g)
          = algebraMap x.A x.Fr x.t ^ (Finset.univ.sup s₀) • z i g from hz'map i g, smul_smul]
      simp only [Finset.sum_apply, Pi.smul_apply] at h1 ⊢
      rw [← hsum, h1]
      simp only [dY, map_sub, map_mul, map_first_order_lift_residue_field]
  have hc' := hind _ key
  have ht : algebraMap x.A x.Fr x.t ≠ 0 := fun h0 =>
    PowerSeries.X_ne_zero ((IsFractionRing.injective x.A x.Fr) (h0.trans (map_zero _).symm))
  funext i
  have hi := congrFun hc' i
  exact (IsFractionRing.injective x.A x.Fr)
    (((mul_eq_zero.mp hi).resolve_right (pow_ne_zero _ ht)).trans (map_zero _).symm)
end
