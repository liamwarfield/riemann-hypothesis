module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.SphRed

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.HeckePolCoeffMem
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Th.AnnihilatorQuotientFinite.frobS :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [IsLocalRing A] (θ : H.X.I.T →* Aˣ) (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] (I : Ideal (H.TK θ a K)) (D : W.GDet n (H.TK θ a K) H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ), H.IsUniv θ a K I D ψ →
    ∀ (i : ℕ) (g : H.Gq) (N : ℕ), ∃ s ∈ Algebra.adjoin c.O (Set.range fun p : H.Wp × Fin n => H.gen θ a K (.inl p)), D.lam i (MonoidAlgebra.single g 1) - s ∈ I ^ N := by
  intro L Ω _ _ _ _ _ l _ n c H hAx A _ _ _ θ a K _ I D ψ hU i g N
  have hlc := hU.cont i N
  obtain ⟨x, ⟨w, hw, B, σ, hB, hσ, rfl⟩, hxU⟩ :=
    hAx.dense.exists_mem_open (hlc.isOpen_fiber _) ⟨g, Set.mem_singleton _⟩
  refine ⟨D.lam i (MonoidAlgebra.single (H.prj σ⁻¹) 1), ?_, ?_⟩
  · have hf := hU.frob ⟨w, hw⟩ B σ hB hσ
    set_option synthInstance.maxHeartbeats 400000 in
    generalize hR : Algebra.adjoin c.O (Set.range fun p : H.Wp × Fin n => H.gen θ a K (.inl p)) = R
    have hgen : ∀ j, H.genW θ a K ⟨w, hw⟩ j ∈ R := by
      intro j
      subst hR
      unfold UpperTheory.V.Hi.HSet.genW
      split_ifs with h
      · exact Algebra.subset_adjoin ⟨(⟨w, hw⟩, _), rfl⟩
      · exact Subalgebra.one_mem _
    show (-1) ^ i * (D.chi _).coeff (n - i) ∈ R
    rw [hf]
    refine R.mul_mem (R.pow_mem (R.neg_mem R.one_mem) _) ?_
    unfold UpperTheory.V.Hi.heckePol
    rw [Polynomial.finsetSum_coeff]
    refine R.sum_mem fun j _ => ?_
    rw [Polynomial.coeff_C_mul_X_pow]
    split_ifs
    · exact R.mul_mem (R.mul_mem (R.pow_mem (R.neg_mem R.one_mem) _)
        (R.pow_mem (R.natCast_mem _) _)) (hgen j)
    · exact R.zero_mem
  · have h1 := Set.mem_singleton_iff.mp hxU
    exact Ideal.Quotient.eq.mp h1.symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.ClosedSub
open IsLocalRing

theorem UpperTheory.V.Th.AnnihilatorQuotientFinite.closedSub :
    ∀ {O T : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O] [CommRing T] [IsLocalRing T] [Algebra O T] (I : Ideal T) [Module.Finite O (T ⧸ I)] (S : Subalgebra O T) (t : T), (∀ N : ℕ, ∃ s ∈ S, t - s ∈ maximalIdeal T ^ N) → ∃ s ∈ S, t - s ∈ I := by
  intro O T _ _ _ _ _ _ I _ S t ht
  let q : T →ₐ[O] T ⧸ I := Ideal.Quotient.mkₐ O I
  have hq : Function.Surjective q := Ideal.Quotient.mkₐ_surjective O I
  haveI : IsNoetherian O (T ⧸ I) := inferInstance
  haveI : IsNoetherianRing (T ⧸ I) := isNoetherian_of_tower O inferInstance
  haveI : Algebra.IsIntegral O (T ⧸ I) := inferInstance
  set K : Ideal (T ⧸ I) := (maximalIdeal T).map q with hK
  set J : Ideal (T ⧸ I) := (maximalIdeal O).map (algebraMap O (T ⧸ I)) with hJ
  have hKJ : K ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P hP => ?_
    obtain ⟨hJP, hPp⟩ := hP
    have hc : (P.comap (algebraMap O (T ⧸ I))).IsMaximal := by
      have h1 : maximalIdeal O ≤ P.comap (algebraMap O (T ⧸ I)) := Ideal.map_le_iff_le_comap.mp hJP
      have h2 : (P.comap (algebraMap O (T ⧸ I))).IsPrime := Ideal.comap_isPrime _ _
      rw [← (maximalIdeal.isMaximal O).eq_of_le h2.ne_top h1]
      exact maximalIdeal.isMaximal O
    haveI := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) P hc
    have h3 : (P.comap q).IsMaximal := Ideal.comap_isMaximal_of_surjective q hq
    have h4 : P.comap q = maximalIdeal T := IsLocalRing.eq_maximalIdeal h3
    rw [hK, Ideal.map_le_iff_le_comap, h4]
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hKJ (IsNoetherian.noetherian K)
  let Sb : Submodule O (T ⧸ I) := (Subalgebra.toSubmodule S).map q.toLinearMap
  have hmem : ∀ k : ℕ, Sb.mkQ (q t) ∈ ((maximalIdeal O) ^ k • ⊤ : Submodule O ((T ⧸ I) ⧸ Sb)) := by
    intro k
    obtain ⟨s, hs, hts⟩ := ht (n * k)
    have h1 : q (t - s) ∈ K ^ (n * k) := by
      rw [hK, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hts
    have h2 : q (t - s) ∈ J ^ k := by
      rw [pow_mul] at h1
      first
        | exact Ideal.pow_right_mono hn k h1
        | exact pow_le_pow_left' hn k h1
    have h3 : q (t - s) ∈ ((maximalIdeal O) ^ k • ⊤ : Submodule O (T ⧸ I)) := by
      rw [Ideal.smul_top_eq_map, Ideal.map_pow]
      exact h2
    have h4 : Sb.mkQ (q t) = Sb.mkQ (q (t - s)) := by
      rw [map_sub, map_sub, eq_comm, sub_eq_self]
      exact (Submodule.Quotient.mk_eq_zero Sb).mpr ⟨s, hs, rfl⟩
    have h5 := Submodule.mem_map_of_mem (f := Sb.mkQ) h3
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at h5
    rw [h4]
    exact h5
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (R := O) (M := (T ⧸ I) ⧸ Sb)
    (maximalIdeal O) (maximalIdeal.isMaximal O).ne_top
  have h0 : Sb.mkQ (q t) = 0 := by
    have hi : Sb.mkQ (q t) ∈ (⨅ i : ℕ, (maximalIdeal O) ^ i • ⊤ : Submodule O ((T ⧸ I) ⧸ Sb)) :=
      Submodule.mem_iInf _ |>.mpr hmem
    rw [hbot] at hi
    exact hi
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
  obtain ⟨s, hs, hsq⟩ := h0
  refine ⟨s, hs, ?_⟩
  exact Ideal.Quotient.eq.mp hsq.symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.AnnFin
open IsLocalRing

theorem UpperTheory.V.Th.AnnihilatorQuotientFinite.annFin :
    ∀ {O A T M : Type} [CommRing O] [IsNoetherianRing O] [CommRing A] [Algebra O A] [CommRing T] [Algebra O T] [AddCommGroup M] [Module A M] [Module.Finite A M] (x : A →ₐ[O] O) (μ : T →+* Module.End A M), (∀ (o : O) (y : M), μ (algebraMap O T o) y = algebraMap O A o • y) → ∃ I : Ideal T, (∀ t, t ∈ I ↔ ∀ y : M, μ t y ∈ (RingHom.ker x • ⊤ : Submodule A M)) ∧ Module.Finite O (T ⧸ I) := by
  intro O A T M _ _ _ _ _ _ _ _ _ x μ hμ
  classical
  set N : Submodule A M := (RingHom.ker x • ⊤ : Submodule A M) with hN
  have hmap : ∀ (f : Module.End A M) (y : M), y ∈ N → f y ∈ N := by
    intro f y hy
    have h : N.map f ≤ N := by
      rw [hN, Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact h ⟨y, hy, rfl⟩
  let I : Ideal T :=
    { carrier := {t | ∀ y : M, μ t y ∈ N}
      add_mem' := by
        intro a b ha hb
        have ha' : ∀ y : M, μ a y ∈ N := ha
        have hb' : ∀ y : M, μ b y ∈ N := hb
        show ∀ y : M, μ (a + b) y ∈ N
        intro y
        rw [map_add (f := _), LinearMap.add_apply]
        exact N.add_mem (ha' y) (hb' y)
      zero_mem' := by
        show ∀ y : M, μ 0 y ∈ N
        intro y
        rw [map_zero, LinearMap.zero_apply]
        exact N.zero_mem
      smul_mem' := by
        intro c t ht
        have ht' : ∀ y : M, μ t y ∈ N := ht
        show ∀ y : M, μ (c • t) y ∈ N
        intro y
        rw [smul_eq_mul, map_mul, Module.End.mul_apply]
        exact hmap _ _ (ht' y) }
  refine ⟨I, fun t => Iff.rfl, ?_⟩
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := M)
  letI : Module O M := Module.compHom M (algebraMap O A)
  haveI : IsScalarTower O A M := ⟨fun o a m => by
    show (o • a) • m = algebraMap O A o • (a • m)
    rw [Algebra.smul_def, mul_smul]⟩
  let N' : Submodule O M := N.restrictScalars O
  have hspanA : ∀ y : M, y ∈ Submodule.span A (Set.range s) := fun y => hs ▸ Submodule.mem_top
  have hfinQ : Module.Finite O (M ⧸ N') := by
    refine ⟨(Submodule.fg_def).2 ⟨_, Set.finite_range (fun i => N'.mkQ (s i)), ?_⟩⟩
    rw [eq_top_iff]
    rintro q -
    obtain ⟨y, rfl⟩ := N'.mkQ_surjective q
    refine Submodule.span_induction ?_ ?_ ?_ ?_ (hspanA y)
    · rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro a b _ _ ha hb
      rw [map_add (f := _)]
      exact Submodule.add_mem _ ha hb
    · intro a z _ hz
      have hd : a - algebraMap O A (x a) ∈ RingHom.ker x := by
        rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
      have he : N'.mkQ (a • z) = x a • N'.mkQ z := by
        rw [← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
          Submodule.restrictScalars_mem]
        show a • z - algebraMap O A (x a) • z ∈ N
        rw [← sub_smul, hN]
        exact Submodule.smul_mem_smul hd Submodule.mem_top
      rw [he]
      exact Submodule.smul_mem _ _ hz
  let φ : T →ₗ[O] (Fin n → M ⧸ N') :=
    { toFun := fun t i => N'.mkQ (μ t (s i))
      map_add' := by
        intro a b
        funext i
        simp [map_add (f := _)]
      map_smul' := by
        intro o t
        funext i
        simp only [RingHom.id_apply, Pi.smul_apply]
        rw [Algebra.smul_def, map_mul, Module.End.mul_apply, hμ]
        exact N'.mkQ.map_smul o (μ t (s i)) }
  have hker : LinearMap.ker φ ≤ LinearMap.ker (Ideal.Quotient.mkₐ O I).toLinearMap := by
    intro t ht
    rw [LinearMap.mem_ker] at ht ⊢
    have hti : ∀ i, μ t (s i) ∈ N := by
      intro i
      have h1 := congrFun ht i
      change N'.mkQ (μ t (s i)) = 0 at h1
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.restrictScalars_mem] at h1
    have htI : t ∈ I := by
      show ∀ y : M, μ t y ∈ N
      intro y
      refine Submodule.span_induction ?_ ?_ ?_ ?_ (hspanA y)
      · rintro _ ⟨i, rfl⟩
        exact hti i
      · rw [map_zero]
        exact N.zero_mem
      · intro a b _ _ ha hb
        rw [map_add (f := _)]
        exact N.add_mem ha hb
      · intro a z _ hz
        rw [LinearMap.map_smul]
        exact N.smul_mem a hz
    show Ideal.Quotient.mkₐ O I t = 0
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact htI
  haveI : Module.Finite O (LinearMap.range φ) := Module.IsNoetherian.finite O _
  haveI : Module.Finite O (T ⧸ LinearMap.ker φ) := Module.Finite.equiv (φ.quotKerEquivRange).symm
  exact Module.Finite.of_surjective ((LinearMap.ker φ).liftQ _ hker) (by
    intro q
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨Submodule.Quotient.mk t, rfl⟩)
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem lam_map {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : W.GDet n A G) (f : A →+* B)
    (g : G) (i : ℕ) : (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1)) := by
  have h0 : (D.map f).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map f := by
    letI : Algebra A (Polynomial B) := ((algebraMap B (Polynomial B)).comp f).toAlgebra
    let φ : Polynomial A →ₐ[A] Polynomial B :=
      { Polynomial.mapRingHom f with commutes' := fun a => Polynomial.map_C f }
    have h := D.nat (Polynomial A) (Polynomial B) φ
      (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.single g 1))
    refine Eq.trans ?_ h
    change D.D (Polynomial B) _ = D.D (Polynomial B) (MonoidAlgebra.mapRingHom G (Polynomial.mapRingHom f) _)
    congr 1
    simp [map_sub, MonoidAlgebra.mapRingHom_single]
  simp [W.GDet.lam, h0]

private theorem red_abs {O R T : Type} [CommRing O] [CommRing R] [CommRing T] [Algebra O R] [Algebra O T] (f : R →ₐ[O] T)
    (I : Ideal T) (S : Subalgebra O T) (hS : ∀ s ∈ S, ∀ k : ℕ, s ^ k ∈ I → s ∈ I) (U : Set R)
    (hU : ∀ u ∈ U, ∃ s ∈ S, f u - s ∈ I) (t : R) (ht : t ∈ Algebra.adjoin O U) (k : ℕ) (hk : f (t ^ k) ∈ I) : f t ∈ I := by
  have key : ∃ s ∈ S, f t - s ∈ I := by
    clear hk
    induction ht using Algebra.adjoin_induction with
    | mem x hx => exact hU x hx
    | algebraMap b => exact ⟨_, S.algebraMap_mem b, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, h1⟩ := hx
      obtain ⟨s', hs', h2⟩ := hy
      refine ⟨s + s', add_mem hs hs', ?_⟩
      have := I.add_mem h1 h2
      rw [map_add (f := _)]; convert this using 1; ring
    | mul x y _ _ hx hy =>
      obtain ⟨s, hs, h1⟩ := hx
      obtain ⟨s', hs', h2⟩ := hy
      refine ⟨s * s', mul_mem hs hs', ?_⟩
      have := I.add_mem (I.mul_mem_left (f x) h2) (I.mul_mem_left s' h1)
      rw [map_mul]; convert this using 1; ring
  obtain ⟨s, hs, h1⟩ := key
  have e : Ideal.Quotient.mk I (f t) = Ideal.Quotient.mk I s := Ideal.Quotient.eq.2 h1
  have h2 : s ^ k ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow, ← e, ← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact hk
  have := I.add_mem h1 (hS s hs k h2)
  simpa using this

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
theorem UpperTheory.V.Th.AnnihilatorQuotientFinite.ctrlMu :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.Aut ι P →
    ∀ (x : A →ₐ[c.O] c.O) (lam : Wt L l n), lam ∈ H.admitted → H.Arith θ ((Algebra.ofId c.O (Qbar l)).comp x).toRingHom lam →
    ∀ (a : H.Op → c.O) (K : H.Lev) [Module.Finite A (H.MK θ a K)] (R : Type) [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq)
      (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ) (μ : R →+* Module.End A (H.MK θ a K)),
      (H.MK θ a K = ⊥ ∨ ∃ (_ : Fact (CommOn (H.MK θ a K) (H.op A))) (_ : Alg.IsCO c.O (H.TK θ a K)) (f : R →ₐ[c.O] H.TK θ a K),
        H.IsMap θ a K D₀ ψ₀ f ∧ ∀ t, μ t = (f t : Module.End A (H.MK θ a K))) →
      ∀ t ∈ Algebra.adjoin c.O {b : R | ∃ i g, b = D₀.lam i (MonoidAlgebra.single g 1)}, ∀ k : ℕ,
        (∀ y, μ (t ^ k) y ∈ (RingHom.ker x • ⊤ : Submodule A (H.MK θ a K))) →
        ∀ y, μ t y ∈ (RingHom.ker x • ⊤ : Submodule A (H.MK θ a K)) := by
  intro L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι P hP x lam hl har a K _ R _ _ D₀ ψ₀ μ hμ t ht k hk y
  rcases hμ with h0 | ⟨_, _, f, hf, hμ⟩
  · have : μ t y = 0 := Subtype.ext ((Submodule.mem_bot A).1 (h0 ▸ (μ t y).2))
    rw [this]
    exact zero_mem _
  haveI := c.dvr
  have hker : RingHom.ker ((Algebra.ofId c.O (Qbar l)).comp x) = RingHom.ker x := by
    ext b
    rw [RingHom.mem_ker, RingHom.mem_ker]
    exact map_eq_zero_iff (algebraMap c.O (Qbar l)) Subtype.val_injective
  obtain ⟨I, hI, hfin⟩ := Th.AnnihilatorQuotientFinite.annFin x (heckeAlg (H.MK θ a K) (H.op A)).val.toRingHom fun o y => by
    rw [IsScalarTower.algebraMap_apply c.O A (H.TK θ a K)]
    rfl
  have h1 := red_abs f I (Algebra.adjoin c.O (Set.range fun p : H.Wp × Fin n => H.gen θ a K (.inl p)))
    (fun s hs k hk => (hI s).2 (by
      have := Th.AnnihilatorQuotientFinite.sphRed L Ω l n c H hH A θ hθ ι P hP _ lam hl har a K s hs k
      rw [hker] at this
      exact this ((hI _).1 hk))) _ (by
      rintro _ ⟨i, g, rfl⟩
      refine Th.AnnihilatorQuotientFinite.closedSub I _ _ fun N => ?_
      have := Th.AnnihilatorQuotientFinite.frobS L Ω l n c H hH A θ a K _ _ _ hf i g N
      rwa [lam_map] at this) t ht k ((hI _).2 fun y => by
      have := hk y
      rwa [hμ] at this)
  rw [hμ]
  exact (hI _).1 h1 y
