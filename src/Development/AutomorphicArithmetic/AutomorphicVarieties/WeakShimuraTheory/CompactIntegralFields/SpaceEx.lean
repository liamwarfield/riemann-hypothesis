module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.DerExtend
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SxUnivD
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SplitRes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KrullDimQuotientComapEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.GenZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.QuotPowNil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.PreOfCore

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.PreLine
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.ResLift
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem res_ps {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsCO Λ (PowerSeries (ResidueField Λ))]
    (x : PowerSeries (ResidueField Λ)) :
    res Λ (PowerSeries (ResidueField Λ)) x = PowerSeries.constantCoeff x := by
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (PowerSeries.constantCoeff x)
  have hm : x - algebraMap Λ (PowerSeries (ResidueField Λ)) a ∈
      maximalIdeal (PowerSeries (ResidueField Λ)) := by
    rw [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, map_sub,
      PowerSeries.algebraMap_apply, PowerSeries.constantCoeff_C,
      IsLocalRing.ResidueField.algebraMap_eq, ha, sub_self]
    exact not_isUnit_zero
  have h0 := (res_eq_zero_iff Λ (PowerSeries (ResidueField Λ)) _).2 hm
  rw [map_sub, sub_eq_zero] at h0
  rw [h0, AlgHom.commutes, IsLocalRing.ResidueField.algebraMap_eq, ha]

theorem UpperTheory.V.Ws.sxResLift :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} [IsCO Λ (PowerSeries (ResidueField Λ))] (Q : PD Φ.ι Γ (ResidueField Λ)[X]), Φ.IsRes (C.comp ((residue Λ).comp a)) Q → Φ.IsRes ((residue Λ).comp a) (Q.map (evalRingHom 0)) ∧ Φ.Lifts a (Q.map (evalRingHom 0)) (Q.map (Polynomial.coeToPowerSeries.ringHom : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ))) := by
  intro O Γ _ _ _ Φ Λ _ _ a _ Q h
  have hev : (evalRingHom (0 : ResidueField Λ)).comp (C.comp ((residue Λ).comp a)) =
      (residue Λ).comp a := by
    ext x
    simp
  have hco : (Polynomial.coeToPowerSeries.ringHom :
      (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)).comp (C.comp ((residue Λ).comp a)) =
      (algebraMap Λ (PowerSeries (ResidueField Λ))).comp a := by
    ext x
    simp [PowerSeries.algebraMap_apply, IsLocalRing.ResidueField.algebraMap_eq]
  have hcont : ∀ {R' : Type} [CommRing R'] (f : (ResidueField Λ)[X] →+* R') (J : Ideal R'),
      (Q.map f).Cont J := by
    intro R' _ f J i j
    exact adicCont_map f bot_le (h.cont i j)
  have hpt : ∀ p : (ResidueField Λ)[X],
      res Λ (PowerSeries (ResidueField Λ)) (p : PowerSeries (ResidueField Λ)) = eval 0 p := by
    intro p
    rw [res_ps, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      coeff_zero_eq_eval_zero]
  obtain ⟨_, hp1, hr1⟩ := sxPdMap (C.comp ((residue Λ).comp a)) (evalRingHom 0) Q
  obtain ⟨_, hp2, _⟩ := sxPdMap (C.comp ((residue Λ).comp a))
    (Polynomial.coeToPowerSeries.ringHom :
      (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) Q
  refine ⟨⟨?_, ?_, hcont _ _⟩, ⟨?_, hcont _ _, ?_⟩⟩
  · have := hp1 h.pair
    rwa [hev] at this
  · have := hr1 h.res
    rwa [hev] at this
  · have := hp2 h.pair
    rwa [hco] at this
  · apply PD.ext
    · refine MonoidHom.ext fun g => Matrix.ext fun i j => ?_
      exact hpt (Q.r g i j)
    · funext v
      refine Matrix.ext fun i j => ?_
      exact hpt (Q.n v i j)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SxCpRes
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem cp_low {R : Type} [CommRing R] (M : M4 R) (σ : Equiv.Perm (Fin 4))
    (h : ∀ i j, i < j → M (σ i) (σ j) = 0) : M.charpoly = ∏ i, (X - C (M i i)) := by
  have h1 : (Matrix.reindex σ.symm σ.symm M).charpoly = M.charpoly := Matrix.charpoly_reindex _ _
  rw [← h1, ← Matrix.charpoly_transpose, Matrix.charpoly_of_upperTriangular]
  · simpa using Equiv.prod_comp σ fun i => X - C (M i i)
  · intro i j hij
    simpa using h j i hij

theorem UpperTheory.V.Ws.sxCpRes :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] {Φ : Fr O Γ} {R : Type} [CommRing R] (a : O →+* R) (P : PD Φ.ι Γ R), Φ.Res a P → ∀ g, (P.r g).charpoly = ∏ i, (X - C (a (Φ.χ i g))) := by
  intro O Γ _ _ Φ R _ a P h g
  simp only [← h.diag g]
  rcases h.shape with ⟨h1, -⟩ | h1
  · refine cp_low _ (Equiv.swap 1 2) fun i j hij => h1 g _ _ ?_ ?_
    · exact fun e => hij.ne ((Equiv.swap 1 2).injective e)
    · revert i j; decide
  · refine cp_low _ 1 fun i j hij => h1 g _ _ hij.ne ?_
    revert i j; decide
end

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem preLine_desc {Λ A T S : Type} [CommRing Λ] [CommRing A] [CommRing T] [CommRing S] [Algebra Λ A]
    [Algebra Λ T] [Algebra Λ S] (f : A →ₐ[Λ] S) (j : T →ₐ[Λ] S) (hj : Function.Injective j)
    (h : ∀ x, f x ∈ j.range) : ∃ g : A →ₐ[Λ] T, ∀ x, j (g x) = f x := by
  refine ⟨(AlgEquiv.ofInjective j hj).symm.toAlgHom.comp (f.codRestrict j.range h), fun x => ?_⟩
  have := congrArg Subtype.val ((AlgEquiv.ofInjective j hj).apply_symm_apply ⟨f x, h x⟩)
  exact this

theorem UpperTheory.V.Ws.sxPreLine :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} (Y : Pre Φ a), Y.Line := by
  intro O Γ _ _ _ Φ Λ _ _ a Y Q hQ
  haveI h0 : IsCO Λ (ResidueField Λ) := (co_res Λ).1
  haveI hS : IsCO Λ (PowerSeries (ResidueField Λ)) := co_mvps Λ (ResidueField Λ) Unit
  obtain ⟨h1, h2⟩ := sxResLift Q hQ
  obtain ⟨f, hf⟩ := Y.univ _ _ _ h1 h2
  let j : (ResidueField Λ)[X] →ₐ[Λ] PowerSeries (ResidueField Λ) :=
    { (Polynomial.coeToPowerSeries.ringHom : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) with
      commutes' := fun x => by
        simp [Polynomial.algebraMap_apply, PowerSeries.algebraMap_apply] }
  have hj : Function.Injective j := Polynomial.coe_injective _
  have hf' : Y.P.map (f : Y.A →+* PowerSeries (ResidueField Λ)) = Q.map (j : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) := hf
  have hr : ∀ g i l, f (Y.P.r g i l) = j (Q.r g i l) := fun g i l =>
    congrArg (fun P : PD Φ.ι Γ _ => P.r g i l) hf'
  have hn : ∀ v i l, f (Y.P.n v i l) = j (Q.n v i l) := fun v i l =>
    congrArg (fun P : PD Φ.ι Γ _ => P.n v i l) hf'
  have hB : f.comp (IsScalarTower.toAlgHom Λ Y.B Y.A) = (j.comp Polynomial.CAlgHom).comp (res Λ Y.B) := by
    refine Y.genB _ _ _ (fun g n => ?_) (fun v i s hs => ?_)
    · show (f : Y.A →+* PowerSeries (ResidueField Λ)) (algebraMap Y.B Y.A _) =
        (j : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) ((C : ResidueField Λ →+* (ResidueField Λ)[X]) ((res Λ Y.B : Y.B →+* ResidueField Λ) _))
      rw [← coeff_map, ← coeff_map, ← coeff_map, ← coeff_map, ← coeff_map, Y.cp_map, Y.cp_red,
        ← Matrix.charpoly_map]
      have e : (Y.P.r g).map (f : Y.A →+* PowerSeries (ResidueField Λ)) = (Q.r g).map (j : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) := by
        ext1 i l
        exact hr g i l
      rw [e, Matrix.charpoly_map, sxCpRes _ Q hQ.res g]
      simp [Polynomial.map_prod]
    · show (f : Y.A →+* PowerSeries (ResidueField Λ)) (algebraMap Y.B Y.A _) = (j : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) (C (res Λ Y.B _))
      rw [Y.ψ_map v i s hs, Y.ψ_red v i s hs, ← (sxPdMap ((algebraMap Λ Y.A).comp a) _ Y.P).1, hf',
        (sxPdMap (C.comp ((residue Λ).comp a)) _ Q).1, hQ.res.char v s hs]
      rfl
  have hB' : ∀ b, f (algebraMap Y.B Y.A b) = j (C (res Λ Y.B b)) := fun b => DFunLike.congr_fun hB b
  have hrange : ∀ x, f x ∈ j.range := by
    intro x
    have hx : x ∈ Algebra.adjoin Y.B _ := Y.gen ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · exact ⟨_, (hr _ _ _).symm⟩
      · exact ⟨_, (hn _ _ _).symm⟩
    | algebraMap b => exact ⟨_, (hB' b).symm⟩
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  obtain ⟨g, hg⟩ := preLine_desc f j hj hrange
  refine ⟨g, ?_, fun b hb => hj ?_⟩
  · refine PD.ext (MonoidHom.ext fun s => Matrix.ext fun i l => hj ?_) (funext fun v => Matrix.ext fun i l => hj ?_)
    · exact (hg _).trans (hr s i l)
    · exact (hg _).trans (hn v i l)
  · rw [hg, hB', (res_eq_zero_iff Λ Y.B b).2 hb, map_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.ContGr
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem UpperTheory.V.Ws.sxContGr_pow {Λ K R : Type} [CommRing Λ] [CommRing K] [CommRing R] [Algebra Λ K] [Algebra Λ R]
    (e : K →ₐ[Λ] R) (J : Ideal K) (Q : Submodule Λ R) (hQ : ∀ x ∈ Q, ∃ y ∈ J, e y = x) (n : ℕ) :
    ∀ x ∈ Q ^ n, ∃ y ∈ J ^ n, e y = x := by
  induction n with
  | zero =>
    intro x hx
    rw [pow_zero, Submodule.one_eq_range] at hx
    obtain ⟨a, rfl⟩ := hx
    exact ⟨algebraMap Λ K a, by simp, e.commutes a⟩
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := ih a ha
      obtain ⟨v, hv, rfl⟩ := hQ b hb
      exact ⟨u * v, by rw [pow_succ]; exact Ideal.mul_mem_mul hu hv, map_mul e u v⟩
    · rintro a b ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
      exact ⟨u + v, add_mem hu hv, map_add e u v⟩

private theorem UpperTheory.V.Ws.sxContGr_mul {Λ K R : Type} [CommRing Λ] [CommRing K] [CommRing R] [Algebra Λ K] [Algebra Λ R]
    (e : K →ₐ[Λ] R) (J : Ideal K) (Q P : Submodule Λ R) (hQ : ∀ x ∈ Q, ∃ y ∈ J, e y = x)
    (hP : ∀ x ∈ P, ∃ y, e y = x) : ∀ x ∈ Q * P, ∃ y ∈ J, e y = x := by
  intro x hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro a ha b hb
    obtain ⟨u, hu, rfl⟩ := hQ a ha
    obtain ⟨v, rfl⟩ := hP b hb
    exact ⟨u * v, J.mul_mem_right v hu, map_mul e u v⟩
  · rintro a b ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    exact ⟨u + v, add_mem hu hv, map_add e u v⟩

private theorem UpperTheory.V.Ws.sxContGr_cont {Λ K R Γ : Type} [CommRing Λ] [CommRing K] [CommRing R] [Algebra Λ K] [Algebra Λ R]
    [TopologicalSpace Γ] (e : K →ₐ[Λ] R) (he : Function.Injective e) (I : Ideal R) (J : Ideal K) (Q P P' : Submodule Λ R)
    (hQ : ∀ x ∈ Q, ∃ y ∈ J, e y = x) (hP : ∀ x ∈ P, ∃ y, e y = x) (hP' : ∀ x ∈ P', ∃ y, e y = x)
    (h : ∀ n : ℕ, ∃ M : ℕ, P' ⊓ (I ^ M).restrictScalars Λ ≤ Q ^ n * P * P')
    (φ : Γ → K) (hφ : ∀ g, e (φ g) ∈ P') (hc : AdicCont I fun g => e (φ g)) : AdicCont J φ := by
  intro N
  obtain ⟨M, hM⟩ := h N
  have key : ∀ x ∈ Q ^ N * P * P', ∃ y ∈ J ^ N, e y = x := by
    intro x hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := UpperTheory.V.Ws.sxContGr_mul e (J ^ N) (Q ^ N) P
        (UpperTheory.V.Ws.sxContGr_pow e J Q hQ N) hP a ha
      obtain ⟨v, rfl⟩ := hP' b hb
      exact ⟨u * v, (J ^ N).mul_mem_right v hu, map_mul e u v⟩
    · rintro a b ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
      exact ⟨u + v, add_mem hu hv, map_add e u v⟩
  have hcM : IsLocallyConstant fun g => (Ideal.Quotient.mk (I ^ M)) (e (φ g)) := hc M
  refine (IsLocallyConstant.iff_exists_open _).2 fun g0 => ?_
  refine ⟨{g | (Ideal.Quotient.mk (I ^ M)) (e (φ g)) = (Ideal.Quotient.mk (I ^ M)) (e (φ g0))},
    hcM.isOpen_fiber _, rfl, fun g hg => ?_⟩
  have hd : e (φ g) - e (φ g0) ∈ I ^ M := Ideal.Quotient.eq.1 hg
  have hd' : e (φ g) - e (φ g0) ∈ P' ⊓ (I ^ M).restrictScalars Λ :=
    Submodule.mem_inf.2 ⟨sub_mem (hφ g) (hφ g0), (Submodule.restrictScalars_mem _ _ _).2 hd⟩
  obtain ⟨y, hy, hye⟩ := key _ (hM hd')
  rw [← map_sub] at hye
  have : y = φ g - φ g0 := he hye
  exact Ideal.Quotient.eq.2 (this ▸ hy)

theorem UpperTheory.V.Ws.sxContGr :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (W : WPres Λ X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ [IsCO Λ (W.gr 0)] {Γ : Type} [TopologicalSpace Γ], (∀ (j : X) (φ : Γ → W.A), (∀ g, φ g ∈ W.gr j) → AdicCont (maximalIdeal R) (fun g => (φ g : R)) → AdicCont ((maximalIdeal (W.gr 0)).map (algebraMap (W.gr 0) W.A)) φ) ∧ ∀ φ : Γ → W.gr 0, AdicCont (maximalIdeal R) (fun g => ((φ g : W.A) : R)) → AdicCont (maximalIdeal (W.gr 0)) φ := by
  intro Λ _ _ _ _ X _ _ _ _ R _ _ _ W hz _ Γ _
  obtain ⟨hmax, -⟩ := wPres_maximalIdeal_gr_zero_eq_sup_span_monomials Λ X R W hz
  have hfilt := part_filt Λ X R W hz
  have hb : ∀ b : W.gr 0, algebraMap (W.gr 0) W.A b = (b : W.A) := fun b => by first | rfl | simp
  have ha : ∀ a : Λ, ((algebraMap Λ (W.gr 0) a : W.A) : R) = algebraMap Λ R a :=
    fun a => by first | rfl | simp
  refine ⟨fun j φ hφ hc => ?_, fun φ hc => ?_⟩
  · refine UpperTheory.V.Ws.sxContGr_cont W.A.val Subtype.val_injective (maximalIdeal R)
      ((maximalIdeal (W.gr 0)).map (algebraMap (W.gr 0) W.A))
      (W.part 0 ⊓ (maximalIdeal R).restrictScalars Λ) (W.part 0) (W.part j) ?_ ?_ ?_
      (fun n => hfilt j n) φ (fun g => hφ g) hc
    · intro x hx
      obtain ⟨hx0, hxm⟩ := Submodule.mem_inf.1 hx
      refine ⟨algebraMap (W.gr 0) W.A ⟨⟨x, W.part_le_A hx0⟩, hx0⟩,
        Ideal.mem_map_of_mem _ ((hmax _).2 ((Submodule.restrictScalars_mem _ _ _).1 hxm)), ?_⟩
      rw [hb]
      rfl
    · exact fun x hx => ⟨⟨x, W.part_le_A hx⟩, rfl⟩
    · exact fun x hx => ⟨⟨x, W.part_le_A hx⟩, rfl⟩
  · let e : W.gr 0 →ₐ[Λ] R := AlgHom.mk ((W.A.val : W.A →+* R).comp (algebraMap (W.gr 0) W.A))
      (fun a => by
        show W.A.val (algebraMap (W.gr 0) W.A (algebraMap Λ (W.gr 0) a)) = _
        rw [hb]
        exact ha a)
    have he : ∀ b : W.gr 0, e b = ((b : W.A) : R) := fun b => by
      show W.A.val (algebraMap (W.gr 0) W.A b) = _
      rw [hb]
      rfl
    have hinj : Function.Injective e := by
      intro b c hbc
      rw [he, he] at hbc
      exact Subtype.ext (Subtype.ext hbc)
    have hc' : AdicCont (maximalIdeal R) fun g => e (φ g) := by
      have hfun : (fun g => e (φ g)) = fun g => ((φ g : W.A) : R) := funext fun g => he _
      rw [hfun]
      exact hc
    refine UpperTheory.V.Ws.sxContGr_cont e hinj (maximalIdeal R) (maximalIdeal (W.gr 0))
      (W.part 0 ⊓ (maximalIdeal R).restrictScalars Λ) (W.part 0) (W.part 0) ?_ ?_ ?_
      (fun n => hfilt 0 n) φ (fun g => by rw [he]; exact (φ g).2) hc'
    · intro x hx
      obtain ⟨hx0, hxm⟩ := Submodule.mem_inf.1 hx
      exact ⟨⟨⟨x, W.part_le_A hx0⟩, hx0⟩,
        (hmax _).2 ((Submodule.restrictScalars_mem _ _ _).1 hxm), he _⟩
    · exact fun x hx => ⟨⟨⟨x, W.part_le_A hx⟩, hx⟩, he _⟩
    · exact fun x hx => ⟨⟨⟨x, W.part_le_A hx⟩, hx⟩, he _⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.PreImage
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem adjoin_top_of_tower {B B' A : Type} [CommRing B] [CommRing B'] [CommRing A] [Algebra B A] [Algebra B B']
    [Algebra B' A] [IsScalarTower B B' A] {s : Set A} (h : Algebra.adjoin B s = ⊤) : Algebra.adjoin B' s = ⊤ := by
  have h1 : Algebra.adjoin B s ≤ (Algebra.adjoin B' s).restrictScalars B :=
    Algebra.adjoin_le fun x hx => (Subalgebra.mem_restrictScalars B).2 (Algebra.subset_adjoin hx)
  rw [h] at h1
  exact eq_top_iff.2 fun x _ => (Subalgebra.mem_restrictScalars B).1 (h1 Algebra.mem_top)

private theorem pre_of_surj {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ]
    [IsLocalRing Λ] {a : O →+* Λ} (Y : Pre Φ a) [Nontrivial Y.A] (B' : Type) [CommRing B'] [Algebra Λ B']
    (p : Y.B →ₐ[Λ] B') (hp : Function.Surjective p) (j : B' →+* Y.A) (hj : ∀ b, j (p b) = algebraMap Y.B Y.A b)
    (hi : Function.Injective j) : ∃ Y' : Pre Φ a, Function.Injective (algebraMap Y'.B Y'.A) := by
  have hp' : Function.Surjective (p : Y.B →+* B') := hp
  haveI : Nontrivial B' := j.domain_nontrivial
  haveI : IsCO Λ B' := co_quot Λ Y.B B' p hp
  letI : Algebra B' Y.A := j.toAlgebra
  letI : Algebra Y.B B' := (p : Y.B →+* B').toAlgebra
  haveI t1 : IsScalarTower Y.B B' Y.A := IsScalarTower.of_algebraMap_eq fun b => (hj b).symm
  haveI t2 : IsScalarTower Λ B' Y.A := IsScalarTower.of_algebraMap_eq fun b => by
    rw [← p.commutes, IsScalarTower.algebraMap_apply Λ Y.B Y.A]
    exact (hj _).symm
  have hm : (maximalIdeal Y.B).map (p : Y.B →+* B') = maximalIdeal B' :=
    IsLocalRing.map_maximalIdeal_of_surjective _ hp'
  have hle : maximalIdeal Y.B ≤ (maximalIdeal B').comap (p : Y.B →+* B') := by
    rw [← hm]; exact Ideal.le_comap_map
  have hc : (algebraMap B' Y.A).comp (p : Y.B →+* B') = algebraMap Y.B Y.A := RingHom.ext hj
  have hr : (res Λ B' : B' →+* ResidueField Λ).comp (p : Y.B →+* B') =
      (res Λ Y.B : Y.B →+* ResidueField Λ) := RingHom.ext fun b => res_map (O := Λ) (R := Y.B) p b
  haveI := Y.ft
  refine ⟨{ A := Y.A, B := B', ft := Algebra.FiniteType.of_restrictScalars_finiteType Y.B _ _
            P := Y.P, pair := Y.pair, cont := ?_, gen := adjoin_top_of_tower Y.gen
            cp := fun g => (Y.cp g).map (p : Y.B →+* B')
            cp_map := fun g => ?_, cp_cont := fun n => ?_, cp_red := fun g => ?_
            ψ := fun v i s => p (Y.ψ v i s)
            ψ_map := fun v i s hs => (hj _).trans (Y.ψ_map v i s hs)
            ψ_cont := fun v i => adicCont_map (p : Y.B →+* B') hle (Y.ψ_cont v i)
            ψ_red := fun v i s hs => (res_map (O := Λ) (R := Y.B) p _).trans (Y.ψ_red v i s hs)
            genB := fun R _ _ _ f f' h1 h2 => ?_
            univ := Y.univ }, hi⟩
  · rw [← hm, Ideal.map_map, hc]
    exact Y.cont
  · rw [Polynomial.map_map, hc, Y.cp_map]
  · simp only [coeff_map]
    exact adicCont_map (p : Y.B →+* B') hle (Y.cp_cont n)
  · rw [Polynomial.map_map, hr, Y.cp_red]
  · have h : f.comp p = f'.comp p := Y.genB R _ _ (fun g n => by
      have h3 := h1 g n
      rw [coeff_map] at h3
      exact h3) h2
    refine AlgHom.ext fun x => ?_
    obtain ⟨b, rfl⟩ := hp x
    exact AlgHom.congr_fun h b

theorem UpperTheory.V.Ws.sxPreImage :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} (Y : Pre Φ a), Nontrivial Y.A → ∃ Y' : Pre Φ a, Function.Injective (algebraMap Y'.B Y'.A) := by
  intro O Γ _ _ _ Φ Λ _ _ a Y hA
  exact pre_of_surj Y (Y.B ⧸ RingHom.ker (algebraMap Y.B Y.A)) (Ideal.Quotient.mkₐ Λ _) Ideal.Quotient.mk_surjective
    (RingHom.kerLift (algebraMap Y.B Y.A)) (fun b => RingHom.kerLift_mk _ b) (RingHom.kerLift_injective _)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.CoreGen
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxCoreGen :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R} {W : WPres Λ (ℤ × ℤ) R}, RD.Graded D W → ∀ (D' : RD Φ W.A), D'.map (W.A.val : W.A →+* R) = D → Algebra.adjoin (W.gr 0) (Set.range fun x : Γ × Fin 4 × Fin 4 => D'.r x.1 x.2.1 x.2.2) = ⊤ := by
  intro O Γ _ _ _ Φ Λ _ _ _ _ R _ _ _ D W hD D' hmap
  have hr : ∀ g i j, D.r g i j = (D'.r g i j : R) := by
    subst hmap
    intro g i j
    first | rfl | simp [RD.map]
  have hψ : ∀ v i t, D.ψ v i t = (D'.ψ v i t : R) := by
    subst hmap
    intro v i t
    first | rfl | simp [RD.map]
  set S := Algebra.adjoin (W.gr 0) (Set.range fun x : Γ × Fin 4 × Fin 4 => D'.r x.1 x.2.1 x.2.2) with hS
  have hbA : ∀ b : W.gr 0, algebraMap (W.gr 0) W.A b = (b : W.A) := fun b => by first | rfl | simp
  have hgr : ∀ x : W.A, (x : R) ∈ W.part 0 → x ∈ S := by
    intro x hx
    have h := Subalgebra.algebraMap_mem S (⟨x, hx⟩ : W.gr 0)
    rwa [hbA] at h
  have hc : ∀ c : Λ, algebraMap Λ W.A c ∈ S := by
    intro c
    apply hgr
    have h0 : algebraMap Λ R c ∈ W.part 0 := by
      have := (algebraMap Λ (W.gr 0) c).2
      first
        | exact this
        | (have e : ((algebraMap Λ (W.gr 0) c : W.A) : R) = algebraMap Λ R c := by first | rfl | simp
           rw [← e]; exact this)
    first | exact h0 | simpa using h0
  have hr' : ∀ g i j, D'.r g i j ∈ S := fun g i j => Algebra.subset_adjoin ⟨(g, i, j), rfl⟩
  have hz : ∀ s, W.zA s ∈ S := by
    intro s
    rcases hD.var s with ⟨g, i, j, c, hzs, -, -⟩ | ⟨v, i, t, c, hzs, -⟩
    · have e : W.zA s = D'.r g i j - algebraMap Λ W.A c := by
        apply Subtype.ext
        show W.z s = _
        rw [hzs, hr]
        rfl
      rw [e]
      exact sub_mem (hr' g i j) (hc c)
    · have e : W.zA s = D'.ψ v i t - algebraMap Λ W.A c := by
        apply Subtype.ext
        show W.z s = _
        rw [hzs, hψ]
        rfl
      rw [e]
      refine sub_mem (hgr _ ?_) (hc c)
      rw [← hψ]
      exact hD.chr v i t
  rw [eq_top_iff]
  intro a ha0
  clear ha0
  have ha : a ∈ Algebra.adjoin Λ (↑(W.gr 0) ∪ Set.range W.zA) := by
    rw [gr_gen Λ R (ℤ × ℤ) W]
    trivial
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | ⟨s, rfl⟩
    · exact hgr x hx
    · exact hz s
  | algebraMap c => exact hc c
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SxSubRD
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxSubRD :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] {Φ : Fr O Γ} {Λ R : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] (a : O →+* Λ) (A : Subalgebra Λ R) (D : RD Φ R), (∀ g i j, D.r g i j ∈ A) → (∀ v i s, D.ψ v i s ∈ A) → Φ.IsRep ((algebraMap Λ R).comp a) D.r → ∃ D' : RD Φ A, D'.map (A.val : A →+* R) = D ∧ Φ.IsRep ((algebraMap Λ A).comp a) D'.r := by
  intro O Γ _ _ Φ Λ R _ _ _ a A D hr hψ h
  have h1 : ∀ i j : Fin 4, (((1 : M4 A) i j : A) : R) = (1 : M4 R) i j := fun i j => by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  let r' : Γ →* M4 A :=
    { toFun := fun g => Matrix.of fun i j => ⟨D.r g i j, hr g i j⟩
      map_one' := by
        ext i j
        rw [h1]; simp
      map_mul' := fun g g' => by
        ext i j
        simp [Matrix.mul_apply] }
  have hr' : ∀ g i j, ((r' g i j : A) : R) = D.r g i j := fun _ _ _ => rfl
  refine ⟨⟨r', fun v i => (D.ψ v i).codRestrict A (hψ v i)⟩, ?_, fun g => ?_, fun g hg => ?_, fun i j hij => ?_⟩
  · refine RD.ext ?_ ?_
    · ext g i j; rfl
    · funext v i; ext s; rfl
  · have := h.mult g
    unfold IsGSp at this ⊢
    ext i j
    have e := congrFun (congrFun this i) j
    simp only [Matrix.smul_apply, smul_eq_mul, MulMemClass.coe_mul, h1]
    simp only [Matrix.smul_apply, smul_eq_mul] at e
    refine Eq.trans ?_ e
    simp [Matrix.mul_apply, adj, hr']
  · ext i j
    rw [h1]
    show D.r g i j = _
    rw [h.kill g hg]
  · exact Subtype.ext (h.nrm hij)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.CpZero
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private def cpZeroPol {Λ A : Type} [CommRing Λ] [CommRing A] [Algebra Λ A] (𝒜 : ℤ × ℤ → Submodule Λ A)
    (w : ℤ × ℤ) : AddSubgroup A[X] where
  carrier := {p | ∀ n, p.coeff n ∈ 𝒜 w}
  add_mem' := fun {p q} hp hq n => by rw [coeff_add]; exact add_mem (hp n) (hq n)
  zero_mem' := fun n => by rw [coeff_zero]; exact zero_mem _
  neg_mem' := fun {p} hp n => by rw [coeff_neg]; exact neg_mem (hp n)

private theorem cpZeroPol_graded {Λ A : Type} [CommRing Λ] [CommRing A] [Algebra Λ A] (𝒜 : ℤ × ℤ → Submodule Λ A)
    [SetLike.GradedMonoid 𝒜] : SetLike.GradedMonoid (cpZeroPol 𝒜) := by
  refine { one_mem := ?_, mul_mem := ?_ }
  · change ∀ n, (1 : A[X]).coeff n ∈ 𝒜 0
    intro n
    rw [coeff_one]
    split_ifs
    · exact SetLike.one_mem_graded 𝒜
    · exact zero_mem _
  · intro i j p q hp hq
    change ∀ n, p.coeff n ∈ 𝒜 i at hp
    change ∀ n, q.coeff n ∈ 𝒜 j at hq
    change ∀ n, (p * q).coeff n ∈ 𝒜 (i + j)
    intro n
    rw [coeff_mul]
    exact Submodule.sum_mem _ fun x _ => SetLike.mul_mem_graded (hp x.1) (hq x.2)

theorem UpperTheory.V.Ws.sxCpZero :
    ∀ {Λ A : Type} [CommRing Λ] [CommRing A] [Algebra Λ A] (𝒜 : ℤ × ℤ → Submodule Λ A) [SetLike.GradedMonoid 𝒜] (M : M4 A), (∀ i j, M i j ∈ 𝒜 (wt i j)) → ∀ n, M.charpoly.coeff n ∈ 𝒜 0 := by
  intro Λ A _ _ _ 𝒜 _ M hM
  have := cpZeroPol_graded 𝒜
  have hC : ∀ i j, C (M i j) ∈ cpZeroPol 𝒜 (wt i j) := fun i j n => by
    rw [coeff_C]
    split_ifs
    · exact hM i j
    · exact zero_mem _
  have hX : (X : A[X]) ∈ cpZeroPol 𝒜 0 := fun n => by
    rw [coeff_X]
    split_ifs
    · exact SetLike.one_mem_graded 𝒜
    · exact zero_mem _
  have hE : ∀ i j, M.charmatrix i j ∈ cpZeroPol 𝒜 (wt i j) := by
    intro i j
    by_cases h : i = j
    · subst h
      rw [Matrix.charmatrix_apply_eq]
      refine sub_mem ?_ (hC i i)
      have : wt i i = 0 := by simp [wt]
      rw [this]; exact hX
    · rw [Matrix.charmatrix_apply_ne _ _ _ h]
      exact neg_mem (hC i j)
  have key : M.charpoly ∈ cpZeroPol 𝒜 0 := by
    rw [Matrix.charpoly, Matrix.det_apply]
    refine AddSubgroup.sum_mem _ fun σ _ => ?_
    have h0 : ∑ i, wt (σ i) i = 0 := by
      have h1 := Equiv.sum_comp σ lamW
      have h2 := Equiv.sum_comp σ muW
      ext
      · simp only [wt, Prod.fst_sum, Finset.sum_sub_distrib, h1, sub_self, Prod.fst_zero]
      · simp only [wt, Prod.snd_sum, Finset.sum_sub_distrib, h2, sub_self, Prod.snd_zero]
    have hp : ∏ i, M.charmatrix (σ i) i ∈ cpZeroPol 𝒜 (∑ i, wt (σ i) i) :=
      SetLike.prod_mem_graded (cpZeroPol 𝒜) (fun i => wt (σ i) i) (fun i => M.charmatrix (σ i) i) fun i _ => hE (σ i) i
    rw [h0] at hp
    rw [Units.smul_def]
    exact AddSubgroup.zsmul_mem _ hp _
  exact key
end

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.spaceEx :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ), Φ.Std l a → Nonempty (Space Φ a) := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hS
  haveI : IsCO Λ (ResidueField Λ) := (co_res Λ).1
  obtain ⟨R, _, _, _, D, hU⟩ := sxUnivD l hS
  obtain ⟨W, hW⟩ := sxGradD hU
  haveI : IsCO Λ (W.gr 0) := wPres_gr_zero_isCO_of_mem_maximalIdeal Λ (ℤ × ℤ) R W hW.max
  haveI : IsScalarTower Λ (W.gr 0) W.A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨D', hD', hrep⟩ := sxSubRD a W.A D (fun g i j => W.part_le_A (hW.ent g i j))
    (fun v i s => W.part_le_A (hW.chr v i s)) hU.1.rep
  have hψ : ∀ v i s, (W.A.val (D'.ψ v i s) : R) = D.ψ v i s := by
    intro v i s
    rw [← hD']
    rfl
  have hr : ∀ g i j, (W.A.val (D'.r g i j) : R) = D.r g i j := by
    intro g i j
    rw [← hD']
    rfl
  have hcp : ∃ cp : Γ → (W.gr 0)[X],
      (∀ g, (cp g).map (algebraMap (W.gr 0) W.A) = (D'.r g).charpoly) ∧
      (∀ n, AdicCont (maximalIdeal (W.gr 0)) fun g => (cp g).coeff n) ∧
      ∀ g, (cp g).map (res Λ (W.gr 0) : W.gr 0 →+* ResidueField Λ) =
        ∏ i, (X - C (residue Λ (a (Φ.χ i g)))) := by
    have hr' : ∀ g, D.r g = (D'.r g).map (W.A.val : W.A →+* R) := fun g => by
      rw [← hD']; rfl
    have hent : ∀ g i j, D'.r g i j ∈ W.gr (wt i j) := fun g i j => by
      have h := hW.ent g i j
      rw [hr'] at h
      exact h
    have hc : ∀ g n, (D'.r g).charpoly.coeff n ∈ W.gr 0 :=
      fun g n => sxCpZero W.gr (D'.r g) (hent g) n
    have hl : ∀ g, ∃ p : (W.gr 0)[X], p.map (algebraMap (W.gr 0) W.A) = (D'.r g).charpoly := fun g => by
      have h : (D'.r g).charpoly ∈ Polynomial.lifts (algebraMap (W.gr 0) W.A) := by
        rw [Polynomial.lifts_iff_coeff_lifts]
        intro n
        exact ⟨⟨_, hc g n⟩, rfl⟩
      exact (Polynomial.mem_lifts _).1 h
    choose cp hcp using hl
    have hco : ∀ g n, (((cp g).coeff n : W.A) : R) = (D.r g).charpoly.coeff n := fun g n => by
      rw [hr', Matrix.charpoly_map, coeff_map, ← hcp, coeff_map]
      rfl
    refine ⟨cp, hcp, fun n => ?_, fun g => ?_⟩
    · refine (sxContGr W hW.max).2 _ ?_
      simp only [hco]
      exact (sxAdicMat (maximalIdeal R) (fun g => D.r g) hU.1.cont).1 n
    · let f : W.gr 0 →ₐ[Λ] R :=
        { (W.A.val : W.A →+* R).comp (algebraMap (W.gr 0) W.A) with
          commutes' := fun _ => rfl }
      have hd : (D.r g).map (res Λ R : R →+* ResidueField Λ) =
          Matrix.diagonal fun i => residue Λ (a (Φ.χ i g)) := by
        ext i j
        by_cases h : i = j
        · subst h
          rw [Matrix.diagonal_apply_eq]
          exact hU.1.diag g i
        · rw [Matrix.diagonal_apply_ne _ h]
          exact (res_eq_zero_iff Λ R _).2 (hU.1.off g i j h le_rfl)
      rw [← Matrix.charpoly_diagonal, ← hd, Matrix.charpoly_map]
      ext n
      rw [coeff_map, coeff_map, ← hco]
      exact (res_map f _).symm
  obtain ⟨cp, hcp1, hcp2, hcp3⟩ := hcp
  have sxCoreGen :
      ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R} {W : WPres Λ (ℤ × ℤ) R}, RD.Graded D W → ∀ (D' : RD Φ W.A), D'.map (W.A.val : W.A →+* R) = D → Algebra.adjoin (W.gr 0) (Set.range fun x : Γ × Fin 4 × Fin 4 => D'.r x.1 x.2.1 x.2.2) = ⊤ := by
    exact @_root_.UpperTheory.V.Ws.sxCoreGen
  have eq_of_forall_sub_mem_maxIdeal_pow_of_adicComplete {R : Type} [CommRing R] [IsLocalRing R]
      [IsAdicComplete (maximalIdeal R) R] {x y : R}
      (h : ∀ N : ℕ, x - y ∈ maximalIdeal R ^ (N + 1)) : x = y := by
    rw [IsHausdorff.eq_iff_smodEq (I := maximalIdeal R)]
    intro n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    cases n with
    | zero => simp
    | succ N => exact h N

  have nontrivial_quotient_maxIdeal_pow_succ {R : Type} [CommRing R] [IsLocalRing R] (N : ℕ) :
      Nontrivial (R ⧸ maximalIdeal R ^ (N + 1)) := by
    apply Ideal.Quotient.nontrivial_iff.mpr
    intro h
    apply (maximalIdeal.isMaximal R).ne_top
    exact top_le_iff.mp (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero N))

  have isNilpotent_maxIdeal_quotient_maxIdeal_pow_succ {R : Type} [CommRing R] [IsLocalRing R] (N : ℕ)
      [IsLocalRing (R ⧸ maximalIdeal R ^ (N + 1))] :
      IsNilpotent (maximalIdeal (R ⧸ maximalIdeal R ^ (N + 1))) := by
    refine ⟨N + 1, ?_⟩
    have hle : maximalIdeal (R ⧸ maximalIdeal R ^ (N + 1)) ≤
        (maximalIdeal R).map (Ideal.Quotient.mk (maximalIdeal R ^ (N + 1))) := by
      intro x hx
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      apply Ideal.mem_map_of_mem
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
      exact fun hu => hx (hu.map _)
    rw [Ideal.zero_eq_bot, eq_bot_iff]
    calc _ ≤ ((maximalIdeal R).map (Ideal.Quotient.mk (maximalIdeal R ^ (N + 1)))) ^ (N + 1) :=
          Ideal.pow_right_mono hle _
      _ = ⊥ := by rw [← Ideal.map_pow, Ideal.map_quotient_self]
  have sxNearA :
      ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R} {W : WPres Λ (ℤ × ℤ) R}, Φ.RUniv a D → RD.Graded D W → ∀ (D' : RD Φ W.A), D'.map (W.A.val : W.A →+* R) = D → ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (τ : ℤ × ℤ →+ ℤ) (Q : RD Φ R'), Φ.Near a τ Q → ∃ f : W.A →ₐ[Λ] R', D'.map (f : W.A →+* R') = Q := by
    intro O Γ _ _ _ Φ Λ _ _ _ _ a R _ _ _ D W hU hG D' hD' R' _ _ _ τ Q hQ
    classical
    have liftNilpotent : ∀ (T : Type) [CommRing T] [Algebra Λ T] [IsCO Λ T] (P : RD Φ T),
        IsNilpotent (maximalIdeal T) → Φ.Near a τ P → ∃ f : W.A →ₐ[Λ] T, D'.map (f : W.A →+* T) = P := by
      intro T _ _ _ P hnil hP
      let c := ∑ p : Fin 4 × Fin 4, (τ (wt p.1 p.2)).natAbs
      have hc : ∀ i j, -(c : ℤ) ≤ τ (wt i j) := by
        intro i j
        have h : (τ (wt i j)).natAbs ≤ c :=
          Finset.single_le_sum (f := fun p : Fin 4 × Fin 4 => (τ (wt p.1 p.2)).natAbs)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i, j))
        omega
      obtain ⟨S, _, _, _, e, he⟩ := sxLaur (Λ := Λ) hnil c
      obtain ⟨P', hP', hr, hψ⟩ := sxScaleRD hnil he hc hP
      obtain ⟨F, hF, -⟩ := hU.2 S P' hP'
      have hFr : ∀ g i j, e (F (D.r g i j)) = HahnSeries.single (τ (wt i j)) (P.r g i j) := by
        intro g i j
        rw [← hr, ← hF]
        rfl
      have hFψ : ∀ v i s, e (F (D.ψ v i s)) = HahnSeries.single 0 (P.ψ v i s) := by
        intro v i s
        rw [← hψ, ← hF]
        rfl
      have hz : ∀ s, ∃ y, e (F (W.z s)) = HahnSeries.single (τ (W.wt s)) y := by
        intro s
        rcases hG.var s with ⟨g, i, j, x, h1, h2, h3⟩ | ⟨v, i, t, x, h1, h2⟩
        · rw [h1, h2, map_sub, map_sub, hFr, AlgHom.commutes, he.alg]
          by_cases hij : i = j
          · rw [(wt_eq_zero i j).2 hij, map_zero]
            exact ⟨_, (HahnSeries.single_sub _ _ _).symm⟩
          · rw [h3 hij]
            exact ⟨P.r g i j, by simp⟩
        · rw [h1, h2, map_sub, map_sub, hFψ, AlgHom.commutes, he.alg, map_zero]
          exact ⟨_, (HahnSeries.single_sub _ _ _).symm⟩
      obtain ⟨f, hf⟩ := sxLaurDesc W he τ F (sxLaurPart W hG.max he τ F hz)
      have er : ∀ g i j, ((D'.r g i j : W.A) : R) = D.r g i j := by
        intro g i j
        rw [← hD']
        rfl
      have eψ : ∀ v i s, ((D'.ψ v i s : W.A) : R) = D.ψ v i s := by
        intro v i s
        rw [← hD']
        rfl
      refine ⟨f, RD.ext ?_ ?_⟩
      · ext g i j
        have hm : D'.r g i j ∈ W.gr (wt i j) := by
          show ((D'.r g i j : W.A) : R) ∈ W.part (wt i j)
          rw [er]
          exact hG.ent g i j
        have h := hf _ _ hm
        rw [er, hFr] at h
        exact (HahnSeries.single_injective _ h).symm
      · funext v i
        ext s
        have hm : D'.ψ v i s ∈ W.gr 0 := by
          show ((D'.ψ v i s : W.A) : R) ∈ W.part 0
          rw [eψ]
          exact hG.chr v i s
        have h := hf _ _ hm
        rw [eψ, hFψ, map_zero] at h
        exact (HahnSeries.single_injective _ h).symm
    have hlev : ∀ N : ℕ, ∃ f : W.A →ₐ[Λ] R' ⧸ maximalIdeal R' ^ (N + 1),
        D'.map (f : W.A →+* _) = Q.map (Ideal.Quotient.mk (maximalIdeal R' ^ (N + 1))) := by
      intro N
      haveI : Nontrivial (R' ⧸ maximalIdeal R' ^ (N + 1)) := nontrivial_quotient_maxIdeal_pow_succ N
      haveI : IsCO Λ (R' ⧸ maximalIdeal R' ^ (N + 1)) :=
        co_quot Λ R' _ (Ideal.Quotient.mkₐ Λ _) (Ideal.Quotient.mkₐ_surjective Λ _)
      exact liftNilpotent _ _ (isNilpotent_maxIdeal_quotient_maxIdeal_pow_succ N)
        (sxNearMap (Ideal.Quotient.mkₐ Λ (maximalIdeal R' ^ (N + 1))) hQ)
    have hval : ∀ s : W.σ, ∃ y : R', ∀ (N : ℕ) (f : W.A →ₐ[Λ] R' ⧸ maximalIdeal R' ^ (N + 1)),
        D'.map (f : W.A →+* _) = Q.map (Ideal.Quotient.mk (maximalIdeal R' ^ (N + 1))) →
        f (W.zA s) = Ideal.Quotient.mk _ y := by
      intro s
      rcases hG.var s with ⟨g, i, j, c, hz, -, -⟩ | ⟨v, i, t, c, hz, -⟩
      · refine ⟨Q.r g i j - algebraMap Λ R' c, fun N f hf => ?_⟩
        have e1 : D.r g i j = ((D'.r g i j : W.A) : R) := by rw [← hD']; rfl
        have hA : W.zA s = D'.r g i j - algebraMap Λ W.A c := by
          apply Subtype.ext
          change W.z s = _
          rw [hz, e1]
          rfl
        have e2 : f (D'.r g i j) = Ideal.Quotient.mk _ (Q.r g i j) :=
          congrArg (fun E => E.r g i j) hf
        rw [hA, map_sub, AlgHom.commutes, e2, map_sub, Ideal.Quotient.mk_algebraMap]
      · refine ⟨Q.ψ v i t - algebraMap Λ R' c, fun N f hf => ?_⟩
        have e1 : D.ψ v i t = ((D'.ψ v i t : W.A) : R) := by rw [← hD']; rfl
        have hA : W.zA s = D'.ψ v i t - algebraMap Λ W.A c := by
          apply Subtype.ext
          change W.z s = _
          rw [hz, e1]
          rfl
        have e2 : f (D'.ψ v i t) = Ideal.Quotient.mk _ (Q.ψ v i t) :=
          congrArg (fun E => E.ψ v i t) hf
        rw [hA, map_sub, AlgHom.commutes, e2, map_sub, Ideal.Quotient.mk_algebraMap]
    choose y hy using hval
    choose fN hfN using hlev
    have huniq : ∀ (N : ℕ) (f f' : W.A →ₐ[Λ] R' ⧸ maximalIdeal R' ^ (N + 1)),
        (∀ s, f (W.zA s) = f' (W.zA s)) → f = f' := by
      intro N f f' h
      haveI : Nontrivial (R' ⧸ maximalIdeal R' ^ (N + 1)) := nontrivial_quotient_maxIdeal_pow_succ N
      haveI : IsCO Λ (R' ⧸ maximalIdeal R' ^ (N + 1)) :=
        co_quot Λ R' _ (Ideal.Quotient.mkₐ Λ _) (Ideal.Quotient.mkₐ_surjective Λ _)
      exact sxExtA W hG.max _ f f' h
    haveI : IsAdicComplete (maximalIdeal R') R' := IsCO.complete (O := Λ)
    obtain ⟨F, hF⟩ := sxLimPt (Λ := Λ) (maximalIdeal R') W.zA y
      (fun N => ⟨fN N, fun s => hy s N (fN N) (hfN N)⟩) huniq
    have hcomp : ∀ N, (Ideal.Quotient.mkₐ Λ (maximalIdeal R' ^ (N + 1))).comp F = fN N := by
      intro N
      apply huniq
      intro s
      rw [AlgHom.comp_apply, hF s, hy s N (fN N) (hfN N)]
      rfl
    have hpt : ∀ (x : W.A) (q : R'), (∀ N, fN N x = Ideal.Quotient.mk _ q) → F x = q := by
      intro x q hx
      apply eq_of_forall_sub_mem_maxIdeal_pow_of_adicComplete
      intro N
      rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← hx N, ← hcomp N]
      rfl
    refine ⟨F, ?_⟩
    apply RD.ext
    · ext g i j
      exact hpt _ _ (fun N => congrArg (fun E => E.r g i j) (hfN N))
    · funext v i
      ext t
      exact hpt _ _ (fun N => congrArg (fun E => E.ψ v i t) (hfN N))
  let ψ : (v : Φ.ι) → Fin 4 → Φ.Gv v → W.gr 0 := fun v i s =>
    ⟨D'.ψ v i s, by
      show W.A.val (D'.ψ v i s) ∈ W.part 0
      rw [hψ]
      exact hW.chr v i s⟩
  have hcont := sxContGr W hW.max (Γ := Γ)
  let C : Core Φ a :=
    { A := W.A
      B := W.gr 0
      ft := (gr_noeth Λ (ℤ × ℤ) R W hW.max).2.1
      D := D'
      rep := hrep
      cont := fun i j => hcont.1 (wt i j) (fun g => D'.r g i j)
        (fun g => by
          show W.A.val (D'.r g i j) ∈ W.part (wt i j)
          rw [hr]
          exact hW.ent g i j)
        (by
          simp only [Subalgebra.coe_val] at hr
          simp only [hr]
          exact hU.1.cont i j)
      gen := sxCoreGen hW D' hD'
      cp := cp
      cp_map := hcp1
      cp_cont := hcp2
      cp_red := hcp3
      ψ := ψ
      ψ_map := fun _ _ _ => rfl
      ψ_cont := fun v i => (sxContGr W hW.max (Γ := Φ.Gv v)).2 (ψ v i) (by
        simp only [Subalgebra.coe_val] at hψ
        simp only [ψ, hψ]
        exact hU.1.contψ v i)
      ψ_red := fun v i s => by
        have h := res_map (O := Λ) ((W.A.val).comp (IsScalarTower.toAlgHom Λ (W.gr 0) W.A)) (ψ v i s)
        rw [← h]
        have h2 : ((W.A.val).comp (IsScalarTower.toAlgHom Λ (W.gr 0) W.A)) (ψ v i s) = D.ψ v i s := hψ v i s
        rw [h2]
        exact hU.1.redψ v i s
      genB := sxGenZero hS.ok hU.1 hW D' hD' cp hcp1 ψ (fun _ _ _ => rfl)
      univ := sxNearA hU hW D' hD' }
  obtain ⟨Y⟩ := sxPreOfCore (fun v s hs => (hS.mu v s hs).1) C
  obtain ⟨hres, hlift⟩ := sxSplitRes hS
  obtain ⟨f, -⟩ := Y.univ (ResidueField Λ) _ _ hres hlift
  haveI : Nontrivial Y.A := f.toRingHom.domain_nontrivial
  obtain ⟨Y', hinj⟩ := sxPreImage Y this
  exact ⟨Y'.toSpace hinj (sxPreLine Y')⟩
