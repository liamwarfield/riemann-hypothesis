module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlgebraActionBundleFiltrationStep

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FilteredExactSequenceProjectorBundles
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FilteredExactSequenceProjectorBundles
open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Flat.DegCurve

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegCurve

theorem subDeg_range_shortExact : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V'') (P : V →ₗ[K] V) (P' : V' →ₗ[K] V') (P'' : V'' →ₗ[K] V''), IsBun C L' → ShortExact C L L' L'' f g → (∀ x, P (P x) = P x) → (∀ x, P' (P' x) = P' x) → (∀ x, P'' (P'' x) = P'' x) → (∀ x, f (P x) = P' (f x)) → (∀ y, g (P' y) = P'' (g y)) → IsHom C L' L' P' → subDeg C L' (LinearMap.range P') = subDeg C L (LinearMap.range P) + subDeg C L'' (LinearMap.range P'') := by
  intro K _ C V _ _ _ V' _ _ _ V'' _ _ _ L L' L'' f g P P' P'' hB hSE hP hP' hP'' hfP hgP hHom
  obtain ⟨hinj, hex, hsurj, hL, hL''⟩ := hSE
  have mP : ∀ v ∈ LinearMap.range P, P v = v := by
    intro v hv
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hv
    exact hP u
  have mP' : ∀ v ∈ LinearMap.range P', P' v = v := by
    intro v hv
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hv
    exact hP' u
  have mP'' : ∀ v ∈ LinearMap.range P'', P'' v = v := by
    intro v hv
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hv
    exact hP'' u
  let f₀ : LinearMap.range P →ₗ[K] LinearMap.range P' :=
    LinearMap.codRestrict (LinearMap.range P') (f.domRestrict (LinearMap.range P)) (fun v =>
      LinearMap.mem_range.2 ⟨f v, by
        show P' (f v) = f v
        rw [← hfP, mP _ v.2]⟩)
  let g₀ : LinearMap.range P' →ₗ[K] LinearMap.range P'' :=
    LinearMap.codRestrict (LinearMap.range P'') (g.domRestrict (LinearMap.range P')) (fun v =>
      LinearMap.mem_range.2 ⟨g v, by
        show P'' (g v) = g v
        rw [← hgP, mP' _ v.2]⟩)
  have hSE0 : ShortExact C (sub C L (LinearMap.range P)) (sub C L' (LinearMap.range P'))
      (sub C L'' (LinearMap.range P'')) f₀ g₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x y h
      apply Subtype.ext
      apply hinj
      exact congrArg Subtype.val h
    · intro y
      constructor
      · intro hy
        have hy' : g (y : V') = 0 := congrArg Subtype.val hy
        obtain ⟨x, hx⟩ := (hex (y : V')).1 hy'
        refine ⟨⟨P x, LinearMap.mem_range_self P x⟩, ?_⟩
        apply Subtype.ext
        show f (P x) = (y : V')
        rw [hfP, hx, mP' _ y.2]
      · rintro ⟨x, rfl⟩
        apply Subtype.ext
        show g (f (x : V)) = 0
        exact (hex _).2 ⟨x, rfl⟩
    · intro z
      obtain ⟨y, hy⟩ := hsurj (z : V'')
      refine ⟨⟨P' y, LinearMap.mem_range_self P' y⟩, ?_⟩
      apply Subtype.ext
      show g (P' y) = (z : V'')
      rw [hgP, hy, mP'' _ z.2]
    · intro i x
      show (x : V) ∈ L i ↔ f (x : V) ∈ L' i
      exact hL i x
    · intro i z
      constructor
      · intro hz
        obtain ⟨y, hyL, hy⟩ := (hL'' i z).1 hz
        refine ⟨⟨P' y, LinearMap.mem_range_self P' y⟩, hHom i y hyL, ?_⟩
        apply Subtype.ext
        show g (P' y) = (z : V'')
        rw [hgP, hy, mP'' _ z.2]
      · rintro ⟨y, hyL, rfl⟩
        exact (hL'' i _).2 ⟨y, hyL, rfl⟩
  have hBW : IsBun C (sub C L' (LinearMap.range P')) :=
    (SubQuot.isBun_sub_quot K C V' L' (LinearMap.range P') hB).1
  exact (deg_shortExact K C (LinearMap.range P) (LinearMap.range P') (LinearMap.range P'')
    (sub C L (LinearMap.range P)) (sub C L' (LinearMap.range P')) (sub C L'' (LinearMap.range P''))
    f₀ g₀ hBW hSE0).2.2

end GlobalTheory.CompanionTheory.Ar.Flat.DegCurve
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FilteredExactSequenceProjectorBundlesStatement
open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Flat.DegCurve
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtered_exact_sequence_projector_bundles : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V'') (P : V →ₗ[K] V) (P' : V' →ₗ[K] V') (P'' : V'' →ₗ[K] V''), IsBun C L' → ShortExact C L L' L'' f g → (∀ x, P (P x) = P x) → (∀ x, P' (P' x) = P' x) → (∀ x, P'' (P'' x) = P'' x) → (∀ x, f (P x) = P' (f x)) → (∀ y, g (P' y) = P'' (g y)) → IsHom C L' L' P' → subDeg C L' (LinearMap.range P') = subDeg C L (LinearMap.range P) + subDeg C L'' (LinearMap.range P'') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.subDeg_range_shortExact | exact GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.subDeg_range_shortExact | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.subDeg_range_shortExact <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModuleBasisLatticeBundleFree
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModuleBasisLatticeBundleFree
noncomputable section

open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegCurve

open GlobalTheory.CompanionTheory.Ar.Crv

private theorem valuation_natCast_le_one_algebra {K : Type} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ)))
    (n : ℕ) : v (n : K) ≤ 1 := by
  induction n with
  | zero => simp
  | succ m ih =>
    push_cast
    exact (v.map_add _ _).trans (max_le ih (le_of_eq v.map_one))

theorem v_intCast_le_one {K : Type} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ)))
    (n : ℤ) : v (n : K) ≤ 1 := by
  cases n with
  | ofNat m =>
    rw [Int.ofNat_eq_natCast, Int.cast_natCast]
    exact valuation_natCast_le_one_algebra v m
  | negSucc m =>
    rw [Int.cast_negSucc, Valuation.map_neg]
    exact_mod_cast valuation_natCast_le_one_algebra v (m + 1)

theorem freeAt_of_basis_lattice (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (O ι k : Type) [CommRing O]
    [Fintype ι] [Field k] [Algebra k K] (b : Module.Basis ι ℤ O) (ρ : O →+* Module.End K V)
    (r : ℕ) (i : C.I) (hL : IsBun C L) (hk : ∀ c : k, C.v i (algebraMap k K c) ≤ 1)
    (h : ∃ x : Fin r → V, LinearIndependent K (fun q : Fin r × ι => ρ (b q.2) (x q.1)) ∧
      ∀ y, y ∈ L i ↔ ∃ c : Fin r × ι → K, (∀ q, C.v i (c q) ≤ 1) ∧
        y = ∑ q, c q • ρ (b q.2) (x q.1)) :
    FreeAt C k (act k ρ) L r i := by
  obtain ⟨x, hli, hL'⟩ := h
  set e : Fin r × ι → V := fun q => ρ (b q.2) (x q.1) with he
  obtain ⟨b0, hb0⟩ := hL.1 i
  have hb0 : ∀ z : V, z ∈ L i ↔ ∀ q, C.v i (b0.repr z q) ≤ 1 := hb0
  have hmemL : ∀ y : V, y ∈ L i → y ∈ Submodule.span K (Set.range e) := by
    intro y hy
    obtain ⟨c, -, rfl⟩ := (hL' y).1 hy
    exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
  have hspan : ⊤ ≤ Submodule.span K (Set.range e) := by
    rw [← b0.span_eq]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    refine hmemL _ ((hb0 _).2 fun q => ?_)
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact (map_one _).le
    · rw [map_zero]
      exact zero_le_one
  let B : Module.Basis (Fin r × ι) K V := Module.Basis.mk hli hspan
  have hBe : ∀ q, B q = e q := fun q => Module.Basis.mk_apply hli hspan q
  have key : ∀ (c : Fin r × ι → K) (q : Fin r × ι), B.coord q (∑ q', c q' • e q') = c q := by
    intro c q
    have hc : ∑ q', c q' • e q' = B.equivFun.symm c := by
      rw [Module.Basis.equivFun_symm_apply]
      simp only [hBe]
    rw [hc, Module.Basis.coord_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have key' : ∀ (c : Fin r × ι → K) (q : Fin r × ι),
      B.coord q (∑ q', c q' • ρ (b q'.2) (x q'.1)) = c q := key
  have hrep : ∀ (o : O) (s' : Fin r), ρ o (x s') =
      ∑ q : Fin r × ι, (if q.1 = s' then ((b.repr o q.2 : ℤ) : K) else 0) • e q := by
    intro o s'
    rw [Fintype.sum_prod_type, Finset.sum_eq_single s' (fun s _ hs => by simp [hs])
      (fun h => absurd (Finset.mem_univ _) h)]
    conv_lhs => rw [← b.sum_repr o]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only
    rw [if_pos rfl, map_zsmul, Int.cast_smul_eq_zsmul]
    rfl
  refine ⟨x, fun l s => ∑ j, algebraMap k K (l (1 ⊗ₜ[ℤ] b j)) • B.coord (s, j), ?_, ?_, ?_, ?_⟩
  · intro s
    rw [hL']
    refine ⟨fun q => if q.1 = s then ((b.repr 1 q.2 : ℤ) : K) else 0, fun q => ?_, ?_⟩
    · dsimp only
      split_ifs
      · exact v_intCast_le_one _ _
      · rw [map_zero]
        exact zero_le_one
    · exact (LinearMap.congr_fun (map_one ρ) (x s)).symm.trans (hrep 1 s)
  · intro l s s' a
    dsimp only
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul c o =>
      rw [act_tmul, LinearMap.smul_apply, map_smul, hrep o s']
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, key, smul_eq_mul]
      split_ifs with hss
      · have h1 : l (c ⊗ₜ[ℤ] o) = c * l ((1 : k) ⊗ₜ[ℤ] o) := by
          rw [← smul_eq_mul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        have h2 : l ((1 : k) ⊗ₜ[ℤ] o) = ∑ j, b.repr o j • l ((1 : k) ⊗ₜ[ℤ] b j) := by
          conv_lhs => rw [← b.sum_repr o]
          set_option synthInstance.maxHeartbeats 100000 in
            rw [TensorProduct.tmul_sum, map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [TensorProduct.tmul_smul, map_zsmul]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [h1, h2, map_mul, map_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_zsmul, zsmul_eq_mul]
        ring
      · simp [hss]
    | add a a' ha ha' =>
      rw [map_add (f := _), LinearMap.add_apply, map_add (f := _), ha, ha']
      split_ifs <;> simp [map_add (f := _)]
  · intro l s y hy
    obtain ⟨c, hc, rfl⟩ := (hL' y).1 hy
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, key', smul_eq_mul]
    refine Valuation.map_sum_le _ fun j _ => ?_
    rw [map_mul]
    exact mul_le_one' (hk _) (hc _)
  · intro y
    have hy : y ∈ Submodule.span K (Set.range e) := hspan Submodule.mem_top
    refine Submodule.span_mono ?_ hy
    rintro _ ⟨q, rfl⟩
    exact ⟨(1 ⊗ₜ[ℤ] b q.2, q.1), by
      show (act k ρ) ((1 : k) ⊗ₜ[ℤ] b q.2) (x q.1) = e q
      rw [act_tmul, map_one, one_smul]⟩

end GlobalTheory.CompanionTheory.Ar.Flat.DegCurve
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModuleBasisLatticeBundleFreeStatement
open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Flat.DegCurve
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.module_basis_lattice_bundle_free : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (O ι k : Type) [CommRing O] [Fintype ι] [Field k] [Algebra k K] (b : Module.Basis ι ℤ O) (ρ : O →+* Module.End K V) (r : ℕ) (i : C.I), IsBun C L → (∀ c : k, C.v i (algebraMap k K c) ≤ 1) → (∃ x : Fin r → V, LinearIndependent K (fun q : Fin r × ι => ρ (b q.2) (x q.1)) ∧ ∀ y, y ∈ L i ↔ ∃ c : Fin r × ι → K, (∀ q, C.v i (c q) ≤ 1) ∧ y = ∑ q, c q • ρ (b q.2) (x q.1)) → FreeAt C k (act k ρ) L r i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.freeAt_of_basis_lattice | exact GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.freeAt_of_basis_lattice | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.freeAt_of_basis_lattice <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IdealDescendingOneDimQuotient
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IdealDescendingOneDimQuotient
open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Flat.DegCurve

namespace GlobalTheory.CompanionTheory.Ar.Flat.StepIdeal

theorem exists_colength_one (k A : Type) [Field k] [CommRing A] [Algebra k A] [Finite A]
    (χ : A →ₐ[k] k) (e : A) (J : Ideal A) (he : IsIdempotentElem e) (hχ : χ e = 1)
    (hnil : ∀ t ∈ RingHom.ker χ, IsNilpotent (e * t)) (hJe : J ≤ Ideal.span {e}) (hJ0 : J ≠ ⊥) :
    ∃ (J₁ : Ideal A) (t : A) (l : A →ₗ[k] k), J₁ < J ∧ t ∈ J ∧
      (∀ a ∈ J, ∃ c : k, a - algebraMap k A c * t ∈ J₁) ∧
      (∀ a ∈ RingHom.ker χ, a * t ∈ J₁) ∧ (∀ a ∈ J₁, l a = 0) ∧ l t = 1 := by
  classical
  set m := RingHom.ker χ with hm
  have hfix : ∀ a ∈ J, e * a = a := by
    intro a ha
    obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.mp (hJe ha)
    calc e * (x * e) = x * (e * e) := by ring
      _ = x * e := by rw [he.eq]
  have hJ : ¬ J ≤ m * J := by
    intro hle
    have hfg : (J : Submodule A A).FG := IsNoetherian.noetherian J
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m
      (J : Submodule A A) hfg (by rwa [Ideal.smul_eq_mul])
    apply hJ0
    rw [eq_bot_iff]
    intro a ha
    have hs : 1 - r ∈ m := by
      have := m.neg_mem hr
      rwa [neg_sub] at this
    have hsa : (1 - r) * a = a := by
      have h0 : r * a = 0 := by simpa [smul_eq_mul] using hr0 a ha
      rw [sub_mul, one_mul, h0, sub_zero]
    have hpow : ∀ n : ℕ, (e * (1 - r)) ^ n * a = a := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc (e * (1 - r)) ^ (n + 1) * a = (e * (1 - r)) ^ n * (e * ((1 - r) * a)) := by ring
          _ = a := by rw [hsa, hfix a ha, ih]
    obtain ⟨n, hn⟩ := hnil (1 - r) hs
    rw [Ideal.mem_bot, ← hpow n, hn, zero_mul]
  obtain ⟨t, htJ, htW⟩ := SetLike.not_le_iff_exists.mp hJ
  let W : Submodule k A := (m * J).restrictScalars k
  have hq : W.mkQ t ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact htW
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k (A ⧸ W), φ (W.mkQ t) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hq ((Module.forall_dual_apply_eq_zero_iff k _).mp hcon)
  set l : A →ₗ[k] k := (φ (W.mkQ t))⁻¹ • (φ ∘ₗ W.mkQ) with hl
  have hlt : l t = 1 := by
    rw [hl, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, inv_mul_cancel₀ hφ]
  have hlW : ∀ a ∈ m * J, l a = 0 := by
    intro a ha
    have : W.mkQ a = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ha
    rw [hl, LinearMap.smul_apply, LinearMap.comp_apply, this, map_zero, smul_zero]
  have hdec : ∀ r : A, r - algebraMap k A (χ r) ∈ m := by
    intro r
    rw [hm, RingHom.mem_ker]
    simp
  let J₁ : Ideal A :=
    { carrier := {a | a ∈ J ∧ l a = 0}
      add_mem' := fun {a b} ha hb => ⟨J.add_mem ha.1 hb.1, by rw [map_add (f := _), ha.2, hb.2, add_zero]⟩
      zero_mem' := ⟨J.zero_mem, map_zero l⟩
      smul_mem' := fun c a ha => by
        refine ⟨J.mul_mem_left c ha.1, ?_⟩
        have hsplit : c * a = χ c • a + (c - algebraMap k A (χ c)) * a := by
          rw [Algebra.smul_def]
          ring
        change l (c * a) = 0
        rw [hsplit, map_add (f := _), map_smul, ha.2, smul_zero, zero_add]
        exact hlW _ (Ideal.mul_mem_mul (hdec c) ha.1) }
  have hmemJ₁ : ∀ a, a ∈ J₁ ↔ a ∈ J ∧ l a = 0 := fun a => Iff.rfl
  refine ⟨J₁, t, l, ?_, htJ, ?_, ?_, ?_, hlt⟩
  · rw [SetLike.lt_iff_le_and_exists]
    refine ⟨fun a ha => ((hmemJ₁ a).mp ha).1, t, htJ, fun h => ?_⟩
    have := ((hmemJ₁ t).mp h).2
    rw [hlt] at this
    exact one_ne_zero this
  · intro a ha
    refine ⟨l a, (hmemJ₁ _).mpr ⟨J.sub_mem ha (J.mul_mem_left _ htJ), ?_⟩⟩
    rw [← Algebra.smul_def, map_sub, map_smul, hlt, smul_eq_mul, mul_one, sub_self]
  · intro a ha
    exact (hmemJ₁ _).mpr ⟨J.mul_mem_left a htJ, hlW _ (Ideal.mul_mem_mul ha htJ)⟩
  · intro a ha
    exact ((hmemJ₁ a).mp ha).2

end GlobalTheory.CompanionTheory.Ar.Flat.StepIdeal
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IdealDescendingOneDimQuotientStatement
open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Flat.DegCurve
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_descending_one_dim_quotient : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Finite A] (χ : A →ₐ[k] k) (e : A) (J : Ideal A), IsIdempotentElem e → χ e = 1 → (∀ t ∈ RingHom.ker χ, IsNilpotent (e * t)) → J ≤ Ideal.span {e} → J ≠ ⊥ → ∃ (J₁ : Ideal A) (t : A) (l : A →ₗ[k] k), J₁ < J ∧ t ∈ J ∧ (∀ a ∈ J, ∃ c : k, a - algebraMap k A c * t ∈ J₁) ∧ (∀ a ∈ RingHom.ker χ, a * t ∈ J₁) ∧ (∀ a ∈ J₁, l a = 0) ∧ l t = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.StepIdeal.exists_colength_one | exact GlobalTheory.CompanionTheory.Ar.Flat.StepIdeal.exists_colength_one | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.StepIdeal.exists_colength_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SplitHermitianGeneratorsExist
noncomputable section
open scoped TensorProduct
namespace GlobalTheory.CompanionTheory.Ar.Flat.DegCurve
open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Crv.SplitProj

theorem exists_idem (A : Type) [CommRing A] [Finite A] (m : Ideal A) :
    ∃ e : A, IsIdempotentElem e ∧ 1 - e ∈ m ∧ ∀ t ∈ m, IsNilpotent (e * t) := by
  classical
  haveI := Fintype.ofFinite A
  have hpow : ∀ t : A, ∃ n : ℕ, 0 < n ∧ IsIdempotentElem (t ^ n) := fun t => by
    obtain ⟨i, j, hij, h⟩ : ∃ i j : ℕ, i < j ∧ t ^ i = t ^ j := by
      obtain ⟨i, j, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => t ^ n)
      rcases lt_or_gt_of_ne hne with hl | hl
      · exact ⟨i, j, hl, h⟩
      · exact ⟨j, i, hl, h.symm⟩

    set d := j - i with hd
    have hd0 : 0 < d := by omega
    have hper : ∀ n a : ℕ, i ≤ a → t ^ (a + n * d) = t ^ a := by
      intro n a ha
      have h1 : ∀ a : ℕ, i ≤ a → t ^ (a + d) = t ^ a := by
        intro a ha
        obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
        have : i + b + d = j + b := by omega
        rw [this, pow_add, pow_add, h]
      induction n with
      | zero => simp
      | succ n ih =>
        rw [show a + (n + 1) * d = (a + n * d) + d by ring, h1 _ (by omega), ih]
    refine ⟨(i + 1) * d, by positivity, ?_⟩
    unfold IsIdempotentElem
    rw [← pow_add]
    exact hper _ _ (by nlinarith)
  choose N hN0 hN using hpow
  let S : Finset A := Finset.univ.filter (· ∈ m)
  refine ⟨∏ t ∈ S, (1 - t ^ N t), ?_, ?_, ?_⟩
  · exact Finset.prod_induction _ IsIdempotentElem (fun a b ha hb => ha.mul hb)
      IsIdempotentElem.one fun t _ => (hN t).one_sub
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_prod, sub_eq_zero]
    refine (Finset.prod_eq_one fun t ht => ?_).symm
    have htm : t ∈ m := (Finset.mem_filter.1 ht).2
    have : t ^ N t ∈ m := Ideal.pow_mem_of_mem m htm _ (hN0 t)
    rw [map_sub, map_one, Ideal.Quotient.eq_zero_iff_mem.2 this, sub_zero]
  · intro t ht
    have hS : t ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, ht⟩
    refine ⟨N t, ?_⟩
    rw [mul_pow, ← Finset.mul_prod_erase S _ hS, mul_pow, mul_comm, ← mul_assoc]
    have h0 : t ^ N t * (1 - t ^ N t) = 0 := by
      rw [mul_sub, mul_one, (hN t).eq, sub_self]
    have h1 : t ^ N t * (1 - t ^ N t) ^ N t = 0 := by
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (hN0 t).ne'
      rw [hn, pow_succ' (1 - t ^ _), ← hn, ← mul_assoc, h0, zero_mul]
    rw [h1, zero_mul]

theorem frobVec_mulVec {K : Type} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] {d : ℕ}
    (M : Matrix (Fin d) (Fin d) K) (u : Fin d → K) :
    frobVec p (M.mulVec u) = (M.map (· ^ p)).mulVec (frobVec p u) := by
  funext j
  simp [frobVec, Matrix.mulVec, dotProduct, sum_pow_char, mul_pow]

theorem frobSub_range (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ)
    (M : Matrix (Fin d) (Fin d) K) :
    frobSub p (LinearMap.range (Matrix.toLin' M)) =
      LinearMap.range (Matrix.toLin' (M.map (· ^ p))) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨frobVec p u, by simp [Matrix.toLin'_apply, frobVec_mulVec]⟩
  · rintro _ ⟨u, rfl⟩
    have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
    have hs : ∀ j : Fin d, frobVec p (Pi.single j (1 : K)) = Pi.single j 1 := fun j => by
      funext r
      by_cases h : r = j
      · subst h; simp [frobVec]
      · simp [frobVec, h, hp]
    have hu : u = ∑ j, u j • (Pi.single j (1 : K) : Fin d → K) := by
      funext r; simp [Finset.sum_apply, Pi.single_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hu, map_sum]
    refine sum_mem fun j _ => ?_
    rw [map_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨M.mulVec (Pi.single j 1), ⟨_, rfl⟩, ?_⟩)
    rw [frobVec_mulVec, hs, Matrix.toLin'_apply]

theorem twist_act (K k O : Type) [Field K] [Field k] [Algebra k K] [CommRing O] (p : ℕ)
    [Fact p.Prime] [CharP K p] [CharP k p] (d : ℕ) (ρ : O →+* Matrix (Fin d) (Fin d) K)
    (x : TensorProduct ℤ k O) :
    act k (toEnd (twist p ρ)) (frobT k O p x) =
      Matrix.toLin' ((LinearMap.toMatrix' (act k (toEnd ρ) x)).map (· ^ p)) := by
  have hF : ∀ M : Matrix (Fin d) (Fin d) K, M.map (· ^ p) = (frobenius K p).mapMatrix M :=
    fun M => by ext; simp [frobenius_def]
  have hend : ∀ (ρ' : O →+* Matrix (Fin d) (Fin d) K) a, toEnd ρ' a = Matrix.toLin' (ρ' a) :=
    fun _ _ => rfl
  simp only [hF]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c a =>
    have h1 : LinearMap.toMatrix' (algebraMap k K c • Matrix.toLin' (ρ a)) =
        algebraMap k K c • ρ a := by
      rw [map_smul, LinearMap.toMatrix'_toLin']
    rw [frobT_tmul, act_tmul, act_tmul, hend, hend, map_pow, twist_apply, hF, h1, ← map_smul]
    congr 1
    ext r s
    simp only [Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, smul_eq_mul,
      frobenius_def, mul_pow]
  | add u w hu hw => simp only [map_add (f := _), hu, hw]

theorem idealV_ker (K k O V : Type) [Field K] [Field k] [Algebra k K] [CommRing O]
    [AddCommGroup V] [Module K V] (ρ : O →+* Module.End K V) (χ : O →+* k) :
    idealV (act k ρ) (RingHom.ker (chiT χ)) =
      ⨆ a : O, LinearMap.range (ρ a - algebraMap k K (χ a) • LinearMap.id) := by
  set W := ⨆ a : O, LinearMap.range (ρ a - algebraMap k K (χ a) • LinearMap.id) with hW
  have hmem : ∀ (a : O) (v : V), ρ a v - algebraMap k K (χ a) • v ∈ W := fun a v =>
    Submodule.mem_iSup_of_mem a ⟨v, by simp⟩
  have h : ∀ (x : TensorProduct ℤ k O) (v : V),
      act k ρ x v - algebraMap k K (chiT χ x) • v ∈ W := by
    intro x v
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c a =>
      rw [act_tmul, chiT_tmul, map_mul, mul_smul, LinearMap.smul_apply, ← smul_sub]
      exact Submodule.smul_mem _ _ (hmem a v)
    | add u w hu hw =>
      have := add_mem hu hw
      simp only [map_add (f := _), LinearMap.add_apply, add_smul]
      convert this using 1
      abel
  refine le_antisymm (iSup_le fun a => ?_) (iSup_le fun a => ?_)
  · rintro _ ⟨v, rfl⟩
    have h0 : chiT χ (a : TensorProduct ℤ k O) = 0 := a.2
    simpa [h0] using h a v
  · rintro _ ⟨v, rfl⟩
    have ht : (1 : k) ⊗ₜ[ℤ] a - (χ a) ⊗ₜ[ℤ] (1 : O) ∈ RingHom.ker (chiT χ) := by
      rw [RingHom.mem_ker, map_sub, chiT_tmul, chiT_tmul]; simp
    refine Submodule.mem_iSup_of_mem ⟨_, ht⟩ ⟨v, ?_⟩
    simp [act_tmul]

theorem exists_finite_subfield (K O : Type) [Field K] [CommRing O] [IsDomain O]
    [Module.Free ℤ O] [Module.Finite ℤ O] [CharZero O] (p : ℕ) [Fact p.Prime] [CharP K p] (χ : O →+* K) :
    ∃ k : Subfield K, Finite k ∧ ∀ a, χ a ∈ k := by
  have hker : RingHom.ker χ ≠ ⊥ := by
    intro h
    have hp : (p : O) ∈ RingHom.ker χ := by
      rw [RingHom.mem_ker, map_natCast]; exact CharP.cast_eq_zero K p
    rw [h, Ideal.mem_bot] at hp
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hp)
  haveI : Finite (O ⧸ RingHom.ker χ) := Ideal.finiteQuotientOfFreeOfNeBot _ hker
  haveI : Finite χ.range := Finite.of_equiv _ (RingHom.quotientKerEquivRange χ).toEquiv
  have hinv : ∀ x ∈ χ.range, x⁻¹ ∈ χ.range := by
    intro x hx
    by_cases h0 : x = 0
    · simp [h0, zero_mem]
    have hinj : Function.Injective (fun y : χ.range => (⟨x, hx⟩ : χ.range) * y) := by
      intro y z h
      have : x * (y : K) = x * z := congrArg Subtype.val h
      exact Subtype.ext (mul_left_cancel₀ h0 this)
    obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.1 hinj) 1
    have : x * (y : K) = 1 := congrArg Subtype.val hy
    rw [inv_eq_of_mul_eq_one_right this]
    exact y.2
  refine ⟨{ χ.range with inv_mem' := hinv }, ?_, fun a => ⟨a, rfl⟩⟩
  exact (inferInstance : Finite χ.range)

theorem act_isHom {K : Type} [Field K] (C : ACurve K) {V : Type} [AddCommGroup V] [Module K V]
    {L : C.I → AddSubgroup V} (hL : IsBun C L) {O k : Type} [CommRing O] [Field k] [Algebra k K]
    (hk : ∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) (ρ : O →+* Module.End K V)
    (hρ : ∀ a, IsHom C L L (ρ a)) (x : TensorProduct ℤ k O) : IsHom C L L (act k ρ x) := by
  induction x using TensorProduct.induction_on with
  | zero => intro i y _; simpa using zero_mem _
  | tmul c a =>
    intro i y hy
    rw [act_tmul]
    exact smul_mem_of_isBun C hL i (hk i c) (hρ a i y hy)
  | add u w hu hw =>
    intro i y hy
    rw [map_add (f := _)]
    exact add_mem (hu i y hy) (hw i y hy)

theorem act_comm {K : Type} [Field K] {V V' : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] {O k : Type} [CommRing O] [Field k] [Algebra k K]
    (ρ : O →+* Module.End K V) (ρ' : O →+* Module.End K V') (f : V →ₗ[K] V')
    (h : ∀ a v, f (ρ a v) = ρ' a (f v)) (x : TensorProduct ℤ k O) (v : V) :
    f (act k ρ x v) = act k ρ' x (f v) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c a => simp [act_tmul, h]
  | add u w hu hw => simp [hu, hw]

theorem idem_apply {A K V : Type} [Field K] [CommRing A] [AddCommGroup V] [Module K V]
    (τ : A →+* Module.End K V) {e : A} (he : IsIdempotentElem e) (x : V) :
    τ e (τ e x) = τ e x := by
  have : τ e * τ e = τ e := by rw [← map_mul, he.eq]
  exact congrArg (fun f : Module.End K V => f x) this

section Data

variable {K : Type} [Field K] {C : ACurve K} {p : ℕ} [Fact p.Prime] [CharP K p] {O : Type}
  [CommRing O] [StarRing O] {d : ℕ} (D : ConjData C p O d) (k : Type) [Field k] [Algebra k K]

theorem hodge_part (hk : ∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) (x : TensorProduct ℤ k O)
    (hx : IsIdempotentElem x) :
    subDeg C D.H (LinearMap.range (act k D.ρH x)) =
      subDeg C (dotDual C D.lie) (LinearMap.range (act k (toEnd (conjT D.ρ)) x)) +
      subDeg C D.lie (LinearMap.range (act k (toEnd D.ρ) x)) := by
  refine GlobalTheory.T.filtered_exact_sequence_projector_bundles K C _ _ _ _ _ _ _ _ _ _ _ D.H_bun D.hodge (idem_apply _ hx) (idem_apply _ hx)
    (idem_apply _ hx) (fun y => ?_) (fun y => ?_) (act_isHom C D.H_bun hk _ D.ρH_hom x)
  · refine (act_comm (toEnd (conjT D.ρ)) D.ρH (LinearMap.inr K _ _) (fun a v => ?_) x y)
    simp [D.ρH_inr, toEnd_apply, conjT_apply]
  · refine (act_comm D.ρH (toEnd D.ρ) (LinearMap.fst K _ _) (fun a v => ?_) x y)
    simp [D.ρH_fst, toEnd_apply]

theorem conj_part (hk : ∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) (x : TensorProduct ℤ k O)
    (hx : IsIdempotentElem x) :
    subDeg C D.H (LinearMap.range (act k D.ρH x)) =
      subDeg C (frobLat C p D.lie) (LinearMap.range (act k (toEnd (twist p D.ρ)) x)) +
      subDeg C (frobLat C p (dotDual C D.lie))
        (LinearMap.range (act k (toEnd (twist p (conjT D.ρ))) x)) := by
  refine GlobalTheory.T.filtered_exact_sequence_projector_bundles K C _ _ _ _ _ _ _ _ _ _ _ D.H_bun D.conj (idem_apply _ hx) (idem_apply _ hx)
    (idem_apply _ hx) (fun y => ?_) (fun y => ?_) (act_isHom C D.H_bun hk _ D.ρH_hom x)
  · refine (act_comm (toEnd (twist p D.ρ)) D.ρH D.α (fun a v => ?_) x y)
    rw [toEnd_apply, twist_apply, D.α_act]
  · refine (act_comm D.ρH (toEnd (twist p (conjT D.ρ))) D.β (fun a v => ?_) x y)
    rw [D.β_act, toEnd_apply, twist_apply, conjT_apply]

theorem range_twist [CharP k p] {n : ℕ} (ρ : O →+* Matrix (Fin n) (Fin n) K)
    (x : TensorProduct ℤ k O) :
    LinearMap.range (act k (toEnd (twist p ρ)) (frobT k O p x)) =
      frobSub p (LinearMap.range (act k (toEnd ρ) x)) := by
  rw [twist_act K k O p n ρ x, ← frobSub_range K p n, Matrix.toLin'_toMatrix']

theorem step [CharP k p] (hk : ∀ i (c : k), C.v i (algebraMap k K c) ≤ 1)
    (x : TensorProduct ℤ k O) (hx : IsIdempotentElem x) :
    subDeg C D.H (LinearMap.range (act k D.ρH (frobT k O p x))) =
      p * subDeg C D.H (LinearMap.range (act k D.ρH x)) := by
  have hx' : IsIdempotentElem (frobT k O p x) := by
    unfold IsIdempotentElem; rw [← map_mul, hx.eq]
  rw [conj_part D k hk _ hx', range_twist k, range_twist k, hodge_part D k hk x hx,
    GlobalTheory.CompanionTheory.Ar.Crv.SubFrob.subDeg_frob K C p d _ _ D.lie_bun,
    GlobalTheory.CompanionTheory.Ar.Crv.SubFrob.subDeg_frob K C p d _ _
      (GlobalTheory.CompanionTheory.Ar.Crv.deg_shortExact K C _ _ _ _ _ _ _ _ D.H_bun D.hodge).1, mul_add, add_comm]

theorem frobT_iterate [CharP k p] (n : ℕ) (hn : ∀ c : k, c ^ p ^ n = c)
    (x : TensorProduct ℤ k O) : (frobT k O p)^[n] x = x := by
  have h : ∀ (j : ℕ) (c : k) (a : O), (frobT k O p)^[j] (c ⊗ₜ[ℤ] a) = (c ^ p ^ j) ⊗ₜ[ℤ] a := by
    intro j c a
    induction j with
    | zero => simp
    | succ j ih => rw [Function.iterate_succ_apply', ih, frobT_tmul, pow_succ, pow_mul]
  induction x using TensorProduct.induction_on with
  | zero => exact iterate_map_zero (frobT k O p) n
  | tmul c a => rw [h, hn]
  | add u w hu hw => rw [iterate_map_add (frobT k O p) n, hu, hw]

theorem vanish [Finite k] [CharP k p] (hk : ∀ i (c : k), C.v i (algebraMap k K c) ≤ 1)
    (x : TensorProduct ℤ k O) (hx : IsIdempotentElem x) :
    subDeg C D.H (LinearMap.range (act k D.ρH x)) = 0 := by
  haveI := Fintype.ofFinite k
  obtain ⟨n, hp, hc⟩ := FiniteField.card k p
  have hn : ∀ c : k, c ^ p ^ (n : ℕ) = c := fun c => by rw [← hc]; exact FiniteField.pow_card c
  have key : ∀ j : ℕ, IsIdempotentElem ((frobT k O p)^[j] x) ∧
      subDeg C D.H (LinearMap.range (act k D.ρH ((frobT k O p)^[j] x))) =
        (p : ℤ) ^ j * subDeg C D.H (LinearMap.range (act k D.ρH x)) := by
    intro j
    induction j with
    | zero => simpa using hx
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      refine ⟨?_, ?_⟩
      · unfold IsIdempotentElem; rw [← map_mul, ih.1.eq]
      · rw [step D k hk _ ih.1, ih.2, pow_succ]; ring
  have h := (key n).2
  rw [frobT_iterate k (n : ℕ) hn x] at h
  have h1 : (1 : ℤ) < (p : ℤ) ^ (n : ℕ) :=
    one_lt_pow₀ (by exact_mod_cast hp.one_lt) n.ne_zero
  by_contra h0
  have : (p : ℤ) ^ (n : ℕ) = 1 := by
    have := mul_right_cancel₀ h0 (show (p : ℤ) ^ (n : ℕ) * _ = 1 * _ by rw [one_mul]; exact h.symm)
    exact this
  omega

end Data

section Count

variable {K : Type} [Field K] (C : ACurve K) {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem subDeg_bot (L : C.I → AddSubgroup V) : subDeg C L ⊥ = 0 := by
  haveI : IsEmpty (Fin (Module.finrank K (⊥ : Submodule K V))) := by
    rw [finrank_bot]; infer_instance
  simp [subDeg, deg, Module.Basis.det_apply, Matrix.det_isEmpty]

theorem idealV_bot {A : Type} [CommRing A] (τ : A →+* Module.End K V) : idealV τ ⊥ = ⊥ := by
  refine iSup_eq_bot.2 fun a => ?_
  have : (a : A) = 0 := a.2
  simp [this]

theorem idealV_span {A : Type} [CommRing A] (τ : A →+* Module.End K V) (e : A) :
    idealV τ (Ideal.span {e}) = LinearMap.range (τ e) := by
  refine le_antisymm (iSup_le fun a => ?_) ?_
  · rintro _ ⟨v, rfl⟩
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 a.2
    refine ⟨τ b v, ?_⟩
    rw [← hb, mul_comm, map_mul]; rfl
  · exact le_iSup (fun a : (Ideal.span {e} : Ideal A) => LinearMap.range (τ a))
      ⟨e, Ideal.mem_span_singleton_self e⟩

theorem deg_count (L : C.I → AddSubgroup V) (k A : Type) [Field k] [Algebra k K] [CommRing A]
    [Algebra k A] [Finite A] (τ : A →+* Module.End K V) (r : ℕ) (χ : A →ₐ[k] k) (e : A)
    (hL : IsBun C L) (hτ : ∀ a, IsHom C L L (τ a))
    (hτk : ∀ (c : k) (x : V), τ (algebraMap k A c) x = algebraMap k K c • x)
    (hk : ∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) (hfree : ∀ i, FreeAt C k τ L r i)
    (he : IsIdempotentElem e) (h1 : χ e = 1)
    (hnil : ∀ t ∈ RingHom.ker χ, IsNilpotent (e * t)) :
    ∃ n : ℕ, 0 < n ∧ subDeg C L (LinearMap.range (τ e)) =
      n * deg C (quot C L (idealV τ (RingHom.ker χ))) := by
  haveI : Finite (Ideal A) :=
    Finite.of_injective (fun J : Ideal A => (J : Set A)) SetLike.coe_injective
  have claim : ∀ J : Ideal A, J ≤ Ideal.span {e} → ∃ n : ℕ,
      subDeg C L (idealV τ J) = n * deg C (quot C L (idealV τ (RingHom.ker χ))) ∧
        (J ≠ ⊥ → 0 < n) := by
    intro J
    induction J using WellFoundedLT.induction with
    | ind J ih =>
      intro hJ
      by_cases h0 : J = ⊥
      · subst h0
        exact ⟨0, by rw [idealV_bot, subDeg_bot]; simp, fun h => absurd rfl h⟩
      · obtain ⟨J₁, t, l, hlt, ht, hJt, hm, hl0, hl1⟩ :=
          GlobalTheory.T.ideal_descending_one_dim_quotient k A χ e J he h1 hnil hJ h0
        obtain ⟨n, hn, -⟩ := ih J₁ hlt (hlt.le.trans hJ)
        refine ⟨n + 1, ?_, fun _ => Nat.succ_pos n⟩
        rw [GlobalTheory.T.algebra_action_bundle_filtration_step K C V L k A τ r χ J₁ J t l hL hτ hτk hk hfree hlt.le ht hJt hm hl0 hl1, hn]
        push_cast; ring
  have he0 : Ideal.span {e} ≠ ⊥ := by
    intro h
    have : e = 0 := Ideal.span_singleton_eq_bot.1 h
    rw [this, map_zero] at h1
    exact zero_ne_one h1
  obtain ⟨n, hn, hpos⟩ := claim _ le_rfl
  exact ⟨n, hpos he0, by rw [← idealV_span, hn]⟩

end Count

theorem v_le_one_of_finite {K : Type} [Field K] (C : ACurve K) (k : Type) [Field k] [Finite k]
    [Algebra k K] (i : C.I) (c : k) : C.v i (algebraMap k K c) ≤ 1 := by
  by_cases h : c = 0
  · simp [h]
  obtain ⟨n, hn, hc⟩ := isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_finite (Units.mk0 c h))
  have h1 : c ^ n = 1 := by simpa using congrArg Units.val hc
  have h2 : C.v i (algebraMap k K c) ^ n = 1 := by rw [← map_pow, ← map_pow, h1]; simp
  exact (pow_eq_one_iff_of_nonneg (zero_le') hn.ne').1 h2 |>.le


open NumberField in
theorem deg_quot_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (d r : ℕ) (D : ConjData C p (𝓞 E) d) (χ : 𝓞 E →+* K), (∀ a : 𝓞 E, ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom K)).Splits) → (∀ i, ∃ x : Fin r → (Fin d → K) × (Fin d → K), LinearIndependent K (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => D.ρH (RingOfIntegers.basis E q.2) (x q.1)) ∧ ∀ y, y ∈ D.H i ↔ ∃ c : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) → K, (∀ q, C.v i (c q) ≤ 1) ∧ y = ∑ q, c q • D.ρH (RingOfIntegers.basis E q.2) (x q.1)) → deg C (quot C D.H (⨆ a : 𝓞 E, LinearMap.range (D.ρH a - χ a • LinearMap.id))) = 0 := by
  intro E _ _ _ K _ C p _ _ d r D χ _ hfr
  obtain ⟨k, hfin, hχ⟩ := exists_finite_subfield K (𝓞 E) p χ
  haveI : CharP k p := (RingHom.charP_iff (algebraMap k K) (algebraMap k K).injective p).2 inferInstance
  let χ₀ : 𝓞 E →+* k := χ.codRestrict k hχ
  have hχ₀ : ∀ a, algebraMap k K (χ₀ a) = χ a := fun a => rfl
  have hk : ∀ i (c : k), C.v i (algebraMap k K c) ≤ 1 := fun i c => v_le_one_of_finite C k i c
  haveI : Finite (TensorProduct ℤ k (𝓞 E)) := Module.finite_of_finite k
  obtain ⟨e, he, h1e, hnil⟩ := exists_idem (TensorProduct ℤ k (𝓞 E)) (RingHom.ker (chiT χ₀))
  have h1 : chiT χ₀ e = 1 := by
    have : chiT χ₀ (1 - e) = 0 := h1e
    rw [map_sub, map_one, sub_eq_zero] at this
    exact this.symm
  obtain ⟨n, hn, hc⟩ := deg_count C D.H k (TensorProduct ℤ k (𝓞 E)) (act k D.ρH) r (chiT χ₀) e
    D.H_bun (act_isHom C D.H_bun hk _ D.ρH_hom)
    (fun c x => by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply, act_tmul]
      simp)
    hk (fun i => GlobalTheory.T.module_basis_lattice_bundle_free K C _ D.H _ _ k (RingOfIntegers.basis E) D.ρH r i D.H_bun (hk i) (hfr i))
    he h1 hnil
  rw [vanish D k hk e he, idealV_ker K k (𝓞 E) _ D.ρH χ₀] at hc
  change _ = _ * deg C (quot C D.H (⨆ a : 𝓞 E, LinearMap.range (D.ρH a - χ a • LinearMap.id))) at hc
  rcases mul_eq_zero.1 hc.symm with h | h
  · exact absurd h (by exact_mod_cast hn.ne')
  · exact h

end GlobalTheory.CompanionTheory.Ar.Flat.DegCurve
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SplitHermitianGeneratorsExistStatement
open NumberField GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_hermitian_generators_exist : ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (d r : ℕ) (D : ConjData C p (𝓞 E) d) (χ : 𝓞 E →+* K), (∀ a : 𝓞 E, ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom K)).Splits) → (∀ i, ∃ x : Fin r → (Fin d → K) × (Fin d → K), LinearIndependent K (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => D.ρH (RingOfIntegers.basis E q.2) (x q.1)) ∧ ∀ y, y ∈ D.H i ↔ ∃ c : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) → K, (∀ q, C.v i (c q) ≤ 1) ∧ y = ∑ q, c q • D.ρH (RingOfIntegers.basis E q.2) (x q.1)) → deg C (quot C D.H (⨆ a : 𝓞 E, LinearMap.range (D.ρH a - χ a • LinearMap.id))) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.deg_quot_eq_zero | exact GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.deg_quot_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.deg_quot_eq_zero <;> assumption)
end
