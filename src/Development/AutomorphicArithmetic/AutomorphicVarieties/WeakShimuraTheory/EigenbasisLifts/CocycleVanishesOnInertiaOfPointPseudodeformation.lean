module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.AwAvg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsNontrivialCharacterPgroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.InertiaTrivialOfCharpolyRootsNearCharacter
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem vb_coeff {K : Type} [NormedField K] [IsUltrametricDist K] (a : K) (ha : ‖a‖ ≤ 1) (s : Multiset K)
    (hs : ∀ t ∈ s, ‖t - a‖ < 1) :
    ∀ i, ‖((s.map fun t => X - C t).prod - (X - C a) ^ s.card).coeff i‖ < 1 ∧ ‖((X - C a) ^ s.card).coeff i‖ ≤ 1 := by
  have step : ∀ (P : K[X]) (b : K) (r : ℝ → Prop), (∀ x y, x ≤ max y y → r y → r x) → r 0 → (∀ x y, r x → r y → r (max x y)) →
      ‖b‖ ≤ 1 → (∀ i, r ‖P.coeff i‖) → ∀ i, r ‖((X - C b) * P).coeff i‖ := by
    intro P b r h1 h0 h2 hb hP i
    have h3 : r ‖(X * P).coeff i‖ := by
      cases i with
      | zero => simpa using h0
      | succ i => simpa using hP i
    have h4 : r ‖b * P.coeff i‖ := h1 _ _ (by
      rw [max_self, norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) hb) (hP i)
    rw [sub_mul, coeff_sub, coeff_C_mul]
    refine h1 _ _ ?_ (h2 _ _ h3 h4)
    rw [max_self, sub_eq_add_neg]
    simpa using IsUltrametricDist.norm_add_le_max ((X * P).coeff i) (-(b * P.coeff i))
  induction s using Multiset.induction_on with
  | empty =>
    intro i
    simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.card_zero, pow_zero, sub_self, coeff_zero, norm_zero,
      zero_lt_one, true_and, coeff_one]
    split_ifs <;> simp
  | cons t s ih =>
    have ih' := ih fun u hu => hs u (Multiset.mem_cons_of_mem hu)
    have hta := hs t (Multiset.mem_cons_self _ _)
    have ht : ‖t‖ ≤ 1 := by
      have := IsUltrametricDist.norm_add_le_max (t - a) a
      rw [sub_add_cancel] at this
      exact this.trans (max_le hta.le ha)
    intro i
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ']
    refine ⟨?_, step _ a (· ≤ 1) (fun x y h h' => h.trans (by simpa using h')) zero_le_one
      (fun x y => max_le) ha (fun j => (ih' j).2) i⟩
    have e : (X - C t) * (s.map fun t => X - C t).prod - (X - C a) * (X - C a) ^ s.card =
        (X - C t) * ((s.map fun t => X - C t).prod - (X - C a) ^ s.card) + C (a - t) * (X - C a) ^ s.card := by
      rw [map_sub]; ring
    rw [e, coeff_add, coeff_C_mul]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · exact step _ t (· < 1) (fun x y h h' => h.trans_lt (by simpa using h')) zero_lt_one
        (fun x y => max_lt) ht (fun j => (ih' j).1) i
    · rw [norm_mul, norm_sub_rev]
      exact (mul_le_of_le_one_right (norm_nonneg _) (ih' i).2).trans_lt hta

attribute [-instance] UpperTheory.V.UnitaryThreeInertia.Coef.isLocalRing in
theorem UpperTheory.V.Ws.Eb.inertia_trivial_of_charpoly_roots_near_character :
    ∀ {p l : ℕ} [Fact p.Prime] [Fact l.Prime], p ≠ l → ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] (φ : H →* Formalism.BasicNotions.Loc.GQ p), Topology.IsOpenEmbedding φ → ∀ (c : Coef l) (κ : H →* (ResidueField c.O)ˣ), (∀ g, φ g ∈ Loc.Iq p → κ g = 1) → (∃ g, residue c.O (Loc.cycA p l c.O (φ g) : c.O) ≠ 1) →
        ∀ {n : ℕ} (ρ : H →* GL (Fin n) (PadicAlgCl l)), Continuous ρ → (∀ g (a : c.O), residue c.O a = κ g → ∀ t ∈ (W.mat ρ g).charpoly.roots, ‖t - (a : PadicAlgCl l)‖ < 1) → ∀ g, φ g ∈ Loc.Iq p → ρ g = 1 := by
  intro p l _ hl hpl H _ _ _ _ φ hφ c κ hκ hω n ρ hρ hroot
  haveI : T2Space H := hφ.isEmbedding.t2Space
  obtain ⟨c', Q, r₀, hle, hQ, hcont⟩ := UpperTheory.V.Ws.Eb.intModel c ρ hρ
  obtain ⟨hcpl, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c'.O
  haveI : Finite (ResidueField c'.O) := hfin
  haveI : CharP (ResidueField c'.O) l := by
    refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
    rw [← map_natCast (residue c'.O), residue_eq_zero_iff]
    exact hlm
  let y : c.O →+* c'.O := (Subalgebra.inclusion hle : c.O →+* c'.O)
  haveI : IsLocalHom y := ⟨fun x hx => by
    by_contra hn
    have h3 : y x ∈ maximalIdeal c'.O :=
      (UpperTheory.V.Fr.sc_norm l c' (y x)).2.2 ((UpperTheory.V.Fr.sc_norm l c x).2.1 hn)
    exact h3 hx⟩
  let f : ResidueField c.O →+* ResidueField c'.O := ResidueField.map y
  have hf : ∀ x, f (residue c.O x) = residue c'.O (y x) := fun x => ResidueField.map_residue y x
  have hQ' : ∀ g, W.pushRep (algebraMap c'.O (PadicAlgCl l)) r₀ g = Q⁻¹ * ρ g * Q := fun g => by
    rw [mul_assoc, hQ, inv_mul_cancel_left]
  have main := (UpperTheory.V.Loc.v0b hpl φ hφ c'.O (W.pushCh f κ) (fun g hg => by simp [hκ g hg]) ?_ r₀
    (fun N i j => hcont i j N) ?_).1
  · intro g hg
    have h3 := hQ g
    rw [MonoidHom.comp_apply, main g hg, map_one, mul_one] at h3
    exact mul_right_cancel (h3.trans (one_mul Q).symm)
  · obtain ⟨g, hg⟩ := hω
    refine ⟨g, fun h => hg (f.injective ?_)⟩
    rw [map_one, ← h, hf]
    rfl
  · intro g
    obtain ⟨a, ha⟩ := residue_surjective (R := c.O) (κ g : ResidueField c.O)
    have e1 : (r₀ g).val.charpoly.map (algebraMap c'.O (PadicAlgCl l)) =
        (W.mat ρ g).charpoly := by
      rw [← Matrix.charpoly_map]
      have e2 : (r₀ g).val.map (algebraMap c'.O (PadicAlgCl l)) =
          (Q⁻¹ * ρ g * Q : GL (Fin n) (PadicAlgCl l)).val := by
        rw [← hQ']
        rfl
      rw [e2, Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, ← mul_assoc, mul_inv_cancel, one_mul]
      rfl
    have hsp : (W.mat ρ g).charpoly.Splits := IsAlgClosed.splits _
    have hcard : (W.mat ρ g).charpoly.roots.card = n := by
      rw [← hsp.natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    have hprod := hsp.eq_prod_roots_of_monic (Matrix.charpoly_monic _)
    have key := vb_coeff (a : PadicAlgCl l) (UpperTheory.V.Fr.sc_norm l c a).1 _ (hroot g a ha)
    rw [← hprod, hcard, ← e1] at key
    have e3 : ((W.pushCh f κ g : (ResidueField c'.O)ˣ) : ResidueField c'.O) = residue c'.O (y a) := by
      rw [← hf, ha]; rfl
    have e4 : (X - C (residue c'.O (y a))) ^ n = ((X - C (y a)) ^ n).map (residue c'.O) := by simp
    rw [Matrix.charpoly_map, e3, e4, ← sub_eq_zero, ← Polynomial.map_sub]
    ext i
    rw [coeff_map, coeff_zero, residue_eq_zero_iff, (UpperTheory.V.Fr.sc_norm l c' _).2]
    have e5 : (X - C (a : PadicAlgCl l)) ^ n = ((X - C (y a)) ^ n).map (algebraMap c'.O (PadicAlgCl l)) := by
      rw [Polynomial.map_pow, Polynomial.map_sub, map_X, map_C]; rfl
    have h6 := (key i).1
    rw [e5, ← Polynomial.map_sub, coeff_map] at h6
    exact h6
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.DblRep
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private def dblMat {K H : Type} [Field K] [TopologicalSpace K] [Group H] [TopologicalSpace H] {n : ℕ}
    (ρ : H →* GL (Fin n) K) (y : H → Matrix (Fin n) (Fin n) K)
    (hy : ∀ g h, y (g * h) = y g + Loc.adGL ρ g (y h)) : H →* Matrix (Fin (n + n)) (Fin (n + n)) K where
  toFun g := Matrix.reindexAlgEquiv K K finSumFinEquiv
    (Matrix.fromBlocks (ρ g : Matrix (Fin n) (Fin n) K) (y g * (ρ g : Matrix (Fin n) (Fin n) K)) 0 (ρ g : Matrix (Fin n) (Fin n) K))
  map_one' := by
    have h1 : y 1 = 0 := by
      have := hy 1 1
      simpa using this
    simp only [map_one, Units.val_one, h1, Matrix.zero_mul, Matrix.fromBlocks_one]
  map_mul' g h := by
    rw [← map_mul, Matrix.fromBlocks_multiply, hy]
    congr 2
    · simp
    · simp only [Loc.adGL, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, map_mul, Units.val_mul,
        Matrix.add_mul, Matrix.mul_assoc, Units.inv_mul_cancel_left]
      exact add_comm _ _
    · simp
    · simp

theorem UpperTheory.V.Ws.Eb.dblRep :
    ∀ {K H : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {n : ℕ} (ρ : H →* GL (Fin n) K), Continuous ρ → ∀ y ∈ Z1 (Loc.adGL ρ),
        ∃ ρ₂ : H →* GL (Fin (n + n)) K, Continuous ρ₂ ∧ (∀ g, (W.mat ρ₂ g).charpoly = (W.mat ρ g).charpoly ^ 2) ∧ ∀ g, ρ₂ g = 1 → y g = 0 := by
  intro K H _ _ _ _ _ _ n ρ hρ y hy
  obtain ⟨hyc, hyco⟩ := hy
  let D := dblMat ρ y hyco
  have hρv : Continuous (fun g => (ρ g : Matrix (Fin n) (Fin n) K)) := Units.continuous_val.comp hρ
  have hblk : Continuous (fun g => Matrix.fromBlocks (ρ g : Matrix (Fin n) (Fin n) K)
      (y g * (ρ g : Matrix (Fin n) (Fin n) K)) 0 (ρ g : Matrix (Fin n) (Fin n) K)) :=
    Continuous.matrix_fromBlocks hρv (hyc.matrix_mul hρv) continuous_const hρv
  have hDc : Continuous (fun g => D g) := by
    have e : (fun g => D g) = fun g => (Matrix.fromBlocks (ρ g : Matrix (Fin n) (Fin n) K)
        (y g * (ρ g : Matrix (Fin n) (Fin n) K)) 0 (ρ g : Matrix (Fin n) (Fin n) K)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm := by
      funext g
      rfl
    rw [e]
    exact hblk.matrix_submatrix _ _
  refine ⟨D.toHomUnits, ?_, ?_, ?_⟩
  · refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact hDc
    · have e : (fun g => ((D.toHomUnits g)⁻¹ : GL (Fin (n + n)) K).val) = fun g => D g⁻¹ := by
        funext g
        rw [← map_inv, MonoidHom.coe_toHomUnits]
      rw [e]
      exact hDc.comp continuous_inv
  · intro g
    show (D g).charpoly = ((ρ g : Matrix (Fin n) (Fin n) K)).charpoly ^ 2
    simp only [D, dblMat, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindexAlgEquiv_apply,
      Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₂₁, pow_two]
  · intro g hg
    have h1 : D g = 1 := by
      rw [← MonoidHom.coe_toHomUnits D g, hg, Units.val_one]
    have h2 : Matrix.fromBlocks (ρ g : Matrix (Fin n) (Fin n) K) (y g * (ρ g : Matrix (Fin n) (Fin n) K))
        0 (ρ g : Matrix (Fin n) (Fin n) K) = Matrix.fromBlocks 1 0 0 1 := by
      rw [Matrix.fromBlocks_one]
      apply (Matrix.reindexAlgEquiv K K finSumFinEquiv).injective
      rw [map_one]
      exact h1
    obtain ⟨-, hB, -, -⟩ := Matrix.fromBlocks_inj.mp h2
    calc y g = y g * (ρ g : Matrix (Fin n) (Fin n) K) * ((ρ g)⁻¹ : GL (Fin n) K) := by
          rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = 0 := by rw [hB, Matrix.zero_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.RootsNear
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem rn_root {K : Type} [NormedField K] [IsUltrametricDist K] (p : K[X]) (hp : p.Monic)
    (hc : ∀ i < p.natDegree, ‖p.coeff i‖ < 1) (s : K) (hs : p.eval s = 0) : ‖s‖ < 1 := by
  by_contra hlt
  push_neg at hlt
  have sumlt : ∀ (t : Finset ℕ) (f : ℕ → K) (r : ℝ), 0 < r → (∀ i ∈ t, ‖f i‖ < r) → ‖∑ i ∈ t, f i‖ < r := by
    intro t f r hr
    induction t using Finset.induction_on with
    | empty => intro _; simpa using hr
    | insert j t hj ih =>
      intro hf
      rw [Finset.sum_insert hj]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
        (max_lt (hf j (Finset.mem_insert_self _ _)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))
  have hsum : p.eval s = s ^ p.natDegree + ∑ i ∈ Finset.range p.natDegree, p.coeff i * s ^ i := by
    conv_lhs => rw [hp.as_sum]
    simp [eval_finsetSum]
  have hpos : 0 < ‖s‖ := lt_of_lt_of_le one_pos hlt
  have hlt2 : ‖∑ i ∈ Finset.range p.natDegree, p.coeff i * s ^ i‖ < ‖s‖ ^ p.natDegree := by
    apply sumlt _ _ _ (pow_pos hpos _)
    intro i hi
    rw [Finset.mem_range] at hi
    rw [norm_mul, norm_pow]
    calc ‖p.coeff i‖ * ‖s‖ ^ i < 1 * ‖s‖ ^ i :=
          mul_lt_mul_of_pos_right (hc i hi) (pow_pos hpos _)
      _ = ‖s‖ ^ i := one_mul _
      _ ≤ ‖s‖ ^ p.natDegree := pow_le_pow_right₀ hlt hi.le
  have heq : s ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree, p.coeff i * s ^ i := by
    rw [hs] at hsum
    exact eq_neg_of_add_eq_zero_left hsum.symm
  have h3 := congrArg norm heq
  rw [norm_neg, norm_pow] at h3
  rw [h3] at hlt2
  exact lt_irrefl _ hlt2

theorem UpperTheory.V.Ws.Eb.rootsNear :
    ∀ {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {c : Coef l} {n : ℕ} {r : W.Resid F c.O n} (B : W.UniversalOrdinaryDeterminantRing r) (x : B.B →ₐ[c.O] PadicAlgCl l) (ρ : F.G₀ →* GL (Fin n) (PadicAlgCl l)), B.u.D.map (x : B.B →+* PadicAlgCl l) = W.GDet.ofRep (W.mat ρ) →
        ∀ g (a : c.O), (∀ i, residue c.O a = r.chib i g) → ∀ t ∈ (W.mat ρ g).charpoly.roots, ‖t - (a : PadicAlgCl l)‖ < 1 := by
  intro l _ F c n r B x ρ hD g a ha t ht
  have hsing : ∀ {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A'),
      MonoidAlgebra.mapRingHom F.G₀ f (MonoidAlgebra.single g 1) = MonoidAlgebra.single g 1 := by
    intro A A' _ _ f
    simp [MonoidAlgebra.mapRingHom]
  set Q := B.u.D.chi (MonoidAlgebra.single g 1) with hQ
  have hx : (W.mat ρ g).charpoly = Q.map (x : B.B →+* PadicAlgCl l) := by
    have h1 := (AlgebraTools.Det.mapApi B.u.D (x : B.B →+* PadicAlgCl l)).1 (MonoidAlgebra.single g 1)
    rw [hsing, hD, (AlgebraTools.Det.repApi (W.mat ρ)).2.1] at h1
    exact h1
  have hred : Q.map (res c.O B.B : B.B →+* ResidueField c.O) = (X - C (residue c.O a)) ^ n := by
    have h1 := (AlgebraTools.Det.mapApi B.u.D (res c.O B.B : B.B →+* ResidueField c.O)).1 (MonoidAlgebra.single g 1)
    rw [hsing, B.u.red, W.Resid.Dbar, (AlgebraTools.Det.repApi _).2.1] at h1
    rw [← h1]
    show (Matrix.diagonal _).charpoly = _
    rw [Matrix.charpoly_diagonal]
    simp [← ha]
  set Q' := Q.comp (X + C (algebraMap c.O B.B a)) with hQ'
  set p := (W.mat ρ g).charpoly.comp (X + C (a : PadicAlgCl l)) with hp
  have hpQ : p = Q'.map (x : B.B →+* PadicAlgCl l) := by
    rw [hp, hQ', hx, Polynomial.map_comp]
    simp
  have hQm : ∀ i < n, Q'.coeff i ∈ maximalIdeal B.B := by
    intro i hi
    rw [← res_eq_zero_iff c.O B.B, ← RingHom.coe_coe (res c.O B.B), ← Polynomial.coeff_map, hQ',
      Polynomial.map_comp, hred]
    simp [ResidueField.algebraMap_eq, Polynomial.coeff_X_pow, hi.ne]
  obtain ⟨_, a0, ha1, _, hb⟩ := (coPt c B.B).1 x
  have hmon : p.Monic := (Matrix.charpoly_monic _).comp_X_add_C _
  have hdeg : p.natDegree = n := by
    rw [hp, Polynomial.natDegree_comp, Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_X_add_C]
    simp
  have hc : ∀ i < p.natDegree, ‖p.coeff i‖ < 1 := by
    intro i hi
    rw [hdeg] at hi
    rw [hpQ, Polynomial.coeff_map]
    have := hb 1 _ (by rw [pow_one]; exact hQm i hi)
    rw [pow_one] at this
    exact this.trans_lt ha1
  have hroot : p.eval (t - (a : PadicAlgCl l)) = 0 := by
    rw [hp, Polynomial.eval_comp]
    simp only [eval_add, eval_X, eval_C, sub_add_cancel]
    exact (Polynomial.mem_roots'.mp ht).2
  exact rn_root p hmon hc _ hroot
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.Eb.cocycle_vanishes_on_inertia_of_point_pseudodeformation :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L]
      [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev)
      {c : Coef l} {n : ℕ} {r : W.Resid (W.HidaSetting.Lev.frame V) c.O n}
      (B : W.UniversalOrdinaryDeterminantRing r) (x : B.Pt)
      (ρ : (W.HidaSetting.Lev.frame V).G₀ →* GL (Fin n) (PadicAlgCl l)),
      r.V0ok → B.u.D.map (x : B.B →+* PadicAlgCl l) = W.GDet.ofRep (W.mat ρ) →
      Continuous ρ → ∀ y ∈ Z1 (Loc.adGL ρ), ∀ g ∈ (W.HidaSetting.Lev.frame V).I0, y g = 0 := by
  intro l _ L Ω _ _ _ _ _ _ s V c n r B x ρ hok hB hρ y hy g hg
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact Subsingleton.elim _ _
  haveI : Fact s.p.Prime := ⟨s.p_prime⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  obtain ⟨hI0, hD0, g0, hg0D, hg0e⟩ := hok
  have hpv : ((s.p : ℕ) : 𝓞 (W.Lp L)) ∈ s.v0.asIdeal := by
    have h := Ideal.absNorm_mem s.v0.asIdeal
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← normV, s.norm_v0_eq_one] at h
  have hpw : ((s.p : ℕ) : 𝓞 L) ∈ (s.w s.v0).asIdeal := by
    rw [← s.hw s.v0]
    have h := (s.hA s.v0 _).mpr hpv
    simpa using h
  obtain ⟨j, hj⟩ := (Loc.decEmb (F := L) (Ω := Ω) (v := s.p)).1 (s.A s.v0) (s.w s.v0) (s.hw s.v0) hpw
  obtain ⟨-, φ, hφo, -, -, hφI, hφc, -⟩ := (Loc.decEmb (F := L) (Ω := Ω) (v := s.p)).2 j
  change g ∈ Subgroup.map V.pr (Ine (s.A s.v0)) at hg
  change ∀ i, Subgroup.map V.pr (Ine (s.A s.v0)) ≤ (r.chib i).ker at hI0
  change ∀ g ∈ Subgroup.map V.pr (Dec (s.A s.v0)), ∀ i j, (r.chib i) g = (r.chib j) g at hD0
  change g0 ∈ Subgroup.map V.pr (Dec (s.A s.v0)) at hg0D
  rw [← hj] at hg hI0 hD0 hg0D
  obtain ⟨ρ₂, hρ₂c, hρ₂p, hρ₂y⟩ := dblRep ρ hρ y hy
  let ψ : ↥(Dec (Loc.placeJ j)) →* V.frame.G₀ := V.pr.comp (Dec (Loc.placeJ j)).subtype
  have hψc : Continuous ψ := (V.pr_cont W.continuous_resP).comp continuous_subtype_val
  haveI : CompactSpace ↥(Dec (Loc.placeJ j)) := isCompact_iff_compactSpace.mp (isClosed_Dec (F := L) (Loc.placeJ j)).isCompact
  let κ : ↥(Dec (Loc.placeJ j)) →* (ResidueField c.O)ˣ := (r.chib ⟨0, hn⟩).comp ψ
  have main := inertia_trivial_of_charpoly_roots_near_character s.p_ne φ hφo c κ ?_ ?_ (ρ₂.comp ψ) (hρ₂c.comp hψc) ?_
  · obtain ⟨h, hh, rfl⟩ := hg
    apply hρ₂y
    exact main ⟨h, Ine_le_Dec _ hh⟩ ((hφI ⟨h, Ine_le_Dec _ hh⟩).2 hh)
  · intro h hh
    have hI : (h : G L Ω) ∈ Ine (Loc.placeJ j) := (hφI h).1 hh
    exact MonoidHom.mem_ker.mp (hI0 ⟨0, hn⟩ ⟨(h : G L Ω), hI, rfl⟩)
  · obtain ⟨h, hh, rfl⟩ := hg0D
    refine ⟨⟨h, hh⟩, fun heq => hg0e ?_⟩
    unfold Loc.cycA at heq
    rw [MonoidHom.comp_apply, hφc] at heq
    have e1 : V.frame.ε (V.frame.η.ker.subtype (V.pr h)) = cycZ L Ω l h := by
      change V.ε (toGS Ω V.S' (W.resP L Ω h)) = _
      rw [← MonoidHom.comp_apply, V.hε]
      rfl
    apply Units.ext
    unfold W.GFrame.eps W.pushCh
    change (algebraMap c.O (ResidueField c.O)) (algebraMap ℤ_[l] c.O
      ↑(V.frame.ε (V.frame.η.ker.subtype (V.pr h)))) = 1
    change (residue c.O) (algebraMap ℤ_[l] c.O ↑(cycZ L Ω l h)) = 1 at heq
    rw [e1, IsLocalRing.ResidueField.algebraMap_eq]
    exact heq
  · intro h a ha t ht
    change t ∈ (W.mat ρ₂ (ψ h)).charpoly.roots at ht
    rw [hρ₂p, Polynomial.roots_pow, Multiset.mem_nsmul] at ht
    refine rootsNear B x ρ hB (ψ h) a (fun i => ?_) t ht.2
    rw [ha]
    exact congrArg Units.val (hD0 (ψ h) ⟨h.1, h.2, rfl⟩ ⟨0, hn⟩ i)
