module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DCorner
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHeckePairIwC

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpRoots
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.spRoots :
    ∀ (R : Type) [CommRing R] (q n : ℕ) (P : Fin q → Polynomial R) (ut : Fin q → Fin n → R) (j : Fin q), (∏ i, (Polynomial.X - Polynomial.C (Sp.u P ut j i))) = (P j).map (algebraMap R (Sp P ut)) ∧ ∀ i, Sp.u P ut j i - algebraMap R (Sp P ut) (ut j i) = Sp.mk P ut (MvPowerSeries.X (j, i)) := by
  intro R _ q n P ut j
  have hC : ∀ a : R, Sp.mk P ut (MvPowerSeries.C a) = algebraMap R (Sp P ut) a := fun a =>
    (Sp.mk P ut).commutes a
  refine ⟨?_, fun i => ?_⟩
  · have h1 : (∏ i, (Polynomial.X - Polynomial.C (Sp.u P ut j i))) =
        (∏ i, (Polynomial.X - Polynomial.C (MvPowerSeries.C (ut j i) + MvPowerSeries.X (j, i) : MvPowerSeries (Fin q × Fin n) R))).map (Sp.mk P ut).toRingHom := by
      rw [Polynomial.map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      rfl
    rw [h1]
    ext k
    rw [Polynomial.coeff_map, Polynomial.coeff_map, ← hC]
    refine (Ideal.Quotient.eq (I := spIdeal P ut)).2 ?_
    exact Ideal.subset_span ⟨j, k, by rw [Polynomial.coeff_sub, Polynomial.coeff_map]⟩
  · rw [Sp.u, map_add (f := _), hC, add_sub_cancel_left]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.CloseLift
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.closeLift :
    ∀ (Ph A B : Type) [Group Ph] [Group A] [Group B] (π : Ph →* A) (π' : Ph →* B) (V : Subgroup Ph) [V.Normal], π.ker ⊔ V = π'.ker ⊔ V → (∀ a b g, Close π π' V a b → π' g = b → ∃ g', π g' = a ∧ g⁻¹ * g' ∈ V) ∧ ∀ k, π' k = 1 → ∃ k', π k' = 1 ∧ k⁻¹ * k' ∈ V := by
  intro Ph A B _ _ _ π π' V _ hsup
  have hdec : ∀ x, π' x = 1 → ∃ k, π k = 1 ∧ ∃ v ∈ V, k * v = x := by
    intro x hx
    have hx' : x ∈ π.ker ⊔ V := by
      rw [hsup]
      exact Subgroup.mem_sup_left (MonoidHom.mem_ker.2 hx)
    obtain ⟨k, hk, v, hv, hkv⟩ := Subgroup.mem_sup_of_normal_right.1 hx'
    exact ⟨k, MonoidHom.mem_ker.1 hk, v, hv, hkv⟩
  refine ⟨fun a b g ⟨g0, g0', ha, hb, hV⟩ hg => ?_, fun k hk => ?_⟩
  · obtain ⟨k, hk, v, hv, hkv⟩ := hdec (g0'⁻¹ * g) (by rw [map_mul, map_inv, hb, hg, inv_mul_cancel])
    refine ⟨g0 * k, by rw [map_mul, ha, hk, mul_one], ?_⟩
    have hg' : g = g0' * (k * v) := by rw [hkv, mul_inv_cancel_left]
    rw [hg']
    have hw : g0'⁻¹ * g0 ∈ V := by
      have := V.inv_mem hV
      rwa [_root_.mul_inv_rev, inv_inv] at this
    have hconj : k⁻¹ * (g0'⁻¹ * g0) * k ∈ V := by
      have := (inferInstance : V.Normal).conj_mem _ hw k⁻¹
      rwa [inv_inv] at this
    have heq : (g0' * (k * v))⁻¹ * (g0 * k) = v⁻¹ * (k⁻¹ * (g0'⁻¹ * g0) * k) := by group
    rw [heq]
    exact V.mul_mem (V.inv_mem hv) hconj
  · obtain ⟨k', hk', v, hv, rfl⟩ := hdec k hk
    refine ⟨k', hk', ?_⟩
    have heq : (k' * v)⁻¹ * k' = v⁻¹ := by group
    rw [heq]
    exact V.inv_mem hv
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.ResPull
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem repAlg_comp {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (φ : H →* G)
    (χ : Fin n → G →* Aˣ) (B : Type) [CommRing B] [Algebra A B] (y : MonoidAlgebra B H) :
    GDet.repAlg (diagRep fun i => (χ i).comp φ) B y =
      GDet.repAlg (diagRep χ) B (MonoidAlgebra.mapDomainRingHom B φ y) := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g r => simp [GDet.repAlg, diagRep]

private theorem star_map {l : ℕ} [Fact l.Prime] {L : Loc} {G G' : Glob l L} (h : G.Hom G') (n : ℕ)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] (B : Type) [CommRing B] [Algebra O B] (y : MonoidAlgebra B G.G₀) :
    MonoidAlgebra.mapDomainRingHom B h.p₀ (G.frame.star O B n y) =
      G'.frame.star O B n (MonoidAlgebra.mapDomainRingHom B h.p₀ y) := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp [GFrame.star]
  | add a b ha hb =>
    simp only [GFrame.star] at ha hb
    simp only [GFrame.star, map_add (f := _), MulOpposite.unop_add, ha, hb]
  | single g r =>
    simp [GFrame.star, GFrame.starOp, ← h.p₀_conj, h.eps_p₀]

theorem UpperTheory.V.Pa.Core.resPull :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' : Glob l L) (h : G.Hom G') (n : ℕ) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (r : Resid G'.frame O n), ∃ r' : Resid G.frame O n, Glob.Compat h r' r := by
  intro l _ L G G' h n O _ _ _ r
  refine ⟨⟨fun i => (r.chib i).comp h.p₀, fun i => (r.chib_open i).preimage h.p₀_cont, ?_, ?_,
    r.psib, r.psib_open, r.th, r.th_comm⟩, fun _ => rfl, rfl, rfl⟩
  · intro i j hij
    apply r.chib_inj
    ext g
    obtain ⟨g, rfl⟩ := h.p₀_surj g
    exact congrArg Units.val (DFunLike.congr_fun hij g)
  · intro B _ _ _ _ y
    have := r.polar B (MonoidAlgebra.mapDomainRingHom B h.p₀ y)
    rw [← star_map] at this
    change (GDet.repAlg _ B _).det = (GDet.repAlg _ B _).det
    rw [repAlg_comp, repAlg_comp]
    exact this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.FoCong
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.foCong :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W) (j N : ℕ), j ≤ N → fo W - fEl (T.Nq N) W.t.U ∈ maximalIdeal W.R ^ j ∧ m.ρ N (fEl (T.Nq N) W.t.U) = fEl (T.Nq N) (A.A N).U ∧ ∃ c : W.R, fo W - fEl (T.Nq N) W.t.U = (l : W.R) ^ j * c := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m j N hj
  have hlO : (l : O) ∈ maximalIdeal O := by
    haveI := IsCoef.char (l := l) (O := O)
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ l
  have hl : (l : W.R) ∈ maximalIdeal W.R := by
    have hco := (inferInstance : IsCO O W.R).isLocalHom
    intro hu
    rw [← map_natCast (algebraMap O W.R)] at hu
    exact hlO (hco.map_nonunit _ hu)
  set I : Ideal W.R := Ideal.span {(l : W.R) ^ j} with hI
  have hq : ∀ jj, (T.Nq N jj : W.R) - 1 ∈ I := by
    intro jj
    obtain ⟨k, hk⟩ := Nat.modEq_iff_dvd.mp (T.Nq_mod N jj).symm
    have h3 := congrArg (Int.cast : ℤ → W.R) hk
    push_cast at h3
    rw [Ideal.mem_span_singleton]
    refine ⟨(l : W.R) ^ (N - j) * (k : W.R), ?_⟩
    rw [h3, ← pow_mul_pow_sub (l : W.R) hj, mul_assoc]
  have hq' : ∀ jj, Ideal.Quotient.mk I (T.Nq N jj : W.R) = 1 := by
    intro jj
    rw [← map_one (Ideal.Quotient.mk I)]
    exact Ideal.Quotient.eq.mpr (hq jj)
  have hmod : Ideal.Quotient.mk I (fo W) = Ideal.Quotient.mk I (fEl (T.Nq N) W.t.U) := by
    simp only [fo, fEl, map_prod, map_mul, map_sub, hq', Nat.cast_one, map_one, one_mul]
  have hdiff : fo W - fEl (T.Nq N) W.t.U ∈ I := Ideal.Quotient.eq.mp hmod
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hdiff
  refine ⟨?_, ?_, ⟨c, hc⟩⟩
  · rw [hc]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hl j)
  · obtain ⟨-, -, -, hU, -⟩ := m.ρ_maps N
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hU
    simp [fEl, map_prod, hU]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.ChiRes
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem chi_diag {n : ℕ} {k G : Type} [CommRing k] [Group G] (χ : Fin n → G →* kˣ) (g : G) :
    (GDet.ofRep (diagRep χ)).chi (MonoidAlgebra.single g 1) =
      ∏ i, (Polynomial.X - Polynomial.C (χ i g : k)) := by
  change (GDet.repAlg (diagRep χ) (Polynomial k) _).det = _
  rw [← Matrix.det_diagonal]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [GDet.repAlg, diagRep, Matrix.one_apply, Matrix.diagonal_apply, h]

theorem UpperTheory.V.Pa.Core.chiRes :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (r : Resid F O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (g : F.G₀) (ut : Fin n → O), (∀ i, residue O (ut i) = r.chib i g) → (u.D.chi (MonoidAlgebra.single g 1)).Monic ∧ (u.D.chi (MonoidAlgebra.single g 1)).natDegree = n ∧ (u.D.chi (MonoidAlgebra.single g 1)).map (residue B) = ∏ i, (Polynomial.X - Polynomial.C (residue B (algebraMap O B (ut i)))) := by
  intro l _ F n O _ _ _ r B _ _ _ u g ut hut
  have hm : (u.D.chi (MonoidAlgebra.single g 1)).Monic := by
    have hchi : u.D.toDet.chi (MonoidAlgebra.single g 1) = u.D.chi (MonoidAlgebra.single g 1) := by
      change u.D.D (Polynomial B) (ofT B F.G₀ (Polynomial B)
        (Polynomial.X ⊗ₜ 1 - 1 ⊗ₜ MonoidAlgebra.single g 1)) = _
      congr 1
      rw [map_sub, ofT_tmul, ofT_tmul, map_one, one_smul,
        MonoidAlgebra.one_def, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
      rfl
    rw [← hchi]
    exact (UpperTheory.V.CA.d_chi _ _).2.2.2.2.1
  have h1 : (u.D.chi (MonoidAlgebra.single g 1)).map (res O B : B →+* ResidueField O) =
      ∏ i, (Polynomial.X - Polynomial.C (residue O (ut i))) := by
    have hchi : (u.D.map (res O B : B →+* ResidueField O)).chi
        (MonoidAlgebra.mapRingHom F.G₀ (res O B : B →+* ResidueField O) (MonoidAlgebra.single g 1)) =
        (u.D.chi (MonoidAlgebra.single g 1)).map (res O B) := by
      let f : B →+* ResidueField O := res O B
      letI : Algebra B (Polynomial (ResidueField O)) := ((algebraMap _ _).comp f).toAlgebra
      let φ : Polynomial B →ₐ[B] Polynomial (ResidueField O) :=
        { Polynomial.mapRingHom f with
          commutes' := fun a => by
            change Polynomial.map f (Polynomial.C a) = Polynomial.C (f a)
            exact Polynomial.map_C f }
      have h := u.D.nat (Polynomial B) (Polynomial (ResidueField O)) φ
        (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom F.G₀ Polynomial.C (MonoidAlgebra.single g 1))
      refine Eq.trans ?_ h
      change u.D.D (Polynomial (ResidueField O)) _ = u.D.D (Polynomial (ResidueField O)) _
      congr 1
      have hφ : (φ : Polynomial B →+* Polynomial (ResidueField O)) = Polynomial.mapRingHom f := rfl
      rw [hφ]
      ext x : 2
      simp
    rw [← hchi, u.red, MonoidAlgebra.mapRingHom_single, map_one, Resid.Dbar,
      chi_diag]
    simp only [hut]
  have hc : (ResidueField.map (algebraMap O B)).comp (res O B : B →+* ResidueField O) = residue B := by
    ext x
    exact (RingEquiv.ofBijective _ (resMap_bijective O B)).apply_symm_apply (residue B x)
  have h2 : (u.D.chi (MonoidAlgebra.single g 1)).map (residue B) =
      ∏ i, (Polynomial.X - Polynomial.C (residue B (algebraMap O B (ut i)))) := by
    conv_lhs => rw [← hc, ← Polynomial.map_map, h1]
    simp [Polynomial.map_prod, ResidueField.map_residue]
  refine ⟨hm, ?_, h2⟩
  rw [← hm.natDegree_map (residue B), h2, Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _]
  simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.LamEqOfKer
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem lam_eq_of_ker {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)
    {x y : E} (h : x - y ∈ D.ker) (i : ℕ) : D.lam i x = D.lam i y := by
  have hchi : D.chi x = D.chi y := by
    have h2 := ((UpperTheory.V.CA.d_ker D (x - y)).2.1.1 h) (Polynomial A) (-1)
      (Polynomial.X ⊗ₜ[A] (1 : E) - 1 ⊗ₜ[A] y)
    unfold Det.chi
    rw [← h2]
    congr 1
    rw [TensorProduct.neg_tmul, TensorProduct.tmul_sub]
    abel
  unfold Det.lam
  rw [hchi]

private theorem sub_mem_ker {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (V : Subgroup G)
    [V.Normal] (hV : ∀ h ∈ V, D.Kills (MonoidAlgebra.single h 1 - 1)) (x : MonoidAlgebra A G) :
    x - MonoidAlgebra.mapDomain (fun q : G ⧸ V => q.out)
      (MonoidAlgebra.mapDomainRingHom A (QuotientGroup.mk' V) x) ∈ D.toDet.ker := by
  have hker : ∀ h ∈ V, MonoidAlgebra.single h (1 : A) - 1 ∈ D.toDet.ker := fun h hh =>
    (UpperTheory.V.CA.d_ker D.toDet _).1.2 ((UpperTheory.V.CA.d_toDet D _).2.2.2.2 (hV h hh))
  rw [MonoidAlgebra.mapDomainRingHom_apply]
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [MonoidAlgebra.mapDomain_add, MonoidAlgebra.mapDomain_add]
    have := D.toDet.ker.add_mem ha hb
    convert this using 1
    abel
  | single g r =>
    rw [MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapDomain_single]
    obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul V g
    have hv' : (QuotientGroup.mk' V g).out = g * v := hv
    rw [hv']
    have heq : MonoidAlgebra.single g r - MonoidAlgebra.single (g * (v : G)) r
        = -(MonoidAlgebra.single g r * (MonoidAlgebra.single (v : G) (1 : A) - 1)) := by
      rw [mul_sub, mul_one, MonoidAlgebra.single_mul_single, mul_one]
      abel
    rw [heq]
    exact D.toDet.ker.neg_mem (D.toDet.ker.mul_mem_left _ _ (hker _ v.2))

theorem UpperTheory.V.Pa.Core.dSees :
    ∀ (n : ℕ) (R G : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (D : GDet n R G) (I : Ideal R), D.IsCont I → ∀ N : ℕ, ∃ V : OpenNormalSubgroup G, Sees D V.toSubgroup (I ^ N) := by
  intro n R G _ _ _ _ _ _ D I hD N
  obtain ⟨V, hV⟩ := UpperTheory.V.CA.exists_openNormalSubgroup_kills_of_groupDetLaw_isCont D I hD N
  refine ⟨V, ?_⟩
  intro i x y hxy
  set f := Ideal.Quotient.mk (I ^ N)
  set D' := D.map f
  have hcomm : ∀ z : MonoidAlgebra R G,
      MonoidAlgebra.mapDomainRingHom (R ⧸ I ^ N) (QuotientGroup.mk' V.toSubgroup)
          (MonoidAlgebra.mapRingHom G f z) =
        MonoidAlgebra.mapRingHom (G ⧸ V.toSubgroup) f
          (MonoidAlgebra.mapDomainRingHom R (QuotientGroup.mk' V.toSubgroup) z) := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g r => simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
  have key : ∀ z : MonoidAlgebra R G, D'.lam i (MonoidAlgebra.mapRingHom G f z) =
      D'.lam i (MonoidAlgebra.mapDomain (fun q : G ⧸ V.toSubgroup => q.out)
        (MonoidAlgebra.mapDomainRingHom (R ⧸ I ^ N) (QuotientGroup.mk' V.toSubgroup)
          (MonoidAlgebra.mapRingHom G f z))) := by
    intro z
    rw [← (UpperTheory.V.CA.d_toDet D' _).2.1 i, ← (UpperTheory.V.CA.d_toDet D' _).2.1 i]
    exact lam_eq_of_ker D'.toDet (sub_mem_ker D' V.toSubgroup hV _) i
  have h1 := key x
  have h2 := key y
  rw [hcomm x, hxy, ← hcomm y, ← h2] at h1
  rw [((UpperTheory.V.CA.d_gmap D).2.2.1 f x).2 i, ((UpperTheory.V.CA.d_gmap D).2.2.1 f y).2 i] at h1
  exact Ideal.Quotient.eq.1 h1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.YPrime
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PrimeApproximation
theorem UpperTheory.Reformulated.B.PrimeApproximation.yPrime_approx :
    ∀ {R σ : Type} [inst : CommRing R] {y : σ → R} {f : R} {BB : Type} [inst_1 : CommRing BB] [inst_2 : Algebra R BB],
      UpperTheory.V.Pa.Core.IsYCpl y f BB →
        ∀ (n : ℕ) (J : Ideal R),
          ∀ x ∈ Ideal.map (Algebra.algebraMap R BB) J,
            ∃ (k : ℕ),
              ∃ a ∈ J,
                (Algebra.algebraMap R BB : R → BB) f ^ k * x - (Algebra.algebraMap R BB : R → BB) a ∈
                  Ideal.map (Algebra.algebraMap R BB) (Ideal.span (Set.range y) ^ n) := by
  intro R σ _ y f BB _ _ h n J x hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨0, a, ha, ?_⟩
    rw [pow_zero, one_mul, sub_self]
    exact Ideal.zero_mem _
  · refine ⟨0, 0, J.zero_mem, ?_⟩
    rw [mul_zero, map_zero, sub_self]
    exact Ideal.zero_mem _
  · rintro u v - - ⟨k, a, ha, hu⟩ ⟨m, b, hb, hv⟩
    refine ⟨k + m, f ^ m * a + f ^ k * b,
      J.add_mem (J.mul_mem_left _ ha) (J.mul_mem_left _ hb), ?_⟩
    have key := Ideal.add_mem _
      (Ideal.mul_mem_left _ (algebraMap R BB f ^ m) hu)
      (Ideal.mul_mem_left _ (algebraMap R BB f ^ k) hv)
    convert key using 1
    simp only [map_add (f := _), map_mul, map_pow]
    ring
  · rintro c u - ⟨k, a, ha, hu⟩
    obtain ⟨j, r, hr⟩ := h.dense n c
    refine ⟨j + k, r * a, J.mul_mem_left _ ha, ?_⟩
    have key := Ideal.add_mem _
      (Ideal.mul_mem_left _ (algebraMap R BB f ^ j * c) hu)
      (Ideal.mul_mem_right (algebraMap R BB a) _ hr)
    convert key using 1
    simp only [map_mul, smul_eq_mul]
    ring
end

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem yPrime_approx {R σ : Type} [CommRing R] {y : σ → R} {f : R} {BB : Type} [CommRing BB]
    [Algebra R BB] (h : IsYCpl y f BB) (n : ℕ) (J : Ideal R) (x : BB) (hx : x ∈ J.map (algebraMap R BB)) :
    ∃ (k : ℕ) (a : R), a ∈ J ∧
      algebraMap R BB f ^ k * x - algebraMap R BB a ∈ (Ideal.span (Set.range y) ^ n).map (algebraMap R BB) :=
  _root_.UpperTheory.Reformulated.B.PrimeApproximation.yPrime_approx h n J x hx

private theorem yPrime_back {R σ : Type} [CommRing R] {y : σ → R} {f : R} {BB : Type} [CommRing BB]
    [Algebra R BB] (h : IsYCpl y f BB) (n : ℕ) (J : Ideal R) (hJ : Ideal.span (Set.range y) ^ n ≤ J)
    (r : R) (hr : algebraMap R BB r ∈ J.map (algebraMap R BB)) : ∃ k : ℕ, f ^ k * r ∈ J := by
  obtain ⟨k, a, ha, h1⟩ := yPrime_approx h n J _ hr
  rw [← map_pow, ← map_mul, ← map_sub] at h1
  obtain ⟨m, hm⟩ := h.strict n _ h1
  refine ⟨m + k, ?_⟩
  convert J.add_mem (hJ hm) (J.mul_mem_left (f ^ m) ha) using 1
  ring

theorem UpperTheory.V.Pa.Core.yPrime :
    ∀ (R σ : Type) [CommRing R] [Fintype σ] (y : σ → R) (f : R) (BB : Type) [CommRing BB] [Algebra R BB], IsYCpl y f BB → ∀ q : Ideal R, q.IsPrime → f ∉ q → (∀ a, y a ∈ q) → (q.map (algebraMap R BB)).IsPrime ∧ (q.map (algebraMap R BB)).comap (algebraMap R BB) = q ∧ (∀ P : Ideal BB, P.IsPrime → (∀ a, algebraMap R BB (y a) ∈ P) → P.comap (algebraMap R BB) ≤ q → P ≤ q.map (algebraMap R BB)) ∧ ∀ (B : Type) [CommRing B] [IsLocalRing B] [Algebra BB B] [Algebra R B] [IsScalarTower R BB B], IsCplAt BB (q.map (algebraMap R BB)) B → IsCplAt R q B := by
  intro R σ _ _ y f BB _ _ h q hq hf hy
  have hI : Ideal.span (Set.range y) ≤ q := by
    rw [Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    exact hy a
  have hfk : ∀ k : ℕ, f ^ k ∉ q := fun k hk => hf (hq.mem_of_pow_mem k hk)
  have hmul : ∀ {s t : R}, s ∉ q → t ∉ q → s * t ∉ q := fun hs ht hst =>
    (hq.mem_or_mem hst).elim hs ht
  have hcom : ∀ r : R, algebraMap R BB r ∈ q.map (algebraMap R BB) → r ∈ q := by
    intro r hr
    obtain ⟨k, hk⟩ := yPrime_back h 1 q (by simpa using hI) r hr
    exact (hq.mem_or_mem hk).resolve_left (hfk k)
  have hcomap : (q.map (algebraMap R BB)).comap (algebraMap R BB) = q :=
    le_antisymm (fun r hr => hcom r hr) Ideal.le_comap_map
  have hIn : ∀ n : ℕ, (Ideal.span (Set.range y) ^ n).map (algebraMap R BB) ≤
      (q ^ n).map (algebraMap R BB) := fun n => Ideal.map_mono (Ideal.pow_right_mono hI n)
  have hI1 : ∀ n : ℕ, (Ideal.span (Set.range y) ^ (n + 1)).map (algebraMap R BB) ≤
      q.map (algebraMap R BB) := fun n =>
    Ideal.map_mono ((Ideal.pow_le_self (Nat.succ_ne_zero n)).trans hI)
  have hI2 : ∀ n : ℕ, (Ideal.span (Set.range y) ^ (n + 1)).map (algebraMap R BB) ≤
      (q ^ n).map (algebraMap R BB) := fun n =>
    (Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ n))).trans (hIn n)
  have hiff : ∀ (n k : ℕ) (x : BB) (r : R), algebraMap R BB f ^ k * x - algebraMap R BB r ∈
      (Ideal.span (Set.range y) ^ (n + 1)).map (algebraMap R BB) →
      (x ∈ q.map (algebraMap R BB) ↔ r ∈ q) := by
    intro n k x r hx
    have h1 := hI1 n hx
    constructor
    · intro hx'
      apply hcom
      have := Ideal.sub_mem _ (Ideal.mul_mem_left _ (algebraMap R BB f ^ k) hx') h1
      simpa using this
    · intro hr
      have := Ideal.add_mem _ h1 (Ideal.mem_map_of_mem (algebraMap R BB) hr)
      rw [sub_add_cancel] at this
      exact (Ideal.unit_mul_mem_iff_mem _ (h.unit.pow k)).1 this
  refine ⟨⟨?_, ?_⟩, hcomap, ?_, ?_⟩
  · intro ht
    apply hq.ne_top
    rw [← hcomap, ht, Ideal.comap_top]
  · intro x z hxz
    obtain ⟨j, r, hr⟩ := h.dense (0 + 1) x
    obtain ⟨k, s, hs⟩ := h.dense (0 + 1) z
    rw [hiff 0 j x r hr, hiff 0 k z s hs]
    apply hq.mem_or_mem
    rw [← hiff 0 (j + k) (x * z) (r * s) ?_]
    · exact hxz
    · convert Ideal.add_mem _ (Ideal.mul_mem_left _ (algebraMap R BB f ^ k * z) hr)
        (Ideal.mul_mem_left _ (algebraMap R BB r) hs) using 1
      simp only [map_mul]
      ring
  · intro P _ hyP hPq x hx
    obtain ⟨j, r, hr⟩ := h.dense (0 + 1) x
    rw [hiff 0 j x r hr]
    apply hPq
    have hIP : (Ideal.span (Set.range y) ^ (0 + 1)).map (algebraMap R BB) ≤ P := by
      rw [zero_add, pow_one, Ideal.map_le_iff_le_comap, Ideal.span_le]
      rintro _ ⟨a, rfl⟩
      exact hyP a
    have := P.sub_mem (P.mul_mem_left (algebraMap R BB f ^ j) hx) (hIP hr)
    rw [Ideal.mem_comap]
    simpa using this
  · intro B _ _ _ _ _ hB
    have hm : ∀ (n : ℕ) (x : BB), x ∈ (q ^ n).map (algebraMap R BB) →
        algebraMap BB B x ∈ maximalIdeal B ^ n := by
      intro n x hx
      have h1 : (q.map (algebraMap R BB)).map (algebraMap BB B) ≤ maximalIdeal B := by
        rw [Ideal.map_le_iff_le_comap, hB.comap_eq]
      apply Ideal.pow_right_mono h1 n
      rw [← Ideal.map_pow, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hx
    refine ⟨hB.noeth, hB.complete, ?_, ?_, ?_⟩
    · rw [IsScalarTower.algebraMap_eq R BB B, ← Ideal.comap_comap, hB.comap_eq, hcomap]
    · intro n b
      obtain ⟨a, s, hs, hb⟩ := hB.dense n b
      obtain ⟨j, s', hs'⟩ := h.dense (n + 1) s
      obtain ⟨k, a', ha'⟩ := h.dense (n + 1) a
      refine ⟨f ^ j * a', f ^ k * s', hmul (hfk k) (fun hh => hs ((hiff n j s s' hs').2 hh)), ?_⟩
      have k1 := hm n _ (hI2 n hs')
      have k2 := hm n _ (hI2 n ha')
      simp only [map_sub, map_mul, map_pow, ← IsScalarTower.algebraMap_apply] at k1 k2
      convert Ideal.add_mem _ (Ideal.sub_mem _
        (Ideal.mul_mem_left _ (algebraMap R B f ^ (j + k)) hb)
        (Ideal.mul_mem_left _ (algebraMap R B f ^ k * b) k1))
        (Ideal.mul_mem_left _ (algebraMap R B f ^ j) k2) using 1
      simp only [map_mul, map_pow]
      ring
    · intro n a ha
      rw [IsScalarTower.algebraMap_apply R BB B] at ha
      obtain ⟨s, hs, hsa⟩ := hB.strict n _ ha
      rw [← Ideal.map_pow] at hsa
      obtain ⟨j, s', hs'⟩ := h.dense (n + 1) s
      have h1 : algebraMap R BB (s' * a) ∈ (q ^ n).map (algebraMap R BB) := by
        convert Ideal.sub_mem _ (Ideal.mul_mem_left _ (algebraMap R BB f ^ j) hsa)
          (Ideal.mul_mem_left _ (algebraMap R BB a) (hI2 n hs')) using 1
        simp only [map_mul]
        ring
      obtain ⟨k, hk⟩ := yPrime_back h n (q ^ n) (Ideal.pow_right_mono hI n) _ h1
      exact ⟨f ^ k * s', hmul (hfk k) (fun hh => hs ((hiff n j s s' hs').2 hh)), by rwa [mul_assoc]⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PmMove
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.pmMove :
    ∀ (BB MM B B' : Type) [CommRing BB] [IsNoetherianRing BB] [AddCommGroup MM] [Module BB MM] [Module.Finite BB MM] [CommRing B] [Algebra BB B] [CommRing B'] [IsLocalRing B'] [Algebra BB B'] (p' : Ideal BB) (Z : Ideal B), IsCplAt BB p' B' → Z.IsPrime → Module.annihilator B (B ⊗[BB] MM) ≤ Z → Z.comap (algebraMap BB B) ≤ p' → ∃ Z' : Ideal B', Z'.IsPrime ∧ Module.annihilator B' (B' ⊗[BB] MM) ≤ Z' ∧ Z'.comap (algebraMap BB B') = Z.comap (algebraMap BB B) := by
  intro BB MM B B' _ _ _ _ _ _ _ _ _ _ p' Z hB' hZ hann hle
  haveI := hZ
  obtain ⟨Q, hQ, hQc⟩ := (IsCplAt.exists_prime_over BB p' B' hB').1 _ (Ideal.IsPrime.comap _) hle
  refine ⟨Q, hQ, ?_, hQc⟩
  let zP : PrimeSpectrum B := ⟨Z, hZ⟩
  let qP : PrimeSpectrum B' := ⟨Q, hQ⟩
  have hz : zP ∈ Module.support B (B ⊗[BB] MM) := Module.mem_support_iff_of_finite.mpr hann
  have hz' := (mem_support_baseChange BB B MM zP).mp hz
  have heq : PrimeSpectrum.comap (algebraMap BB B') qP = PrimeSpectrum.comap (algebraMap BB B) zP :=
    PrimeSpectrum.ext hQc
  have hq : qP ∈ Module.support B' (B' ⊗[BB] MM) := by
    rw [mem_support_baseChange, heq]
    exact hz'
  exact Module.mem_support_iff_of_finite.mp hq
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PatchedModuleAnnihilatorLeComapIffIdealLe
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem ann_baseChange_le_iff (B S : Type) [CommRing B] [CommRing S] [Algebra B S] (M : Type) [AddCommGroup M]
    [Module B M] [Module.Finite B M] (P : Ideal S) (hP : P.IsPrime) :
    Module.annihilator S (S ⊗[B] M) ≤ P ↔ Module.annihilator B M ≤ P.comap (algebraMap B S) := by
  have h := UpperTheory.V.AlgebraTools.mem_support_baseChange B S M ⟨P, hP⟩
  rw [Module.mem_support_iff_of_finite, Module.mem_support_iff_of_finite] at h
  exact h

theorem UpperTheory.V.Pa.Core.patchedModule_annihilator_le_comap_iff_ideal_le :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Function.Surjective m.π → ∀ P : Ideal (Spo A), P.IsPrime → (Module.annihilator W.R (X0 m) ≤ P.comap m.π ↔ J ≤ P.comap (algebraMap B (Spo A))) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m hπ P hP
  have hfin : Module.Finite B A.b.M := by
    letI : Algebra (abelian₂ O Unit D) B := A.b.lam.toRingHom.toAlgebra
    haveI : IsScalarTower (abelian₂ O Unit D) B A.b.M :=
      IsScalarTower.of_algebraMap_smul fun a x => (A.b.smul_lam a x).symm
    haveI := A.b.fin
    exact Module.Finite.of_restrictScalars_finite (abelian₂ O Unit D) B A.b.M
  have h1 : Module.annihilator W.R (X0 m) =
      (Module.annihilator (Spo A) (Spo A ⊗[B] A.b.M)).comap m.π := by
    ext a
    rw [Ideal.mem_comap, Module.mem_annihilator, Module.mem_annihilator]
    exact Iff.rfl
  rw [h1, Ideal.comap_le_comap_iff_of_surjective m.π hπ, ann_baseChange_le_iff B (Spo A) A.b.M P hP]
  exact A.b.supp _ (Ideal.comap_isPrime _ P)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PmFib
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.pmFib :
    ∀ (R σ : Type) [CommRing R] [IsNoetherianRing R] [Fintype σ] (y : σ → R) (f : R) (ii : Ideal R) (X : Type) [AddCommGroup X] [Module R X] [Module.Finite R X] (P : PMod y f ii X) (B : Type) [CommRing B] [Algebra P.BB B] (Q : Ideal B), Q.IsPrime → (∀ a, algebraMap P.BB B (algebraMap R P.BB (y a)) ∈ Q) → (Module.annihilator B (B ⊗[P.BB] P.MM) ≤ Q ↔ Module.annihilator R X ≤ (Q.comap (algebraMap P.BB B)).comap (algebraMap R P.BB)) := by
  intro R σ _ _ _ y f ii X _ _ _ P B _ _ Q hQ hy
  haveI := P.fin
  let Qp : PrimeSpectrum B := ⟨Q, hQ⟩
  let q := PrimeSpectrum.comap (algebraMap P.BB B) Qp
  have h1 := Module.mem_support_iff_of_finite (R := B) (M := B ⊗[P.BB] P.MM) (p := Qp)
  have h2 := mem_support_baseChange P.BB B P.MM Qp
  have h3 := Module.support_quotient (R := P.BB) (M := P.MM)
    (Ideal.span (Set.range fun a => algebraMap R P.BB (y a)))
  have h4 := P.fib.support_eq
  have h5 := mem_support_baseChange R P.BB X q
  have h6 := Module.mem_support_iff_of_finite (R := R) (M := X) (p := PrimeSpectrum.comap (algebraMap R P.BB) q)
  have hz : q ∈ PrimeSpectrum.zeroLocus (Ideal.span (Set.range fun a => algebraMap R P.BB (y a)) : Set P.BB) := by
    rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    exact hy a
  calc Module.annihilator B (B ⊗[P.BB] P.MM) ≤ Q ↔ Qp ∈ Module.support B (B ⊗[P.BB] P.MM) := h1.symm
    _ ↔ q ∈ Module.support P.BB P.MM := h2
    _ ↔ q ∈ Module.support P.BB (P.MM ⧸ (Ideal.span (Set.range fun a => algebraMap R P.BB (y a)) • ⊤ : Submodule P.BB P.MM)) := by
      rw [h3]
      exact ⟨fun h => ⟨h, hz⟩, fun h => h.1⟩
    _ ↔ q ∈ Module.support P.BB (P.BB ⊗[R] X) := by rw [h4]
    _ ↔ PrimeSpectrum.comap (algebraMap R P.BB) q ∈ Module.support R X := h5
    _ ↔ _ := h6
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.ChainAbs
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.chainAbs :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [IsNoetherianRing R] (s : MvPowerSeries σ Λ →+* R) (ii ann : Ideal R) (h d : ℕ) (q : Fin (h + 1) → Ideal R) (o : PatchedSupportCompletions s ii ann q d) (St : Ideal (R ⧸ ii) → Prop) (Th : ∀ i, Ideal (o.B i) → Prop), (∀ i, (q i).IsPrime ∧ ii ≤ q i) → (∀ p p', p ≤ p' → St p' → St p) → (∀ i (Z Q : Ideal (o.B i)), Z.IsPrime → Q.IsPrime → St (Z.comap (algebraMap (R ⧸ ii) (o.B i))) → (d : WithBot ℕ∞) ≤ ringKrullDim (o.B i ⧸ Z) → St (Q.comap (algebraMap (R ⧸ ii) (o.B i))) ∨ Th i Q → Z ≤ Q) → ∀ E : Fin h → Ideal (R ⧸ ii), (∀ i, (E i).IsPrime ∧ (∀ a, Ideal.Quotient.mk ii (s (MvPowerSeries.X a)) ∈ E i) ∧ (E i).comap (Ideal.Quotient.mk ii) ≤ q i.castSucc ∧ (E i).comap (Ideal.Quotient.mk ii) ≤ q i.succ ∧ ∀ Q : Ideal (o.B i.castSucc), Q.IsPrime → Q.comap (algebraMap (R ⧸ ii) _) = E i → Th _ Q) → (∃ p : Ideal (R ⧸ ii), p.IsPrime ∧ (∀ a, Ideal.Quotient.mk ii (s (MvPowerSeries.X a)) ∈ p) ∧ p.comap (Ideal.Quotient.mk ii) ≤ q 0 ∧ St p ∧ ann ≤ p.comap (Ideal.Quotient.mk ii)) → ∀ p : Ideal (R ⧸ ii), p.IsPrime → (∀ a, Ideal.Quotient.mk ii (s (MvPowerSeries.X a)) ∈ p) → p.comap (Ideal.Quotient.mk ii) ≤ q (Fin.last h) → (St p ∨ ∀ Q : Ideal (o.B (Fin.last h)), Q.IsPrime → Q.comap (algebraMap (R ⧸ ii) _) = p → Th _ Q) → ann ≤ p.comap (Ideal.Quotient.mk ii) := by
  intro Λ R σ _ _ _ _ s ii ann h d q o St Th hq hSt hkey E hE h0 p hp hpX hpq hpS
  have hOver : ∀ (j : Fin (h + 1)) (P : Ideal (R ⧸ ii)), P.IsPrime →
      P.comap (Ideal.Quotient.mk ii) ≤ q j →
      ∃ Q : Ideal (o.B j), Q.IsPrime ∧ Q.comap (algebraMap (R ⧸ ii) (o.B j)) = P := by
    intro j P hP hle
    apply (IsCplAt.exists_prime_over (R ⧸ ii) _ (o.B j) (o.cpl j)).1 P hP
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.mem_map_of_mem _ (hle hx)
  have hInv : ∀ j : Fin (h + 1), ∃ Z : Ideal (o.B j), Z.IsPrime ∧ o.S j ≤ Z ∧
      St (Z.comap (algebraMap (R ⧸ ii) (o.B j))) := by
    intro j
    induction j using Fin.induction with
    | zero =>
      obtain ⟨p0, hp0, hp0X, hp0q, hp0St, hp0ann⟩ := h0
      obtain ⟨Q, hQ, hQc⟩ := hOver 0 p0 hp0 hp0q
      refine ⟨Q, hQ, ?_, by rw [hQc]; exact hp0St⟩
      refine (o.fib 0 Q hQ ?_).mpr ?_
      · intro a
        have hx := hp0X a
        rw [← hQc] at hx
        exact hx
      · rw [hQc]
        exact hp0ann
    | succ i ih =>
      obtain ⟨Z, hZ, hSZ, hStZ⟩ := ih
      obtain ⟨hEp, hEX, hEc, hEs, hETh⟩ := hE i
      obtain ⟨Q, hQ, hQc⟩ := hOver i.castSucc (E i) hEp hEc
      have hThQ := hETh Q hQ hQc
      obtain ⟨Z0, hZ0, hZ0le⟩ := Ideal.exists_minimalPrimes_le hSZ
      have hStZ0 := hSt _ _ (Ideal.comap_mono hZ0le) hStZ
      have hZ0Q := hkey i.castSucc Z0 Q hZ0.1.1 hQ hStZ0 (o.dim _ Z0 hZ0) (Or.inr hThQ)
      have hQX : ∀ a, algebraMap (R ⧸ ii) (o.B i.castSucc)
          (Ideal.Quotient.mk ii (s (MvPowerSeries.X a))) ∈ Q := by
        intro a
        have hx := hEX a
        rw [← hQc] at hx
        exact hx
      obtain ⟨Z', hZ', hSZ', hZ'c⟩ := o.move i.castSucc i.succ Z0 Q hZ0.1.1 hQ hZ0.1.2 hZ0Q hQX
        (by rw [hQc]; exact hEs)
      exact ⟨Z', hZ', hSZ', by rw [hZ'c]; exact hStZ0⟩
  obtain ⟨Z, hZ, hSZ, hStZ⟩ := hInv (Fin.last h)
  obtain ⟨Q, hQ, hQc⟩ := hOver (Fin.last h) p hp hpq
  have hQX : ∀ a, algebraMap (R ⧸ ii) (o.B (Fin.last h))
      (Ideal.Quotient.mk ii (s (MvPowerSeries.X a))) ∈ Q := by
    intro a
    have hx := hpX a
    rw [← hQc] at hx
    exact hx
  obtain ⟨Z0, hZ0, hZ0le⟩ := Ideal.exists_minimalPrimes_le hSZ
  have hStZ0 := hSt _ _ (Ideal.comap_mono hZ0le) hStZ
  have hQc' : St (Q.comap (algebraMap (R ⧸ ii) (o.B (Fin.last h)))) ∨ Th (Fin.last h) Q := by
    rcases hpS with h1 | h1
    · left
      rw [hQc]
      exact h1
    · right
      exact h1 Q hQ hQc
  have hZ0Q := hkey (Fin.last h) Z0 Q hZ0.1.1 hQ hStZ0 (o.dim _ Z0 hZ0) hQc'
  have hann := (o.fib _ Q hQ hQX).mp (hZ0.1.2.trans hZ0Q)
  rw [hQc] at hann
  exact hann
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.OutOfNil
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem comap_comap_quot {R B : Type} [CommRing R] [CommRing B] [Algebra R B] (ii : Ideal R)
    (Q : Ideal (B ⧸ ii.map (algebraMap R B))) :
    (Q.comap (algebraMap (R ⧸ ii) (B ⧸ ii.map (algebraMap R B)))).comap (Ideal.Quotient.mk ii) =
      (Q.comap (Ideal.Quotient.mk (ii.map (algebraMap R B)))).comap (algebraMap R B) := by
  ext x
  rfl

private theorem dim_quot {B : Type} [CommRing B] (I S : Ideal B) (h : I ≤ S.radical) (d : WithBot ℕ∞)
    (hd : ∀ P ∈ S.minimalPrimes, d ≤ ringKrullDim (B ⧸ P)) (P : Ideal (B ⧸ I))
    (hP : P ∈ (S.map (Ideal.Quotient.mk I)).minimalPrimes) : d ≤ ringKrullDim ((B ⧸ I) ⧸ P) := by
  rw [Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker] at hP
  obtain ⟨P', hP', rfl⟩ := hP
  have hIP : I ≤ P' := le_sup_right.trans hP'.1.2
  have hmin : P' ∈ S.minimalPrimes := by
    refine ⟨⟨hP'.1.1, le_sup_left.trans hP'.1.2⟩, ?_⟩
    intro Q hQ hQP
    haveI := hQ.1
    exact hP'.2 ⟨hQ.1, sup_le hQ.2 (h.trans ((Ideal.IsPrime.radical_le_iff hQ.1).mpr hQ.2))⟩ hQP
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup I P'), sup_eq_right.mpr hIP]
  exact hd P' hmin

theorem UpperTheory.V.Pa.Core.outOfNil :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [IsNoetherianRing R] (s : MvPowerSeries σ Λ →+* R) (ii ann : Ideal R) (ι : Type) (q : ι → Ideal R) (d : ℕ) (B : ι → Type) [∀ i, CommRing (B i)] [∀ i, IsLocalRing (B i)] [∀ i, Algebra R (B i)] (S : ∀ i, Ideal (B i)), (∀ i, ii ≤ q i) → (∀ i, IsCplAt R (q i) (B i)) → (∀ i, ii ≤ (S i).radical.comap (algebraMap R (B i))) → (∀ i, ∀ P ∈ (S i).minimalPrimes, (d : WithBot ℕ∞) ≤ ringKrullDim (B i ⧸ P)) → (∀ i (Q : Ideal (B i)), Q.IsPrime → ii.map (algebraMap R (B i)) ≤ Q → (∀ a, algebraMap R (B i) (s (MvPowerSeries.X a)) ∈ Q) → (S i ≤ Q ↔ ann ≤ Q.comap (algebraMap R (B i)))) → (∀ i i' (Z Q : Ideal (B i)), Z.IsPrime → Q.IsPrime → S i ≤ Z → Z ≤ Q → (∀ a, algebraMap R (B i) (s (MvPowerSeries.X a)) ∈ Q) → Q.comap (algebraMap R (B i)) ≤ q i' → ∃ Z' : Ideal (B i'), Z'.IsPrime ∧ S i' ≤ Z' ∧ Z'.comap (algebraMap R (B i')) = Z.comap (algebraMap R (B i))) → Nonempty (PatchedSupportCompletions s ii ann q d) := by
  intro Λ R σ _ _ _ _ s ii ann ι q d B _ _ _ S hq hcpl hrad hdim hfib hmove
  let J : ∀ i, Ideal (B i) := fun i => ii.map (algebraMap R (B i))
  have hJmax : ∀ i, J i ≤ maximalIdeal (B i) := by
    intro i
    rw [Ideal.map_le_iff_le_comap, (hcpl i).comap_eq]
    exact hq i
  have hJne : ∀ i, J i ≠ ⊤ := fun i h => (IsLocalRing.maximalIdeal.isMaximal (B i)).ne_top (top_le_iff.mp (h ▸ hJmax i))
  haveI : ∀ i, Nontrivial (B i ⧸ J i) := fun i => Ideal.Quotient.nontrivial_iff.mpr (hJne i)
  haveI : ∀ i, IsLocalRing (B i ⧸ J i) := fun i => .of_surjective' _ Ideal.Quotient.mk_surjective
  have hker : ∀ i, J i ≤ RingHom.ker (Ideal.Quotient.mk (J i)) := fun i => by rw [Ideal.mk_ker]
  have hcomap : ∀ i (Z : Ideal (B i ⧸ J i)),
      (Z.comap (algebraMap (R ⧸ ii) (B i ⧸ J i))).comap (Ideal.Quotient.mk ii) =
        (Z.comap (Ideal.Quotient.mk (J i))).comap (algebraMap R (B i)) :=
    fun i Z => comap_comap_quot ii Z
  have hJle : ∀ i (Z : Ideal (B i ⧸ J i)), J i ≤ Z.comap (Ideal.Quotient.mk (J i)) := by
    intro i Z x hx
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact Z.zero_mem
  have hgen : ∀ i (Q : Ideal (B i ⧸ J i)),
      ((∀ a, algebraMap (R ⧸ ii) (B i ⧸ J i) (Ideal.Quotient.mk ii (s (MvPowerSeries.X a))) ∈ Q) ↔
        ∀ a, algebraMap R (B i) (s (MvPowerSeries.X a)) ∈ Q.comap (Ideal.Quotient.mk (J i))) := by
    intro i Q
    rfl
  refine ⟨⟨fun i => B i ⧸ J i, fun i => ?_, fun i => (S i).map (Ideal.Quotient.mk (J i)), fun i => ?_,
    fun i Q hQ hgQ => ?_, fun i i' Z Q hZ hQ hSZ hZQ hgQ hQq => ?_⟩⟩
  · exact IsCplAt.quotient R (q i) (B i) (R ⧸ ii) ((q i).map (Ideal.Quotient.mk ii)) (B i ⧸ J i) (hcpl i)
      Ideal.Quotient.mk_surjective
      (by
        show Ideal.comap (Ideal.Quotient.mk ii) _ = _
        rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
          Ideal.mk_ker]
        exact sup_eq_left.mpr (hq i))
      Ideal.Quotient.mk_surjective
      (by
        show RingHom.ker (Ideal.Quotient.mk (J i)) = Ideal.map _ (RingHom.ker (Ideal.Quotient.mk ii))
        rw [Ideal.mk_ker, Ideal.mk_ker])
  · intro P hP
    exact dim_quot (J i) (S i) (Ideal.map_le_iff_le_comap.mpr (hrad i)) d (hdim i) P hP
  · haveI := hQ
    rw [Ideal.map_le_iff_le_comap, hcomap]
    exact hfib i _ (Ideal.comap_isPrime _ Q) (hJle i Q) ((hgen i Q).mp hgQ)
  · haveI := hZ
    haveI := hQ
    rw [hcomap] at hQq
    obtain ⟨Z'', hZ''p, hSZ'', hZ''⟩ := hmove i i' (Z.comap (Ideal.Quotient.mk (J i)))
      (Q.comap (Ideal.Quotient.mk (J i))) (Ideal.comap_isPrime _ Z) (Ideal.comap_isPrime _ Q)
      (Ideal.map_le_iff_le_comap.mp hSZ) (Ideal.comap_mono hZQ) ((hgen i Q).mp hgQ) hQq
    have hiiZ : ii ≤ Z''.comap (algebraMap R (B i')) := by
      rw [hZ'', ← Ideal.map_le_iff_le_comap]
      exact hJle i Z
    have hJZ : J i' ≤ Z'' := Ideal.map_le_iff_le_comap.mpr hiiZ
    have hkZ : RingHom.ker (Ideal.Quotient.mk (J i')) ≤ Z'' := by rw [Ideal.mk_ker]; exact hJZ
    refine ⟨Z''.map (Ideal.Quotient.mk (J i')), Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hkZ,
      Ideal.map_mono hSZ'', ?_⟩
    apply Ideal.comap_injective_of_surjective _ (Ideal.Quotient.mk_surjective (I := ii))
    rw [hcomap, hcomap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hkZ, hZ'']
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PatchedLamConjTwistApproxAnnihilated
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem ker_open {l : ℕ} [Fact l.Prime] {Γ S : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CommRing S] (ε : Γ →* ℤ_[l]ˣ) (hε : Continuous ε) (φ : ℤ_[l] →+* S) (j : ℕ) (hφ : φ ((l : ℤ_[l]) ^ j) = 0) :
    IsOpen ((pushCh φ ε).ker : Set Γ) := by
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  have hc : Continuous fun g => ‖((ε g : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ :=
    ((Units.continuous_val.comp hε).sub continuous_const).norm
  have hp : (0 : ℝ) < (l : ℝ) ^ (-(j : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  have ho : IsOpen {g | ‖((ε g : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ < (l : ℝ) ^ (-(j : ℤ))} := isOpen_lt hc continuous_const
  refine Filter.mem_of_superset (ho.mem_nhds (by simpa using hp)) fun g hg => ?_
  have h1 := (PadicInt.norm_le_pow_iff_mem_span_pow _ j).1 (le_of_lt hg)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
  have h2 : φ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
    have := congrArg φ hc
    rw [map_mul, hφ, mul_zero, map_sub, map_one] at this
    exact (sub_eq_zero.1 this.symm)
  exact Units.ext h2

private theorem lam_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G)
    (i : ℕ) (h : H) (a : A) :
    (D.comap φ).lam i (MonoidAlgebra.single h a) = D.lam i (MonoidAlgebra.single (φ h) a) := by
  have : (D.comap φ).chi (MonoidAlgebra.single h a) = D.chi (MonoidAlgebra.single (φ h) a) := by
    change D.D _ (MonoidAlgebra.mapDomainRingHom _ φ _) = D.D _ _
    congr 1
    rw [map_sub]
    simp
  simp only [GDet.lam, this]

private theorem lam_map {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : GDet n A G) (f : A →+* B)
    (i : ℕ) (h : G) (a : A) :
    f (D.lam i (MonoidAlgebra.single h a)) = (D.map f).lam i (MonoidAlgebra.single h (f a)) := by
  rw [← ((UpperTheory.V.CA.d_gmap D).2.2.1 f (MonoidAlgebra.single h a)).2 i, MonoidAlgebra.mapRingHom_single]

theorem UpperTheory.V.Pa.Core.patched_lam_conj_twist_approx_annihilated :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Adapted T (r := r) → ∀ (i : ℕ) (g g' : Ph0 Λ), (g' : Λ.Ph) = Λ.ct * g * Λ.ct⁻¹ → ∀ j : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), ∃ a' : W.R, (W.t.D.lam i (MonoidAlgebra.single g'⁻¹ ((Λ.G.frame.eps O W.R (πo0 Λ g) ^ (1 - (n : ℤ)) : W.Rˣ) : W.R)) - W.t.D.lam i (MonoidAlgebra.single g 1)) - a' ∈ maximalIdeal W.R ^ j ∧ (m.ρ N a' = 0 ∨ ∀ x : (A.A N).M, (fEl (T.Nq N) (A.A N).U * m.ρ N a') ^ A.ex • x = 0) := by
  intro l _ L G0 T Λ n O _ _ _ hO _ r B _ _ _ u J D A W m _ i g g' hg j
  have hlO : (l : O) ∈ maximalIdeal O := by
    haveI := hO.char
    rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ l
  have hlR : (l : W.R) ∈ maximalIdeal W.R := by
    have := map_nonunit (algebraMap O W.R) _ hlO
    rwa [map_natCast] at this
  let q := Ideal.Quotient.mk (maximalIdeal W.R ^ j)
  let φ : ℤ_[l] →+* W.R ⧸ maximalIdeal W.R ^ j := q.comp ((algebraMap O W.R).comp (algebraMap ℤ_[l] O))
  have hφ : φ ((l : ℤ_[l]) ^ j) = 0 := by
    rw [map_pow, map_natCast, ← map_natCast q, ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hlR j)
  let V : OpenNormalSubgroup G0.Γ :=
    { toSubgroup := (pushCh φ G0.ε).ker
      isOpen' := ker_open G0.ε G0.ε_cont φ j hφ
      isNormal' := MonoidHom.normal_ker _ }
  refine (Λ.p_lim V).mono fun N hN => ?_
  have h1 : pushCh φ G0.ε ((T.h N).p (Λ.π N g) * (Λ.h.p (Λ.πo g))⁻¹) = 1 := hN g
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  have h2 : Units.map (q : W.R →* W.R ⧸ maximalIdeal W.R ^ j) ((T.GN N).frame.eps O W.R (πN0 Λ N g)) =
      Units.map (q : W.R →* W.R ⧸ maximalIdeal W.R ^ j) (Λ.G.frame.eps O W.R (πo0 Λ g)) := by
    have h3 := congrArg Units.val h1
    change φ (G0.ε _ : ℤ_[l]ˣ) = φ (G0.ε _ : ℤ_[l]ˣ) at h3
    rw [(T.h N).ε, Λ.h.ε] at h3
    exact Units.ext h3
  refine ⟨W.t.D.lam i (MonoidAlgebra.single g'⁻¹
      (((T.GN N).frame.eps O W.R (πN0 Λ N g) ^ (1 - (n : ℤ)) : W.Rˣ) : W.R)) -
      W.t.D.lam i (MonoidAlgebra.single g 1), ?_, Or.inl ?_⟩
  · rw [sub_sub_sub_cancel_right, ← Ideal.Quotient.eq]
    change q _ = q _
    rw [lam_map, lam_map]
    have h4 := congrArg (fun z : (W.R ⧸ maximalIdeal W.R ^ j)ˣ => ((z ^ (1 - (n : ℤ)) : _ˣ) : W.R ⧸ maximalIdeal W.R ^ j)) h2
    simp only [← map_zpow (Units.map (q : W.R →* W.R ⧸ maximalIdeal W.R ^ j))] at h4
    exact congrArg (fun z => (W.t.D.map q).lam i (MonoidAlgebra.single g'⁻¹ z)) h4.symm
  · rw [map_sub, sub_eq_zero]
    change (m.ρ N).toRingHom _ = (m.ρ N).toRingHom _
    rw [lam_map, lam_map, (m.ρ_maps N).1, lam_comap, lam_comap, map_one, ← (A.A N).p.P i (πN0 Λ N g)]
    have e1 : πN0 Λ N g' = (T.GN N).frame.conj (πN0 Λ N g) := Subtype.ext (by
      change Λ.π N g' = (T.GN N).c * Λ.π N g * (T.GN N).c⁻¹
      rw [hg, map_mul, map_mul, map_inv, Λ.ct_N])
    have e2 : Units.map ((m.ρ N).toRingHom : W.R →* (A.A N).R) ((T.GN N).frame.eps O W.R (πN0 Λ N g)) =
        (T.GN N).frame.eps O (A.A N).R (πN0 Λ N g) := Units.ext ((m.ρ N).commutes _)
    have e3 : (m.ρ N).toRingHom (((T.GN N).frame.eps O W.R (πN0 Λ N g) ^ (1 - (n : ℤ)) : W.Rˣ) : W.R) =
        (((T.GN N).frame.eps O (A.A N).R (πN0 Λ N g) ^ (1 - (n : ℤ)) : (A.A N).Rˣ) : (A.A N).R) := by
      rw [← e2, ← map_zpow (Units.map ((m.ρ N).toRingHom : W.R →* (A.A N).R))]
      rfl
    rw [e3, map_inv, e1]
    congr 1
    simp [GFrame.star, GFrame.starOp]
end
