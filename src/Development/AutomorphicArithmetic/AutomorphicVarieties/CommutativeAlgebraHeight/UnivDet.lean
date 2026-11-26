module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ExistsAdjoinCoeffCharacterSubMemMaximalIdealPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DiffTwoNatural
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ClosureIdeal

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.AevalNat
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section

variable {n : ℕ} {A G : Type} [CommRing A] [Group G]

private noncomputable def pol (D : GDet n A G) (s : Finset G) : MvPolynomial s A :=
  D.D _ (∑ a : s, MonoidAlgebra.single (a : G) (MvPolynomial.X a))

private theorem pol_homog (D : GDet n A G) (s : Finset G) : (pol D s).IsHomogeneous n := by
  have h := (d_poly D.toDet (fun a : s => (MonoidAlgebra.single (a : G) 1 : MonoidAlgebra A G))).1
  have h2 : D.toDet.poly (fun a : s => (MonoidAlgebra.single (a : G) 1 : MonoidAlgebra A G)) = pol D s := by
    change D.D _ (ofT A G _ _) = D.D _ _
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Det.gen, map_sum, ofT_tmul]
  rwa [h2] at h

private theorem nat' (D : GDet n A G) {A' : Type} [CommRing A'] (f : A →+* A') {S S' : Type} [CommRing S]
    [Algebra A S] [CommRing S'] [Algebra A' S'] (φ : S →+* S')
    (h : ∀ a, φ (algebraMap A S a) = algebraMap A' S' (f a)) (y : MonoidAlgebra S G) :
    (D.map f).D S' (MonoidAlgebra.mapRingHom G φ y) = φ (D.D S y) :=
  letI : Algebra A S' := ((algebraMap A' S').comp f).toAlgebra
  D.nat S S' { φ with commutes' := h } y

private theorem pol_map (D : GDet n A G) {A' : Type} [CommRing A'] (f : A →+* A') (s : Finset G) :
    pol (D.map f) s = MvPolynomial.map f (pol D s) := by
  rw [pol, pol, ← nat' D f (MvPolynomial.map f) (by simp)]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum]

private theorem sum_single {S : Type} [CommRing S] (s : Finset G) (y : MonoidAlgebra S G)
    (hy : y.coeff.support ⊆ s) : ∑ a : s, MonoidAlgebra.single (a : G) (y.coeff a) = y := by
  classical
  rw [Finset.sum_coe_sort s (fun a => MonoidAlgebra.single a (y.coeff a))]
  ext g
  simp only [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.1 fun h' => h (hy h')).symm

private theorem pol_eval (D : GDet n A G) (s : Finset G) {S : Type} [CommRing S] [Algebra A S]
    (y : MonoidAlgebra S G) (hy : y.coeff.support ⊆ s) :
    D.D S y = MvPolynomial.aeval (fun a : s => y.coeff a) (pol D s) := by
  rw [pol, ← D.nat]
  congr 1
  conv_lhs => rw [← sum_single s y hy]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum]

private theorem aeval_nat {σ A' : Type} [CommRing A'] (f : A →+* A') {S S' : Type} [CommRing S]
    [Algebra A S] [CommRing S'] [Algebra A' S'] (φ : S →+* S')
    (h : ∀ a, φ (algebraMap A S a) = algebraMap A' S' (f a)) (c : σ → S) (p : MvPolynomial σ A) :
    φ (MvPolynomial.aeval c p) = MvPolynomial.aeval (fun a => φ (c a)) (MvPolynomial.map f p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [h]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.map_X]

private theorem supp_map {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (y : MonoidAlgebra S G) :
    (MonoidAlgebra.mapRingHom G φ y).coeff.support ⊆ y.coeff.support := by
  intro g hg
  rw [Finsupp.mem_support_iff] at hg ⊢
  intro h
  apply hg
  simp [h]

private theorem sep (I : Ideal A) [IsAdicComplete I A] {σ : Type} {p q : MvPolynomial σ A}
    (h : ∀ N : ℕ, MvPolynomial.map (Ideal.Quotient.mk (I ^ N)) p = MvPolynomial.map (Ideal.Quotient.mk (I ^ N)) q) :
    p = q := by
  ext m
  refine sub_eq_zero.1 (IsHausdorff.haus (I := I) inferInstance _ fun N => ?_)
  have := congrArg (AddMonoidAlgebra.coeff · m) (h N)
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map, Ideal.Quotient.eq] at this
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact this

private theorem lim0 (I : Ideal A) [IsAdicComplete I A] (c : ∀ N : ℕ, A ⧸ I ^ N)
    (h : ∀ (N M : ℕ) (h : M ≤ N), Ideal.Quotient.factor (Ideal.pow_le_pow_right h) (c N) = c M) :
    ∃ a : A, ∀ N, Ideal.Quotient.mk (I ^ N) a = c N := by
  choose f hf using fun N => Ideal.Quotient.mk_surjective (c N)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) inferInstance (f := f) (fun {m k} hmk => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq, hf, ← h k m hmk, ← hf k,
      Ideal.Quotient.factor_mk])
  refine ⟨L, fun N => ?_⟩
  have := hL N
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq, hf] at this
  exact this.symm

private theorem lim1 (I : Ideal A) [IsAdicComplete I A] {σ : Type} [Finite σ]
    (c : ∀ N : ℕ, MvPolynomial σ (A ⧸ I ^ N)) (hc : ∀ N, (c N).IsHomogeneous n)
    (h : ∀ (N M : ℕ) (h : M ≤ N),
      MvPolynomial.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right h)) (c N) = c M) :
    ∃ p : MvPolynomial σ A, ∀ N, MvPolynomial.map (Ideal.Quotient.mk (I ^ N)) p = c N := by
  classical
  choose a ha using fun m : σ →₀ ℕ => lim0 I (fun N => (c N).coeff m) fun N M hle => by
    rw [← h N M hle, MvPolynomial.coeff_map]
  refine ⟨∑ m ∈ (Finsupp.finite_of_degree_le (σ := σ) n).toFinset, MvPolynomial.monomial m (a m), fun N => ?_⟩
  ext m
  simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hm
  · exact ha m N
  · rw [map_zero, (hc N).coeff_eq_zero]
    intro hd
    exact hm (by simp [hd])

private theorem lift_ex {S : Type} [CommRing S] [Algebra A S] (y : MonoidAlgebra S G) :
    ∃ y' : MonoidAlgebra (MvPolynomial S A) G, y'.coeff.support ⊆ y.coeff.support ∧
      MonoidAlgebra.mapRingHom G ((MvPolynomial.aeval id : MvPolynomial S A →ₐ[A] S) : MvPolynomial S A →+* S) y' = y := by
  classical
  refine ⟨∑ a : y.coeff.support, MonoidAlgebra.single (a : G) (MvPolynomial.X (y.coeff a)), ?_, ?_⟩
  · intro g hg
    by_contra h
    rw [Finsupp.mem_support_iff] at hg
    apply hg
    simp only [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun a _ => Finsupp.single_eq_of_ne ?_
    rintro rfl
    exact h a.2
  · conv_rhs => rw [← sum_single _ y le_rfl]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]

end

theorem UpperTheory.V.CA.u_lim :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (I : Ideal A) [IsAdicComplete I A] (Ds : ∀ N : ℕ, GDet n (A ⧸ I ^ N) G), (∀ (N M : ℕ) (h : M ≤ N), (Ds N).map (Ideal.Quotient.factor (Ideal.pow_le_pow_right h)) = Ds M) → ∃! D : GDet n A G, ∀ N, D.map (Ideal.Quotient.mk (I ^ N)) = Ds N := by
  intro n A G _ _ I _ Ds hDs
  choose P hP using fun s : Finset G => lim1 I (fun N => pol (Ds N) s) (fun N => pol_homog _ s)
    fun N M h => by rw [← pol_map, hDs N M h]
  have red : ∀ (N : ℕ) (s : Finset G) {S S' : Type} [CommRing S] [Algebra A S] [CommRing S'] [Algebra (A ⧸ I ^ N) S']
      (φ : S →+* S') (_ : ∀ a, φ (algebraMap A S a) = algebraMap _ S' (Ideal.Quotient.mk (I ^ N) a))
      (y : MonoidAlgebra S G), y.coeff.support ⊆ s →
      φ (MvPolynomial.aeval (fun a : s => y.coeff a) (P s)) = (Ds N).D S' (MonoidAlgebra.mapRingHom G φ y) := by
    intro N s S S' _ _ _ _ φ h y hy
    rw [aeval_nat _ φ h, hP, pol_eval _ s _ ((supp_map φ y).trans hy)]
    simp
  have red' : ∀ (N : ℕ) (s : Finset G) {σ : Type} (y : MonoidAlgebra (MvPolynomial σ A) G), y.coeff.support ⊆ s →
      MvPolynomial.map (Ideal.Quotient.mk (I ^ N)) (MvPolynomial.aeval (fun a : s => y.coeff a) (P s)) =
        (Ds N).D _ (MonoidAlgebra.mapRingHom G (MvPolynomial.map (Ideal.Quotient.mk (I ^ N))) y) :=
    fun N s σ y hy => red N s _ (by simp) y hy
  have nat : ∀ (s : Finset G) {S S' : Type} [CommRing S] [Algebra A S] [CommRing S'] [Algebra A S']
      (φ : S →ₐ[A] S') (y : MonoidAlgebra S G),
      MvPolynomial.aeval (fun a : s => (MonoidAlgebra.mapRingHom G (φ : S →+* S') y).coeff a) (P s) =
        φ (MvPolynomial.aeval (fun a : s => y.coeff a) (P s)) := by
    intro s S S' _ _ _ _ φ y
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    simp
  have indep : ∀ (s : Finset G) {S : Type} [CommRing S] [Algebra A S] (y : MonoidAlgebra S G),
      y.coeff.support ⊆ s → MvPolynomial.aeval (fun a : y.coeff.support => y.coeff a) (P _) =
        MvPolynomial.aeval (fun a : s => y.coeff a) (P s) := by
    intro s S _ _ y hy
    obtain ⟨y', h1, h2⟩ := lift_ex (A := A) y
    have e1 := nat s (MvPolynomial.aeval id) y'
    have e2 := nat y.coeff.support (MvPolynomial.aeval id) y'
    rw [h2] at e1 e2
    rw [e1, e2]
    congr 1
    exact sep I fun N => by rw [red' N _ _ h1, red' N _ _ (h1.trans hy)]
  let E : ∀ (S : Type) [CommRing S] [Algebra A S], MonoidAlgebra S G → S :=
    fun S _ _ y => MvPolynomial.aeval (fun a : y.coeff.support => y.coeff a) (P _)
  have Enat : ∀ (S S' : Type) [CommRing S] [Algebra A S] [CommRing S'] [Algebra A S']
      (φ : S →ₐ[A] S') (y : MonoidAlgebra S G), E S' (MonoidAlgebra.mapRingHom G (φ : S →+* S') y) = φ (E S y) :=
    fun S S' _ _ _ _ φ y => (indep _ _ (supp_map _ y)).trans (nat _ φ y)
  have Ered : ∀ (N : ℕ) {σ : Type} (y : MonoidAlgebra (MvPolynomial σ A) G),
      MvPolynomial.map (Ideal.Quotient.mk (I ^ N)) (E _ y) =
        (Ds N).D _ (MonoidAlgebra.mapRingHom G (MvPolynomial.map (Ideal.Quotient.mk (I ^ N))) y) :=
    fun N σ y => red' N _ y le_rfl
  have Eone : ∀ (S : Type) [CommRing S] [Algebra A S], E S 1 = 1 := by
    intro S _ _
    have h1 : E (MvPolynomial S A) 1 = 1 := sep I fun N => by simp only [Ered, map_one]
    have := Enat _ S (MvPolynomial.aeval id) 1
    rwa [h1, map_one, map_one] at this
  have Emul : ∀ (S : Type) [CommRing S] [Algebra A S] (x y), E S (x * y) = E S x * E S y := by
    intro S _ _ x y
    obtain ⟨x', -, rfl⟩ := lift_ex (A := A) x
    obtain ⟨y', -, rfl⟩ := lift_ex (A := A) y
    rw [← map_mul, Enat, Enat, Enat, ← map_mul]
    congr 1
    exact sep I fun N => by simp only [Ered, map_mul]
  have Ehom : ∀ (S : Type) [CommRing S] [Algebra A S] (b : S) (x), E S (b • x) = b ^ n * E S x := by
    intro S _ _ b x
    obtain ⟨x', -, rfl⟩ := lift_ex (A := A) x
    have h1 : E _ ((MvPolynomial.X b : MvPolynomial S A) • x') = MvPolynomial.X b ^ n * E _ x' :=
      sep I fun N => by
        rw [map_mul, map_pow, Ered, Ered, ← (Ds N).homog]
        congr 1
        ext1
        ext1
        simp
    have h2 := Enat _ S (MvPolynomial.aeval id) ((MvPolynomial.X b : MvPolynomial S A) • x')
    rw [h1, map_mul, map_pow, MvPolynomial.aeval_X, ← Enat] at h2
    refine Eq.trans ?_ h2
    congr 1
    ext g
    simp
  refine ⟨⟨fun S _ _ => ⟨⟨E S, Eone S⟩, Emul S⟩, Enat, Ehom⟩, fun N => ?_, ?_⟩
  · ext B _ _ y
    letI : Algebra A B := ((algebraMap (A ⧸ I ^ N) B).comp (Ideal.Quotient.mk (I ^ N))).toAlgebra
    have := red N _ (RingHom.id B) (fun _ => rfl) y le_rfl
    refine Eq.trans this ?_
    congr 1
    ext g
    simp
  · intro D hD
    ext B _ _ y
    have : pol D y.coeff.support = P _ := sep I fun N => by rw [hP, ← pol_map, hD]
    rw [pol_eval D _ y le_rfl, this]
    rfl
end

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

noncomputable section

variable {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ}
  {G : Type} [Group G] [TopologicalSpace G] {Dbar : GDet n (ResidueField O) G}
  {σ : Type} (s : σ → ℕ × G) {A A' : Type} [CommRing A] [Algebra O A] [IsCO O A] [CommRing A'] [Algebra O A'] [IsCO O A']

private def cst (x : ResidueField O) : O := (residue_surjective x).choose

private theorem cst_spec (x : ResidueField O) : algebraMap O (ResidueField O) (cst x) = x :=
  (residue_surjective x).choose_spec

private theorem mem_max_map (f : A →ₐ[O] A') {x : A} : f x ∈ maximalIdeal A' ↔ x ∈ maximalIdeal A := by
  rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]

private theorem pow_le_comap (f : A →ₐ[O] A') (N : ℕ) :
    maximalIdeal A ^ N ≤ (maximalIdeal A' ^ N).comap (f : A →+* A') := by
  refine (Ideal.pow_right_mono ?_ N).trans (Ideal.le_comap_pow _ N)
  intro x hx
  exact (mem_max_map f).2 hx

private theorem mem_pow_map (f : A →ₐ[O] A') (N : ℕ) {x : A} (hx : x ∈ maximalIdeal A ^ N) :
    f x ∈ maximalIdeal A' ^ N := pow_le_comap f N hx

private theorem map_pow_max (f : A →ₐ[O] A') (hf : Function.Surjective f) (N : ℕ) :
    (maximalIdeal A ^ N).map (f : A →+* A') = maximalIdeal A' ^ N := by
  rw [Ideal.map_pow]
  congr 1
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact (mem_max_map f).2 hx
  · intro y hy
    obtain ⟨x, rfl⟩ := hf y
    exact Ideal.mem_map_of_mem _ ((mem_max_map f).1 hy)

private theorem fin_quot (O A : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CommRing A]
    [Algebra O A] [IsCO O A] (N : ℕ) : Finite (A ⧸ maximalIdeal A ^ N) := by
  haveI : Finite (A ⧸ maximalIdeal A) := Finite.of_surjective _ (resMap_bijective O A).2
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) N

private theorem co_trunc (O A : Type) [CommRing O] [IsLocalRing O] [CommRing A]
    [Algebra O A] [IsCO O A] (N : ℕ) : IsCO O (A ⧸ maximalIdeal A ^ (N + 1)) := by
  haveI : Nontrivial (A ⧸ maximalIdeal A ^ (N + 1)) := Ideal.Quotient.nontrivial_iff.2 (by
    intro h
    have h2 := Ideal.pow_le_self (I := maximalIdeal A) (Nat.succ_ne_zero N)
    rw [h, top_le_iff] at h2
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top h2)
  exact co_quot O A _ (Ideal.Quotient.mkₐ O _) (Ideal.Quotient.mkₐ_surjective O _)

private theorem trunc_pow (N : ℕ) [IsCO O (A ⧸ maximalIdeal A ^ N)] :
    maximalIdeal (A ⧸ maximalIdeal A ^ N) ^ N = ⊥ := by
  rw [← map_pow_max (Ideal.Quotient.mkₐ O (maximalIdeal A ^ N)) (Ideal.Quotient.mkₐ_surjective O _)]
  exact Ideal.map_quotient_self _

private theorem res_self [IsCO O (ResidueField O)] (x : ResidueField O) : res O (ResidueField O) x = x := by
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  exact (res O (ResidueField O)).commutes a

private theorem isDef_iff (D : GDet n A G) : IsDef O Dbar D ↔
    (∀ i, AdicCont (maximalIdeal A) fun g => coord D (i, g)) ∧ ∀ t, res O A (coord D t) = coord Dbar t := by
  constructor
  · rintro ⟨hc, hr⟩
    refine ⟨fun i => hc i, fun t => ?_⟩
    rw [← hr, coord_map] <;> rfl
  · rintro ⟨hc, hr⟩
    refine ⟨fun i => hc i, coord_ext fun t => ?_⟩
    rw [coord_map]
    exact hr t

omit [TopologicalSpace G] [IsLocalRing O] [IsCO O A] [IsCO O A'] in
private theorem coord_mapA (D : GDet n A G) (f : A →ₐ[O] A') (t : ℕ × G) :
    coord (D.map (f : A →+* A')) t = f (coord D t) := coord_map D _ t

private theorem isDef_map {D : GDet n A G} (h : IsDef O Dbar D) (f : A →ₐ[O] A') :
    IsDef O Dbar (D.map (f : A →+* A')) := by
  rw [isDef_iff] at h ⊢
  refine ⟨fun i N => ?_, fun t => by rw [coord_mapA, res_map, h.2]⟩
  simp only [coord_mapA]
  exact (h.1 i N).comp (Ideal.quotientMap _ (f : A →+* A') (pow_le_comap f N))

private def IsEv (Dbar : GDet n (ResidueField O) G) (D : GDet n A G) (F : MvPowerSeries σ O →ₐ[O] A) : Prop :=
  ∀ t : σ, F (MvPowerSeries.X t) = coord D (s t) - algebraMap O A (cst (coord Dbar (s t)))

private def Gen (O : Type) [CommRing O] [IsLocalRing O] [Algebra O A] (D : GDet n A G) : Prop :=
  ∀ f f' : A →ₐ[O] DualNumber (ResidueField O), (∀ t, f (coord D t) = f' (coord D t)) → f = f'

private theorem sub_cst_mem {D : GDet n A G} (h : IsDef O Dbar D) (t : ℕ × G) :
    coord D t - algebraMap O A (cst (coord Dbar t)) ∈ maximalIdeal A := by
  rw [← res_eq_zero_iff O A, map_sub, AlgHom.commutes, cst_spec, ((isDef_iff D).1 h).2 t, sub_self]

omit [TopologicalSpace G] in
private theorem IsEv.map {D : GDet n A G} {F : MvPowerSeries σ O →ₐ[O] A} (h : IsEv s Dbar D F)
    (f : A →ₐ[O] A') : IsEv s Dbar (D.map (f : A →+* A')) (f.comp F) := fun t => by
  rw [AlgHom.comp_apply, h t, map_sub, AlgHom.commutes, coord_mapA]

omit [TopologicalSpace G] in
private theorem Gen.surj {D : GDet n A G} (f : A →ₐ[O] A') (h : Gen O (D.map (f : A →+* A'))) :
    Function.Surjective f := by
  apply co_surj O A A' f
  have key := co_span O A' A f ∅ (Set.empty_subset _) (fun f1 f2 hc _ => h f1 f2 (fun t => by
    rw [coord_mapA]
    exact congrArg (fun φ : A →ₐ[O] DualNumber (ResidueField O) => φ (coord D t)) hc))
  simpa using key

private theorem pair [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (N : ℕ) {D : GDet n A G} {D' : GDet n A' G}
    (h : IsDef O Dbar D) (h' : IsDef O Dbar D') (k : maximalIdeal A ^ (N + 1) = ⊥)
    (k' : maximalIdeal A' ^ (N + 1) = ⊥) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra O B) (_ : IsCO O B) (E : GDet n B G) (p : B →ₐ[O] A)
      (p' : B →ₐ[O] A'), IsDef O Dbar E ∧ maximalIdeal B ^ (N + 1) = ⊥ ∧ Gen O E ∧
        E.map (p : B →+* A) = D ∧ E.map (p' : B →+* A') = D' := by
  classical
  haveI hd : IsCO O (DualNumber (ResidueField O)) := (co_res O).2
  obtain ⟨H, hH⟩ := exists_comap_level D (maximalIdeal A) h.cont k
  obtain ⟨H', hH'⟩ := exists_comap_level D' (maximalIdeal A') h'.cont k'
  let K : Subgroup G := (H.toOpenSubgroup : Subgroup G) ⊓ (H'.toOpenSubgroup : Subgroup G)
  haveI hKn : K.Normal := inferInstance
  have hKo : IsOpen (K : Set G) := H.toOpenSubgroup.isOpen.inter H'.toOpenSubgroup.isOpen
  haveI : Finite (G ⧸ K) := Subgroup.quotient_finite_of_isOpen K hKo
  obtain ⟨D0, hD0⟩ := hH K inf_le_left
  obtain ⟨D0', hD0'⟩ := hH' K inf_le_right
  have lc : ∀ {X : Type} (φ : G ⧸ K → X), IsLocallyConstant (fun g : G => φ (QuotientGroup.mk g)) := by
    intro X φ
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have ho : IsOpen ((fun y => x * y) '' (K : Set G)) := (Homeomorph.mulLeft x).isOpenMap _ hKo
    filter_upwards [ho.mem_nhds ⟨1, K.one_mem, mul_one x⟩] with y hy
    obtain ⟨c, hc, rfl⟩ := hy
    congr 1
    exact QuotientGroup.eq.2 (by rw [mul_inv_rev, inv_mul_cancel_right]; exact K.inv_mem hc)
  letI : TopologicalSpace (G ⧸ K) := ⊥
  haveI : DiscreteTopology (G ⧸ K) := ⟨rfl⟩
  have inj : ∀ {C : Type} [CommRing C] (X Y : GDet n C (G ⧸ K)),
      X.comap (QuotientGroup.mk' K) = Y.comap (QuotientGroup.mk' K) → X = Y := by
    intro C _ X Y hXY
    refine coord_ext fun t => ?_
    obtain ⟨i, q⟩ := t
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have e := congrArg (fun Z => coord Z (i, g)) hXY
    simpa [coord_comap] using e
  have cm : ∀ {C C' : Type} [CommRing C] [CommRing C'] (X : GDet n C (G ⧸ K)) (ψ : C →+* C'),
      (X.map ψ).comap (QuotientGroup.mk' K) = (X.comap (QuotientGroup.mk' K)).map ψ := by
    intro C C' _ _ X ψ
    refine coord_ext fun t => ?_
    simp [coord_comap, coord_map]
  obtain ⟨Dbar0, hDbar0def⟩ : ∃ X : GDet n (ResidueField O) (G ⧸ K), X = D0.map ↑(res O A) := ⟨_, rfl⟩
  have hDbar0 : Dbar0.comap (QuotientGroup.mk' K) = Dbar := by
    rw [hDbar0def, cm, hD0, h.red]
  have hDbar0' : D0'.map ↑(res O A') = Dbar0 := by
    apply inj
    rw [cm, hD0', h'.red, hDbar0]
  have hd0 : IsDef O Dbar0 D0 := ⟨fun i M => IsLocallyConstant.of_discrete _, hDbar0def.symm⟩
  have hd0' : IsDef O Dbar0 D0' := ⟨fun i M => IsLocallyConstant.of_discrete _, hDbar0'⟩
  obtain ⟨R, _, _, _, DU, hU⟩ := u_fin O Dbar0
  obtain ⟨f, hf, -⟩ := hU.univ A D0 hd0
  obtain ⟨f', hf', -⟩ := hU.univ A' D0' hd0'
  let I : Ideal R := RingHom.ker (f : R →+* A) ⊓ RingHom.ker (f' : R →+* A')
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 (by
    intro hI
    have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
    have h2 := (RingHom.mem_ker).1 (Ideal.mem_inf.1 h1).1
    rw [map_one] at h2
    exact one_ne_zero h2)
  haveI : IsCO O (R ⧸ I) := co_quot O R (R ⧸ I) (Ideal.Quotient.mkₐ O I) (Ideal.Quotient.mkₐ_surjective O I)
  let E : GDet n (R ⧸ I) G := (DU.map (Ideal.Quotient.mkₐ O I : R →+* R ⧸ I)).comap (QuotientGroup.mk' K)
  have hEc : ∀ i (g : G), coord E (i, g) = Ideal.Quotient.mkₐ O I (coord DU (i, (g : G ⧸ K))) := by
    intro i g
    rw [coord_comap, coord_mapA] <;> rfl
  let p : R ⧸ I →ₐ[O] A := Ideal.Quotient.liftₐ I f (fun a ha => (RingHom.mem_ker).1 (Ideal.mem_inf.1 ha).1)
  let p' : R ⧸ I →ₐ[O] A' := Ideal.Quotient.liftₐ I f' (fun a ha => (RingHom.mem_ker).1 (Ideal.mem_inf.1 ha).2)
  refine ⟨R ⧸ I, inferInstance, inferInstance, inferInstance, E, p, p', ⟨fun i M => ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · show IsLocallyConstant fun g : G => Ideal.Quotient.mk (maximalIdeal (R ⧸ I) ^ M) (coord E (i, g))
    simp only [hEc]
    exact lc (fun q => Ideal.Quotient.mk (maximalIdeal (R ⧸ I) ^ M) (Ideal.Quotient.mkₐ O I (coord DU (i, q))))
  · refine coord_ext fun t => ?_
    obtain ⟨i, g⟩ := t
    rw [coord_mapA, hEc, res_map, ← hDbar0, coord_comap, ← hU.isDef.red, coord_mapA] <;> rfl
  · have hle : maximalIdeal R ^ (N + 1) ≤ I := fun x hx => Ideal.mem_inf.2
      ⟨(RingHom.mem_ker).2 (by
          have hm := mem_pow_map f (N + 1) hx
          rw [k] at hm
          exact (Ideal.mem_bot).1 hm),
       (RingHom.mem_ker).2 (by
          have hm := mem_pow_map f' (N + 1) hx
          rw [k'] at hm
          exact (Ideal.mem_bot).1 hm)⟩
    rw [← map_pow_max (Ideal.Quotient.mkₐ O I) (Ideal.Quotient.mkₐ_surjective O I) (N + 1)]
    exact eq_bot_iff.2 ((Ideal.map_mono hle).trans (Ideal.map_quotient_self I).le)
  · intro f1 f2 hf12
    have hc1 : ∀ t : ℕ × (G ⧸ K), (f1.comp (Ideal.Quotient.mkₐ O I)) (coord DU t) =
        (f2.comp (Ideal.Quotient.mkₐ O I)) (coord DU t) := by
      rintro ⟨i, q⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      have e := hf12 (i, g)
      rw [hEc] at e
      exact e
    have hd1 := isDef_map hU.isDef (f1.comp (Ideal.Quotient.mkₐ O I))
    have heq : DU.map (f2.comp (Ideal.Quotient.mkₐ O I) : R →+* DualNumber (ResidueField O)) =
        DU.map (f1.comp (Ideal.Quotient.mkₐ O I) : R →+* DualNumber (ResidueField O)) :=
      coord_ext fun t => by
        rw [coord_mapA, coord_mapA]
        exact (hc1 t).symm
    have e := (hU.univ _ _ hd1).unique rfl heq
    refine AlgHom.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective O I x
    exact congrArg (fun φ : R →ₐ[O] DualNumber (ResidueField O) => φ a) e
  · refine coord_ext fun t => ?_
    obtain ⟨i, g⟩ := t
    rw [coord_mapA, hEc]
    show f (coord DU (i, (g : G ⧸ K))) = _
    rw [← coord_mapA DU f, hf, ← hD0, coord_comap] <;> rfl
  · refine coord_ext fun t => ?_
    obtain ⟨i, g⟩ := t
    rw [coord_mapA, hEc]
    show f' (coord DU (i, (g : G ⧸ K))) = _
    rw [← coord_mapA DU f', hf', ← hD0', coord_comap] <;> rfl

variable [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite σ]

private theorem ev_exu {D : GDet n A G} (h : IsDef O Dbar D) : ∃! F, IsEv s Dbar D F := by
  obtain ⟨F, ⟨-, h1⟩, hu⟩ := co_ev O O A σ (Algebra.ofId O A) _ fun t => sub_cst_mem h (s t)
  exact ⟨F, h1, fun G hG => hu G ⟨fun x => G.commutes x, hG⟩⟩

private instance : IsCO O (MvPowerSeries σ O) := co_mvps O O _

private def Seps (Dbar : GDet n (ResidueField O) G) [IsCO O (DualNumber (ResidueField O))] (s : σ → ℕ × G) : Prop :=
  ∀ D D' : GDet n (DualNumber (ResidueField O)) G, IsDef O Dbar D → IsDef O Dbar D' →
    (∀ t, coord D (s t) = coord D' (s t)) → D = D'

variable [IsCO O (DualNumber (ResidueField O))]

private theorem ev_surj (hs : Seps Dbar s) {D : GDet n A G} (hD : IsDef O Dbar D) (hr : Gen O D)
    {F : MvPowerSeries σ O →ₐ[O] A} (h : IsEv s Dbar D F) : Function.Surjective F := by
  apply co_surj O (MvPowerSeries σ O) A F
  have key := co_span O A (MvPowerSeries σ O) F ∅ (Set.empty_subset _) (fun f1 f2 hc _ => hr f1 f2 (fun t => by
    have e := hs _ _ (isDef_map hD f1) (isDef_map hD f2) (fun u => by
      rw [coord_mapA, coord_mapA]
      have hu : coord D (s u) = F (MvPowerSeries.X u) + algebraMap O A (cst (coord Dbar (s u))) := by
        rw [h u]
        ring
      rw [hu, map_add (f := _), map_add (f := _), AlgHom.commutes, AlgHom.commutes]
      congr 1
      exact congrArg (fun φ : MvPowerSeries σ O →ₐ[O] DualNumber (ResidueField O) => φ (MvPowerSeries.X u)) hc)
    have e2 := congrArg (fun E => coord E t) e
    simpa [coord_mapA] using e2))
  simpa using key

private theorem level [Finite (ResidueField O)] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (hs : Seps Dbar s) (hc : Dbar.IsCont (maximalIdeal (ResidueField O))) (N : ℕ) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra O A) (_ : IsCO O A) (D : GDet n A G), IsDef O Dbar D ∧
      maximalIdeal A ^ (N + 1) = ⊥ ∧ Gen O D ∧ ∀ (A' : Type) [CommRing A'] [Algebra O A'] [IsCO O A']
        (D' : GDet n A' G), IsDef O Dbar D' → maximalIdeal A' ^ (N + 1) = ⊥ →
          ∃ f : A →ₐ[O] A', D.map (f : A →+* A') = D' := by
  classical
  haveI hk : IsCO O (ResidueField O) := (co_res O).1
  haveI hQ : Finite (MvPowerSeries σ O ⧸ maximalIdeal (MvPowerSeries σ O) ^ (N + 1)) :=
    fin_quot O (MvPowerSeries σ O) (N + 1)
  have bound : ∀ (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (E : GDet n B G), IsDef O Dbar E →
      maximalIdeal B ^ (N + 1) = ⊥ → Gen O E →
        Finite B ∧ Nat.card B ≤ Nat.card (MvPowerSeries σ O ⧸ maximalIdeal (MvPowerSeries σ O) ^ (N + 1)) := by
    intro B _ _ _ E hE hN hG
    obtain ⟨F, hF, -⟩ := ev_exu s hE
    have hs' := ev_surj s hs hE hG hF
    let q : MvPowerSeries σ O ⧸ maximalIdeal (MvPowerSeries σ O) ^ (N + 1) →+* B :=
      Ideal.Quotient.lift _ (F : MvPowerSeries σ O →+* B) (fun a ha => by
        have hm := mem_pow_map F (N + 1) ha
        rw [hN] at hm
        exact (Ideal.mem_bot).1 hm)
    have hq : Function.Surjective q := by
      intro b
      obtain ⟨a, rfl⟩ := hs' b
      exact ⟨Ideal.Quotient.mk _ a, rfl⟩
    exact ⟨Finite.of_surjective q hq, Nat.card_le_card_of_surjective q hq⟩
  let T : Set ℕ := {c | ∃ (B : Type) (_ : CommRing B) (_ : Algebra O B) (_ : IsCO O B) (E : GDet n B G),
      IsDef O Dbar E ∧ maximalIdeal B ^ (N + 1) = ⊥ ∧ Gen O E ∧ Nat.card B = c}
  have hne : T.Nonempty := by
    refine ⟨_, ResidueField O, inferInstance, inferInstance, hk, Dbar, ⟨hc, coord_ext fun t => ?_⟩, ?_, ?_, rfl⟩
    · rw [coord_map]
      exact res_self _
    · refine eq_bot_iff.2 fun x hx => ?_
      have hx' := Ideal.pow_le_self (Nat.succ_ne_zero N) hx
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not] at hx'
      exact (Ideal.mem_bot).2 hx'
    · intro f f' _
      refine AlgHom.ext fun x => ?_
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
      exact (f.commutes a).trans (f'.commutes a).symm
  have hbdd : BddAbove T := by
    refine ⟨Nat.card (MvPowerSeries σ O ⧸ maximalIdeal (MvPowerSeries σ O) ^ (N + 1)), ?_⟩
    rintro c ⟨B, _, _, _, E, h1, h2, h3, rfl⟩
    exact (bound B E h1 h2 h3).2
  obtain ⟨A, _, _, _, D, hD, hN, hG, hcard⟩ := Nat.sSup_mem hne hbdd
  refine ⟨A, _, _, _, D, hD, hN, hG, fun A' _ _ _ D' hD' hN' => ?_⟩
  obtain ⟨B, _, _, _, E, p, p', hE, hEN, hEG, hp, hp'⟩ := pair N hD hD' hN hN'
  have hps : Function.Surjective p := Gen.surj p (by rw [hp]; exact hG)
  have hB := bound B E hE hEN hEG
  haveI := hB.1
  have hle : Nat.card B ≤ Nat.card A := by
    rw [hcard]
    exact le_csSup hbdd ⟨B, _, _, _, E, hE, hEN, hEG, rfl⟩
  have hbij := hps.bijective_of_nat_card_le hle
  refine ⟨p'.comp (AlgEquiv.ofBijective p hbij).symm.toAlgHom, coord_ext fun t => ?_⟩
  rw [coord_mapA, ← hp, ← hp', coord_mapA, coord_mapA, AlgHom.comp_apply]
  congr 1
  exact (AlgEquiv.ofBijective p hbij).symm_apply_apply (coord E t)

private theorem assemble (hs : Seps Dbar s) (A : ℕ → Type) [∀ N, CommRing (A N)] [∀ N, Algebra O (A N)]
    [∀ N, IsCO O (A N)] (r : ∀ N, GDet n (A N) G) (h0 : ∀ N, IsDef O Dbar (r N))
    (h1 : ∀ N, maximalIdeal (A N) ^ (N + 1) = ⊥)
    (h2 : ∀ N, Gen O (r N)) (h3 : ∀ N (A' : Type) [CommRing A'] [Algebra O A'] [IsCO O A']
        (D' : GDet n A' G), IsDef O Dbar D' → maximalIdeal A' ^ (N + 1) = ⊥ →
          ∃ f : A N →ₐ[O] A', (r N).map (f : A N →+* A') = D') :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (D : GDet n R G), IsUnivDet O Dbar D := by
  classical
  have hev := fun N => ev_exu s (h0 N)
  choose F hF hFu using hev
  have hFs : ∀ N, Function.Surjective (F N) := fun N => ev_surj s hs (h0 N) (h2 N) (hF N)
  have evu : ∀ (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (E : GDet n B G), IsDef O Dbar E →
      ∀ G1 G2 : MvPowerSeries σ O →ₐ[O] B, IsEv s Dbar E G1 → IsEv s Dbar E G2 → G1 = G2 := by
    intro B _ _ _ E hE G1 G2 e1 e2
    obtain ⟨G0, -, hu⟩ := ev_exu s hE
    rw [hu G1 e1, hu G2 e2]
  have hJ1 : ∀ N, maximalIdeal (MvPowerSeries σ O) ^ (N + 1) ≤
      RingHom.ker (F N : MvPowerSeries σ O →+* A N) := by
    intro N x hx
    have hm := mem_pow_map (F N) (N + 1) hx
    rw [h1 N] at hm
    exact (RingHom.mem_ker).2 ((Ideal.mem_bot).1 hm)
  have trans : ∀ M N, M ≤ N → ∃ g : A N →ₐ[O] A M, (r N).map (g : A N →+* A M) = r M ∧ g.comp (F N) = F M := by
    intro M N hMN
    have hpow : maximalIdeal (A M) ^ (N + 1) = ⊥ :=
      eq_bot_iff.2 ((Ideal.pow_le_pow_right (by omega)).trans (h1 M).le)
    obtain ⟨g, hg⟩ := h3 N (A M) (r M) (h0 M) hpow
    refine ⟨g, hg, ?_⟩
    apply evu (A M) (r M) (h0 M)
    · rw [← hg]
      exact IsEv.map s (hF N) g
    · exact hF M
  have hJmono : ∀ M N, M ≤ N → RingHom.ker (F N : MvPowerSeries σ O →+* A N) ≤
      RingHom.ker (F M : MvPowerSeries σ O →+* A M) := by
    intro M N hMN x hx
    obtain ⟨g, -, hg⟩ := trans M N hMN
    have e := congrArg (fun φ : MvPowerSeries σ O →ₐ[O] A M => φ x) hg
    simp only [AlgHom.comp_apply] at e
    rw [RingHom.mem_ker]
    show F M x = 0
    rw [← e, show F N x = 0 from hx, map_zero]
  have hJ2 : ∀ N, RingHom.ker (F N : MvPowerSeries σ O →+* A N) ≤
      RingHom.ker (F (N + 1) : MvPowerSeries σ O →+* A (N + 1)) ⊔ maximalIdeal (MvPowerSeries σ O) ^ (N + 1) := by
    intro N x hx
    haveI : IsCO O (A (N + 1) ⧸ maximalIdeal (A (N + 1)) ^ (N + 1)) := co_trunc O (A (N + 1)) N
    have hdq := isDef_map (h0 (N + 1)) (Ideal.Quotient.mkₐ O (maximalIdeal (A (N + 1)) ^ (N + 1)))
    obtain ⟨g, hg⟩ := h3 N _ _ hdq (trunc_pow (O := O) (A := A (N + 1)) (N + 1))
    have heq : g.comp (F N) = (Ideal.Quotient.mkₐ O (maximalIdeal (A (N + 1)) ^ (N + 1))).comp (F (N + 1)) := by
      apply evu _ _ hdq
      · rw [← hg]
        exact IsEv.map s (hF N) g
      · exact IsEv.map s (hF (N + 1)) _
    have h0x : (Ideal.Quotient.mkₐ O (maximalIdeal (A (N + 1)) ^ (N + 1))) (F (N + 1) x) = 0 := by
      rw [← AlgHom.comp_apply, ← heq, AlgHom.comp_apply, show F N x = 0 from hx, map_zero]
    simp only [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at h0x
    rw [← map_pow_max (F (N + 1)) (hFs (N + 1)) (N + 1)] at h0x
    obtain ⟨y, hy, hFy⟩ := (Ideal.mem_map_iff_of_surjective _ (hFs (N + 1))).1 h0x
    have hxy : x - y + y = x := by ring
    rw [← hxy]
    refine Submodule.add_mem_sup ?_ hy
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact hFy.symm
  obtain ⟨Kinf, hKinf⟩ : ∃ K : Ideal (MvPowerSeries σ O), K = ⨅ N, RingHom.ker (F N : MvPowerSeries σ O →+* A N) :=
    ⟨_, rfl⟩
  have hKJ : ∀ N, Kinf ≤ RingHom.ker (F N : MvPowerSeries σ O →+* A N) := by
    intro N
    rw [hKinf]
    exact iInf_le _ N
  haveI hpre : IsPrecomplete (maximalIdeal (MvPowerSeries σ O)) (MvPowerSeries σ O) :=
    (inferInstance : IsCO O (MvPowerSeries σ O)).complete.toIsPrecomplete
  have hJK : ∀ N₀, RingHom.ker (F N₀ : MvPowerSeries σ O →+* A N₀) ≤
      Kinf ⊔ maximalIdeal (MvPowerSeries σ O) ^ (N₀ + 1) := by
    intro N₀ y hy
    have hJ2' : ∀ k (a : MvPowerSeries σ O), a ∈ RingHom.ker (F k : MvPowerSeries σ O →+* A k) →
        ∃ b, b ∈ RingHom.ker (F (k + 1) : MvPowerSeries σ O →+* A (k + 1)) ∧
          a - b ∈ maximalIdeal (MvPowerSeries σ O) ^ (k + 1) := by
      intro k a ha
      obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.1 (hJ2 k ha)
      exact ⟨b, hb, by simpa using hc⟩
    choose! st hst1 hst2 using hJ2'
    let q : ℕ → MvPowerSeries σ O := fun j => Nat.rec y (fun j a => st (N₀ + j) a) j
    have hq : ∀ j, q j ∈ RingHom.ker (F (N₀ + j) : MvPowerSeries σ O →+* A (N₀ + j)) := by
      intro j
      induction j with
      | zero => exact hy
      | succ j ih => exact hst1 (N₀ + j) (q j) ih
    obtain ⟨x, hx1, hx2⟩ := UpperTheory.exists_limit_of_successive_diff_mem_filtration (MvPowerSeries σ O) (maximalIdeal (MvPowerSeries σ O))
      (fun N => RingHom.ker (F N : MvPowerSeries σ O →+* A N)) hJ1 hJ2 N₀ (fun N => q (N - N₀)) (by
        intro N hN
        obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hN
        show q (N₀ + j + 1 - N₀) - q (N₀ + j - N₀) ∈ RingHom.ker (F (N₀ + j) : MvPowerSeries σ O →+* A (N₀ + j))
        rw [show N₀ + j + 1 - N₀ = j + 1 by omega, show N₀ + j - N₀ = j by omega]
        change st (N₀ + j) (q j) - q j ∈ _
        rw [← neg_sub]
        exact (Ideal.neg_mem_iff _).2 (hJ1 _ (hst2 (N₀ + j) (q j) (hq j))))
    have hx2' : x - y ∈ maximalIdeal (MvPowerSeries σ O) ^ (N₀ + 1) := by
      have e := hx2
      simp only [Nat.sub_self] at e
      exact e
    have hxK : x ∈ Kinf := by
      rw [hKinf, Submodule.mem_iInf]
      intro N
      rcases le_or_gt N₀ N with hN | hN
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hN
        have e := hx1 (N₀ + j) hN
        simp only [show N₀ + j - N₀ = j by omega] at e
        have e2 := Ideal.add_mem _ e (hq j)
        simpa using e2
      · apply hJmono N N₀ hN.le
        have e := hx1 N₀ le_rfl
        simp only [Nat.sub_self] at e
        have e' : x - y ∈ RingHom.ker (F N₀ : MvPowerSeries σ O →+* A N₀) := e
        have e2 := Ideal.add_mem _ e' hy
        simpa using e2
    have hyx : x + (y - x) = y := by ring
    rw [← hyx]
    exact Submodule.add_mem_sup hxK (by rw [← neg_sub]; exact (Ideal.neg_mem_iff _).2 hx2')
  have hausd : ∀ (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (x : B),
      (∀ N, x ∈ maximalIdeal B ^ (N + 1)) → x = 0 := by
    intro B _ _ hB x hx
    apply hB.complete.toIsHausdorff.haus
    intro N
    simp only [SModEq.sub_mem, sub_zero, Ideal.smul_eq_mul, Ideal.mul_top]
    cases N with
    | zero => simp
    | succ N => exact hx N
  have hKtop : Kinf ≠ ⊤ := by
    intro hK
    have h1' : (1 : MvPowerSeries σ O) ∈ RingHom.ker (F 0 : MvPowerSeries σ O →+* A 0) :=
      hKJ 0 (hK ▸ Submodule.mem_top)
    rw [RingHom.mem_ker, map_one] at h1'
    exact one_ne_zero h1'
  haveI : Nontrivial (MvPowerSeries σ O ⧸ Kinf) := Ideal.Quotient.nontrivial_iff.2 hKtop
  haveI hR : IsCO O (MvPowerSeries σ O ⧸ Kinf) :=
    co_quot O _ _ (Ideal.Quotient.mkₐ O Kinf) (Ideal.Quotient.mkₐ_surjective O Kinf)
  let ρ : ∀ N, MvPowerSeries σ O ⧸ Kinf →ₐ[O] A N := fun N =>
    Ideal.Quotient.liftₐ Kinf (F N) (fun a ha => (RingHom.mem_ker).1 (hKJ N ha))
  have hkerρ : ∀ N (x : MvPowerSeries σ O ⧸ Kinf), ρ N x = 0 →
      x ∈ maximalIdeal (MvPowerSeries σ O ⧸ Kinf) ^ (N + 1) := by
    intro N x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective O Kinf x
    have ha : a ∈ RingHom.ker (F N : MvPowerSeries σ O →+* A N) := (RingHom.mem_ker).2 hx
    obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.1 (hJK N ha)
    have hb0 : Ideal.Quotient.mkₐ O Kinf b = 0 := (Ideal.Quotient.eq_zero_iff_mem (I := Kinf)).2 hb
    rw [map_add (f := _), hb0, zero_add]
    exact mem_pow_map _ (N + 1) hc
  have hsepR : ∀ x y : MvPowerSeries σ O ⧸ Kinf, (∀ N, ρ N x = ρ N y) → x = y := by
    intro x y hxy
    rw [← sub_eq_zero]
    exact hausd _ (x - y) (fun N => hkerρ N _ (by rw [map_sub, hxy N, sub_self]))
  let ψ : ∀ N, MvPowerSeries σ O →ₐ[O] (MvPowerSeries σ O ⧸ Kinf) ⧸ maximalIdeal (MvPowerSeries σ O ⧸ Kinf) ^ N :=
    fun N => (Ideal.Quotient.mkₐ O _).comp (Ideal.Quotient.mkₐ O Kinf)
  have hψ : ∀ N, ∀ a ∈ RingHom.ker (F N : MvPowerSeries σ O →+* A N), ψ N a = 0 := by
    intro N a ha
    have hm := hkerρ N (Ideal.Quotient.mkₐ O Kinf a) ((RingHom.mem_ker).1 ha)
    exact (Ideal.Quotient.eq_zero_iff_mem (I := maximalIdeal (MvPowerSeries σ O ⧸ Kinf) ^ N)).2
      (Ideal.pow_le_pow_right (Nat.le_succ N) hm)
  let φ : ∀ N, A N →ₐ[O] (MvPowerSeries σ O ⧸ Kinf) ⧸ maximalIdeal (MvPowerSeries σ O ⧸ Kinf) ^ N :=
    fun N => (Ideal.Quotient.liftₐ _ (ψ N) (fun a ha => hψ N a ha)).comp
      (Ideal.quotientKerAlgEquivOfSurjective (hFs N)).symm.toAlgHom
  have hφ : ∀ N a, φ N (F N a) =
      Ideal.Quotient.mk (maximalIdeal (MvPowerSeries σ O ⧸ Kinf) ^ N) (Ideal.Quotient.mkₐ O Kinf a) := by
    intro N a
    have h' : (Ideal.quotientKerAlgEquivOfSurjective (hFs N)).symm (F N a) = Ideal.Quotient.mk _ a := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    show Ideal.Quotient.liftₐ _ (ψ N) (fun a ha => hψ N a ha)
      ((Ideal.quotientKerAlgEquivOfSurjective (hFs N)).symm (F N a)) = _
    rw [h']
    rfl
  have hcompat : ∀ (N M : ℕ) (h : M ≤ N), ((r N).map (φ N : A N →+* (MvPowerSeries σ O ⧸ Kinf) ⧸ maximalIdeal (MvPowerSeries σ O ⧸ Kinf) ^ N)).map
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right h)) = (r M).map (φ M : A M →+* (MvPowerSeries σ O ⧸ Kinf) ⧸ maximalIdeal (MvPowerSeries σ O ⧸ Kinf) ^ M) := by
    intro N M hMN
    obtain ⟨g, hg, hgF⟩ := trans M N hMN
    refine coord_ext fun t => ?_
    rw [coord_map, coord_mapA, ← hg, coord_mapA, coord_mapA]
    obtain ⟨a, ha⟩ := hFs N (coord (r N) t)
    rw [← ha, hφ N a]
    have e := congrArg (fun φ' : MvPowerSeries σ O →ₐ[O] A M => φ' a) hgF
    simp only [AlgHom.comp_apply] at e
    rw [e, hφ M a, Ideal.Quotient.factor_mk]
  haveI := hR.complete
  obtain ⟨D, hD, -⟩ := u_lim (maximalIdeal (MvPowerSeries σ O ⧸ Kinf)) (fun N => (r N).map (φ N : A N →+* (MvPowerSeries σ O ⧸ Kinf) ⧸ maximalIdeal (MvPowerSeries σ O ⧸ Kinf) ^ N)) hcompat
  have hρeq : ∀ N (x y : MvPowerSeries σ O ⧸ Kinf),
      Ideal.Quotient.mk (maximalIdeal (MvPowerSeries σ O ⧸ Kinf) ^ (N + 1)) x =
        Ideal.Quotient.mk (maximalIdeal (MvPowerSeries σ O ⧸ Kinf) ^ (N + 1)) y → ρ N x = ρ N y := by
    intro N x y hxy
    rw [Ideal.Quotient.eq] at hxy
    have hm := mem_pow_map (ρ N) (N + 1) hxy
    rw [h1 N, Ideal.mem_bot, map_sub, sub_eq_zero] at hm
    exact hm
  have hρD : ∀ N t, ρ N (coord D t) = coord (r N) t := by
    intro N t
    obtain ⟨g, hg, hgF⟩ := trans N (N + 1) (Nat.le_succ N)
    obtain ⟨a, ha⟩ := hFs (N + 1) (coord (r (N + 1)) t)
    have e1 : Ideal.Quotient.mk (maximalIdeal (MvPowerSeries σ O ⧸ Kinf) ^ (N + 1)) (coord D t) =
        Ideal.Quotient.mk _ (Ideal.Quotient.mkₐ O Kinf a) := by
      rw [← coord_map, hD (N + 1)]
      show coord ((r (N + 1)).map (φ (N + 1) : A (N + 1) →+* (MvPowerSeries σ O ⧸ Kinf) ⧸
        maximalIdeal (MvPowerSeries σ O ⧸ Kinf) ^ (N + 1))) t = _
      rw [coord_mapA, ← ha, hφ]
    rw [hρeq N _ _ e1, ← hg, coord_mapA, ← ha]
    have e := congrArg (fun φ' : MvPowerSeries σ O →ₐ[O] A N => φ' a) hgF
    exact e.symm
  have lcr : ∀ M i, IsLocallyConstant fun g : G => coord (r M) (i, g) := by
    intro M i
    refine IsLocallyConstant.desc _ (Ideal.Quotient.mk (maximalIdeal (A M) ^ (M + 1))) ((h0 M).cont i (M + 1)) ?_
    intro a b hab
    rw [Ideal.Quotient.eq, h1 M, Ideal.mem_bot, sub_eq_zero] at hab
    exact hab
  have hEvD : IsEv s Dbar D (Ideal.Quotient.mkₐ O Kinf) := by
    intro t
    apply hsepR
    intro N
    show F N (MvPowerSeries.X t) = ρ N _
    rw [hF N t, map_sub, AlgHom.commutes, hρD N]
  refine ⟨MvPowerSeries σ O ⧸ Kinf, inferInstance, inferInstance, hR, D, ⟨⟨fun i M => ?_, ?_⟩, ?_⟩⟩
  · show IsLocallyConstant fun g : G =>
      Ideal.Quotient.mk (maximalIdeal (MvPowerSeries σ O ⧸ Kinf) ^ M) (coord D (i, g))
    have e : ∀ g : G, Ideal.Quotient.mk (maximalIdeal (MvPowerSeries σ O ⧸ Kinf) ^ M) (coord D (i, g)) =
        φ M (coord (r M) (i, g)) := by
      intro g
      rw [← coord_map, hD M]
      exact coord_mapA _ _ _
    simp only [e]
    exact (lcr M i).comp _
  · refine coord_ext fun t => ?_
    rw [coord_mapA, ← res_map (ρ 0), hρD 0 t, ← coord_mapA (r 0) (res O (A 0)) t, (h0 0).red]
  · intro R' _ _ _ D' hD'
    obtain ⟨F', hF', hF'u⟩ := ev_exu s hD'
    have lvl : ∀ N, ∃ g : A N →ₐ[O] R' ⧸ maximalIdeal R' ^ (N + 1),
        (r N).map (g : A N →+* R' ⧸ maximalIdeal R' ^ (N + 1)) =
          D'.map (Ideal.Quotient.mkₐ O (maximalIdeal R' ^ (N + 1)) : R' →+* R' ⧸ maximalIdeal R' ^ (N + 1)) ∧
        g.comp (F N) = (Ideal.Quotient.mkₐ O (maximalIdeal R' ^ (N + 1))).comp F' := by
      intro N
      haveI : IsCO O (R' ⧸ maximalIdeal R' ^ (N + 1)) := co_trunc O R' N
      have hdq := isDef_map hD' (Ideal.Quotient.mkₐ O (maximalIdeal R' ^ (N + 1)))
      obtain ⟨g, hg⟩ := h3 N _ _ hdq (trunc_pow (O := O) (A := R') (N + 1))
      refine ⟨g, hg, ?_⟩
      apply evu _ _ hdq
      · rw [← hg]
        exact IsEv.map s (hF N) g
      · exact IsEv.map s hF' _
    have hK' : ∀ a ∈ Kinf, F' a = 0 := by
      intro a ha
      apply hausd R'
      intro N
      obtain ⟨g, -, heq⟩ := lvl N
      have e := congrArg (fun φ' : MvPowerSeries σ O →ₐ[O] R' ⧸ maximalIdeal R' ^ (N + 1) => φ' a) heq
      simp only [AlgHom.comp_apply] at e
      rw [show F N a = 0 from (RingHom.mem_ker).1 (hKJ N ha), map_zero] at e
      exact (Ideal.Quotient.eq_zero_iff_mem (I := maximalIdeal R' ^ (N + 1))).1 e.symm
    refine ⟨Ideal.Quotient.liftₐ Kinf F' hK', ?_, ?_⟩
    · refine coord_ext fun t => ?_
      rw [coord_mapA, ← sub_eq_zero]
      apply hausd R'
      intro N
      obtain ⟨g, hg, heq⟩ := lvl N
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
      have key : ∀ x, Ideal.Quotient.mk (maximalIdeal R' ^ (N + 1)) (Ideal.Quotient.liftₐ Kinf F' hK' x) =
          g (ρ N x) := by
        intro x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective O Kinf x
        have e := congrArg (fun φ' : MvPowerSeries σ O →ₐ[O] R' ⧸ maximalIdeal R' ^ (N + 1) => φ' a) heq
        exact e.symm
      rw [key, hρD N t]
      have e2 := congrArg (fun E => coord E t) hg
      simp only [coord_mapA] at e2
      exact e2
    · intro f2 hf2
      have e1 : f2.comp (Ideal.Quotient.mkₐ O Kinf) = F' := by
        apply hF'u
        rw [← hf2]
        exact IsEv.map s hEvD f2
      refine AlgHom.ext fun x => ?_
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective O Kinf x
      exact congrArg (fun φ' : MvPowerSeries σ O →ₐ[O] R' => φ' a) e1

end

theorem UpperTheory.V.CA.univDet :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] {n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (Dbar : GDet n (ResidueField O) G), PhiCond G l → Dbar.IsCont (maximalIdeal (ResidueField O)) → Module.Finite (ResidueField O) (Dbar.CHQuot ∅) → ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (D : GDet n R G), IsUnivDet O Dbar D := by
  intro l _ O _ _ _ _ _ _ n G _ _ _ _ _ Dbar hphi hc hfin
  classical
  haveI hk : IsCO O (ResidueField O) := (co_res O).1
  haveI hd : IsCO O (DualNumber (ResidueField O)) := (co_res O).2
  obtain ⟨U, hU⟩ := u_tan l Dbar hphi hc hfin
  haveI : Finite (G ⧸ (U : Subgroup G)) :=
    Subgroup.quotient_finite_of_isOpen _ U.toOpenSubgroup.isOpen
  have hres : ∀ x : DualNumber (ResidueField O), res O (DualNumber (ResidueField O)) x = TrivSqZeroExt.fst x := by
    intro x
    have hm : x - algebraMap O (DualNumber (ResidueField O)) (cst (TrivSqZeroExt.fst x)) ∈
        maximalIdeal (DualNumber (ResidueField O)) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have hu' := hu.map (TrivSqZeroExt.fstHom (ResidueField O) (ResidueField O) (ResidueField O))
      have h0 : TrivSqZeroExt.fstHom (ResidueField O) (ResidueField O) (ResidueField O)
          (x - algebraMap O (DualNumber (ResidueField O)) (cst (TrivSqZeroExt.fst x))) = 0 := by
        simp [TrivSqZeroExt.algebraMap_eq_inl, cst_spec]
        rw [sub_eq_zero]
        exact (cst_spec _).symm
      rw [h0] at hu'
      exact not_isUnit_zero hu'
    have h1 := (res_eq_zero_iff O _ _).2 hm
    rw [map_sub, AlgHom.commutes, cst_spec, sub_eq_zero] at h1
    exact h1
  have hred : ∀ D : GDet n (DualNumber (ResidueField O)) G, IsDef O Dbar D →
      D.map ↑(TrivSqZeroExt.fstHom (ResidueField O) (ResidueField O) (ResidueField O)) = Dbar := by
    intro D hD
    rw [← hD.red]
    exact coord_ext fun t => by
      rw [coord_map, coord_map]
      exact (hres _).symm
  have hs : Seps Dbar (fun p : Fin n × (G ⧸ (U : Subgroup G)) => ((p.1 : ℕ) + 1, Quotient.out p.2)) := by
    intro D D' hD hD' hagree
    have key : ∀ (E : GDet n (DualNumber (ResidueField O)) G), IsDef O Dbar E → ∀ i g,
        coord E (i, g) = coord E (i, Quotient.out (QuotientGroup.mk g : G ⧸ (U : Subgroup G))) := by
      intro E hE i g
      obtain ⟨E0, hE0⟩ := exists_comap_quot E (U : Subgroup G) (hU E hE.cont (hred E hE))
      rw [← hE0, coord_comap, coord_comap]
      simp [QuotientGroup.out_eq']
    apply d_gext
    intro g i h1 h2
    change coord D (i, g) = coord D' (i, g)
    rw [key D hD, key D' hD']
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    exact hagree (⟨j, by omega⟩, QuotientGroup.mk g)
  have lev := fun N => level _ hs hc N
  choose A iA jA kA r h0 h1 h2 h3 using lev
  exact assemble _ hs A r h0 h1 h2 h3
