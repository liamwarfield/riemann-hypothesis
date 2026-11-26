module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DChKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DCorner
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.StarFacts

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.LiftSurj
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.ChQuot
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.chQuot :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E), ∃ (E' : Type) (_ : Ring E') (_ : Algebra A E') (π : E →ₐ[A] E') (D' : Det n A E'), Function.Surjective π ∧ D'.pull π = D ∧ D'.IsCH ∧ ∀ y, π y = 0 → y ∈ D.ker := by
  intro n A E _ _ _ D
  let π : E →ₐ[A] D.CH.ringCon.Quotient := RingCon.mkₐ A D.CH.ringCon
  have hmem : ∀ x, π x = 0 ↔ x ∈ D.CH := fun x => by
    rw [← map_zero π]
    exact (RingCon.eq _)
  have hsurj : Function.Surjective π := fun q => Quotient.exists_rep q
  have hk : ∀ y, π y = 0 → y ∈ D.ker := fun y hy => UpperTheory.V.CA.d_ch_ker D ((hmem y).1 hy)
  obtain ⟨D', hD', -⟩ := UpperTheory.V.CA.d_factor D π hsurj hk
  refine ⟨_, _, _, π, D', hsurj, hD', ?_, hk⟩
  refine eq_bot_iff.2 fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := ((UpperTheory.V.CA.d_pull D' π).2.2.2 hsurj).2 y hy
  rw [hD'] at hx
  rw [TwoSidedIdeal.mem_bot, hmem]
  exact hx
end

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem lift_surj {B E E' P : Type} [CommRing B] [Ring E] [Ring E'] [Ring P] [Algebra B E] [Algebra B E']
    [Algebra B P] (q : E →ₐ[B] E') (hq : Function.Surjective q) (ρ : E →ₐ[B] P) (h : ∀ x, q x = 0 → ρ x = 0) :
    ∃ π : E' →ₐ[B] P, ∀ x, π (q x) = ρ x := by
  have key : ∀ x y, q x = q y → ρ x = ρ y := fun x y hxy =>
    sub_eq_zero.1 (by rw [← map_sub]; exact h _ (by rw [map_sub, hxy, sub_self]))
  choose s hs using hq
  have hq' : ∀ x, ρ (s (q x)) = ρ x := fun x => key _ _ (hs _)
  refine ⟨⟨⟨⟨⟨fun y => ρ (s y), ?_⟩, fun a b => ?_⟩, ?_, fun a b => ?_⟩, fun r => ?_⟩, hq'⟩
  · rw [← map_one q, hq', map_one]
  · change ρ (s (a * b)) = ρ (s a) * ρ (s b)
    rw [← map_mul]
    exact key _ _ (by rw [map_mul, hs, hs, hs])
  · change ρ (s 0) = 0
    rw [← map_zero q, hq', map_zero]
  · change ρ (s (a + b)) = ρ (s a) + ρ (s b)
    rw [← map_add (f := _)]
    exact key _ _ (by rw [map_add (f := _), hs, hs, hs])
  · change ρ (s (algebraMap B E' r)) = _
    rw [← q.commutes, hq', ρ.commutes]

theorem UpperTheory.V.Th.Coc.gma :
    ∀ {n : ℕ} {O R G : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [Group G] (D : GDet n R G) (χ : Fin n → G →* (ResidueField O)ˣ), 1 ≤ n → Function.Injective χ → D.map (res O R : R →+* ResidueField O) = GDet.ofRep (diagRep χ) → ∃ (E : Type) (_ : Ring E) (_ : Algebra R E) (π : MonoidAlgebra R G →ₐ[R] E) (τ : E →ₗ[R] R) (e : Fin n → E), Function.Surjective π ∧ (∀ y, τ (π y) = D.tr y) ∧ IsTrGMA τ e := by
  intro n O R G _ _ _ _ _ _ D χ hn hχ hred
  obtain ⟨E, _, _, q, DE, hsurj, hDE, hCH, -⟩ := chQuot D.toDet
  obtain ⟨π0, hs0, -, -, hchi0⟩ := CA.f_chars χ hχ
  letI : Algebra R (ResidueField O) := (res O R : R →+* ResidueField O).toAlgebra
  have hal : algebraMap R (ResidueField O) = (res O R : R →+* ResidueField O) := rfl
  let ρ : MonoidAlgebra R G →ₐ[R] (Fin n → ResidueField O) :=
    (π0.restrictScalars R).comp (MonoidAlgebra.mapAlgHom G (Algebra.ofId R (ResidueField O)))
  have hρ : ∀ x, ρ x = π0 (MonoidAlgebra.mapRingHom G (res O R : R →+* ResidueField O) x) := fun x => rfl
  have hchi : ∀ x, (DE.chi (q x)).map (res O R : R →+* ResidueField O) = ∏ i, (Polynomial.X - Polynomial.C (ρ x i)) := fun x => by
    rw [← (CA.d_pull DE q).1, hDE, (CA.d_toDet D x).1, ← ((CA.d_gmap D).2.2.1 (res O R : R →+* ResidueField O) x).1, hred, hρ]
    exact hchi0 _
  have hker : ∀ x, q x = 0 → ρ x = 0 := fun x hx => by
    have h1 := hchi x
    rw [hx, ← map_zero q, hchi 0, map_zero] at h1
    funext i
    have h2 := congrArg (Polynomial.eval (ρ x i)) h1
    rw [Polynomial.eval_prod, Polynomial.eval_prod,
      Finset.prod_eq_zero (f := fun j => Polynomial.eval (ρ x i) (Polynomial.X - Polynomial.C (ρ x j)))
      (Finset.mem_univ i) (by simp)] at h2
    obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.1 h2
    simpa using hj
  obtain ⟨π, hπ⟩ := lift_surj q hsurj ρ hker
  have hmap : ∀ y : MonoidAlgebra (ResidueField O) G, ∃ x, MonoidAlgebra.mapRingHom G (res O R : R →+* ResidueField O) x = y := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => exact ⟨0, map_zero _⟩
    | add a b ha hb =>
      obtain ⟨a', rfl⟩ := ha
      obtain ⟨b', rfl⟩ := hb
      exact ⟨a' + b', map_add _ _ _⟩
    | single g r =>
      obtain ⟨c, rfl⟩ := residue_surjective r
      exact ⟨MonoidAlgebra.single g (algebraMap O R c), (MonoidAlgebra.mapRingHom_single _ _ _).trans
        (congrArg _ ((res O R).commutes c))⟩
  have hπs : Function.Surjective π := fun v => by
    obtain ⟨y, rfl⟩ := hs0 v
    obtain ⟨x, rfl⟩ := hmap y
    exact ⟨q x, by rw [hπ, hρ]⟩
  have hchiE : ∀ x, (DE.chi x).map (algebraMap R (ResidueField O)) = ∏ i, (Polynomial.X - Polynomial.C (π x i)) := fun x => by
    obtain ⟨y, rfl⟩ := hsurj x
    rw [hπ, hal, hchi]
  haveI : IsLocalHom (algebraMap R (ResidueField O)) := ⟨fun a ha => by
    by_contra hn
    exact ha.ne_zero ((res_eq_zero_iff O R a).2 hn)⟩
  obtain ⟨-, e, he, -⟩ := CA.f_gma DE π hCH hπs hchiE
  obtain ⟨h1, h2, -⟩ := CA.d_tr DE
  obtain ⟨t, ht⟩ := h1 hn
  have hc := fun i => CA.d_corner DE (e i) he.ch (he.idem.idem i) (he.rank i) hn
  refine ⟨E, _, _, q, t, e, hsurj, fun y => ?_, fun a b => ?_, he.idem, fun i a => ?_, fun i => ?_⟩
  · rw [ht, ← (CA.d_toDet D y).2.2.1, ← hDE]
    unfold Det.tr Det.lam
    rw [(CA.d_pull DE q).1]
  · rw [ht, ht]
    exact h2 1 a b
  · rw [ht]
    exact (hc i).1 a
  · rw [ht]
    exact (hc i).2.1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.LiftOfS
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.liftOfS :
    ∀ {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ} {E : Type} [Ring E] [Algebra R E] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ : E →+* Matrix (Fin n) (Fin n) O) (τ : E → R) (s : E →ₗ[R] Matrix (Fin n) (Fin n) R) (β : R) (b : O), IsDer x δ → (∀ (r : R) a, ρ (r • a) = x r • ρ a) → (∀ a, (ρ a).trace = x (τ a)) → x β = b → (∀ a a', s a * s a' = β • s (a * a')) → (∀ a, (s a).map x = b • ρ a) → (∀ a, (s a).trace = β * τ a) → ∃ d : E →+ Matrix (Fin n) (Fin n) X, IsLift x δ ρ τ (b * b) d := by
  intro O R X _ _ _ _ _ n E _ _ x δ ρ τ s β b hδ hρ htr hβ hs hx hst
  have hx' : ∀ a i j, x (s a i j) = b * ρ a i j := fun a i j => congrFun (congrFun (hx a) i) j
  have sm : ∀ (a : O) (y : X), a • y = algebraMap O X a * y := fun a y => Algebra.smul_def a y
  have en : ∀ a i j, (b • ((s a).map δ - δ β • bar X (ρ a))) i j =
      algebraMap O X b * (δ (s a i j) - δ β * algebraMap O X (ρ a i j)) := fun a i j => by
    rw [Matrix.smul_apply, sm]; rfl
  refine ⟨{ toFun := fun a => b • ((s a).map δ - δ β • bar X (ρ a))
            map_zero' := by ext i j; simp [bar]
            map_add' := fun a a' => by
              ext i j
              rw [Matrix.add_apply, en, en, en, map_add s, map_add ρ, Matrix.add_apply, Matrix.add_apply, map_add (f := _), map_add (f := _)]
              ring }, fun a a' => ?_, fun r a => ?_, fun a => ?_⟩
  · ext i k
    have h1 := congrArg δ (congrFun (congrFun (hs a a') i) k)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum, Matrix.smul_apply, smul_eq_mul, hδ β, hβ, hx'] at h1
    simp only [hδ _ _, hx', sm, map_mul] at h1
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.add_apply, Matrix.mul_apply, en, Matrix.map_apply]
    rw [mul_sub, eq_sub_of_add_eq h1.symm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, map_mul, map_sum, Finset.mul_sum, Finset.sum_mul]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  · ext i j
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.add_apply, en]
    rw [Matrix.smul_apply, en, Matrix.smul_apply, map_smul s, hρ, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, hδ r, hx']
    simp only [sm, map_mul, Matrix.map_apply]
    ring
  · have h1 : ((s a).map δ).trace = δ (s a).trace := by simp [Matrix.trace, map_sum]
    have h2 : (bar X (ρ a)).trace = algebraMap O X (ρ a).trace := by simp [bar, Matrix.trace, map_sum]
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.trace_smul, Matrix.trace_sub, h1, h2, hst, hδ _ _, hβ, htr]
    simp only [sm, map_mul, smul_eq_mul]
    ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.TrSingle
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem corner_eq {R : Type} [CommRing R] {n : ℕ} {E : Type} [Ring E] [Algebra R E] {τ : E →ₗ[R] R}
    {e : Fin n → E} (h : IsTrGMA τ e) (i : Fin n) (z : E) (hz : e i * z * e i = z) : z = τ z • e i := by
  have hidem : e i * e i = e i := (h.idem.idem i).eq
  have h1 : e i * z = z := by
    calc e i * z = e i * (e i * z * e i) := by rw [hz]
      _ = e i * z * e i := by rw [← mul_assoc, ← mul_assoc, hidem]
      _ = z := hz
  calc z = e i * z * e i := hz.symm
    _ = τ (e i * z) • e i := h.corner i z
    _ = τ z • e i := by rw [h1]

private theorem tr_single {O : Type} [CommRing O] {n : ℕ} (o i j : Fin n) (c : O) (A : Matrix (Fin n) (Fin n) O) :
    ((c • Matrix.single o i (1 : O)) * A * (c • Matrix.single j o (1 : O))).trace = c ^ 2 * A i j := by
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.single_mul_mul_single]
  simp [Matrix.trace_smul, pow_two, mul_assoc]

theorem UpperTheory.V.Th.Coc.smat :
    ∀ {O R : Type} [CommRing O] [CommRing R] [Algebra O R] {n : ℕ} {E : Type} [Ring E] [Algebra R E] (x : R →ₐ[O] O) (ρ : E →+* Matrix (Fin n) (Fin n) O) (τ : E →ₗ[R] R) (e : Fin n → E) (c : O), 1 ≤ n → IsTrGMA τ e → (∀ i, ρ (e i) = Matrix.single i i 1) → (∀ a, (ρ a).trace = x (τ a)) → (∀ Z, ∃ a, ρ a = c • Z) → ∃ (s : E →ₗ[R] Matrix (Fin n) (Fin n) R) (β : R), x β = c ^ (2 * n) ∧ (∀ a b, s a * s b = β • s (a * b)) ∧ (∀ a, (s a).map x = c ^ (2 * n) • ρ a) ∧ ∀ a, (s a).trace = β * τ a := by
  intro O R _ _ _ n E _ _ x ρ τ e c hn hT hρe htr hsurj
  classical
  obtain ⟨o, -⟩ : ∃ o : Fin n, True := ⟨⟨0, hn⟩, trivial⟩
  have hidem : ∀ i, e i * e i = e i := fun i => (hT.idem.idem i).eq
  have hρE : ∀ (i j : Fin n) (r : O), Matrix.single i i (1 : O) * (r • Matrix.single i j (1 : O)) *
      Matrix.single j j (1 : O) = r • Matrix.single i j (1 : O) := by
    intro i j r
    ext u v
    simp only [Matrix.single_mul_mul_single, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    split_ifs <;> simp_all
  choose hh hhρ using fun i : Fin n => hsurj (Matrix.single o i (1 : O))
  choose kk kkρ using fun j : Fin n => hsurj (Matrix.single j o (1 : O))
  obtain ⟨p, hp⟩ : ∃ p : Fin n → E, ∀ i, p i = e o * hh i * e i := ⟨_, fun _ => rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : Fin n → E, ∀ j, q j = e j * kk j * e o := ⟨_, fun _ => rfl⟩
  have ρp : ∀ i, ρ (p i) = c • Matrix.single o i (1 : O) := by
    intro i
    simp only [hp, map_mul, hρe, hhρ]
    exact hρE o i c
  have ρq : ∀ j, ρ (q j) = c • Matrix.single j o (1 : O) := by
    intro j
    simp only [hq, map_mul, hρe, kkρ]
    exact hρE j o c
  have hpl : ∀ i, e o * p i = p i := by
    intro i
    simp only [hp, ← mul_assoc, hidem]
  have hpr : ∀ i, p i * e i = p i := by
    intro i
    simp only [hp, mul_assoc, hidem]
  have hql : ∀ j, e j * q j = q j := by
    intro j
    simp only [hq, ← mul_assoc, hidem]
  have hqr : ∀ j, q j * e o = q j := by
    intro j
    simp only [hq, mul_assoc, hidem]
  have hcorner : ∀ i z, e i * z * e i = z → z = τ z • e i := fun i z hz => corner_eq hT i z hz
  obtain ⟨γ, hγ⟩ : ∃ γ : Fin n → R, ∀ j, γ j = τ (q j * p j) := ⟨_, fun _ => rfl⟩
  have hqp : ∀ j, q j * p j = γ j • e j := by
    intro j
    rw [hγ]
    apply hcorner
    rw [← mul_assoc, hql, mul_assoc, hpr]
  have hxγ : ∀ j, x (γ j) = c ^ 2 := by
    intro j
    rw [hγ, ← htr, map_mul, ρq, ρp]
    have h := tr_single j o o c (1 : Matrix (Fin n) (Fin n) O)
    rw [Matrix.mul_one, Matrix.one_apply_eq, mul_one] at h
    exact h
  have hρs : ∀ r : R, ρ (r • e o) = Matrix.single o o (x r) := by
    intro r
    have hz : e o * (r • e o) * e o = r • e o := by
      rw [mul_smul_comm, smul_mul_assoc, hidem, hidem]
    have h1 : ρ (r • e o) = Matrix.single o o ((ρ (r • e o)) o o) := by
      conv_lhs => rw [← hz]
      rw [map_mul, map_mul, hρe, Matrix.single_mul_mul_single, one_mul, mul_one]
    have h2 : (ρ (r • e o)).trace = x r := by
      rw [htr, map_smul, hT.one, smul_eq_mul, mul_one]
    rw [h1] at h2 ⊢
    congr 1
    simpa [Matrix.trace, Matrix.single_apply] using h2
  obtain ⟨Γj, hΓj⟩ : ∃ Γj : Fin n → R, ∀ j, Γj j = ∏ l ∈ Finset.univ.erase j, γ l := ⟨_, fun _ => rfl⟩
  obtain ⟨q', hq'⟩ : ∃ q' : Fin n → E, ∀ j, q' j = q j * (Γj j • e o) := ⟨_, fun _ => rfl⟩
  have hq'p : ∀ j, q' j * p j = (∏ l, γ l) • e j := by
    intro j
    rw [hq', mul_smul_comm, smul_mul_assoc, hqr, hqp, smul_smul, hΓj,
      Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  have hsum : ∑ j, q' j * p j = (∏ l, γ l) • (1 : E) := by
    simp_rw [hq'p]
    rw [← Finset.smul_sum, hT.idem.complete]
  have hq'r : ∀ j, q' j * e o = q' j := by
    intro j
    rw [hq', mul_assoc, smul_mul_assoc, hidem]
  have hX : ∀ i j a, p i * a * q' j = τ (p i * a * q' j) • e o := by
    intro i j a
    apply hcorner
    have h : e o * (p i * a * q' j) * e o = (e o * p i) * a * (q' j * e o) := by simp only [mul_assoc]
    rw [h, hpl, hq'r]
  have hτmul : ∀ i k j a b, τ (p i * a * q' k) * τ (p k * b * q' j) =
      τ (p i * a * q' k * (p k * b * q' j)) := by
    intro i k j a b
    have hl : e o * (p k * b * q' j) = p k * b * q' j := by simp only [← mul_assoc, hpl]
    conv_rhs => rw [hX i k a, smul_mul_assoc, hl, map_smul, smul_eq_mul]
  have hρq' : ∀ j, ρ (q' j) = x (Γj j) • (c • Matrix.single j o (1 : O)) := by
    intro j
    rw [hq', map_mul, ρq, hρs]
    ext u v
    simp only [Matrix.smul_mul, Matrix.single_mul_single_same, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    split_ifs <;> ring
  have hxΓj : ∀ j, x (Γj j) = (c ^ 2) ^ (n - 1) := by
    intro j
    rw [hΓj, map_prod]
    simp_rw [hxγ]
    rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  let s : E →ₗ[R] Matrix (Fin n) (Fin n) R :=
    { toFun := fun a => Matrix.of fun i j => τ (p i * a * q' j)
      map_add' := by
        intro a b
        ext i j
        simp only [Matrix.of_apply, Matrix.add_apply, mul_add, add_mul, map_add (f := _)]
      map_smul' := by
        intro r a
        ext i j
        simp only [Matrix.of_apply, Matrix.smul_apply, mul_smul_comm, smul_mul_assoc, map_smul,
          RingHom.id_apply] }
  have hs : ∀ a i j, s a i j = τ (p i * a * q' j) := fun _ _ _ => rfl
  refine ⟨s, ∏ l, γ l, ?_, ?_, ?_, ?_⟩
  · rw [map_prod]
    simp_rw [hxγ]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  · intro a b
    ext i j
    rw [Matrix.mul_apply, Matrix.smul_apply, hs, smul_eq_mul]
    simp_rw [hs, hτmul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum]
    have hrw : ∑ k, p i * a * q' k * (p k * b * q' j) = p i * a * (∑ k, q' k * p k) * b * q' j := by
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by simp only [mul_assoc]
    rw [hrw, hsum, mul_smul_comm, mul_one, smul_mul_assoc, smul_mul_assoc, map_smul, smul_eq_mul,
      mul_assoc (p i) a b]
  · intro a
    ext i j
    rw [Matrix.map_apply, hs, Matrix.smul_apply, smul_eq_mul, ← htr, map_mul, map_mul, ρp, hρq',
      Matrix.mul_smul, Matrix.trace_smul, tr_single, smul_eq_mul, hxΓj, ← mul_assoc, ← pow_succ,
      ← pow_mul, Nat.sub_add_cancel hn]
  · intro a
    have hc : ∀ i, τ (p i * a * q' i) = τ (a * (q' i * p i)) := by
      intro i
      rw [mul_assoc, hT.comm, mul_assoc]
    simp only [Matrix.trace, Matrix.diag_apply, hs, hc]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, ← Finset.mul_sum, hsum, mul_smul_comm, mul_one, map_smul, smul_eq_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.IdemDiag
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.idemDiag :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (e : Fin n → Matrix (Fin n) (Fin n) O), CompleteOrthogonalIdempotents e → (∀ i, (e i).trace = 1) → ∃ Q : GL (Fin n) O, ∀ i, ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * e i * (Q : Matrix (Fin n) (Fin n) O) = Matrix.single i i 1 := by
  intro O _ _ n e he htr
  classical
  have hmul : ∀ i j, e i * e j = if i = j then e i else 0 := by
    intro i j
    split_ifs with hij
    · subst hij
      exact (he.idem i).eq
    · exact he.ortho hij
  have hentry : ∀ i j a b, (e i * e j) a b = if i = j then e i a b else 0 := by
    intro i j a b
    rw [hmul]
    split_ifs <;> simp
  have hc : ∀ i, ∃ c, IsUnit (e i c c) := by
    intro i
    by_contra hne
    push_neg at hne
    have hmem : (e i).trace ∈ IsLocalRing.maximalIdeal O :=
      Ideal.sum_mem _ (fun c _ => (IsLocalRing.mem_maximalIdeal _).mpr (hne c))
    rw [htr i] at hmem
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem isUnit_one
  choose c hcu using hc
  let Qm : Matrix (Fin n) (Fin n) O := Matrix.of fun r j => e j r (c j)
  let Sm : Matrix (Fin n) (Fin n) O := Matrix.of fun i r => e i (c i) r
  have hSQ : Sm * Qm = Matrix.diagonal fun i => e i (c i) (c i) := by
    ext i j
    change (e i * e j) (c i) (c j) = _
    rw [hentry, Matrix.diagonal_apply]
    split_ifs with h
    · subst h
      rfl
    · rfl
  have hdet : IsUnit (Sm * Qm).det := by
    rw [hSQ, Matrix.det_diagonal]
    exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one (fun i _ => hcu i)
  rw [Matrix.det_mul] at hdet
  obtain ⟨U, hU⟩ := (Matrix.isUnit_iff_isUnit_det Qm).mpr (isUnit_of_mul_isUnit_right hdet)
  refine ⟨U, fun i => ?_⟩
  have heQ : e i * Qm = Qm * Matrix.single i i 1 := by
    ext r j
    change (e i * e j) r (c j) = _
    rw [hentry, Matrix.mul_apply]
    simp only [Matrix.single_apply, Qm, Matrix.of_apply]
    split_ifs with h
    · subst h
      simp
    · simp [h]
  rw [mul_assoc, hU, heQ, ← hU, Units.inv_mul_cancel_left]
end

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private def conjHom {O : Type} [CommRing O] {n : ℕ} (Q : GL (Fin n) O) :
    Matrix (Fin n) (Fin n) O →+* Matrix (Fin n) (Fin n) O where
  toFun Z := ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * Z * (Q : Matrix (Fin n) (Fin n) O)
  map_one' := by rw [Matrix.mul_one, Units.inv_mul]
  map_mul' a b := by
    simp only [Matrix.mul_assoc]
    rw [Units.mul_inv_cancel_left]
  map_zero' := by rw [Matrix.mul_zero, Matrix.zero_mul]
  map_add' a b := by rw [Matrix.mul_add, Matrix.add_mul]

theorem UpperTheory.V.Th.Coc.liftG :
    ∀ {n : ℕ} {O R X G : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [CommRing X] [Algebra O X] [Group G] (D : GDet n R G) (χ : Fin n → G →* (ResidueField O)ˣ) (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ : G →* Matrix (Fin n) (Fin n) O) (c₀ : O), 1 ≤ n → Function.Injective χ → D.map (res O R : R →+* ResidueField O) = GDet.ofRep (diagRep χ) → D.map x.toRingHom = GDet.ofRep ρ → c₀ ≠ 0 → (∀ Z : Matrix (Fin n) (Fin n) O, c₀ • Z ∈ Submodule.span O (Set.range ρ)) → IsDer x δ → ∃ d : MonoidAlgebra R G →+ Matrix (Fin n) (Fin n) X, IsLift x δ (repR x ρ) D.tr (c₀ ^ (2 * n) * c₀ ^ (2 * n)) d := by
  intro n O R X G _ _ _ _ _ _ _ _ _ D χ x δ ρ c₀ hn hχ hres hx hc hspan hδ
  obtain ⟨E, _, _, π, τ, e, hπ, hτ, hg⟩ := UpperTheory.V.Th.Coc.gma (O := O) D χ hn hχ hres
  obtain ⟨htr, hsm, -⟩ := UpperTheory.V.Th.Coc.trRep D x ρ hn hx
  obtain ⟨k1, -⟩ := UpperTheory.V.Th.Coc.kill0 ρ c₀ hc hspan
  have hs : ∀ g, repR x ρ (MonoidAlgebra.single g (1 : R)) = ρ g := fun g => by
    rw [repR_single, map_one, one_smul]
  have hker : RingHom.ker π.toRingHom ≤ RingHom.ker (repR x ρ) := by
    intro y hy
    have hy' : π y = 0 := hy
    refine k1 _ fun g => ?_
    have h := htr (MonoidAlgebra.single g 1 * y)
    rw [map_mul, hs, ← hτ, map_mul, hy', mul_zero, map_zero, map_zero] at h
    exact h
  obtain ⟨ρE, hρE⟩ : ∃ ρE : E →+* Matrix (Fin n) (Fin n) O, ∀ y, ρE (π y) = repR x ρ y :=
    ⟨π.toRingHom.liftOfSurjective hπ ⟨repR x ρ, hker⟩, fun y =>
      π.toRingHom.liftOfRightInverse_comp_apply _ _ ⟨repR x ρ, hker⟩ y⟩
  have htrE : ∀ a, (ρE a).trace = x (τ a) := fun a => by
    obtain ⟨y, rfl⟩ := hπ a
    rw [hρE, htr, hτ]
  have hsmE : ∀ (r : R) a, ρE (r • a) = x r • ρE a := fun r a => by
    obtain ⟨y, rfl⟩ := hπ a
    rw [← map_smul π, hρE, hρE, hsm]
  have hrange : ∀ Z ∈ Submodule.span O (Set.range ρ), ∃ a, ρE a = Z := by
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem Z hZ =>
      obtain ⟨g, rfl⟩ := hZ
      exact ⟨π (MonoidAlgebra.single g 1), by rw [hρE, hs]⟩
    | zero => exact ⟨0, map_zero _⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', rfl⟩ := ha
      obtain ⟨b', rfl⟩ := hb
      exact ⟨a' + b', map_add _ _ _⟩
    | smul o a _ ha =>
      obtain ⟨a', rfl⟩ := ha
      exact ⟨algebraMap O R o • a', by rw [hsmE, AlgHom.commutes]; rfl⟩
  obtain ⟨Q, hQ⟩ := UpperTheory.V.Th.Coc.idemDiag (fun i => ρE (e i)) (hg.idem.map ρE)
    (fun i => by rw [htrE, hg.one, map_one])
  let ρ' : E →+* Matrix (Fin n) (Fin n) O := (conjHom Q).comp ρE
  have hρ' : ∀ a, ρ' a = ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * ρE a * (Q : Matrix (Fin n) (Fin n) O) :=
    fun a => rfl
  have htr' : ∀ a, (ρ' a).trace = x (τ a) := fun a => by
    rw [hρ', Matrix.trace_mul_comm, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, htrE]
  have hsm' : ∀ (r : R) a, ρ' (r • a) = x r • ρ' a := fun r a => by
    rw [hρ', hρ', hsmE, Matrix.mul_smul, Matrix.smul_mul]
  have hsurj' : ∀ Z, ∃ a, ρ' a = c₀ • Z := fun Z => by
    obtain ⟨a, ha⟩ := hrange _ (hspan ((Q : Matrix (Fin n) (Fin n) O) * Z *
      ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O)))
    refine ⟨a, ?_⟩
    rw [hρ', ha, Matrix.mul_smul, Matrix.smul_mul]
    simp only [Matrix.mul_assoc]
    rw [Units.inv_mul_cancel_left, Units.inv_mul, Matrix.mul_one]
  obtain ⟨s, β, hβ, h1, h2, h3⟩ := UpperTheory.V.Th.Coc.smat x ρ' τ e c₀ hn hg hQ htr' hsurj'
  obtain ⟨d, hd⟩ := UpperTheory.V.Th.Coc.liftOfS x δ ρ' τ s β (c₀ ^ (2 * n)) hδ hsm' htr' hβ h1 h2 h3
  obtain ⟨d', hd', -⟩ := UpperTheory.V.Th.Coc.liftConj x δ ρE ρ' τ _ Q d (fun a => by
    rw [hρ']
    simp only [Matrix.mul_assoc]
    rw [Units.mul_inv_cancel_left, Units.mul_inv, Matrix.mul_one]) hd
  refine ⟨d'.comp π.toRingHom.toAddMonoidHom, ?_, ?_, ?_⟩
  · intro a b
    have h := hd'.mul (π a) (π b)
    rw [← map_mul, hρE, hρE] at h
    exact h
  · intro r a
    have h := hd'.smul r (π a)
    rw [← map_smul π, hρE] at h
    exact h
  · intro a
    have h := hd'.tr (π a)
    rw [hτ] at h
    exact h
