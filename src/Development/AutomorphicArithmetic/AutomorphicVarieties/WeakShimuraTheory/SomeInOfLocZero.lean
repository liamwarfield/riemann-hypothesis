module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SpaceMap

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SomeInOfLocZero
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.AlgHomResUnique
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem algHom_res_unique {Λ B : Type} [CommRing Λ] [IsLocalRing Λ] [CommRing B] [Algebra Λ B] [IsCO Λ B]
    (f : B →ₐ[Λ] ResidueField Λ) (b : B) : f b = res Λ B b := by
  obtain ⟨c, hc⟩ := IsCO.res_surj (O := Λ) b
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨d, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨algebraMap Λ B d, by rw [AlgHom.commutes]; rfl⟩
  have hmax : (RingHom.ker (f : B →+* ResidueField Λ)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ hsurj
  have hk : RingHom.ker (f : B →+* ResidueField Λ) = maximalIdeal B := IsLocalRing.eq_maximalIdeal hmax
  have h1 : f (b - algebraMap Λ B c) = 0 := by
    have hm : b - algebraMap Λ B c ∈ RingHom.ker (f : B →+* ResidueField Λ) := hk ▸ hc
    simpa using hm
  have h2 : res Λ B (b - algebraMap Λ B c) = 0 := (res_eq_zero_iff Λ B _).2 hc
  rw [map_sub, sub_eq_zero] at h1 h2
  rw [h1, h2, AlgHom.commutes, AlgHom.commutes]

private theorem point_ext {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ]
    [IsLocalRing Λ] {a : O →+* Λ} (X : Space Φ a) (x y : X.A →ₐ[Λ] ResidueField Λ)
    (h : X.P.map (x : X.A →+* ResidueField Λ) = X.P.map (y : X.A →+* ResidueField Λ)) (z : X.A) : x z = y z := by
  have hB : ∀ b : X.B, x (algebraMap X.B X.A b) = y (algebraMap X.B X.A b) := by
    intro b
    have h1 := algHom_res_unique (x.comp (IsScalarTower.toAlgHom Λ X.B X.A)) b
    have h2 := algHom_res_unique (y.comp (IsScalarTower.toAlgHom Λ X.B X.A)) b
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at h1 h2
    rw [h1, h2]
  have hz : z ∈ (⊤ : Subalgebra X.B X.A) := trivial
  rw [← X.gen] at hz
  induction hz using Algebra.adjoin_induction with
  | mem w hw =>
    rcases hw with ⟨⟨g, i, j⟩, rfl⟩ | ⟨⟨v, i, j⟩, rfl⟩
    · exact congrArg (fun Q => Q.r g i j) h
    · exact congrArg (fun Q => Q.n v i j) h
  | algebraMap b => exact hB b
  | add u w _ _ hu hw => rw [map_add (f := _), map_add (f := _), hu, hw]
  | mul u w _ _ hu hw => rw [map_mul, map_mul, hu, hw]

private theorem ker_le_of_eval {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type}
    [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} (X : Space Φ a) (x : X.A →ₐ[Λ] ResidueField Λ)
    (f : X.A →ₐ[Λ] (ResidueField Λ)[X]) (t : ResidueField Λ)
    (h : (X.P.map (f : X.A →+* (ResidueField Λ)[X])).map (evalRingHom t) = X.P.map (x : X.A →+* ResidueField Λ)) :
    RingHom.ker f ≤ RingHom.ker x := by
  intro z hz
  have hy : X.P.map ((((Polynomial.aeval t).restrictScalars Λ).comp f : X.A →ₐ[Λ] ResidueField Λ) :
      X.A →+* ResidueField Λ) = X.P.map (x : X.A →+* ResidueField Λ) := by
    rw [← h]; rfl
  have hxz := point_ext X _ x hy z
  rw [RingHom.mem_ker] at hz ⊢
  rw [← hxz]
  simp [hz]

theorem UpperTheory.V.Ws.conn :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ), Φ.Std l a → ∀ (X : Space Φ a) (J : Ideal X.B) (x x' : X.A →ₐ[Λ] ResidueField Λ),
      Φ.Linked ((residue Λ).comp a) (X.P.map (x : X.A →+* ResidueField Λ)) (X.P.map (x' : X.A →+* ResidueField Λ)) →
      (X.AllIn J (RingHom.ker x) → X.SomeIn J (RingHom.ker x')) ∧ (X.AllIn J (RingHom.ker x') → X.SomeIn J (RingHom.ker x)) := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a _ X J x x' hL
  obtain ⟨Q, hQ, h0, h1⟩ := hL
  obtain ⟨f, hf, -⟩ := X.line Q hQ
  have k0 : RingHom.ker f ≤ RingHom.ker x := ker_le_of_eval X x f 0 (by rw [hf, h0])
  have k1 : RingHom.ker f ≤ RingHom.ker x' := ker_le_of_eval X x' f 1 (by rw [hf, h1])
  haveI : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  obtain ⟨q, hq, hqf⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal X.A)) (J := RingHom.ker f) bot_le
  exact ⟨fun hA => ⟨q, hq, hqf.trans k1, hA q hq (hqf.trans k0)⟩,
    fun hA => ⟨q, hq, hqf.trans k0, hA q hq (hqf.trans k1)⟩⟩
end

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.Asm

section
variable {O Γ R R' : Type} [CommRing O] [Group Γ] [CommRing R] [CommRing R'] {Φ : Fr O Γ} {a : O →+* R} {P : PD Φ.ι Γ R}

theorem res_map' (h : Φ.Res a P) (f : R →+* R') : Φ.Res (f.comp a) (P.map f) := by
  have e : ∀ (S : Finset (ℤ × ℤ)) (X : M4 R), SuppM S X → SuppM S (X.map f) := fun S X hX i j h1 h2 => by
    rw [Matrix.map_apply, hX i j h1 h2, map_zero]
  refine ⟨fun g i => congrArg f (h.diag g i), fun v s hs i => ?_, ?_⟩
  · rw [PD.map_ψ, h.char v s hs i]; rfl
  · exact h.shape.imp (fun k => ⟨fun g => e _ _ (k.1 g), fun v => e _ _ (k.2 v)⟩) fun k g => e _ _ (k g)

theorem isRes_map [TopologicalSpace Γ] (h : Φ.IsRes a P) (f : R →+* R') : Φ.IsRes (f.comp a) (P.map f) :=
  ⟨h.pair.map f, res_map' h.res f, h.cont.map f bot_le⟩

theorem pair_of (f : R →+* R') (hf : Function.Injective f) (h : Φ.IsPair (f.comp a) (P.map f)) : Φ.IsPair a P := by
  have hi : ∀ X Y : M4 R, X.map f = Y.map f → X = Y := fun X Y e => Matrix.map_injective hf e
  have z : ∀ x, f x = 0 → x = 0 := fun x => (map_eq_zero_iff f hf).1
  have gs : ∀ (ν : R) (X : M4 R), IsGSp (f ν) (X.map f) → IsGSp ν X := fun ν X k => by
    unfold IsGSp at k ⊢
    apply hi
    rw [Matrix.map_mul, ← adj_map, k]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  refine ⟨fun g => gs _ _ (h.mult g), fun g hg => hi _ _ ?_, fun i j hij => z _ (h.nrm hij),
    fun v => ⟨gs _ _ (by rw [map_one]; exact (h.low v).1), fun i => hf ?_, fun i j hij => z _ ((h.low v).2.2 i j hij)⟩,
    fun v s hs i j hij => z _ ?_, fun v s hs i => hf ?_⟩
  · exact (h.kill g hg).trans (Matrix.map_one f (map_zero f) (map_one f)).symm
  · rw [map_one]; exact (h.low v).2.1 i
  · have k := h.flag v s hs i j hij
    rwa [PD.map_flag] at k
  · rw [map_one, ← PD.map_ψ]; exact h.mu v s hs i

theorem linked_self [TopologicalSpace Γ] (h : Φ.IsRes a P) : Φ.Linked a P P := by
  have e : ∀ t : R, (P.map C).map (evalRingHom t) = P := fun t => by
    have : (evalRingHom t).comp C = RingHom.id R := by ext; simp
    rw [PD.map_map, this]; rfl
  exact ⟨P.map C, isRes_map h C, e 0, e 1⟩

theorem linked_isRes [TopologicalSpace Γ] {P' : PD Φ.ι Γ R} (h : Φ.Linked a P P') : Φ.IsRes a P' := by
  obtain ⟨Q, hQ, -, rfl⟩ := h
  have k := isRes_map hQ (evalRingHom 1)
  have : (evalRingHom (1 : R)).comp (C.comp a) = a := by ext; simp
  rwa [this] at k

theorem chain_end [TopologicalSpace Γ] {P' : PD Φ.ι Γ R} (hP : Φ.IsRes a P) (h : Φ.Chain a P P') :
    Φ.IsRes a P' ∧ Φ.Good a P' := by
  obtain ⟨hg, hc⟩ := h
  induction hc with
  | refl => exact ⟨hP, hg⟩
  | tail _ hl _ => exact ⟨linked_isRes hl.2, hl.1⟩

end

section
variable {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ]
  {a : O →+* Λ} (X : Space Φ a) (J : Ideal X.B)

theorem end_pt {s t : PD Φ.ι Γ (ResidueField Λ)} (h : Φ.Linked ((residue Λ).comp a) s t) :
    ∃ x : X.A →ₐ[Λ] ResidueField Λ, X.P.map (x : X.A →+* ResidueField Λ) = t := by
  obtain ⟨Q, hQ, -, rfl⟩ := h
  obtain ⟨f, rfl, -⟩ := X.line Q hQ
  refine ⟨((aeval (1 : ResidueField Λ) : (ResidueField Λ)[X] →ₐ[ResidueField Λ] ResidueField Λ).restrictScalars Λ).comp f, ?_⟩
  rw [PD.map_map]
  congr 1

theorem someIn_of_locZero {K : Type} [CommRing K] [IsDomain K] (y : X.A →+* K) (h : X.LocZero J y) {p : Ideal X.A}
    (hp : RingHom.ker y ≤ p) : X.SomeIn J p := by
  haveI := RingHom.ker_isPrime y
  obtain ⟨q, hq, hle⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal X.A)) (J := RingHom.ker y) bot_le
  haveI : q.IsPrime := hq.1.1
  exact ⟨q, hq, hle.trans hp, Ideal.map_le_iff_le_comap.2 (h _ (Ideal.comap_isPrime _ q) fun s hs => hle hs)⟩

theorem zero_of_allIn {K : Type} [CommRing K] [IsDomain K] (y : X.A →+* K) {p : Ideal X.A} (h : X.AllIn J p)
    (hp : RingHom.ker y ≤ p) : ∀ b ∈ J, y (algebraMap X.B X.A b) = 0 := fun b hb => by
  haveI := RingHom.ker_isPrime y
  obtain ⟨q, hq, hle⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal X.A)) (J := RingHom.ker y) bot_le
  exact hle (h q hq (hle.trans hp) (Ideal.mem_map_of_mem _ hb))

end

theorem allIn_of_chain {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    [TotallyDisconnectedSpace Γ] {Φ : Fr O Γ} {l : ℕ} [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ]
    [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] {a : O →+* Λ} (hΦ : Φ.Std l a)
    (X : Space Φ a) (J : Ideal X.B)
    (hch : ∀ x : X.A →ₐ[Λ] ResidueField Λ, Φ.IsRes ((residue Λ).comp a) (X.P.map (x : X.A →+* ResidueField Λ)) →
      Φ.Good ((residue Λ).comp a) (X.P.map (x : X.A →+* ResidueField Λ)) → X.SomeIn J (RingHom.ker x) → X.AllIn J (RingHom.ker x))
    (x₀ x₁ : X.A →ₐ[Λ] ResidueField Λ) (hs : Φ.IsRes ((residue Λ).comp a) (X.P.map (x₀ : X.A →+* ResidueField Λ)))
    (hc : Φ.Chain ((residue Λ).comp a) (X.P.map (x₀ : X.A →+* ResidueField Λ)) (X.P.map (x₁ : X.A →+* ResidueField Λ)))
    (h₁ : X.SomeIn J (RingHom.ker x₁)) : X.AllIn J (RingHom.ker x₀) := by
  have key : ∀ s, Relation.ReflTransGen (fun x y => Φ.Good ((residue Λ).comp a) y ∧ Φ.Linked ((residue Λ).comp a) x y) s
      (X.P.map (x₁ : X.A →+* ResidueField Λ)) → Φ.IsRes ((residue Λ).comp a) s → Φ.Good ((residue Λ).comp a) s →
      ∀ x : X.A →ₐ[Λ] ResidueField Λ, X.P.map (x : X.A →+* ResidueField Λ) = s → X.AllIn J (RingHom.ker x) := by
    intro s h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro k1 k2 x e
      have hl : Φ.Linked ((residue Λ).comp a) (X.P.map (x : X.A →+* ResidueField Λ))
          (X.P.map (x₁ : X.A →+* ResidueField Λ)) := by
        rw [e]
        exact linked_self k1
      exact hch x (e ▸ k1) (e ▸ k2) ((conn Φ l a hΦ X J x x₁ hl).2 (hch x₁ k1 k2 h₁))
    | head hl _ ih =>
      rintro k1 k2 x rfl
      obtain ⟨x', rfl⟩ := end_pt X hl.2
      exact hch x k1 k2 ((conn Φ l a hΦ X J x x' hl.2).2 (ih (linked_isRes hl.2) hl.1 x' rfl))
  exact key _ hc.2 hs hc.1 x₀ rfl

end UpperTheory.V.Ws.Asm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedDual
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws

section
variable {R : Type} [CommRing R]

private theorem rd_adj_mul (X Y : M4 R) : adj (X * Y) = adj Y * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

private theorem rd_adj_one : adj (1 : M4 R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.one_apply]

private theorem rd_sp {n n' m : M4 R} (h1 : n * m = 1) (h : adj n' * n + adj n * n' = 0) : n' * m ∈ sp4 R := by
  show adj _ = -_
  have e : adj n' = -(adj n * (n' * m)) := by
    have := congrArg (· * m) h
    simp only [add_mul, mul_assoc, h1, mul_one, zero_mul] at this
    exact eq_neg_of_add_eq_zero_left this
  rw [rd_adj_mul, e, mul_neg, ← mul_assoc, ← rd_adj_mul, h1, rd_adj_one, one_mul]

private theorem rd_up_mul {X Y : M4 R} (hX : IsUp X) (hY : IsUp Y) : IsUp (X * Y) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l < i
  · rw [hX i l hl, zero_mul]
  · rw [hY l j (lt_of_lt_of_le hij (not_lt.1 hl)), mul_zero]

end

section
variable {k : Type} [Field k]

private theorem rd_snd_mul (X Y : M4 (DualNumber k)) :
    (X * Y).map TrivSqZeroExt.snd = X.map TrivSqZeroExt.snd * Y.map TrivSqZeroExt.fst
      + X.map TrivSqZeroExt.fst * Y.map TrivSqZeroExt.snd := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four, TrivSqZeroExt.snd_add,
    DualNumber.snd_mul]
  ring

private theorem rd_fst_mul (X Y : M4 (DualNumber k)) :
    (X * Y).map TrivSqZeroExt.fst = X.map TrivSqZeroExt.fst * Y.map TrivSqZeroExt.fst := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_four, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_mul]

private theorem rd_snd_adj (X : M4 (DualNumber k)) : (adj X).map TrivSqZeroExt.snd = adj (X.map TrivSqZeroExt.snd) := by
  ext i j
  simp only [adj_apply, Matrix.map_apply, TrivSqZeroExt.snd_smul]

private theorem rd_fst_adj (X : M4 (DualNumber k)) : (adj X).map TrivSqZeroExt.fst = adj (X.map TrivSqZeroExt.fst) := by
  ext i j
  simp only [adj_apply, Matrix.map_apply, TrivSqZeroExt.fst_smul]

private theorem rd_gsp {ν : DualNumber k} (hν : ν.snd = 0) {X : M4 (DualNumber k)} (h : IsGSp ν X) :
    adj (X.map TrivSqZeroExt.snd) * X.map TrivSqZeroExt.fst + adj (X.map TrivSqZeroExt.fst) * X.map TrivSqZeroExt.snd = 0 := by
  rw [← rd_snd_adj, ← rd_fst_adj, ← rd_snd_mul, h]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij, hν]

private theorem rd_gsp_one {X : M4 (DualNumber k)} (h : IsGSp 1 X) :
    adj (X.map TrivSqZeroExt.fst) * X.map TrivSqZeroExt.fst = 1 := by
  rw [← rd_fst_adj, ← rd_fst_mul, h]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

end

end UpperTheory.V.Ws

theorem UpperTheory.V.Ws.redDual :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (Φ : Fr O Γ) {k : Type} [Field k] (a : O →+* DualNumber k) (S : Finset (ℤ × ℤ)) (c : PD Φ.ι Γ k) (Q : PD Φ.ι Γ (DualNumber k)),
          (∀ x, (a x).snd = 0) → Φ.IsPair a Q → (∀ i j, IsLocallyConstant fun g => Q.r g i j) → (∀ g i j, (Q.r g i j).fst = c.r g i j) → (∀ v i j, (Q.n v i j).fst = c.n v i j) → Supp S Q.r →
          ((fun g => (Q.r g).map TrivSqZeroExt.snd * c.r g⁻¹, fun v => (Q.n v).map TrivSqZeroExt.snd * adj (c.n v)) : (Γ → M4 k) × (Φ.ι → M4 k)) ∈ Φ.Tan S c := by
  intro O Γ _ _ _ _ Φ k _ a S c Q ha hP hlc hr hn hS
  have er : ∀ g, (Q.r g).map TrivSqZeroExt.fst = c.r g := fun g => Matrix.ext (hr g)
  have en : ∀ v, (Q.n v).map TrivSqZeroExt.fst = c.n v := fun v => Matrix.ext (hn v)
  have i1 : ∀ g, c.r g * c.r g⁻¹ = 1 := fun g => by rw [← map_mul, mul_inv_cancel, map_one]
  have i2 : ∀ g, c.r g⁻¹ * c.r g = 1 := fun g => by rw [← map_mul, inv_mul_cancel, map_one]
  have n1 : ∀ v, adj (c.n v) * c.n v = 1 := fun v => en v ▸ rd_gsp_one (hP.low v).1
  have n2 : ∀ v, c.n v * adj (c.n v) = 1 := fun v => mul_eq_one_comm.1 (n1 v)
  have n3 : ∀ v, adj ((Q.n v).map TrivSqZeroExt.snd) * c.n v + adj (c.n v) * (Q.n v).map TrivSqZeroExt.snd = 0 :=
    fun v => en v ▸ rd_gsp rfl (hP.low v).1
  have hl : IsLocallyConstant fun g => Q.r g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have : ∀ᶠ y in nhds x, ∀ i j, Q.r y i j = Q.r x i j :=
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (hlc i j).eventually_eq x
    exact this.mono fun y hy => Matrix.ext hy
  refine ⟨?_, fun g => ?_, fun g h => ?_, fun g hg => ?_, ?_, fun g i j hij hw => ?_, fun v => ⟨rd_sp (n2 v) (n3 v), fun i j hij => ?_⟩,
    fun v s hs => ?_⟩
  · have h1 := hl.comp fun X : M4 (DualNumber k) => X.map TrivSqZeroExt.snd
    have h2 := (hl.comp fun X : M4 (DualNumber k) => X.map TrivSqZeroExt.fst).comp_continuous continuous_inv
    have h3 := h1.mul h2
    convert h3 using 1
    funext g
    simp only [Function.comp_apply, Pi.mul_apply, er]
  · exact rd_sp (i1 g) (er g ▸ rd_gsp (ha _) (hP.mult g))
  · show _ * _ = _ * _ + _ * (_ * _) * _
    rw [map_mul, rd_snd_mul, er, er, mul_inv_rev, map_mul, add_mul, mul_assoc, ← mul_assoc (c.r h), i1, one_mul]
    simp only [mul_assoc]
  · show _ * _ = _
    rw [hP.kill g hg]
    have : (1 : M4 (DualNumber k)).map TrivSqZeroExt.snd = 0 := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    rw [this, zero_mul]
  · have d1 : ((Q.r Φ.g0).map TrivSqZeroExt.snd).IsDiag := hP.nrm.map rfl
    have d2 : (c.r Φ.g0).IsDiag := er _ ▸ hP.nrm.map rfl
    intro i j hij
    have e := i1 Φ.g0
    rw [← d2.diagonal_diag] at e
    have e1 := congrFun (congrFun e i) i
    have e2 := congrFun (congrFun e i) j
    rw [Matrix.diagonal_mul, Matrix.one_apply_eq] at e1
    rw [Matrix.diagonal_mul, Matrix.one_apply_ne hij] at e2
    have e3 := (mul_eq_zero.1 e2).resolve_left (left_ne_zero_of_mul_eq_one e1)
    show (_ * _ : M4 k) i j = 0
    rw [← d1.diagonal_diag, Matrix.diagonal_mul, e3, mul_zero]
  · show (_ * _ * _ : M4 k) i j = 0
    rw [mul_assoc, i2, mul_one, Matrix.map_apply, hS g i j hij hw]
    rfl
  · show (_ * (_ * _) * _ : M4 k) i j = 0
    rw [mul_assoc, mul_assoc, n1, mul_one, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : i < l
    · rw [adj_apply, ← hn, (hP.low v).2.2 _ _ (Fin.rev_lt_rev.2 hl)]
      simp
    · rw [Matrix.map_apply]
      rcases ((not_lt.1 hl).trans hij).lt_or_eq with h | h
      · rw [(hP.low v).2.2 _ _ h]; simp
      · rw [h, (hP.low v).2.1]; simp
  · have u1 : IsUp ((adj (Q.n v) * Q.r s * Q.n v).map TrivSqZeroExt.snd) := fun i j hij => by
      rw [Matrix.map_apply, hP.flag v s hs i j hij]; rfl
    have u2 : IsUp ((adj (Q.n v) * Q.r s⁻¹ * Q.n v).map TrivSqZeroExt.fst) := fun i j hij => by
      rw [Matrix.map_apply, hP.flag v _ (inv_mem hs) i j hij]; rfl
    have u := rd_up_mul u1 u2
    simp only [rd_snd_mul, rd_fst_mul, rd_snd_adj, rd_fst_adj, er, en] at u
    convert u using 1
    have k1 : ∀ X : M4 k, c.n v * (adj (c.n v) * X) = X := fun X => by rw [← mul_assoc, n2, one_mul]
    have k2 : ∀ X : M4 k, c.r s * (c.r s⁻¹ * X) = X := fun X => by rw [← mul_assoc, i1, one_mul]
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, k1, k2, n1, mul_one, eq_neg_of_add_eq_zero_left (n3 v)]
    abel
end
