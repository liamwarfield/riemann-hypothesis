module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.PdMapAdj

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UpDiagMul
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe40.M4 :
    Type → Type :=
    fun (R : Type) ↦ Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) R

noncomputable def UpperTheory.Reformulated.B.Qe40.IsUp :
    {R : Type} → [CommRing R] → UpperTheory.Reformulated.B.Qe40.M4 R → Prop :=
    fun {R : Type} [CommRing R] (X : UpperTheory.Reformulated.B.Qe40.M4 R) ↦ ∀ (i j : Fin (4 : ℕ)), j < i → X i j = (0 : R)

theorem UpperTheory.Reformulated.B.Qe40.up_diag_mul :
    ∀ {R : Type} [inst : CommRing R] {X Y : UpperTheory.Reformulated.B.Qe40.M4 R},
      UpperTheory.Reformulated.B.Qe40.IsUp X → UpperTheory.Reformulated.B.Qe40.IsUp Y → ∀ (i : Fin (4 : ℕ)), (X * Y) i i = X i i * Y i i := by
  intro R _ X Y hX hY i
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hX i k h, zero_mul]
  · rw [hY k i h, mul_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.PairNear
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem up_diag_mul {R : Type} [CommRing R] {X Y : M4 R} (hX : IsUp X) (hY : IsUp Y) (i : Fin 4) :
    (X * Y) i i = X i i * Y i i :=
  _root_.UpperTheory.Reformulated.B.Qe40.up_diag_mul hX hY i

private theorem low_inv {R : Type} [CommRing R] {n : M4 R} (h : IsLow n) : adj n * n = 1 ∧ n * adj n = 1 := by
  have h1 : adj n * n = 1 := by
    have := h.1
    rwa [IsGSp, one_smul] at this
  exact ⟨h1, mul_eq_one_comm.1 h1⟩

private def grChar {O Γ : Type} [CommRing O] [Group Γ] {Φ : Fr O Γ} {R : Type} [CommRing R] {a : O →+* R}
    (Q : PD Φ.ι Γ R) (h : Φ.IsPair a Q) (v : Φ.ι) (i : Fin 4) : Φ.Gv v →* R where
  toFun s := Q.ψ v i s
  map_one' := by
    show (adj (Q.n v) * Q.r 1 * Q.n v) i i = 1
    rw [map_one, mul_one, (low_inv (h.low v)).1, Matrix.one_apply_eq]
  map_mul' s t := by
    show (adj (Q.n v) * Q.r (s * t) * Q.n v) i i =
      (adj (Q.n v) * Q.r s * Q.n v) i i * (adj (Q.n v) * Q.r t * Q.n v) i i
    rw [← up_diag_mul (h.flag v s s.2) (h.flag v t t.2), map_mul]
    have e : adj (Q.n v) * Q.r s * Q.n v * (adj (Q.n v) * Q.r t * Q.n v) =
        adj (Q.n v) * Q.r s * (Q.n v * adj (Q.n v)) * Q.r t * Q.n v := by simp only [mul_assoc]
    rw [e, (low_inv (h.low v)).2]
    simp only [mul_assoc, one_mul]

private def lin (p q : ℤ) : ℤ × ℤ →+ ℤ where
  toFun w := p * w.1 + q * w.2
  map_zero' := by simp
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add]; ring

private theorem tau_nP : ∀ i j : Fin 4, (-2) * (wt i j).1 + (-1) * (wt i j).2 ≤ 0 → wt i j ∉ nP := by decide

private theorem tau_nM : ∀ i j : Fin 4, (-1) * (wt i j).1 + (-2) * (wt i j).2 ≤ 0 → wt i j ∉ nM := by decide

theorem UpperTheory.V.Ws.sxPairNear :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (c : PD Φ.ι Γ (ResidueField Λ)) (Q : PD Φ.ι Γ R), Φ.IsRes ((residue Λ).comp a) c → Φ.Lifts a c Q → ∃ (τ : ℤ × ℤ →+ ℤ) (D : RD Φ R), Φ.Near a τ D ∧ D.r = Q.r ∧ D.Flags Q.n := by
  intro O Γ _ _ _ Φ Λ _ _ a R _ _ _ c Q hc hQ
  have hr : ∀ g i j, res Λ R (Q.r g i j) = c.r g i j := fun g i j => by
    rw [← hQ.red]; rfl
  have hτ : ∃ τ : ℤ × ℤ →+ ℤ, ∀ g i j, i ≠ j → τ (wt i j) ≤ 0 → c.r g i j = 0 := by
    rcases hc.res.shape with h | h
    · exact ⟨lin (-2) (-1), fun g i j hij ht => h.1 g i j hij (tau_nP i j ht)⟩
    · exact ⟨lin (-1) (-2), fun g i j hij ht => h g i j hij (tau_nM i j ht)⟩
  obtain ⟨τ, hτ⟩ := hτ
  refine ⟨τ, ⟨Q.r, grChar Q hQ.pair⟩, ⟨⟨hQ.pair.mult, hQ.pair.kill, hQ.pair.nrm⟩, hQ.cont, fun v i N => ?_,
    fun g i => ?_, fun g i j hij ht => ?_, fun v i s => ?_⟩, rfl,
    ⟨hQ.pair.low, hQ.pair.flag, fun _ _ _ => rfl, fun v i s hs => hQ.pair.mu v s hs i⟩⟩
  · exact ((sxAdicMat (maximalIdeal R) (fun g => Q.r g) hQ.cont).2 (adj (Q.n v)) (Q.n v) i i N).comp_continuous
      continuous_subtype_val
  · exact (hr g i i).trans (hc.res.diag g i)
  · exact (res_eq_zero_iff Λ R _).1 ((hr g i j).trans (hτ g i j hij ht))
  · have h1 := (sxPdMap ((algebraMap Λ R).comp a) (res Λ R : R →+* ResidueField Λ) Q).1 v i s
    rw [hQ.red] at h1
    exact h1.symm.trans (hc.res.char v s s.2 i)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.ChConj
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section
variable {O Γ : Type} [CommRing O] [Group Γ] {Φ : Fr O Γ} {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

private theorem ch_adj (g : R →+* R') (X : M4 R) : adj (X.map g) = (adj X).map g := by
  ext i j
  simp [adj]

private theorem ch_map (D : RD Φ R) (f : R →+* R') (g : R' →+* R'') : (D.map f).map g = D.map (g.comp f) := by
  apply RD.ext
  · ext s i j
    rfl
  · funext v i
    ext s
    rfl

private theorem ch_conj (D : RD Φ R) (g : R →+* R') (X : M4 R) (s : Γ) (i j : Fin 4) :
    (adj (X.map g) * (D.map g).r s * X.map g) i j = g ((adj X * D.r s * X) i j) := by
  rw [ch_adj]
  show ((adj X).map g * (D.r s).map g * X.map g) i j = _
  rw [← Matrix.map_mul, ← Matrix.map_mul]
  rfl

private theorem ch_gsp (g : R →+* R') (X : M4 R) (i j : Fin 4) :
    (adj (X.map g) * X.map g - 1) i j = g ((adj X * X - 1) i j) := by
  rw [ch_adj, ← Matrix.map_mul, Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, map_sub,
    Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

private def chEq (D : RD Φ R) (n : Φ.ι → M4 R) : Set R :=
  {x | (∃ v i j, x = (adj (n v) * n v - 1) i j) ∨ (∃ v i, x = n v i i - 1) ∨ (∃ v i j, i < j ∧ x = n v i j) ∨
    (∃ v, ∃ s ∈ Φ.Gv v, ∃ i j, j < i ∧ x = (adj (n v) * D.r s * n v) i j) ∨
    (∃ v i, ∃ s : Φ.Gv v, x = (adj (n v) * D.r s * n v) i i - D.ψ v i s) ∨
    ∃ v i, ∃ s : Φ.Gv v, (s : Γ) ∈ Φ.Mu v ∧ x = D.ψ v i s - 1}

private theorem ch_iff (D : RD Φ R) (n : Φ.ι → M4 R) (g : R →+* R') :
    (D.map g).Flags (fun v => (n v).map g) ↔ ∀ x ∈ chEq D n, g x = 0 := by
  constructor
  · rintro ⟨hlow, hflag, hchar, hmu⟩ x hx
    rcases hx with ⟨v, i, j, rfl⟩ | ⟨v, i, rfl⟩ | ⟨v, i, j, hij, rfl⟩ | ⟨v, s, hs, i, j, hij, rfl⟩ |
      ⟨v, i, s, rfl⟩ | ⟨v, i, s, hs, rfl⟩
    · have hl : IsLow ((n v).map g) := hlow v
      unfold IsLow IsGSp at hl
      rw [← ch_gsp, hl.1]
      simp
    · have hl : IsLow ((n v).map g) := hlow v
      unfold IsLow at hl
      rw [map_sub, map_one, sub_eq_zero]
      exact hl.2.1 i
    · have hl : IsLow ((n v).map g) := hlow v
      unfold IsLow at hl
      exact hl.2.2 i j hij
    · rw [← ch_conj]
      exact hflag v s hs i j hij
    · rw [map_sub, sub_eq_zero, ← ch_conj]
      exact hchar v i s
    · rw [map_sub, map_one, sub_eq_zero]
      exact hmu v i s hs
  · intro h
    refine ⟨fun v => ?_, fun v s hs i j hij => ?_, fun v i s => ?_, fun v i s hs => ?_⟩
    · unfold IsLow IsGSp
      refine ⟨?_, fun i => ?_, fun i j hij => ?_⟩
      · ext i j
        have hx := h _ (Or.inl ⟨v, i, j, rfl⟩)
        rw [← ch_gsp, Matrix.sub_apply, sub_eq_zero] at hx
        rw [one_smul]
        exact hx
      · have hx := h _ (Or.inr (Or.inl ⟨v, i, rfl⟩))
        rw [map_sub, map_one, sub_eq_zero] at hx
        exact hx
      · exact h _ (Or.inr (Or.inr (Or.inl ⟨v, i, j, hij, rfl⟩)))
    · have hx := h _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨v, s, hs, i, j, hij, rfl⟩))))
      rw [← ch_conj] at hx
      exact hx
    · have hx := h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨v, i, s, rfl⟩)))))
      rw [map_sub, sub_eq_zero, ← ch_conj] at hx
      exact hx
    · have hx := h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨v, i, s, hs, rfl⟩)))))
      rw [map_sub, map_one, sub_eq_zero] at hx
      exact hx

end

theorem UpperTheory.V.Ws.sxChart :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] {Φ : Fr O Γ} {A₀ : Type} [CommRing A₀] (D : RD Φ A₀), ∃ (A : Type) (_ : CommRing A) (_ : Algebra A₀ A) (n : Φ.ι → M4 A), Algebra.FiniteType A₀ A ∧ Algebra.adjoin A₀ (Set.range fun x : Φ.ι × Fin 4 × Fin 4 => n x.1 x.2.1 x.2.2) = ⊤ ∧ (D.map (algebraMap A₀ A)).Flags n ∧ ∀ (R : Type) [CommRing R] (f : A₀ →+* R) (n' : Φ.ι → M4 R), (D.map f).Flags n' → ∃ F : A →+* R, F.comp (algebraMap A₀ A) = f ∧ ∀ v, (n v).map F = n' v := by
  intro O Γ _ _ Φ A₀ _ D
  classical
  let σ := Φ.ι × Fin 4 × Fin 4
  let N : Φ.ι → M4 (MvPolynomial σ A₀) := fun v => Matrix.of fun i j => MvPolynomial.X (v, i, j)
  let I : Ideal (MvPolynomial σ A₀) := Ideal.span (chEq (D.map MvPolynomial.C) N)
  let n : Φ.ι → M4 (MvPolynomial σ A₀ ⧸ I) := fun v => (N v).map (Ideal.Quotient.mk I)
  have hfac : algebraMap A₀ (MvPolynomial σ A₀ ⧸ I) = (Ideal.Quotient.mk I).comp MvPolynomial.C :=
    RingHom.ext fun _ => rfl
  refine ⟨MvPolynomial σ A₀ ⧸ I, inferInstance, inferInstance, n, ?_, ?_, ?_, ?_⟩
  · exact Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A₀ I) (Ideal.Quotient.mkₐ_surjective A₀ I)
  · have hset : (Set.range fun x : Φ.ι × Fin 4 × Fin 4 => n x.1 x.2.1 x.2.2) =
        (Ideal.Quotient.mkₐ A₀ I) '' Set.range (MvPolynomial.X : σ → MvPolynomial σ A₀) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨MvPolynomial.X x, ⟨x, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, rfl⟩
    rw [hset, Algebra.adjoin_image, MvPolynomial.adjoin_range_X, Algebra.map_top, AlgHom.range_eq_top]
    exact Ideal.Quotient.mkₐ_surjective A₀ I
  · rw [hfac, ← ch_map]
    exact (ch_iff _ _ _).2 fun x hx => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span hx)
  · intro R _ f n' hn'
    let φ : MvPolynomial σ A₀ →+* R := MvPolynomial.eval₂Hom f fun x => n' x.1 x.2.1 x.2.2
    have hφC : φ.comp MvPolynomial.C = f := MvPolynomial.eval₂Hom_comp_C f _
    have hN : ∀ v, (N v).map φ = n' v := by
      intro v
      ext i j
      simp [φ, N]
    have hfl : ((D.map MvPolynomial.C).map φ).Flags (fun v => (N v).map φ) := by
      have hfun : (fun v => (N v).map φ) = n' := funext hN
      rw [ch_map, hφC, hfun]
      exact hn'
    have hker : I ≤ RingHom.ker φ :=
      Ideal.span_le.2 fun x hx => RingHom.mem_ker.2 ((ch_iff _ _ _).1 hfl x hx)
    refine ⟨Ideal.Quotient.lift I φ fun a ha => RingHom.mem_ker.1 (hker ha), ?_, ?_⟩
    · rw [hfac, ← RingHom.comp_assoc, Ideal.Quotient.lift_comp_mk, hφC]
    · intro v
      rw [← hN v]
      ext i j
      simp [n]
end

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem isGSp_map' {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {ν : R} {X : M4 R}
    (h : IsGSp ν X) : IsGSp (f ν) (X.map f) := by
  unfold IsGSp at *
  ext i j
  have := congrArg f (congrFun (congrFun h i) j)
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [Matrix.mul_apply, adj_apply, Matrix.one_apply, map_sum, apply_ite f] using this

open Classical in
theorem UpperTheory.V.Ws.sxPreOfCore :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ}, (∀ v, ∀ s ∈ Φ.Mu v, s ∈ Φ.Gv v) → Core Φ a → Nonempty (Pre Φ a) := by
  intro O Γ _ _ _ Φ Λ _ _ a hMu X
  obtain ⟨A, cA, aA, n, hft, hgen, hfl, huniv⟩ := sxChart X.D
  letI aBA : Algebra X.B A := ((algebraMap X.A A).comp (algebraMap X.B X.A)).toAlgebra
  letI aLA : Algebra Λ A := ((algebraMap X.A A).comp (algebraMap Λ X.A)).toAlgebra
  have hB : ∀ b, algebraMap X.B A b = algebraMap X.A A (algebraMap X.B X.A b) := fun _ => rfl
  have hL : ∀ b, algebraMap Λ A b = algebraMap X.A A (algebraMap Λ X.A b) := fun _ => rfl
  haveI t1 : IsScalarTower X.B X.A A := IsScalarTower.of_algebraMap_eq hB
  haveI t2 : IsScalarTower Λ X.B A := IsScalarTower.of_algebraMap_eq fun x => by
    rw [hB, hL, ← IsScalarTower.algebraMap_apply Λ X.B X.A]
  let P : PD Φ.ι Γ A := ⟨mapRep (algebraMap X.A A) X.D.r, n⟩
  have hr : ∀ g, P.r g = (X.D.r g).map (algebraMap X.A A) := fun _ => rfl
  have hψ : ∀ v i (s : Φ.Gv v), P.ψ v i s = algebraMap X.A A (X.D.ψ v i s) := fun v i s => hfl.char v i s
  refine ⟨{ A := A, B := X.B, ft := X.ft.trans hft, P := P, pair := ?_, cont := ?_, gen := ?_, cp := X.cp,
            cp_map := ?_, cp_cont := X.cp_cont, cp_red := X.cp_red,
            ψ := fun v i s => if h : s ∈ Φ.Gv v then X.ψ v i ⟨s, h⟩ else 0,
            ψ_map := ?_, ψ_cont := ?_, ψ_red := ?_, genB := ?_, univ := ?_ }⟩
  · refine ⟨fun g => isGSp_map' (algebraMap X.A A) (X.rep.mult g), fun g hg => ?_, ?_, hfl.low, hfl.flag,
      fun v s hs i => ?_⟩
    · rw [hr, X.rep.kill g hg, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [hr]
      exact X.rep.nrm.map (map_zero _)
    · exact (hfl.char v i ⟨s, hMu v s hs⟩).trans (hfl.mu v i ⟨s, hMu v s hs⟩ hs)
  · intro i j
    refine adicCont_map (algebraMap X.A A) ?_ (X.cont i j)
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    exact Ideal.mem_map_of_mem (algebraMap X.B A) hb
  · rw [eq_top_iff]
    set S := Algebra.adjoin X.B ((Set.range fun x : Γ × Fin 4 × Fin 4 => P.r x.1 x.2.1 x.2.2) ∪
      Set.range fun x : Φ.ι × Fin 4 × Fin 4 => P.n x.1 x.2.1 x.2.2) with hS
    have h0 : ∀ x : X.A, algebraMap X.A A x ∈ S := by
      intro x
      have hx : x ∈ Algebra.adjoin X.B (Set.range fun x : Γ × Fin 4 × Fin 4 => X.D.r x.1 x.2.1 x.2.2) := by
        rw [X.gen]; trivial
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨y, rfl⟩ := hx
        exact Algebra.subset_adjoin (Or.inl ⟨y, rfl⟩)
      | algebraMap b => exact S.algebraMap_mem b
      | add x y _ _ hx hy => rw [map_add (f := _)]; exact S.add_mem hx hy
      | mul x y _ _ hx hy => rw [map_mul]; exact S.mul_mem hx hy
    rintro x -
    have hx : x ∈ Algebra.adjoin X.A (Set.range fun x : Φ.ι × Fin 4 × Fin 4 => n x.1 x.2.1 x.2.2) := by
      rw [hgen]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin (Or.inr hx)
    | algebraMap b => exact h0 b
    | add x y _ _ hx hy => exact S.add_mem hx hy
    | mul x y _ _ hx hy => exact S.mul_mem hx hy
  · intro g
    rw [hr, Matrix.charpoly_map, ← X.cp_map, Polynomial.map_map]
    rfl
  · intro v i s hs
    rw [dite_eq_left hs, hB, X.ψ_map]
    exact (hψ v i ⟨s, hs⟩).symm
  · intro v i
    simpa using X.ψ_cont v i
  · intro v i s hs
    rw [dite_eq_left hs]
    exact X.ψ_red v i ⟨s, hs⟩
  · intro R _ _ _ f f' h1 h2
    refine X.genB R f f' h1 fun v i s => ?_
    simpa using h2 v i s s.2
  · intro R _ _ _ c Q hc hQ
    obtain ⟨τ, D', hN, hDr, hF⟩ := sxPairNear c Q hc hQ
    obtain ⟨f, hf⟩ := X.univ R τ D' hN
    obtain ⟨F, hF1, hF2⟩ := huniv R (f : X.A →+* R) Q.n (hf ▸ hF)
    have hF3 : ∀ x, F (algebraMap X.A A x) = f x := fun x => RingHom.congr_fun hF1 x
    refine ⟨{ F with commutes' := fun x => ?_ }, ?_⟩
    · exact (hF3 _).trans (f.commutes x)
    · refine PD.ext ?_ (funext hF2)
      rw [← hDr, ← hf]
      ext g i j
      exact hF3 _
