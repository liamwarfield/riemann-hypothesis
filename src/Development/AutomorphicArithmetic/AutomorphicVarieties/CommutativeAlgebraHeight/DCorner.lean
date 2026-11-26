module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DkerOfKills
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DFactor

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DCorner
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section aux

variable {A E : Type} [CommRing A] [Ring E] [Algebra A E]

private lemma map_smul_c {B B' : Type} [CommRing B] [Algebra A B] [CommRing B'] [Algebra A B'] (φ : B →ₐ[A] B')
    (c : B) (w : B ⊗[A] E) :
    Algebra.TensorProduct.map φ (AlgHom.id A E) (c • w) = φ c • Algebra.TensorProduct.map φ (AlgHom.id A E) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [smul_tmul']
  | add a b ha hb => simp only [smul_add, map_add (f := _), ha, hb]

private lemma map_map_c {B B' B'' : Type} [CommRing B] [Algebra A B] [CommRing B'] [Algebra A B']
    [CommRing B''] [Algebra A B''] (φ : B →ₐ[A] B') (ψ : B' →ₐ[A] B'') (χ : B →ₐ[A] B'') (h : ∀ b, ψ (φ b) = χ b)
    (w : B ⊗[A] E) :
    Algebra.TensorProduct.map ψ (AlgHom.id A E) (Algebra.TensorProduct.map φ (AlgHom.id A E) w) =
      Algebra.TensorProduct.map χ (AlgHom.id A E) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [h]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

private lemma add_of_homog (f : ∀ (B : Type) [CommRing B] [Algebra A B], B ⊗[A] E → B)
    (nat : ∀ (B B' : Type) [CommRing B] [Algebra A B] [CommRing B'] [Algebra A B'] (φ : B →ₐ[A] B') (x : B ⊗[A] E),
      f B' (Algebra.TensorProduct.map φ (AlgHom.id A E) x) = φ (f B x))
    (hom : ∀ (B : Type) [CommRing B] [Algebra A B] (b : B) (x : B ⊗[A] E), f B (b • x) = b * f B x)
    (B : Type) [CommRing B] [Algebra A B] (x y : B ⊗[A] E) : f B (x + y) = f B x + f B y := by
  let i2 : B →ₐ[A] TrivSqZeroExt B (B × B) := IsScalarTower.toAlgHom A B _
  let i1 : B →ₐ[A] TrivSqZeroExt B B := IsScalarTower.toAlgHom A B _
  let z : TrivSqZeroExt B (B × B) ⊗[A] E :=
    (TrivSqZeroExt.inr (1, 0) : TrivSqZeroExt B (B × B)) • Algebra.TensorProduct.map i2 (AlgHom.id A E) x +
    (TrivSqZeroExt.inr (0, 1) : TrivSqZeroExt B (B × B)) • Algebra.TensorProduct.map i2 (AlgHom.id A E) y
  have key : ∀ (g : (B × B) →ₗ[B] B), g (f _ z).snd = (f _
      ((TrivSqZeroExt.inr (g (1, 0)) : TrivSqZeroExt B B) • Algebra.TensorProduct.map i1 (AlgHom.id A E) x +
       (TrivSqZeroExt.inr (g (0, 1)) : TrivSqZeroExt B B) • Algebra.TensorProduct.map i1 (AlgHom.id A E) y)).snd := by
    intro g
    have h := nat _ _ ((TrivSqZeroExt.map g).restrictScalars A) z
    have hc : ∀ b, ((TrivSqZeroExt.map g).restrictScalars A) (i2 b) = i1 b := fun b =>
      (TrivSqZeroExt.map g).commutes b
    simp only [z, map_add (f := _), map_smul_c, map_map_c i2 _ i1 hc] at h
    have h2 := congrArg TrivSqZeroExt.snd h
    simp only [AlgHom.restrictScalars_apply, TrivSqZeroExt.map_inr, TrivSqZeroExt.snd_map] at h2
    exact h2.symm
  have ev : ∀ w : B ⊗[A] E, (f _ ((TrivSqZeroExt.inr 1 : TrivSqZeroExt B B) •
      Algebra.TensorProduct.map i1 (AlgHom.id A E) w)).snd = f B w := by
    intro w
    rw [hom, nat]
    simp [i1, TrivSqZeroExt.algebraMap_eq_inl]
  have k1 := key (LinearMap.fst B B B)
  have k2 := key (LinearMap.snd B B B)
  have k3 := key (LinearMap.fst B B B + LinearMap.snd B B B)
  simp only [LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.add_apply, TrivSqZeroExt.inr_zero, zero_smul,
    add_zero, zero_add, ← smul_add, ← map_add, ev] at k1 k2 k3
  rw [← k1, ← k2, ← k3]

end aux

section aux2

variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (e : E)

private noncomputable def cornerF (B : Type) [CommRing B] [Algebra A B] (z : B ⊗[A] E) : B :=
  D.D B (1 - (1 : B) ⊗ₜ[A] e + (1 : B) ⊗ₜ[A] e * z * (1 : B) ⊗ₜ[A] e)

private lemma cornerF_nat (B B' : Type) [CommRing B] [Algebra A B] [CommRing B'] [Algebra A B'] (φ : B →ₐ[A] B')
    (x : B ⊗[A] E) :
    cornerF D e B' (Algebra.TensorProduct.map φ (AlgHom.id A E) x) = φ (cornerF D e B x) := by
  unfold cornerF
  rw [← D.nat]
  simp

variable {D e}

private lemma one_add_e (h1 : D.D A[X] (1 + X ⊗ₜ e) = 1 + X) (B : Type) [CommRing B] [Algebra A B] (b : B) :
    D.D B (1 + b ⊗ₜ e) = 1 + b := by
  have := D.nat A[X] B (aeval b) (1 + X ⊗ₜ e)
  rw [h1] at this
  simpa using this

private lemma ee (he : IsIdempotentElem e) (B : Type) [CommRing B] [Algebra A B] :
    ((1 : B) ⊗ₜ[A] e) * ((1 : B) ⊗ₜ[A] e) = (1 : B) ⊗ₜ[A] e := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, he.eq, one_mul]

private lemma tmul_eq (B : Type) [CommRing B] [Algebra A B] (b : B) (x : E) :
    b ⊗ₜ[A] x = b • ((1 : B) ⊗ₜ[A] x) := by
  simp [smul_tmul']

private lemma cornerF_hom (he : IsIdempotentElem e) (h1 : D.D A[X] (1 + X ⊗ₜ e) = 1 + X)
    (B : Type) [CommRing B] [Algebra A B] (b : B) (x : B ⊗[A] E) :
    cornerF D e B (b • x) = b * cornerF D e B x := by
  unfold cornerF
  have h := one_add_e h1 B (b - 1)
  rw [add_sub_cancel] at h
  conv_rhs => rw [← h, ← map_mul]
  congr 1
  rw [tmul_eq B (b - 1)]
  have h2 := ee (A := A) he B
  generalize ((1 : B) ⊗ₜ[A] e) = ε at h2 ⊢
  simp only [add_mul, mul_add, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, ← mul_assoc, h2, sub_smul,
    one_smul, sub_mul]
  abel

private lemma cornerF_add (he : IsIdempotentElem e) (h1 : D.D A[X] (1 + X ⊗ₜ e) = 1 + X)
    (B : Type) [CommRing B] [Algebra A B] (x y : B ⊗[A] E) :
    cornerF D e B (x + y) = cornerF D e B x + cornerF D e B y :=
  add_of_homog (cornerF D e) (cornerF_nat D e) (cornerF_hom he h1) B x y

private lemma cornerF_e (he : IsIdempotentElem e) (h1 : D.D A[X] (1 + X ⊗ₜ e) = 1 + X)
    (B : Type) [CommRing B] [Algebra A B] (b : B) : cornerF D e B (b ⊗ₜ e) = b := by
  rw [tmul_eq, cornerF_hom he h1, cornerF, ee he, ee he, sub_add_cancel, map_one, mul_one]

private lemma cornerF_tmul (he : IsIdempotentElem e) (h1 : D.D A[X] (1 + X ⊗ₜ e) = 1 + X)
    (B : Type) [CommRing B] [Algebra A B] (b : B) (u : E) :
    cornerF D e B (b ⊗ₜ u) = b * algebraMap A B (cornerF D e A (1 ⊗ₜ u)) := by
  rw [tmul_eq, cornerF_hom he h1]
  congr 1
  have := cornerF_nat D e A B (Algebra.ofId A B) (1 ⊗ₜ u)
  simpa [Algebra.ofId_apply] using this

private lemma cornerF_tr (he : IsIdempotentElem e) (h1 : D.D A[X] (1 + X ⊗ₜ e) = 1 + X) (hn : 1 ≤ n)
    (u : E) (hu : e * u * e = u) : D.tr u = cornerF D e A (1 ⊗ₜ u) := by
  have h : D.D A[X] (1 + X ⊗ₜ u) = cornerF D e A[X] (1 ⊗ₜ e + X ⊗ₜ u) := by
    unfold cornerF
    congr 1
    simp [mul_add, add_mul, he.eq, hu, ← add_assoc]
  rw [cornerF_add he h1, cornerF_e he h1, cornerF_tmul he h1, (d_chi D u).2.2.1] at h
  have h2 := congrArg (fun p => p.coeff 1) h
  simp only [finsetSum_coeff, coeff_C_mul_X_pow] at h2
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.2 (by omega))] at h2
  simpa [Det.tr, coeff_one] using h2

private lemma compl_e (he : IsIdempotentElem e) (h1 : D.D A[X] (1 + X ⊗ₜ e) = 1 + X) (hn : 1 ≤ n)
    (S : Type) [CommRing S] [Algebra A S] :
    D.D S[X] (X ⊗ₜ 1 - X ⊗ₜ e + 1 ⊗ₜ e) = X ^ (n - 1) := by
  have h := one_add_e h1 S[X] (X - 1)
  rw [add_sub_cancel] at h
  have h2 : D.D S[X] (X ⊗ₜ 1 - X ⊗ₜ e + 1 ⊗ₜ e) * X = X ^ (n - 1) * X := by
    conv_lhs => enter [2]; rw [← h]
    rw [← map_mul, ← pow_succ, Nat.sub_add_cancel hn]
    have := D.homog S[X] X 1
    rw [map_one, mul_one] at this
    rw [← this]
    congr 1
    simp only [mul_add, add_mul, sub_mul, mul_one, Algebra.TensorProduct.tmul_mul_tmul, he.eq, one_mul, mul_sub,
      sub_tmul, Algebra.TensorProduct.one_def, smul_tmul', smul_eq_mul]
    abel
  exact (Polynomial.isRegular_X.right) h2

private lemma chiS_corner (he : IsIdempotentElem e) (h1 : D.D A[X] (1 + X ⊗ₜ e) = 1 + X) (hn : 1 ≤ n)
    (S : Type) [CommRing S] [Algebra A S] (s : S) (u : E) (hu : e * u * e = u) :
    D.chiS S (1 ⊗ₜ e + s ⊗ₜ u) = X ^ (n - 1) * (X - C (1 + s * algebraMap A S (D.tr u))) := by
  have hl : e * u = u := by rw [← hu, ← mul_assoc, ← mul_assoc, he.eq]
  have hr : u * e = u := by rw [← hu, mul_assoc, he.eq]
  have h : cornerF D e S[X] ((X - 1) ⊗ₜ e + (- C s) ⊗ₜ u) = X - C (1 + s * algebraMap A S (D.tr u)) := by
    rw [cornerF_add he h1, cornerF_e he h1, cornerF_tmul he h1, ← cornerF_tr he h1 hn u hu]
    simp [Polynomial.algebraMap_apply]
    ring
  rw [← h, ← compl_e he h1 hn, cornerF, ← map_mul, Det.chiS]
  congr 1
  simp only [mul_add, add_mul, sub_mul, mul_one, Algebra.TensorProduct.tmul_mul_tmul, he.eq, one_mul, mul_sub,
      sub_tmul, Algebra.TensorProduct.one_def, hr, hl, map_add, Algebra.TensorProduct.map_tmul, map_one,
      AlgHom.id_apply, IsScalarTower.toAlgHom_apply, Polynomial.algebraMap_eq, neg_tmul, mul_neg, neg_mul]
  abel

private lemma corner_eq (hD : D.IsCH) (he : IsIdempotentElem e) (h1 : D.D A[X] (1 + X ⊗ₜ e) = 1 + X) (hn : 1 ≤ n)
    (u : E) (hu : e * u * e = u) : u = D.tr u • e := by
  have hl : e * u = u := by rw [← hu, ← mul_assoc, ← mul_assoc, he.eq]
  have hr : u * e = u := by rw [← hu, mul_assoc, he.eq]
  let s : TrivSqZeroExt A A := TrivSqZeroExt.inr 1
  have hs : s * s = 0 := TrivSqZeroExt.inr_mul_inr _ _ _
  have h := (d_chS D (TrivSqZeroExt A A)).1 (1 ⊗ₜ e + s ⊗ₜ u)
  rw [chiS_corner he h1 hn _ s u hu, show D.CH = ⊥ from hD] at h
  have h0 := (Submodule.span_le (p := ⊥)).2 (by
    rintro _ ⟨z, hz, rfl⟩
    have : z = 0 := by simpa using hz
    simp [this]) h
  rw [Submodule.mem_bot, map_mul, map_pow, map_sub, aeval_X, aeval_C] at h0
  have h2 : ((1 ⊗ₜ e + s ⊗ₜ u : TrivSqZeroExt A A ⊗[A] E) - algebraMap (TrivSqZeroExt A A) _
      (1 + s * algebraMap A _ (D.tr u))) * (1 ⊗ₜ e) = s ⊗ₜ (u - D.tr u • e) := by
    simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, sub_mul, add_mul,
      Algebra.TensorProduct.tmul_mul_tmul, he.eq, hr, mul_one, one_mul, add_tmul, tmul_sub]
    rw [← smul_tmul, Algebra.smul_def, mul_comm s]
    abel
  have h3 : ∀ k : ℕ, (1 ⊗ₜ e + s ⊗ₜ u : TrivSqZeroExt A A ⊗[A] E) ^ k * (s ⊗ₜ (u - D.tr u • e)) =
      s ⊗ₜ (u - D.tr u • e) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_assoc, ih, add_mul, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, hs, zero_tmul, add_zero, one_mul, mul_sub, hl, mul_smul_comm, he.eq]
  have h4 := congrArg (· * ((1 : TrivSqZeroExt A A) ⊗ₜ[A] e)) h0
  simp only [mul_assoc, h2, h3, zero_mul] at h4
  have h5 := congrArg (fun w => TensorProduct.lid A E ((TrivSqZeroExt.sndHom A A).rTensor E w)) h4
  simpa [s, sub_eq_zero] using h5

end aux2

theorem UpperTheory.V.CA.d_corner :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (e : E), D.IsCH → IsIdempotentElem e → D.D A[X] (1 + X ⊗ₜ e) = 1 + X → 1 ≤ n → (∀ x, e * x * e = D.tr (e * x) • e) ∧ D.tr e = 1 ∧ (∀ a : A, a • e = 0 → a = 0) ∧ ∀ a : A, D.D A[X] (1 + X ⊗ₜ (a • e)) = 1 + C a * X := by
  intro n A E _ _ _ D e hD he h1 hn
  have h4 : ∀ a : A, D.D A[X] (1 + X ⊗ₜ (a • e)) = 1 + C a * X := by
    intro a
    rw [← smul_tmul, one_add_e h1, Polynomial.smul_eq_C_mul]
  refine ⟨fun x => ?_, ?_, fun a ha => ?_, h4⟩
  · have h := corner_eq hD he h1 hn (e * x * e) (by
      rw [← mul_assoc, ← mul_assoc, he.eq, mul_assoc _ e e, he.eq])
    have h2 : D.tr (e * x * e) = D.tr (e * x) := by
      rw [Det.tr, (d_tr D).2.1 1 (e * x) e, ← mul_assoc, he.eq, Det.tr]
    rw [← h2]; exact h
  · rw [cornerF_tr he h1 hn e (by rw [he.eq, he.eq]), cornerF_e he h1]
  · have h := h4 a
    rw [ha, tmul_zero, add_zero, map_one] at h
    have h2 := congrArg (fun p => p.coeff 1) h
    simpa [coeff_one] using h2.symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ExistsOpenNormalSubgroupKillsOfGroupDetLawIsCont
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem lc_nhds {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    {f : G → X} (hf : IsLocallyConstant f) : ∀ᶠ h in nhds (1 : G), ∀ g, f (g * h) = f g := by
  have h1 : ∀ y ∈ Set.range f, ∀ᶠ h in nhds (1 : G), ∀ g, f g = y → f (g * h) = y := by
    intro y _
    obtain ⟨T, hT, hW⟩ := IsTopologicalGroup.exist_mul_closure_nhds (hf.isClopen_fiber y)
    filter_upwards [hT] with h hh g hg
    exact hW (Set.mul_mem_mul (show g ∈ {x | f x = y} from hg) hh)
  filter_upwards [(Filter.eventually_all_finite hf.range_finite).2 h1] with h hh g
  exact hh _ ⟨g, rfl⟩ g rfl

private theorem lift_single {A G ι : Type} [CommRing A] [Group G] (g : ι → G) (w : FreeMonoid ι) :
    FreeMonoid.lift (fun a => (MonoidAlgebra.single (g a) 1 : MonoidAlgebra A G)) w =
      MonoidAlgebra.single (FreeMonoid.lift g w) 1 := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [MonoidAlgebra.one_def]
  | of_mul a w ih => simp [ih, MonoidAlgebra.single_mul_single]

private theorem lift_mk {G ι : Type} [Group G] (H : Subgroup G) [H.Normal] (g g' : ι → G)
    (hg : ∀ a, (g a : G ⧸ H) = g' a) (w : FreeMonoid ι) :
    ((FreeMonoid.lift g w : G) : G ⧸ H) = (FreeMonoid.lift g' w : G) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul a w ih => simp [ih, hg]

private theorem key_fin {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (H : Subgroup G) [H.Normal]
    (hD : ∀ i ≤ n, ∀ h ∈ H, ∀ g, D.lam i (MonoidAlgebra.single (g * h) 1) = D.lam i (MonoidAlgebra.single g 1))
    {k : ℕ} (g g' : Fin k → G) (hg : ∀ a, (g a : G ⧸ H) = g' a) (S : Type) [CommRing S] [Algebra A S]
    (s : Fin k → S) :
    D.D S (1 + ∑ a, MonoidAlgebra.single (g a) (s a)) = D.D S (1 + ∑ a, MonoidAlgebra.single (g' a) (s a)) := by
  have h1 : ∀ g : Fin k → G, D.D S (1 + ∑ a, MonoidAlgebra.single (g a) (s a)) =
      MvPolynomial.aeval s (D.toDet.D (MvPolynomial (Fin k) A)
        (1 + Det.gen fun a => (MonoidAlgebra.single (g a) 1 : MonoidAlgebra A G))) := by
    intro g
    rw [← D.toDet.nat]
    change _ = D.D S (ofT A G S _)
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Det.gen, map_sum, ofT_tmul]
  rw [h1, h1]
  congr 1
  ext α
  obtain ⟨P, hP, -, hP'⟩ := d_amitsur n k α
  rw [hP', hP']
  refine MvPolynomial.hom_congr_vars ?_ ?_ rfl
  · ext a
    simp
  · intro v hv _
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X, lift_single, (d_toDet D _).2.1]
    have h2 := QuotientGroup.eq.1 (lift_mk H g g' hg v.2)
    rw [← hD v.1 (hP v hv).2.1 _ h2, mul_inv_cancel_left]

private theorem key {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (H : Subgroup G) [H.Normal]
    (hD : ∀ i ≤ n, ∀ h ∈ H, ∀ g, D.lam i (MonoidAlgebra.single (g * h) 1) = D.lam i (MonoidAlgebra.single g 1))
    {ι : Type} [Fintype ι] (g g' : ι → G) (hg : ∀ a, (g a : G ⧸ H) = g' a) (S : Type) [CommRing S] [Algebra A S]
    (s : ι → S) :
    D.D S (1 + ∑ a, MonoidAlgebra.single (g a) (s a)) = D.D S (1 + ∑ a, MonoidAlgebra.single (g' a) (s a)) := by
  let e := (Fintype.equivFin ι).symm
  rw [← e.sum_comp, ← e.sum_comp (fun a => MonoidAlgebra.single (g' a) (s a))]
  exact key_fin D H hD (g ∘ e) (g' ∘ e) (fun a => hg _) S (s ∘ e)

private theorem kills {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (H : Subgroup G) [H.Normal]
    (hD : ∀ i ≤ n, ∀ h ∈ H, ∀ g, D.lam i (MonoidAlgebra.single (g * h) 1) = D.lam i (MonoidAlgebra.single g 1))
    {h : G} (hh : h ∈ H) : D.Kills (MonoidAlgebra.single h 1 - 1) := by
  intro S _ _ u
  have hu : ∃ (ι : Type) (_ : Fintype ι) (g : ι → G) (s : ι → S), u = ∑ a, MonoidAlgebra.single (g a) (s a) := by
    induction u using MonoidAlgebra.induction_linear with
    | zero => exact ⟨Empty, inferInstance, Empty.elim, Empty.elim, by simp⟩
    | single g r => exact ⟨Unit, inferInstance, fun _ => g, fun _ => r, by simp⟩
    | add a b ha hb =>
      obtain ⟨ι, _, g, s, rfl⟩ := ha
      obtain ⟨ι', _, g', s', rfl⟩ := hb
      exact ⟨ι ⊕ ι', inferInstance, Sum.elim g g', Sum.elim s s', by simp⟩
  obtain ⟨ι, _, g, s, rfl⟩ := hu
  have h1 := key D H hD (ι := ι ⊕ ι) (Sum.elim (fun a => g a * h) g) (Sum.elim g g)
    (by rintro (a | a)
        · simpa using hh
        · rfl) S (Sum.elim s fun a => - s a)
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, MonoidAlgebra.single_neg, Finset.sum_neg_distrib,
    add_neg_cancel, add_zero, map_one] at h1
  rw [← h1]
  congr 2
  simp [mul_sub, Finset.sum_mul, MonoidAlgebra.single_mul_single, sub_eq_add_neg, mul_add]

theorem UpperTheory.V.CA.exists_openNormalSubgroup_kills_of_groupDetLaw_isCont :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (I : Ideal A), D.IsCont I → ∀ N : ℕ, ∃ H : OpenNormalSubgroup G, ∀ h ∈ H, (D.map (Ideal.Quotient.mk (I ^ N))).Kills (MonoidAlgebra.single h 1 - 1) := by
  intro n A G _ _ D _ _ _ _ I hD N
  have h1 := (Filter.eventually_all_finite (Set.finite_Iic n)).2 fun i _ => lc_nhds (hD i N)
  obtain ⟨U, hU, hUo, hU1⟩ := mem_nhds_iff.1 h1
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUo hU1
  refine ⟨H, fun h hh => kills _ H.toSubgroup ?_ hh⟩
  intro i hi h hh g
  have h2 : ∀ g : G, (D.map (Ideal.Quotient.mk (I ^ N))).lam i (MonoidAlgebra.single g 1) =
      Ideal.Quotient.mk (I ^ N) (D.lam i (MonoidAlgebra.single g 1)) := by
    intro g
    rw [← ((d_gmap D).2.2.1 _ _).2 i, MonoidAlgebra.mapRingHom_single, map_one]
  rw [h2, h2]
  exact hU (hH hh) i hi g
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FgChi
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem fg_ev {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (e : E) (r : ℕ)
    (h : D.D A[X] (1 + X ⊗ₜ e) = (1 + X) ^ r) (b : A[X]) : D.D A[X] (1 + (b - 1) ⊗ₜ e) = b ^ r := by
  have h2 := D.nat A[X] A[X] (aeval (b - 1)) (1 + X ⊗ₜ e)
  rw [h] at h2
  simpa using h2

private theorem fg_chi {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (e : E)
    (he : IsIdempotentElem e) (r s : ℕ) (h : D.D A[X] (1 + X ⊗ₜ e) = (1 + X) ^ r)
    (h' : D.D A[X] (1 + X ⊗ₜ (1 - e)) = (1 + X) ^ s) : D.chi e = X ^ s * (X - 1) ^ r := by
  rw [← fg_ev D e r h, ← fg_ev D (1 - e) s h', ← map_mul, Det.chi]
  congr 1
  rw [add_mul, mul_add, mul_add, Algebra.TensorProduct.tmul_mul_tmul, he.one_sub_mul_self, tmul_zero]
  simp only [one_mul, mul_one, tmul_sub, sub_tmul, ← Algebra.TensorProduct.one_def]
  abel

private theorem fg_one {k : Type} [Field k] {r s m : ℕ} (h : (X : k[X]) ^ s * (X - 1) ^ r = (X - 1) * X ^ m) :
    r = 1 := by
  rcases r with _ | _ | r
  · simpa using congrArg (eval 1) h
  · rfl
  · have h0 : (X - 1 : k[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1 : k)
    rw [pow_succ' _ (r + 1), mul_left_comm] at h
    simpa using congrArg (eval 1) (mul_left_cancel₀ h0 h)

theorem UpperTheory.V.CA.f_gma :
    ∀ {n : ℕ} {B E k : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] [Ring E] [Algebra B E] [Field k] [Algebra B k] [IsLocalHom (algebraMap B k)] (D : Det n B E) (π : E →ₐ[B] (Fin n → k)), D.IsCH → Function.Surjective π → (∀ x, (D.chi x).map (algebraMap B k) = ∏ i, (X - C (π x i))) → (∀ x, π x = 0 ↔ x ∈ Ring.jacobson E) ∧ ∃ e : Fin n → E, IsGMA D e ∧ ∀ i, π (e i) = Pi.single i 1 := by
  intro n B E k _ _ _ _ _ _ _ _ _ D π hD hs hchi
  obtain ⟨hu, hint⟩ := d_unit D hD
  have hunit : ∀ x, π x = 1 → IsUnit x := by
    intro x hx
    rw [hu, ← (d_chi D x).2.2.2.1, Det.lam, Nat.sub_self]
    refine (isUnit_one.neg.pow n).mul ?_
    refine (isUnit_map_iff (algebraMap B k) _).1 ?_
    rw [← coeff_map, hchi, hx, coeff_zero_eq_eval_zero, isUnit_iff_ne_zero]
    simp [eval_prod]
  have hk : ∀ x, π x = 0 → x ∈ Ring.jacobson E := by
    intro x hx
    rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff]
    intro y
    obtain ⟨u, hu'⟩ := hunit (y * x + 1) (by simp [hx])
    refine ⟨↑u⁻¹, ?_⟩
    rw [Ideal.mem_bot, sub_eq_zero, ← u.inv_mul, hu', mul_add, mul_one, mul_assoc]
  refine ⟨fun x => ⟨hk x, fun hx => ?_⟩, ?_⟩
  · rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff] at hx
    funext i
    by_contra hi
    obtain ⟨y, hy⟩ := hs fun _ => -(π x i)⁻¹
    obtain ⟨z, hz⟩ := hx y
    rw [Ideal.mem_bot] at hz
    have h1 := congrFun (congrArg π hz) i
    have hi' : π x i ≠ 0 := hi
    simp only [map_sub, map_add (f := _), map_mul, map_one, map_zero, hy, Pi.sub_apply, Pi.add_apply, Pi.mul_apply,
      Pi.one_apply, Pi.zero_apply] at h1
    rw [mul_assoc, neg_mul, inv_mul_cancel₀ hi'] at h1
    simp at h1
  · obtain ⟨e, he, he'⟩ := d_lift_idem π hs hk (fun i => Pi.single i 1)
      (CompleteOrthogonalIdempotents.single fun _ : Fin n => k)
    refine ⟨e, ⟨hD, he, fun i => ?_⟩, he'⟩
    obtain ⟨r, -, hr⟩ := d_idem_rank D (e i) (he.idem i)
    obtain ⟨s, -, hs'⟩ := d_idem_rank D (1 - e i) (he.idem i).one_sub
    have h1 := hchi (e i)
    rw [fg_chi D _ (he.idem i) r s hr hs', he', ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      Finset.prod_congr rfl (g := fun _ => X) (fun j hj => by
        simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hj)]), Finset.prod_const] at h1
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, map_X, Polynomial.map_one,
      Pi.single_eq_same, map_one] at h1
    rw [hr, fg_one h1, pow_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DExtPoly
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DPolyExt
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_poly_ext :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (D' : Det n A E) (M : Set E), Submodule.span A M = ⊤ → (∀ (k : ℕ) (x : Fin k → E), (∀ a, x a ∈ M) → D.poly x = D'.poly x) → D = D' := by
  intro n A E _ _ _ D D' M hM h
  refine Det.ext' fun S _ _ y => ?_
  have h1 : ∀ x : E, (1 : S) ⊗ₜ[A] x ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' M) := by
    intro x
    have hx : x ∈ Submodule.span A M := hM ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [tmul_add]; exact add_mem ha hb
    | smul a z _ hz => rw [tmul_smul]; exact Submodule.smul_of_tower_mem _ a hz
  have h2 : y ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' M) := by
    induction y with
    | add a b ha hb => exact add_mem ha hb
    | tmul s x =>
      have : s ⊗ₜ[A] x = s • ((1 : S) ⊗ₜ[A] x) := by simp [smul_tmul']
      rw [this]; exact Submodule.smul_mem _ s (h1 x)
  obtain ⟨k, s, g, rfl⟩ := Submodule.mem_span_set'.1 h2
  choose x hxM hx using fun a => (g a).2
  have h3 : ∑ a, s a • (g a : S ⊗[A] E) =
      Algebra.TensorProduct.map (MvPolynomial.aeval s) (AlgHom.id A E) (Det.gen x) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Det.gen, map_sum, Algebra.TensorProduct.map_tmul, MvPolynomial.aeval_X, AlgHom.id_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hx a]; simp [smul_tmul']
  rw [h3, D.nat, D'.nat]
  exact congrArg _ (h k x hxM)
end

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem d_ext_unit {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D D' : Det n A E)
    {k : ℕ} (x : Fin k → E)
    (h : D.D (MvPolynomial (Fin k) A) (1 + Det.gen x) = D'.D (MvPolynomial (Fin k) A) (1 + Det.gen x))
    (B : Type) [CommRing B] [Algebra A B] (u v : B) (huv : u * v = 1) (b : Fin k → B) :
    D.D B (u ⊗ₜ 1 + ∑ a, b a ⊗ₜ x a) = D'.D B (u ⊗ₜ 1 + ∑ a, b a ⊗ₜ x a) := by
  have e : (u ⊗ₜ[A] (1 : E) + ∑ a, b a ⊗ₜ[A] x a) =
      u • Algebra.TensorProduct.map (MvPolynomial.aeval fun a => v * b a) (AlgHom.id A E) (1 + Det.gen x) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Det.gen, map_add (f := _), map_one, map_sum, Algebra.TensorProduct.map_tmul, MvPolynomial.aeval_X,
      AlgHom.id_apply, smul_add, Finset.smul_sum, smul_tmul', smul_eq_mul, ← mul_assoc, huv, one_mul]
    rw [Algebra.TensorProduct.one_def, smul_tmul', smul_eq_mul, mul_one]
  rw [e, D.homog, D'.homog, D.nat, D'.nat, h]

private theorem d_ext_poly {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D D' : Det n A E)
    {k : ℕ} (x : Fin k → E)
    (h : D.D (MvPolynomial (Fin k) A) (1 + Det.gen x) = D'.D (MvPolynomial (Fin k) A) (1 + Det.gen x)) :
    D.poly x = D'.poly x := by
  let R := MvPolynomial (Fin k) A
  let L := Localization.Away (X : R[X])
  let y : R[X] ⊗[A] E := (X : R[X]) ⊗ₜ 1 + ∑ a, C (MvPolynomial.X a) ⊗ₜ x a
  have hinj : Function.Injective (algebraMap R[X] L) :=
    IsLocalization.injective L (M := Submonoid.powers (X : R[X]))
      ((Submonoid.powers_le).2 X_mem_nonzeroDivisors)
  have h1 : D.D R[X] y = D'.D R[X] y := by
    apply hinj
    let f : R[X] →ₐ[A] L := IsScalarTower.toAlgHom A R[X] L
    change f _ = f _
    rw [← D.nat, ← D'.nat]
    have e : Algebra.TensorProduct.map f (AlgHom.id A E) y =
        f X ⊗ₜ 1 + ∑ a, f (C (MvPolynomial.X a)) ⊗ₜ x a := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [y, map_add (f := _), map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [e]
    exact d_ext_unit D D' x h L _ (IsLocalization.Away.invSelf (X : R[X]))
      (IsLocalization.Away.mul_invSelf (S := L) (X : R[X])) _
  let g : R[X] →ₐ[A] R := (Polynomial.aeval (0 : R)).restrictScalars A
  have e : Algebra.TensorProduct.map g (AlgHom.id A E) y = Det.gen x := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [y, g, map_add (f := _), map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      AlgHom.coe_restrictScalars', aeval_X, aeval_C, zero_tmul, zero_add, Det.gen]
    rfl
  have h2 := congrArg g h1
  rw [← D.nat, ← D'.nat, e] at h2
  exact h2

theorem UpperTheory.V.CA.d_ext :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (D' : Det n A E) (M : Submonoid E), Submodule.span A (M : Set E) = ⊤ → (∀ x ∈ M, ∀ i, 1 ≤ i → i ≤ n → D.lam i x = D'.lam i x) → D = D' := by
  intro n A E _ _ _ D D' M hM h
  refine d_poly_ext D D' (M : Set E) hM fun k x hx => d_ext_poly D D' x ?_
  ext α
  obtain ⟨P, hP, -, hc⟩ := d_amitsur n k α
  rw [hc D x, hc D' x]
  refine MvPolynomial.eval₂Hom_congr' rfl (fun v hv _ => ?_) rfl
  refine h _ ?_ _ (hP v hv).1 (hP v hv).2.1
  induction v.2 using FreeMonoid.inductionOn' with
  | one => rw [map_one]; exact M.one_mem
  | of_mul a w ih => rw [map_mul, FreeMonoid.lift_eval_of]; exact M.mul_mem (hx a) ih
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DCoefMem
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem aeval_cons_monomial {A : Type} [CommRing A] {k : ℕ} (c : MvPolynomial (Fin k) A)
    (β : Fin (k + 1) →₀ ℕ) (a : A) :
    MvPolynomial.aeval (Fin.cons c MvPolynomial.X : Fin (k + 1) → MvPolynomial (Fin k) A)
      (MvPolynomial.monomial β a) = c ^ β 0 * MvPolynomial.monomial β.tail a := by
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_succ,
    MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
  simp only [Fin.cons_zero, Fin.cons_succ, Finsupp.tail_apply, MvPolynomial.algebraMap_eq]
  ring

private theorem coeff_cons_eq {A : Type} [CommRing A] {k n : ℕ} (P : MvPolynomial (Fin (k + 1)) A)
    (hP : P.IsHomogeneous n) (α : Fin k →₀ ℕ) (hα : α.degree = n) :
    AddMonoidAlgebra.coeff (MvPolynomial.aeval (Fin.cons 0 MvPolynomial.X : Fin (k + 1) → MvPolynomial (Fin k) A) P) α =
    AddMonoidAlgebra.coeff (MvPolynomial.aeval (Fin.cons 1 MvPolynomial.X : Fin (k + 1) → MvPolynomial (Fin k) A) P) α := by
  classical
  rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, MvPolynomial.coeff_sum, aeval_cons_monomial]
  refine Finset.sum_congr rfl fun β hβ => ?_
  have hd : β.degree = n := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.1 hβ) (hP.coeff_eq_zero h)
  by_cases h0 : β 0 = 0
  · simp [h0]
  · have hne : β.tail ≠ α := by
      rintro rfl
      rw [Finsupp.degree_eq_sum] at hd hα
      rw [Fin.sum_univ_succ] at hd
      simp only [Finsupp.tail_apply] at hα
      omega
    simp [h0, MvPolynomial.coeff_monomial, hne]

private theorem coef_mem_fin {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)
    (M : Submonoid E) (A₀ : Subring A) (h : ∀ x ∈ M, ∀ i, 1 ≤ i → i ≤ n → D.lam i x ∈ A₀) {k : ℕ}
    (x : Fin k → E) (hx : ∀ a, x a ∈ M) (α : Fin k →₀ ℕ) : AddMonoidAlgebra.coeff (D.poly x) α ∈ A₀ := by
  classical
  by_cases hα : α.degree = n
  swap
  · rw [(d_poly D x).1.coeff_eq_zero hα]; exact A₀.zero_mem
  obtain ⟨hh, hev⟩ := d_poly D (Fin.cons 1 x : Fin (k + 1) → E)
  have h0 := hev (MvPolynomial (Fin k) A) (Fin.cons 0 MvPolynomial.X)
  have h1 := hev (MvPolynomial (Fin k) A) (Fin.cons 1 MvPolynomial.X)
  rw [Fin.sum_univ_succ] at h0 h1
  simp only [Fin.cons_zero, Fin.cons_succ, zero_tmul, zero_add] at h0 h1
  obtain ⟨P, hv, -, hP⟩ := d_amitsur n k α
  have e : AddMonoidAlgebra.coeff (D.poly x) α =
      AddMonoidAlgebra.coeff (D.D (MvPolynomial (Fin k) A) (1 + Det.gen x)) α := by
    unfold Det.poly Det.gen
    rw [Algebra.TensorProduct.one_def, h0, h1]
    exact coeff_cons_eq _ hh α hα
  rw [e, hP D x, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine A₀.sum_mem fun d hd => A₀.mul_mem (by simp) (A₀.prod_mem fun v hvd => A₀.pow_mem ?_ _)
  obtain ⟨h1, h2, -⟩ := hv v ((MvPolynomial.mem_vars_iff_mem_support v).2 ⟨d, hd, hvd⟩)
  refine h _ ?_ _ h1 h2
  rw [FreeMonoid.lift_apply]
  refine M.list_prod_mem fun y hy => ?_
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hy
  exact hx a

theorem UpperTheory.V.CA.d_coef_mem :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (M : Submonoid E) (A₀ : Subring A), (∀ x ∈ M, ∀ i, 1 ≤ i → i ≤ n → D.lam i x ∈ A₀) → ∀ {ι : Type} [Fintype ι] (x : ι → E), (∀ a, x a ∈ M) → ∀ α, AddMonoidAlgebra.coeff (D.poly x) α ∈ A₀ := by
  intro n A E _ _ _ D M A₀ h ι _ x hx α
  let e := (Fintype.equivFin ι).symm
  have h1 := (d_poly D (x ∘ e)).2 (MvPolynomial ι A) (MvPolynomial.X ∘ e)
  have h2 : D.poly x = MvPolynomial.rename e (D.poly (x ∘ e)) := by
    rw [MvPolynomial.rename_eq_aeval, ← h1]
    unfold Det.poly Det.gen
    congr 1
    exact (Equiv.sum_comp e fun a => (MvPolynomial.X a : MvPolynomial ι A) ⊗ₜ[A] x a).symm
  have h3 : α = (α.mapDomain e.symm).mapDomain e := by
    rw [← Finsupp.mapDomain_comp]; simp
  rw [h2, h3, MvPolynomial.coeff_rename_mapDomain _ e.injective]
  exact coef_mem_fin D M A₀ h _ (fun a => hx _) _
end
