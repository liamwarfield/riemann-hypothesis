module

public import ReciprocityTheory.DualLattices.KilledGen

@[expose] public section

section -- merged from ReciprocityTheory.DualLattices.RestrictedHopfOrderApproximationStatement
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def psiW {p : ℕ} [Fact p.Prime] {g r : ℕ} (Bw : Matrix (Ix g) (Fin r) ℤ_[p]) :
    (Fin r → ZMod p) →+ Nb p g :=
  (Matrix.mulVecLin (Bw.map PadicInt.toZMod)).toAddMonoidHom

def RestrictedHopfOrderStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp) (a : O), a * a = a →
    ∀ (r : ℕ) (Bw : Matrix (Ix g) (Fin r) ℤ_[p]),
      LinearMap.range (Matrix.mulVecLin Bw) = LinearMap.range (Matrix.mulVecLin (H.ρ a)) →
      LinearMap.ker (Matrix.mulVecLin Bw) = ⊥ →
    ∀ d : ℕ, Nonempty (LinearMap.range (Matrix.mulVecLin (H.ρL a)) ≃ₗ[R] (Fin d → R)) →
    ∃ AW : HopfOrder (C := C) R (Fin r → ZMod p),
      AW.carrier = H.AA.carrier.map (LinearMap.funLeft R C (psiW Bw)) ∧
      HasLen v R (OmAA AW.carrier) (v (algebraMap R C (p : R)) ^ d)

def RestrictedHopfOrderApproximationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp) (m : ℕ) (e : Fin m → O)
    (π : Equiv.Perm (Fin m)),
    (∀ i j, e i * e j = if i = j then e i else 0) → (∀ i, σ (e i) = e (π i)) →
    (∑ i, H.ρ (e i)) + H.P = 1 → (∀ i, H.ρ (e i) * H.P = 0) →
    (∑ i, H.ρL (e i)) + H.PL = 1 → (∀ i, H.ρL (e i) * H.PL = 0) →
    ∀ w, π w ≠ w → ∀ (r : ℕ) (Bw : Matrix (Ix g) (Fin r) ℤ_[p]),
      LinearMap.range (Matrix.mulVecLin Bw) = LinearMap.range (Matrix.mulVecLin (H.ρ (e w))) →
      LinearMap.ker (Matrix.mulVecLin Bw) = ⊥ →
    ∀ (lam : Fin r → R) (dj : R),
      dj • lam ∈ Submodule.span R (Set.range fun k : Fin g ⊕ Fin g =>
        fun i : Fin r => (phiP H e * Bw.map (algebraMap ℤ_[p] R)) k i) →
      v (algebraMap R C cp) ≤ v (algebraMap R C dj) →
      ∃ f ∈ H.AA.carrier.map (LinearMap.funLeft R C (psiW Bw)), ∀ x : Fin r → ℤ_[p],
        v (f (fun i => PadicInt.toZMod (x i)) -
          algebraMap R C (dj * ∑ i, lam i * algebraMap ℤ_[p] R (x i))) < v (algebraMap R C dj)

end ReciprocityTheory.PGsh.Up
end
end

section -- merged from ReciprocityTheory.DualLattices.HtLinStatement
noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

structure ATowerL (R₀ : Type u) [CommRing R₀] (p : ℕ) extends ATower R₀ p where
  r' : ∀ n, LHom (R' (n + 1)) (R' n)
  r : ∀ n, LHom (R (n + 1)) (R n)
  r_π : ∀ n (x : (R' (n + 1) : Type u)), (r n).1 ((π (n + 1)).1 x) = (π n).1 ((r' n).1 x)
  r_q : ∀ n (x : (O : Type u)), (r n).1 ((q (n + 1)).1 x) = (q n).1 x
  r'_ξ : ∀ n, (r' n).1 (ξ (n + 1)) = ξ n
  complete : ∀ x : ∀ n, (R n : Type u), (∀ n, (r n).1 (x (n + 1)) = x n) →
    ∃ a : (O : Type u), ∀ n, (q n).1 a = x n

variable {R₀ : Type u} [CommRing R₀]

structure DualTower {p : ℕ} (Tw : ATowerL R₀ p) where
  Dp : ∀ n, DualPair (Tw.R n)
  d : ∀ n, LHom (Dp (n + 1)).D (Dp n).D
  d_π : ∀ n (x : ((Dp (n + 1)).D : Type u)), (Dp n).π.1 ((d n).1 x) = (Tw.r n).1 ((Dp (n + 1)).π.1 x)
  d_σ : ∀ n (x : (Tw.R (n + 1) : Type u)), (d n).1 ((Dp (n + 1)).σ.1 x) = (Dp n).σ.1 ((Tw.r n).1 x)
  d_η : ∀ n, (d n).1 (Dp (n + 1)).η = (Dp n).η

def LimStatement (B : BX R₀) {p : ℕ} (Tw : ATowerL R₀ p) (Dt : DualTower Tw) : Prop :=
  ∀ (ι : Type) (τ : ι → ℕ → B.G Tw.O),
    (∀ i n, (p ^ (n + 1)) • τ i n = 0) → (∀ i n, τ i n = p • τ i (n + 1)) →
    ∃ (ht : ι → B.gg →ₗ[R₀] (Tw.O : Type u)) (bt : ι → B.gg ⊗[R₀] (Tw.O : Type u)),
      (∀ i n, B.IsHeight (Dt.Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ i n))
        ((Tw.q n).1.toLinearMap ∘ₗ ht i)) ∧
      (∀ i n, ∃ (th : B.G (Tw.R' n)) (w : B.gg ⊗[R₀] (Tw.R' n : Type u)),
        B.map (Tw.π n) th = B.map (Tw.q n) (τ i n) ∧
        (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
          (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) ∧
        LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap w =
          LinearMap.lTensor B.gg (Tw.q n).1.toLinearMap (bt i))

def HtLinStatement (B : BX R₀) {p : ℕ} (Tw : ATower R₀ p) (Dp : ∀ n, DualPair (Tw.R n)) : Prop :=
  ∀ (ι : Type) [Fintype ι] (τ : ι → ℕ → B.G Tw.O) (ht : ι → B.gg →ₗ[R₀] (Tw.O : Type u))
    (a : ι → ℕ → ℤ) (α : ι → (Tw.O : Type u)),
    (∀ i n, (p ^ (n + 1)) • τ i n = 0) →
    (∀ i n, B.IsHeight (Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ i n))
      ((Tw.q n).1.toLinearMap ∘ₗ ht i)) →
    (∀ i n, (Tw.q n).1 (α i) = a i n) →
    ∀ n, B.IsHeight (Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (∑ i, a i n • τ i n))
      ((Tw.q n).1.toLinearMap ∘ₗ ∑ i, α i • ht i)

end ReciprocityTheory.PGsh
end
end

section -- merged from ReciprocityTheory.DualLattices.EigenLengthProductStatementHolds
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

namespace Tot

section len

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem hasLen_equiv {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) {x : NNReal} (h : HasLen v R N x) : HasLen v R M x := by
  obtain ⟨m, c, ⟨f⟩, hx⟩ := h
  exact ⟨m, c, ⟨e.trans f⟩, hx⟩

theorem hasLen_pi {m : ℕ} (M : Fin m → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (X : Fin m → NNReal) (h : ∀ i, HasLen v R (M i) (X i)) :
    HasLen v R ((i : Fin m) → M i) (∏ i, X i) := by
  classical
  choose n c he hX using h
  let e : ∀ i, M i ≃ₗ[R] ((j : Fin (n i)) → R ⧸ Ideal.span {c i j}) := fun i => (he i).some
  let σ : Fin (Fintype.card (Σ i, Fin (n i))) ≃ (Σ i, Fin (n i)) := (Fintype.equivFin _).symm
  refine ⟨Fintype.card (Σ i, Fin (n i)), fun k => c (σ k).1 (σ k).2, ⟨?_⟩, ?_⟩
  · exact (LinearEquiv.piCongrRight e).trans
      ((LinearEquiv.piCurry R (fun i j => R ⧸ Ideal.span {c i j})).symm.trans
        (LinearEquiv.piCongrLeft R (fun p : Σ i, Fin (n i) => R ⧸ Ideal.span {c p.1 p.2}) σ).symm)
  · rw [Fintype.prod_equiv σ (fun k => v (algebraMap R C (c (σ k).1 (σ k).2)))
      (fun p => v (algebraMap R C (c p.1 p.2))) (fun k => rfl), Fintype.prod_sigma]
    exact Finset.prod_congr rfl fun i _ => hX i

end len

variable {R : Type} [CommRing R]

theorem sum_fromBlocks_diag {g : ℕ} {ι : Type} (s : Finset ι)
    (A D : ι → Matrix (Fin g) (Fin g) R) :
    ∑ i ∈ s, fromBlocks (A i) 0 0 (D i) = fromBlocks (∑ i ∈ s, A i) 0 0 (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fromBlocks_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih, fromBlocks_add,
      add_zero]

theorem sum_mulVec' {n : Type} [Fintype n] {ι : Type} (s : Finset ι) (A : ι → Matrix n n R)
    (w : n → R) : (∑ i ∈ s, A i) *ᵥ w = ∑ i ∈ s, A i *ᵥ w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_mulVec, ih]

end Tot

open Tot in
theorem eigenLengthProductStatement_holds : EigenLengthProductStatement := by
  intro C _ v R _ _ hv g m Ht Bt εT εL π hπ hTo hTs hLo hLs hHt hBt X hX
  classical
  set Φ := fromRows Ht Bt with hΦ
  set Pm : Fin m → Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R :=
    fun i => fromBlocks ((εL (π i))ᵀ) 0 0 (εL i) with hPm
  have hPmv : ∀ i w, Pm i *ᵥ w =
      Sum.elim ((εL (π i))ᵀ *ᵥ (w ∘ Sum.inl)) (εL i *ᵥ (w ∘ Sum.inr)) := by
    intro i w
    simp only [hPm, fromBlocks_mulVec, zero_mulVec, add_zero, zero_add]
  have hmem : ∀ i w, Pm i *ᵥ w ∈ qE εL i (π i) := by
    intro i w
    refine Submodule.mem_inf.2 ⟨⟨w ∘ Sum.inl, ?_⟩, ⟨w ∘ Sum.inr, ?_⟩⟩
    · show (εL (π i))ᵀ *ᵥ (w ∘ Sum.inl) = (Pm i *ᵥ w) ∘ Sum.inl
      rw [hPmv]; rfl
    · show εL i *ᵥ (w ∘ Sum.inr) = (Pm i *ᵥ w) ∘ Sum.inr
      rw [hPmv]; rfl
  have hsel : ∀ i k w, w ∈ qE εL i (π i) → Pm k *ᵥ w = if k = i then w else 0 := by
    intro i k w hw
    obtain ⟨⟨y1, hy1⟩, ⟨y2, hy2⟩⟩ := Submodule.mem_inf.1 hw
    have e1 : w ∘ Sum.inl = (εL (π i))ᵀ *ᵥ y1 := hy1.symm
    have e2 : w ∘ Sum.inr = εL i *ᵥ y2 := hy2.symm
    rw [hPmv, e1, e2, mulVec_mulVec, mulVec_mulVec, ← transpose_mul, hLo, hLo]
    by_cases hki : k = i
    · subst hki
      simp only [if_true]
      rw [← e1, ← e2, Sum.elim_comp_inl_inr]
    · have hne : π i ≠ π k := fun h => hki (π.injective h).symm
      simp only [hki, hne, if_false, transpose_zero, zero_mulVec]
      ext s; cases s <;> rfl
  have hT : ∑ i, (εL (π i))ᵀ = 1 := by
    rw [← transpose_sum, Equiv.sum_comp π εL, hLs, transpose_one]
  have hPsum : ∑ i, Pm i = 1 := by
    simp only [hPm]
    rw [sum_fromBlocks_diag, hT, hLs, fromBlocks_one]
  have hsum : ∀ w, ∑ i, Pm i *ᵥ w = w := by
    intro w
    rw [← sum_mulVec', hPsum, one_mulVec]
  have hPΦ : ∀ i, Pm i * Φ = Φ * εT i := by
    intro i
    rw [hΦ, hPm, fromBlocks_mul_fromRows, fromRows_mul, Matrix.zero_mul, Matrix.zero_mul, add_zero,
      zero_add,
      hHt, hBt]
  set Ψ : (Fin g ⊕ Fin g → R) →ₗ[R] ((i : Fin m) → xModE Ht Bt εT εL π i) :=
    LinearMap.pi fun i => Submodule.mkQ _ ∘ₗ
      LinearMap.codRestrict (qE εL i (π i)) (mulVecLin (Pm i)) (hmem i) with hΨdef
  have hΨ : ∀ w i, Ψ w i = Submodule.Quotient.mk ⟨Pm i *ᵥ w, hmem i w⟩ := fun _ _ => rfl
  have hsurj : Function.Surjective Ψ := by
    intro q
    choose w hw using fun i => Submodule.Quotient.mk_surjective _ (q i)
    refine ⟨∑ i, ((w i : qE εL i (π i)) : Fin g ⊕ Fin g → R), funext fun k => ?_⟩
    rw [hΨ, ← hw k]
    congr 1
    apply Subtype.ext
    show Pm k *ᵥ ∑ i, ((w i : qE εL i (π i)) : Fin g ⊕ Fin g → R) = (w k : Fin g ⊕ Fin g → R)
    rw [mulVec_sum]
    simp only [fun i => hsel i k _ (w i).2]
    simp
  have hker : LinearMap.ker Ψ = LinearMap.range (mulVecLin Φ) := by
    ext w
    rw [LinearMap.mem_ker]
    constructor
    · intro h
      have hi : ∀ i, ∃ t, Φ *ᵥ (εT i *ᵥ t) = Pm i *ᵥ w := by
        intro i
        have := congrFun h i
        rw [hΨ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero] at this
        obtain ⟨y, ⟨t, rfl⟩, hy⟩ := this
        exact ⟨t, hy⟩
      choose t ht using hi
      refine ⟨∑ i, εT i *ᵥ t i, ?_⟩
      show Φ *ᵥ ∑ i, εT i *ᵥ t i = w
      rw [mulVec_sum]
      simp only [ht]
      exact hsum w
    · rintro ⟨t, rfl⟩
      funext i
      rw [hΨ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero]
      refine ⟨εT i *ᵥ t, ⟨t, rfl⟩, ?_⟩
      show Φ *ᵥ (εT i *ᵥ t) = Pm i *ᵥ (Φ *ᵥ t)
      rw [mulVec_mulVec, mulVec_mulVec, hPΦ]
  have iso : ((Fin g ⊕ Fin g → R) ⧸ LinearMap.range (mulVecLin Φ)) ≃ₗ[R]
      ((i : Fin m) → xModE Ht Bt εT εL π i) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (Ψ.quotKerEquivOfSurjective hsurj)
  set e : Fin g ⊕ Fin g ≃ Fin (g + g) := finSumFinEquiv with he
  set Φ' := reindex e e Φ with hΦ'
  have hdet : Φ'.det = Φ.det := det_reindex_self e Φ
  set F : (Fin (g + g) → R) ≃ₗ[R] (Fin g ⊕ Fin g → R) := LinearEquiv.funCongrLeft R R e with hF
  have hFapp : ∀ y, F y = y ∘ e := fun y => rfl
  have hcomm : ∀ y, F (Φ' *ᵥ y) = Φ *ᵥ F y := by
    intro y
    rw [hFapp, hFapp, hΦ', reindex_apply, submatrix_mulVec_equiv]
    ext s
    simp
  have hmap : (LinearMap.range (mulVecLin Φ')).map F.toLinearMap = LinearMap.range (mulVecLin Φ) := by
    ext z
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨F y, (hcomm y).symm⟩
    · rintro ⟨t, rfl⟩
      refine ⟨Φ' *ᵥ F.symm t, ⟨F.symm t, rfl⟩, ?_⟩
      show F (Φ' *ᵥ F.symm t) = Φ *ᵥ t
      rw [hcomm, LinearEquiv.apply_symm_apply]
  have hcok := Submodule.Quotient.equiv _ _ F hmap
  have hL1 := Smith.hasLen_coker_det (C := C) (v := v) hv Φ'
  have hL2 : HasLen v R ((Fin (g + g) → R) ⧸ LinearMap.range (mulVecLin Φ')) (∏ i, X i) :=
    hasLen_equiv (hcok.trans iso) (hasLen_pi _ X hX)
  rw [hasLen_unique hv hL2 hL1, hdet]

end ReciprocityTheory.PGsh.Up
end
end

section -- merged from ReciprocityTheory.DualLattices.ATowerInh
noncomputable section

open PowerSeries

namespace ReciprocityTheory.PGsh

namespace TowerExample

variable (p : ℕ) [Fact p.Prime]

lemma ne_top (m : ℕ) (hm : 0 < m) : Ideal.span {(X : (ZMod p)⟦X⟧) ^ m} ≠ ⊤ := by
  rw [Ne, Ideal.span_singleton_eq_top, PowerSeries.isUnit_iff_constantCoeff]
  simp [zero_pow hm.ne']

lemma isLocalHom_of_surj {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [Nontrivial S]
    (f : R →+* S) (hf : Function.Surjective f) : IsLocalHom f := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  obtain ⟨c, hc⟩ := hf (↑ha.unit⁻¹ : S)
  have hker : RingHom.ker f ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f)
  have h1 : 1 - a * c ∈ RingHom.ker f := by
    rw [RingHom.mem_ker, RingHom.map_sub, map_one, map_mul, hc, IsUnit.mul_val_inv, sub_self]
  have h2 : a * c ∈ IsLocalRing.maximalIdeal R :=
    Ideal.mul_mem_right c _ ((IsLocalRing.mem_maximalIdeal a).2 hna)
  have h3 := Ideal.add_mem _ (hker h1) h2
  rw [sub_add_cancel] at h3
  exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal R).ne_top h3

end TowerExample

end ReciprocityTheory.PGsh
end
end

section -- merged from ReciprocityTheory.DualLattices.EigenLiftsFrobeniusStatement
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

structure Lifts {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal}
    {R : Type} [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O]
    [Algebra ℤ_[p] O] {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal) where
  κ : Ix g → Fin U.m
  card_phi : ∀ i, (Finset.univ.filter fun j => κ j = U.φ i).card =
    (Finset.univ.filter fun j => κ j = i).card
  r_zero : ∀ i, (∀ j, κ j ≠ i) → U.r i = 0
  Λ : Matrix (Ix g) (Ix g) R
  Λ_det : IsUnit Λ.det
  Λ_block : ∀ j, Matrix.vecMul (Λ j) (U.εT (κ j)) = Λ j
  ε : Ix g → R
  ε_ne : ∀ j, ε j ≠ 0
  ε_prod : ∀ i, ∏ j ∈ Finset.univ.filter (fun j => κ j = i), v (algebraMap R C (ε j)) = X i
  u : Ix g → Nb p g → C
  u_int : ∀ j y, v (u j y) ≤ 1
  u_cong : ∀ j (y : Nb p g), v (u j y - algebraMap R C (∑ k, Λ j k * ((y k).val : R))) < 1
  x_mem : ∀ j, (fun y => algebraMap R C (ε j) * u j y) ∈ augIdeal H.AA.carrier
  s : ℕ
  b : Fin s → O
  eig : ∀ j k (t : TT p g),
    u j (red p g (H.ρ (b k) *ᵥ t)) = algebraMap R C (U.sg (κ j) (b k)) * u j (red p g t)
  frobChar : ∀ j k, U.sg (U.φ (κ j)) (b k) = U.sg (κ j) (b k) ^ p
  sep : ∀ j j', κ j ≠ κ j' → ∃ k, v (algebraMap R C (U.sg (κ j) (b k) - U.sg (κ j') (b k))) = 1

def EigenLiftsStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    p ≠ 2 → HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal),
    (∀ i, HasLen v R (xModE H.Ht (bt2 H U) U.εT U.εL U.cj i) (X i)) → Nonempty (Lifts H U X)

def EigenLiftsBasisStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal),
    ∏ i, X i = v (algebraMap R C cp) ^ g → ∀ D : Lifts H U X,
    H.AA.carrier = Submodule.span R (Set.range fun (α : Nb p g) (y : Nb p g) =>
      ∏ j, (algebraMap R C (D.ε j) * D.u j y) ^ (α j).val)

def EigenLiftsFrobeniusStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    p ≠ 2 → HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal) (D : Lifts H U X),
    H.AA.carrier = Submodule.span R (Set.range fun (α : Nb p g) (y : Nb p g) =>
      ∏ j, (algebraMap R C (D.ε j) * D.u j y) ^ (α j).val) →
    ∀ i, X i ^ p ≤ X (U.φ i) * v (algebraMap R C (p : R)) ^ U.r (U.φ i)

theorem core_of (hL : EigenLiftsStatement) (hB : EigenLiftsBasisStatement) (hF : EigenLiftsFrobeniusStatement) :
    EigenLengthFrobeniusStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hp hS H U X hX hprod i
  obtain ⟨D⟩ := hL p g C v R O σ cp hp hS H U X hX
  exact hF p g C v R O σ cp hp hS H U X D (hB p g C v R O σ cp hS H U X hprod D) i

end ReciprocityTheory.PGsh.Up
end
end

section -- merged from ReciprocityTheory.DualLattices.ThmAFull
section -- merged from ReciprocityTheory.DualLattices.OneAddPowOfSq
noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

lemma BX.ev_map (B : BX R₀) {R S : LAlg R₀} (f : (R : Type u) →ₐ[R₀] (S : Type u))
    (h : B.gg →ₗ[R₀] (R : Type u)) (v : B.gg ⊗[R₀] (R : Type u)) :
    f (B.ev h v) = B.ev (f.toLinearMap ∘ₗ h) (LinearMap.lTensor B.gg f.toLinearMap v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp [BX.ev]
  | tmul g r => simp [BX.ev]
  | add a b ha hb =>
    simp only [BX.ev, map_add (f := _)] at ha hb ⊢
    rw [ha, hb]

private lemma one_add_pow_of_sq {S : Type*} [CommRing S] (a : S) (ha : a * a = 0) (k : ℕ) :
    (1 + a) ^ k = 1 + k * a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination (k : S) * ha

theorem b4 (B : BX R₀) (hB1 : PairingPropertiesStatement B) (hB3 : TangentPairingStatement B) {p : ℕ}
    (Tw : ATower R₀ p) : NsetExpInjectiveSurjective B Tw := by
  intro Dp ι τ E ht bt h1 h2 h3 i j
  apply sub_eq_zero.mp
  apply Tw.sep
  intro n
  obtain ⟨k, hk, hpair⟩ := h1 i j n
  obtain ⟨thi, wi, hmi, hNi, hwi⟩ := h3 i n
  obtain ⟨thj, wj, hmj, hNj, hwj⟩ := h3 j n
  have hsurjL : Function.Surjective (Tw.π n).1.toLinearMap := Tw.surj n
  obtain ⟨hsi, hsi_spec⟩ := Module.projective_lifting_property (Tw.π n).1.toLinearMap
    ((Tw.q n).1.toLinearMap ∘ₗ ht i) hsurjL
  obtain ⟨hsj, hsj_spec⟩ := Module.projective_lifting_property (Tw.π n).1.toLinearMap
    ((Tw.q n).1.toLinearMap ∘ₗ ht j) hsurjL
  obtain ⟨-, -, -, -, -, -, hnat, -⟩ := hB1
  have hpq := hnat _ _ (Tw.q n) _ _ _ _ hpair
  rw [← hmi, ← hmj] at hpq
  have hB3' := hB3 (Tw.R' n) (Tw.R n) (Tw.π n) (Tw.ξ n) (Dp n) (p ^ (n + 1)) (Tw.surj n)
    (Tw.ker_eq n) (Tw.ξ_sq n) (Tw.ann n) (Tw.char n) thi thj
    (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) wi)
    (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) wj)
    hsi hsj (Tw.zh n ^ k) _ hNi hNj
    (by rw [hmi, hsi_spec]; exact h2 i n) (by rw [hmj, hsj_spec]; exact h2 j n) hpq
    (Units.ext (by simp [Tw.ζ_spec]))
  have hev : ∀ (h : B.gg →ₗ[R₀] (Tw.R' n : Type u)) (w : B.gg ⊗[R₀] (Tw.R' n : Type u)),
      B.evK (Tw.π n) h (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) =
        Tw.ξ n * B.ev h w := by
    intro h w
    induction w using TensorProduct.induction_on with
    | zero => simp [BX.evK, BX.ev]
    | tmul g r =>
      simp [BX.evK, BX.ev, ξmul]
      ring
    | add a b ha hb =>
      simp only [BX.evK, BX.ev, map_add (f := _)] at ha hb ⊢
      rw [ha, hb, mul_add]
  rw [hev, hev] at hB3'
  have hpow : ((Tw.zh n ^ k : (Tw.R' n : Type u)ˣ) : (Tw.R' n : Type u)) ^ (p ^ (n + 1)) =
      1 + (k : (Tw.R' n : Type u)) * (Tw.cp n * Tw.ξ n) := by
    rw [Units.val_pow_eq_pow_val, pow_right_comm, Tw.zh_pow n]
    apply one_add_pow_of_sq
    calc Tw.cp n * Tw.ξ n * (Tw.cp n * Tw.ξ n) = Tw.cp n * Tw.cp n * (Tw.ξ n * Tw.ξ n) := by ring
      _ = 0 := by rw [Tw.ξ_sq n, mul_zero]
  have hξ : ((k : (Tw.R' n : Type u)) * Tw.cp n - (B.ev hsj wi - B.ev hsi wj)) * Tw.ξ n = 0 := by
    have hh := hB3'.symm.trans hpow
    linear_combination -hh
  have hmem := Tw.ann n _ hξ
  rw [← Tw.ker_eq n, RingHom.mem_ker] at hmem
  have e1 : (Tw.π n).1 (B.ev hsj wi) = (Tw.q n).1 (B.ev (ht j) (bt i)) := by
    rw [BX.ev_map B (Tw.π n).1 hsj wi, hsj_spec, hwi, ← BX.ev_map B (Tw.q n).1 (ht j) (bt i)]
  have e2 : (Tw.π n).1 (B.ev hsi wj) = (Tw.q n).1 (B.ev (ht i) (bt j)) := by
    rw [BX.ev_map B (Tw.π n).1 hsi wj, hsi_spec, hwj, ← BX.ev_map B (Tw.q n).1 (ht i) (bt j)]
  simp only [map_sub, map_mul, map_natCast, Tw.cp_spec, e1, e2] at hmem
  rw [map_sub, map_sub, map_mul, hk]
  linear_combination hmem

end ReciprocityTheory.PGsh
end
end

noncomputable section

open TensorProduct Matrix

namespace ReciprocityTheory.PGsh

variable {R₀ : Type} [CommRing R₀]

end ReciprocityTheory.PGsh
end
end

section -- merged from ReciprocityTheory.DualLattices.StdJForm
section -- merged from ReciprocityTheory.DualLattices.ThmAUses
noncomputable section

open Matrix TensorProduct

namespace ReciprocityTheory.PGsh

section Mat

variable {D : Type} [CommRing D] {g : ℕ}

lemma stdJ_mul_self : stdJ D g * stdJ D g = -1 := by
  ext (i | i) (j | j) <;> simp [stdJ, Matrix.fromBlocks_multiply, Matrix.one_apply]

lemma det_stdJ_sq : (stdJ D g).det ^ 2 = 1 := by
  rw [sq, ← Matrix.det_mul, stdJ_mul_self, Matrix.det_neg, Matrix.det_one, mul_one, Fintype.card_sum,
    Fintype.card_fin, ← two_mul, pow_mul]
  simp

lemma isUnit_det_stdJ : IsUnit (stdJ D g).det := by
  exact isUnit_iff_exists_inv.2 ⟨(stdJ D g).det, by rw [← sq, det_stdJ_sq]⟩

lemma det_sq_eq (E Φ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D) (c : D)
    (hJ : Φᵀ * stdJ D g * Φ = c • E) :
    Φ.det ^ 2 = c ^ (2 * g) * (E.det * (stdJ D g).det) := by
  have h := congrArg Matrix.det hJ
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Fintype.card_sum, Fintype.card_fin,
    ← two_mul] at h
  have hJ2 := det_stdJ_sq (D := D) (g := g)
  calc Φ.det ^ 2 = Φ.det ^ 2 * ((stdJ D g).det ^ 2) := by rw [hJ2, mul_one]
    _ = (Φ.det * (stdJ D g).det * Φ.det) * (stdJ D g).det := by ring
    _ = c ^ (2 * g) * (E.det * (stdJ D g).det) := by rw [h]; ring

end Mat

section Span

variable {R₀ : Type} [CommRing R₀]

end Span

section Val

variable {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]

end Val

end ReciprocityTheory.PGsh
end
end

section -- merged from ReciprocityTheory.DualLattices.IsotypicAveragingStatement
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def IsotypicAveragingStatement : Prop :=
  ∀ (S : Type) [CommRing S] (g m : ℕ) (Ht Bt : Matrix (Fin g) (Ix g) S)
    (E : Matrix (Ix g) (Ix g) S) (cp : S)
    (εT : Fin m → Matrix (Ix g) (Ix g) S) (εL : Fin m → Matrix (Fin g) (Fin g) S)
    (π : Equiv.Perm (Fin m)),
    (∀ i, π (π i) = i) →
    (∀ i j, εT i * εT j = if i = j then εT i else 0) → ∑ i, εT i = 1 →
    (∀ i j, εL i * εL j = if i = j then εL i else 0) → ∑ i, εL i = 1 →
    (∀ i, Ht * εT i = (εL (π i))ᵀ * Ht) →
    (∀ i, (εT i)ᵀ * E = E * εT (π i)) →
    Btᵀ * Ht - Htᵀ * Bt = cp • E →
    let Bt' := ∑ i, εL i * Bt * εT i
    (Bt'ᵀ * Ht - Htᵀ * Bt' = cp • E) ∧ (∀ i, Bt' * εT i = εL i * Bt') ∧
    (Matrix.fromRows Ht Bt').det ^ 2 = cp ^ (2 * g) * E.det

end ReciprocityTheory.PGsh.Up
end
end

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

private lemma stdJ_form' {D : Type} [CommRing D] {g : ℕ}
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D) (i j : Fin g ⊕ Fin g) :
    (Mᵀ * stdJ D g * M) i j =
      ∑ a, (M (Sum.inr a) i * M (Sum.inl a) j - M (Sum.inl a) i * M (Sum.inr a) j) := by
  simp [stdJ, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Finset.sum_sub_distrib,
    sub_eq_add_neg, add_comm]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring

private lemma stdJ_eq (D : Type) [CommRing D] (g : ℕ) :
    stdJ D g = fromBlocks 1 (-1) 0 1 * fromBlocks 1 0 1 1 * fromBlocks 1 (-1) 0 1 := by
  rw [stdJ]
  simp [Matrix.fromBlocks_multiply]

private lemma det_stdJ (D : Type) [CommRing D] (g : ℕ) : (stdJ D g).det = 1 := by
  rw [stdJ_eq, Matrix.det_mul, Matrix.det_mul]
  simp [Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂]

theorem u1 : IsotypicAveragingStatement := by
  intro S _ g m Ht Bt E cp εT εL π hπ hT hT1 hL hL1 hHt hE hBH
  intro Bt'
  have hBt' : Bt' = ∑ i, εL i * Bt * εT i := rfl
  have hLt : ∀ i, (εL i)ᵀ * Ht = Ht * εT (π i) := by
    intro i
    have h := hHt (π i)
    rw [hπ] at h
    exact h.symm
  have hHtL : ∀ i, Htᵀ * εL i = (εT (π i))ᵀ * Htᵀ := by
    intro i
    have h := congrArg Matrix.transpose (hLt i)
    simpa [Matrix.transpose_mul] using h
  have part2 : ∀ i, Bt' * εT i = εL i * Bt' := by
    intro i
    have l : ∀ j, εL j * Bt * εT j * εT i = if j = i then εL j * Bt * εT j else 0 := by
      intro j
      rw [Matrix.mul_assoc (εL j * Bt), hT j i]
      split_ifs with h
      · subst h; rfl
      · simp
    have r : ∀ j, εL i * (εL j * Bt * εT j) = if j = i then εL j * Bt * εT j else 0 := by
      intro j
      by_cases h : j = i
      · subst h
        rw [if_pos rfl, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hL, if_pos rfl]
      · rw [if_neg h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hL, if_neg (Ne.symm h),
          Matrix.zero_mul, Matrix.zero_mul]
    rw [hBt', Matrix.sum_mul, Matrix.mul_sum]
    simp only [l, r]
  have hA : Bt'ᵀ * Ht = ∑ i, (εT i)ᵀ * Btᵀ * Ht * εT (π i) := by
    rw [hBt', Matrix.transpose_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.transpose_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [hLt i]
  have hB : Htᵀ * Bt' = ∑ i, (εT i)ᵀ * Htᵀ * Bt * εT (π i) := by
    rw [hBt', Matrix.mul_sum, ← Equiv.sum_comp π (fun i => Htᵀ * (εL i * Bt * εT i))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [← Matrix.mul_assoc]
    rw [hHtL (π i), hπ]
  have part1 : Bt'ᵀ * Ht - Htᵀ * Bt' = cp • E := by
    rw [hA, hB, ← Finset.sum_sub_distrib]
    have h : ∀ i, (εT i)ᵀ * Btᵀ * Ht * εT (π i) - (εT i)ᵀ * Htᵀ * Bt * εT (π i) =
        cp • (E * εT (π i)) := by
      intro i
      rw [Matrix.mul_assoc ((εT i)ᵀ) Btᵀ Ht, Matrix.mul_assoc ((εT i)ᵀ) Htᵀ Bt, ← Matrix.sub_mul,
        ← Matrix.mul_sub, hBH, Matrix.mul_smul, hE i, Matrix.smul_mul, Matrix.mul_assoc, hT,
        if_pos rfl]
    simp only [h]
    rw [← Finset.smul_sum, ← Matrix.mul_sum, Equiv.sum_comp π εT, hT1, Matrix.mul_one]
  have hJ : (Matrix.fromRows Ht Bt')ᵀ * stdJ S g * Matrix.fromRows Ht Bt' = cp • E := by
    rw [← part1]
    ext i j
    rw [stdJ_form']
    simp [Matrix.sub_apply, Matrix.mul_apply, Finset.sum_sub_distrib]
  refine ⟨part1, part2, ?_⟩
  rw [det_sq_eq E _ cp hJ, det_stdJ, mul_one]

end ReciprocityTheory.PGsh.Up
end
end

section -- merged from ReciprocityTheory.DualLattices.LenIdBStatement
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

variable {R : Type} [CommRing R] {g m : ℕ}

def inclE (εL : Fin m → Matrix (Fin g) (Fin g) R) (i j : Fin m) :
    LinearMap.range (Matrix.mulVecLin (εL i)) →ₗ[R] qE εL i j where
  toFun x := ⟨Sum.elim (0 : Fin g → R) (x : Fin g → R), by
    refine ⟨?_, ?_⟩
    · show (Sum.elim (0 : Fin g → R) (x : Fin g → R)) ∘ Sum.inl ∈ LinearMap.range (Matrix.mulVecLin (εL j)ᵀ)
      exact ⟨0, by funext k; simp⟩
    · show (Sum.elim (0 : Fin g → R) (x : Fin g → R)) ∘ Sum.inr ∈ LinearMap.range (Matrix.mulVecLin (εL i))
      exact x.2⟩
  map_add' x y := by ext k; rcases k with k | k <;> simp
  map_smul' c x := by ext k; rcases k with k | k <;> simp

def projE (εL : Fin m → Matrix (Fin g) (Fin g) R) (i j : Fin m) :
    qE εL i j →ₗ[R] LinearMap.range (Matrix.mulVecLin (εL j)ᵀ) where
  toFun q := ⟨(q : Fin g ⊕ Fin g → R) ∘ Sum.inl, q.2.1⟩
  map_add' x y := rfl
  map_smul' c x := rfl

abbrev sxE (Ht Bt : Matrix (Fin g) (Ix g) R) (εT : Fin m → Matrix (Ix g) (Ix g) R)
    (εL : Fin m → Matrix (Fin g) (Fin g) R) (π : Equiv.Perm (Fin m)) (i : Fin m) :
    Submodule R (qE εL i (π i)) :=
  ((LinearMap.range (Matrix.mulVecLin (εT i))).map (Matrix.mulVecLin (fromRows Ht Bt))).comap
    (qE εL i (π i)).subtype

abbrev yModE (Ht Bt : Matrix (Fin g) (Ix g) R) (εT : Fin m → Matrix (Ix g) (Ix g) R)
    (εL : Fin m → Matrix (Fin g) (Fin g) R) (π : Equiv.Perm (Fin m)) (i : Fin m) :=
  LinearMap.range (Matrix.mulVecLin (εL i)) ⧸ (sxE Ht Bt εT εL π i).comap (inclE εL i (π i))

private theorem fromRows_mulVec_comp_inl (Ht Bt : Matrix (Fin g) (Ix g) R) (w : Ix g → R) :
    (fromRows Ht Bt *ᵥ w) ∘ Sum.inl = Ht *ᵥ w := by
  funext k
  rfl

private theorem fromRows_mulVec_comp_inr (Ht Bt : Matrix (Fin g) (Ix g) R) (w : Ix g → R) :
    (fromRows Ht Bt *ᵥ w) ∘ Sum.inr = Bt *ᵥ w := by
  funext k
  rfl

private theorem coe_inclE_eq_elim_zero (εL : Fin m → Matrix (Fin g) (Fin g) R) (i j : Fin m)
    (x : LinearMap.range (Matrix.mulVecLin (εL i))) :
    ((inclE εL i j x : qE εL i j) : Fin g ⊕ Fin g → R) =
      Sum.elim (0 : Fin g → R) (x : Fin g → R) := rfl

private theorem coe_projE_eq_comp_inl (εL : Fin m → Matrix (Fin g) (Fin g) R) (i j : Fin m)
    (q : qE εL i j) :
    ((projE εL i j q : LinearMap.range (Matrix.mulVecLin (εL j)ᵀ)) : Fin g → R) =
      (q : Fin g ⊕ Fin g → R) ∘ Sum.inl := rfl

private theorem projE_inclE_eq_zero (εL : Fin m → Matrix (Fin g) (Fin g) R) (i j : Fin m)
    (x : LinearMap.range (Matrix.mulVecLin (εL i))) :
    projE εL i j (inclE εL i j x) = 0 := by
  apply Subtype.ext
  funext k
  rfl

private theorem sxE_le_comap_projE (Ht Bt : Matrix (Fin g) (Ix g) R)
    (εT : Fin m → Matrix (Ix g) (Ix g) R)
    (εL : Fin m → Matrix (Fin g) (Fin g) R) (π : Equiv.Perm (Fin m)) (i : Fin m) :
    sxE Ht Bt εT εL π i ≤
      (((LinearMap.range (Matrix.mulVecLin (εT i))).map (Matrix.mulVecLin Ht)).comap
        (LinearMap.range (Matrix.mulVecLin (εL (π i))ᵀ)).subtype).comap (projE εL i (π i)) := by
  intro q hq
  obtain ⟨w, hw, hwq⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp hq)
  refine Submodule.mem_comap.mpr (Submodule.mem_comap.mpr (Submodule.mem_map.mpr ⟨w, hw, ?_⟩))
  rw [Submodule.subtype_apply, coe_projE_eq_comp_inl, Matrix.mulVecLin_apply, ← fromRows_mulVec_comp_inl Ht Bt w]
  rw [Submodule.subtype_apply, Matrix.mulVecLin_apply] at hwq
  rw [hwq]

theorem xModE_len {C : Type} [Field C] {v : Valuation C NNReal} [Algebra R C]
    (hS2 : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (X : Matrix κ κ R),
      HasLen v R ((κ → R) ⧸ LinearMap.range X.mulVecLin) (v (algebraMap R C X.det)))
    (Ht Bt : Matrix (Fin g) (Ix g) R) (εT : Fin m → Matrix (Ix g) (Ix g) R)
    (εL : Fin m → Matrix (Fin g) (Fin g) R) (π : Equiv.Perm (Fin m)) (i : Fin m)
    (hHt : Ht * εT i = (εL (π i))ᵀ * Ht) (hBt : Bt * εT i = εL i * Bt) {y c₂ : NNReal}
    (hy : HasLen v R (yModE Ht Bt εT εL π i) y)
    (hc : HasLen v R (cokE Ht εT εL (π i) i) c₂) :
    HasLen v R (xModE Ht Bt εT εL π i) (y * c₂) := by
  refine hasLen_ext hS2
    (Submodule.mapQ ((sxE Ht Bt εT εL π i).comap (inclE εL i (π i)))
      (sxE Ht Bt εT εL π i) (inclE εL i (π i)) le_rfl)
    (Submodule.mapQ (sxE Ht Bt εT εL π i)
      (((LinearMap.range (Matrix.mulVecLin (εT i))).map (Matrix.mulVecLin Ht)).comap
        (LinearMap.range (Matrix.mulVecLin (εL (π i))ᵀ)).subtype)
      (projE εL i (π i)) (sxE_le_comap_projE Ht Bt εT εL π i))
    ?_ ?_ ?_ hy hc
  · intro a b hab
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq] at hab
    rw [Submodule.Quotient.eq, Submodule.mem_comap, map_sub]
    exact hab
  · intro z
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    refine ⟨Submodule.Quotient.mk ⟨Sum.elim (z : Fin g → R) (0 : Fin g → R), by
      refine ⟨?_, ?_⟩
      · show (Sum.elim (z : Fin g → R) (0 : Fin g → R)) ∘ Sum.inl ∈
          LinearMap.range (Matrix.mulVecLin (εL (π i))ᵀ)
        exact z.2
      · show (Sum.elim (z : Fin g → R) (0 : Fin g → R)) ∘ Sum.inr ∈
          LinearMap.range (Matrix.mulVecLin (εL i))
        exact ⟨0, by funext k; simp⟩⟩, ?_⟩
    rw [Submodule.mapQ_apply]
    exact congrArg Submodule.Quotient.mk (Subtype.ext rfl)
  · apply le_antisymm
    · intro x hx
      obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hx
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero,
        projE_inclE_eq_zero]
      exact Submodule.zero_mem _
    · intro x hx
      obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨w, hw, hwq⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp hx)
      obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hw
      rw [Submodule.subtype_apply, coe_projE_eq_comp_inl, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply] at hwq
      have hB' : Bt *ᵥ (εT i *ᵥ u) ∈ LinearMap.range (Matrix.mulVecLin (εL i)) :=
        ⟨Bt *ᵥ u, by rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hBt]⟩
      have hq2 : (q : Fin g ⊕ Fin g → R) ∘ Sum.inr ∈ LinearMap.range (Matrix.mulVecLin (εL i)) := q.2.2
      have hr : (q : Fin g ⊕ Fin g → R) ∘ Sum.inr - Bt *ᵥ (εT i *ᵥ u) ∈
          LinearMap.range (Matrix.mulVecLin (εL i)) := Submodule.sub_mem _ hq2 hB'
      refine LinearMap.mem_range.mpr ⟨Submodule.Quotient.mk ⟨_, hr⟩, ?_⟩
      rw [Submodule.mapQ_apply, eq_comm, Submodule.Quotient.eq]
      refine Submodule.mem_comap.mpr (Submodule.mem_map.mpr ⟨(εT i).mulVecLin u, ⟨u, rfl⟩, ?_⟩)
      rw [Submodule.subtype_apply, Submodule.coe_sub, coe_inclE_eq_elim_zero, Matrix.mulVecLin_apply,
        Matrix.mulVecLin_apply]
      funext k
      rcases k with k | k
      · have hF := congrFun (fromRows_mulVec_comp_inl Ht Bt (εT i *ᵥ u)) k
        have hk := congrFun hwq k
        simp only [Function.comp_apply] at hF hk
        rw [Pi.sub_apply, hF, Sum.elim_inl, Pi.zero_apply, sub_zero]
        exact hk
      · have hF := congrFun (fromRows_mulVec_comp_inr Ht Bt (εT i *ᵥ u)) k
        simp only [Function.comp_apply] at hF
        rw [Pi.sub_apply, hF, Sum.elim_inr]
        show _ = _ - (((q : Fin g ⊕ Fin g → R) ∘ Sum.inr - Bt *ᵥ (εT i *ᵥ u)) k)
        rw [Pi.sub_apply, Function.comp_apply, sub_sub_cancel]

def LenIdBStatement : Prop :=
  ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → ∀ (g m : ℕ) (Ht Bt : Matrix (Fin g) (Ix g) R) (E : Matrix (Ix g) (Ix g) R)
    (cp : R), cp ≠ 0 → IsUnit E.det → Btᵀ * Ht - Htᵀ * Bt = cp • E →
    ∀ (εT : Fin m → Matrix (Ix g) (Ix g) R) (εL : Fin m → Matrix (Fin g) (Fin g) R)
    (π : Equiv.Perm (Fin m)), (∀ i, π (π i) = i) →
    (∀ i j, εT i * εT j = if i = j then εT i else 0) → ∑ i, εT i = 1 →
    (∀ i j, εL i * εL j = if i = j then εL i else 0) → ∑ i, εL i = 1 →
    (∀ i, Ht * εT i = (εL (π i))ᵀ * Ht) → (∀ i, Bt * εT i = εL i * Bt) →
    (∀ i, (εT i)ᵀ * E = E * εT (π i)) →
    ∀ (i : Fin m) (d : ℕ), Nonempty (LinearMap.range (Matrix.mulVecLin (εL i)) ≃ₗ[R] (Fin d → R)) →
    ∀ c₁ : NNReal, HasLen v R (cokE Ht εT εL i (π i)) c₁ →
      ∃ y : NNReal, HasLen v R (yModE Ht Bt εT εL π i) y ∧ y * c₁ = v (algebraMap R C cp) ^ d

theorem lenId_of
    (hS2 : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
      v.Integers R → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (X : Matrix κ κ R),
      HasLen v R ((κ → R) ⧸ LinearMap.range X.mulVecLin) (v (algebraMap R C X.det)))
    (hB : LenIdBStatement) : LenIdStatement := by
  intro C _ v R _ _ hv g m Ht Bt E cp hcp hE hform εT εL π hπ hεT hsumT hεL hsumL hHt hBt hεE i d hd
    c₁ c₂ hc₁ hc₂
  obtain ⟨y, hy, hyc⟩ := hB C v R hv g m Ht Bt E cp hcp hE hform εT εL π hπ hεT hsumT hεL hsumL hHt hBt
    hεE i d hd c₁ hc₁
  refine ⟨y * c₂, xModE_len (hS2 C v R hv) Ht Bt εT εL π i (hHt i) (hBt i) hy hc₂, ?_⟩
  rw [mul_right_comm, hyc]

end ReciprocityTheory.PGsh.Up
end
end
