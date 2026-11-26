module

public import ReciprocityTheory.DualLattices.UnramifiedCokernelLowerBoundOf
public import ReciprocityTheory.DualLattices.LinPairStatement
public import ReciprocityTheory.DualLattices.IsPairingValueAddRight

@[expose] public section

section -- merged from ReciprocityTheory.DualLattices.KilledGen
noncomputable section

namespace ReciprocityTheory.PGsh.Up

theorem killedGen : KilledGenStatement := by
  intro C _ v R _ _ hv M _ _ x d c hx hy hc
  obtain ⟨y, hy⟩ := hy
  have h := prod_le_of_gen hv hx y hy (fun _ => c) (fun i => ⟨0, by simp [hc]⟩)
  simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

end ReciprocityTheory.PGsh.Up
end
end

section -- merged from ReciprocityTheory.DualLattices.IdemGen
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

theorem idemGen : IdemGenStatement := by
  rintro R _ g d P hP ⟨e⟩

  let L : (Fin g → R) →ₗ[R] (Fin d → R) := e.toLinearMap ∘ₗ (mulVecLin P).rangeRestrict
  let T : (Fin d → R) →ₗ[R] (Fin g → R) :=
    (LinearMap.range (mulVecLin P)).subtype ∘ₗ e.symm.toLinearMap
  obtain ⟨M, hLM⟩ : ∃ M : Matrix (Fin d) (Fin g) R, Matrix.toLin' M = L :=
    ⟨_, Matrix.toLin'_toMatrix' L⟩
  obtain ⟨N, hTN⟩ : ∃ N : Matrix (Fin g) (Fin d) R, Matrix.toLin' N = T :=
    ⟨_, Matrix.toLin'_toMatrix' T⟩

  have hPNM : P = N * M := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, hLM, hTN]
    refine LinearMap.ext fun x => ?_
    simp [L, T, Matrix.toLin'_apply]

  have hMP : M * P = M := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, hLM]
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply, L, LinearMap.coe_comp,
      Function.comp_apply, LinearEquiv.coe_coe]
    congr 1
    apply Subtype.ext
    simp [Matrix.mulVec_mulVec, hP]

  have hrow : ∀ i, Pᵀ *ᵥ M i = M i := by
    intro i
    funext j
    have h := congrFun (congrFun hMP i) j
    simp only [Matrix.mul_apply] at h
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    rw [← h]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  refine ⟨fun i => ⟨M i, LinearMap.mem_range.mpr ⟨M i, by rw [Matrix.mulVecLin_apply]; exact hrow i⟩⟩, ?_⟩
  rw [eq_top_iff]
  rintro ⟨w, hw⟩ -
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hw

  have key : mulVecLin Pᵀ v = ∑ i, (Nᵀ *ᵥ v) i • M i := by
    rw [Matrix.mulVecLin_apply, hPNM, Matrix.transpose_mul, ← Matrix.mulVec_mulVec]
    funext j
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  refine (Submodule.mem_span_range_iff_exists_fun R).mpr ⟨fun i => (Nᵀ *ᵥ v) i, ?_⟩
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  exact key.symm

end ReciprocityTheory.PGsh.Up
end
end

section -- merged from ReciprocityTheory.DualLattices.LenEx
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

theorem lenEx : LenExStatement := by
  intro C _ v R _ _ hv g Ht A B
  classical
  have : IsDomain R := hv.hom_inj.isDomain
  have := ValuationRing.of_integers v hv
  set Mm := LinearMap.range (Matrix.mulVecLin Aᵀ) with hMm
  set N := (LinearMap.range (Matrix.mulVecLin B)).map (Matrix.mulVecLin Ht) with hN
  have hfgM : Mm.FG := by
    rw [hMm, LinearMap.range_eq_map]; exact Module.Finite.fg_top.map _
  have hfgN : N.FG := by
    rw [hN, LinearMap.range_eq_map]; exact (Module.Finite.fg_top.map _).map _
  set S := Mm ⊔ N with hS
  have hfgS : S.FG := hfgM.sup hfgN
  have : Module.Finite R S := Module.Finite.iff_fg.2 hfgS
  have : Module.Free R S := L2.SecondCohomologyLattice.free_of_finite_torsionFree S (by
    rintro r ⟨x, hx⟩ hr h
    apply Subtype.ext
    funext i
    have := congrFun (congrArg Subtype.val h) i
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Submodule.coe_zero,
      Pi.zero_apply] at this
    exact (mul_eq_zero.1 this).resolve_left hr)
  set bS := (Module.Free.chooseBasis R S).reindex (Fintype.equivFin _) with hbS
  set e := bS.equivFun with he
  set N' := N.comap S.subtype with hN'
  have hfgN' : N'.FG := by
    apply Submodule.fg_of_fg_map_injective S.subtype S.injective_subtype
    rw [hN', Submodule.map_comap_subtype, inf_eq_right.2 le_sup_right]
    exact hfgN
  set K := N'.map e.toLinearMap with hK
  have hfgK : K.FG := hfgN'.map _
  obtain ⟨n, gK, hgK⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfgK
  have smithGen (b : ℕ) (f : Fin n → Fin b → R) :
      ∃ c : Fin b → R, Nonempty (((Fin b → R) ⧸ Submodule.span R (Set.range f)) ≃ₗ[R]
        ((i : Fin b) → R ⧸ Ideal.span {c i})) := by
    induction b with
    | zero =>
      exact ⟨Fin.elim0, ⟨LinearEquiv.ofSubsingleton _ _⟩⟩
    | succ b ih =>
      obtain ⟨i, a, u, s, hu, hau, hs, -, -⟩ := Smith.exists_pivot hv (b := b) f
      obtain ⟨ep⟩ := Smith.pivot_equiv f i a u s hu hau hs
      obtain ⟨c, ⟨er⟩⟩ := ih (fun j => Fin.removeNth i (f j - s j • a • u))
      exact ⟨Fin.cons a c,
        ⟨(ep.trans ((LinearEquiv.refl R _).prodCongr er)).trans (Smith.consEquiv a c)⟩⟩
  obtain ⟨c, ⟨ec⟩⟩ := smithGen _ gK
  refine ⟨∏ i, v (algebraMap R C (c i)), _, c, ⟨?_⟩, rfl⟩
  have h1 : N.comap Mm.subtype = Mm.comap Mm.subtype ⊓ N.comap Mm.subtype := by
    rw [Submodule.comap_subtype_self, top_inf_eq]
  exact (Submodule.quotEquivOfEq _ _ h1).trans ((LinearMap.quotientInfEquivSupQuotient Mm N).trans
    ((Submodule.Quotient.equiv N' K e rfl).trans ((Submodule.quotEquivOfEq _ _ hgK.symm).trans ec)))

end ReciprocityTheory.PGsh.Up
end
end

section -- merged from ReciprocityTheory.DualLattices.CokernelLengthComparisonOf
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section Defs

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}

def btP (H : HodgeTateDatum p g v R O σ cp) {m : ℕ} (e : Fin m → O) : Matrix (Fin g) (Ix g) R :=
  ∑ i, H.ρL (e i) * H.Bt * (H.ρ (e i)).map (algebraMap ℤ_[p] R) +
    H.PL * H.Bt * H.P.map (algebraMap ℤ_[p] R)

def phiP (H : HodgeTateDatum p g v R O σ cp) {m : ℕ} (e : Fin m → O) : Matrix (Fin g ⊕ Fin g) (Ix g) R :=
  fromRows H.Ht (btP H e)

def qW (H : HodgeTateDatum p g v R O σ cp) (a b : O) : Submodule R (Fin g ⊕ Fin g → R) :=
  (lieDPart H b).comap (LinearMap.funLeft R R Sum.inl) ⊓
    (LinearMap.range (Matrix.mulVecLin (H.ρL a))).comap (LinearMap.funLeft R R Sum.inr)

abbrev xMod (H : HodgeTateDatum p g v R O σ cp) {m : ℕ} (e : Fin m → O) (π : Equiv.Perm (Fin m)) (w : Fin m) :=
  qW H (e w) (e (π w)) ⧸
    ((tPart H (e w)).map (Matrix.mulVecLin (phiP H e))).comap (qW H (e w) (e (π w))).subtype

end Defs

def WdetLenStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp) (m : ℕ) (e : Fin m → O)
    (π : Equiv.Perm (Fin m)),
    (∀ i j, e i * e j = if i = j then e i else 0) → (∀ i, σ (e i) = e (π i)) →
    (∑ i, H.ρ (e i)) + H.P = 1 → (∀ i, H.ρ (e i) * H.P = 0) →
    (∑ i, H.ρL (e i)) + H.PL = 1 → (∀ i, H.ρL (e i) * H.PL = 0) →
    ∀ w, π w ≠ w → ∀ cw cwb : NNReal,
      HasLen v R (htCoker H (e w) (e (π w))) cw →
      HasLen v R (htCoker H (e (π w)) (e w)) cwb →
      ∃ (d : ℕ) (X : NNReal),
        Nonempty (LinearMap.range (Matrix.mulVecLin (H.ρL (e w))) ≃ₗ[R] (Fin d → R)) ∧
        HasLen v R (xMod H e π w) X ∧ X * cw = v (algebraMap R C cp) ^ d * cwb

def WdetDegStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp) (m : ℕ) (e : Fin m → O)
    (π : Equiv.Perm (Fin m)),
    (∀ i j, e i * e j = if i = j then e i else 0) → (∀ i, σ (e i) = e (π i)) →
    (∑ i, H.ρ (e i)) + H.P = 1 → (∀ i, H.ρ (e i) * H.P = 0) →
    (∑ i, H.ρL (e i)) + H.PL = 1 → (∀ i, H.ρL (e i) * H.PL = 0) →
    ∀ w, π w ≠ w → ∀ (d : ℕ) (X : NNReal),
      Nonempty (LinearMap.range (Matrix.mulVecLin (H.ρL (e w))) ≃ₗ[R] (Fin d → R)) →
      HasLen v R (xMod H e π w) X → X ≤ v (algebraMap R C cp) ^ d

theorem cokernelLengthComparison_of (hW1 : WdetLenStatement) (hW2 : WdetDegStatement) : CokernelLengthComparisonStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H m e π he hσ h1 h2 h3 h4 w hw cw cwb hcw hcwb
  obtain ⟨d, X, hd, hX, hXe⟩ :=
    hW1 p g C v R O σ cp hS H m e π he hσ h1 h2 h3 h4 w hw cw cwb hcw hcwb
  have hle := hW2 p g C v R O σ cp hS H m e π he hσ h1 h2 h3 h4 w hw d X hd hX
  have hcp : v (algebraMap R C cp) ≠ 0 := by
    intro h0
    have h5 := hS.cp_val
    rw [h0, zero_pow (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt).ne'] at h5
    exact hS.p_ne h5.symm
  have hpos : 0 < v (algebraMap R C cp) ^ d := pow_pos (pos_iff_ne_zero.mpr hcp) d
  have h6 : v (algebraMap R C cp) ^ d * cwb ≤ v (algebraMap R C cp) ^ d * cw := by
    rw [← hXe]
    exact mul_le_mul_of_nonneg_right hle zero_le
  exact le_of_mul_le_mul_left h6 hpos

end ReciprocityTheory.PGsh.Up
end
end

section -- merged from ReciprocityTheory.DualLattices.NsetExpInjectiveSurjective
section -- merged from ReciprocityTheory.DualLattices.StThmA
noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

def ξmul {R' R : LAlg R₀} (π : LHom R' R) (ξ : (R' : Type u)) (hξ : ξ ∈ π.ker) :
    (R' : Type u) →ₗ[R₀] π.ker where
  toFun r := ⟨ξ * r, by
    rw [Submodule.restrictScalars_mem] at hξ ⊢
    exact Ideal.mul_mem_right r _ hξ⟩
  map_add' a b := by ext; simp [mul_add]
  map_smul' c r := by ext; simp

namespace BX

variable (B : BX R₀)

def ev {R' : LAlg R₀} (h : B.gg →ₗ[R₀] R') (v : B.gg ⊗[R₀] (R' : Type u)) : R' :=
  LinearMap.mul' R₀ R' (TensorProduct.map h LinearMap.id v)

end BX

end ReciprocityTheory.PGsh
end
end

noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

structure ATower (R₀ : Type u) [CommRing R₀] (p : ℕ) where
  O : LAlg R₀
  R' : ℕ → LAlg R₀
  R : ℕ → LAlg R₀
  π : ∀ n, LHom (R' n) (R n)
  q : ∀ n, LHom O (R n)
  ξ : ∀ n, (R' n : Type u)
  surj : ∀ n, Function.Surjective (π n).1
  ker_eq : ∀ n, RingHom.ker (π n).1 = Ideal.span {ξ n}
  ξ_sq : ∀ n, ξ n * ξ n = 0
  ann : ∀ n (a : (R' n : Type u)), a * ξ n = 0 → a ∈ Ideal.span {ξ n}
  char : ∀ n, ((p ^ (n + 1) : ℕ) : (R' n : Type u)) = 0
  sep : ∀ a : (O : Type u), (∀ n, (q n).1 a = 0) → a = 0
  c : (O : Type u)
  cp : ∀ n, (R' n : Type u)
  cp_spec : ∀ n, (π n).1 (cp n) = (q n).1 c
  zh : ∀ n, (R' n : Type u)ˣ
  zh_pow : ∀ n, (zh n : (R' n : Type u)) ^ (p ^ (n + 1)) = 1 + cp n * ξ n
  ζ : ∀ n, (O : Type u)ˣ
  ζ_spec : ∀ n, (q n).1 (ζ n : (O : Type u)) = (π n).1 (zh n : (R' n : Type u))

variable {R₀ : Type u} [CommRing R₀]

lemma ATower.ξ_mem {p : ℕ} (Tw : ATower R₀ p) (n : ℕ) : Tw.ξ n ∈ (Tw.π n).ker := by
  rw [LHom.ker, Submodule.restrictScalars_mem, Tw.ker_eq]
  exact Ideal.subset_span (Set.mem_singleton _)

lemma ATower.sqZero {p : ℕ} (Tw : ATower R₀ p) (n : ℕ) : (Tw.π n).SqZero := ⟨Tw.surj n, by
    rw [Tw.ker_eq, sq, Ideal.span_singleton_mul_span_singleton, Tw.ξ_sq, Ideal.span_singleton_eq_bot]⟩

def NsetExpInjectiveSurjective (B : BX R₀) {p : ℕ} (Tw : ATower R₀ p) : Prop :=
  ∀ (Dp : ∀ n, DualPair (Tw.R n)) (ι : Type) (τ : ι → ℕ → B.G Tw.O)
    (E : ι → ι → (Tw.O : Type u)) (ht : ι → B.gg →ₗ[R₀] (Tw.O : Type u))
    (bt : ι → B.gg ⊗[R₀] (Tw.O : Type u)),
    (∀ i j n, ∃ k : ℕ, (Tw.q n).1 (E i j) = k ∧
      B.IsPairing (p ^ (n + 1)) (τ i n) (τ j n) (Tw.ζ n ^ k)) →
    (∀ i n, B.IsHeight (Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ i n))
      ((Tw.q n).1.toLinearMap ∘ₗ ht i)) →
    (∀ i n, ∃ (th : B.G (Tw.R' n)) (w : B.gg ⊗[R₀] (Tw.R' n : Type u)),
      B.map (Tw.π n) th = B.map (Tw.q n) (τ i n) ∧
      (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
        (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) ∧
      LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap w =
        LinearMap.lTensor B.gg (Tw.q n).1.toLinearMap (bt i)) →
    ∀ i j, Tw.c * E i j = B.ev (ht j) (bt i) - B.ev (ht i) (bt j)

end ReciprocityTheory.PGsh
end
end

section -- merged from ReciprocityTheory.DualLattices.MemOfSumSingleEqZero
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

section

variable {R : Type} [CommRing R]

lemma single_smul_self {m : ℕ} (c : Fin m → R) (i : Fin m) :
    c i • (Pi.single i (1 : R ⧸ Ideal.span {c i}) : (i : Fin m) → R ⧸ Ideal.span {c i}) = 0 := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [Algebra.smul_def, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton_self]
  · simp [Pi.single_eq_of_ne hk]

lemma eq_sum_single {m : ℕ} (c : Fin m → R) (x : (i : Fin m) → R ⧸ Ideal.span {c i}) :
    x = ∑ i, (Quotient.out (x i) : R) • (Pi.single i (1 : R ⧸ Ideal.span {c i}) :
      (i : Fin m) → R ⧸ Ideal.span {c i}) := by
  funext k
  rw [Finset.sum_apply, Finset.sum_eq_single k (fun j _ hj => by simp [Pi.single_eq_of_ne' hj]) (by simp)]
  simp [Algebra.smul_def]

end

theorem hasLen_ext {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C]
    (hS2 : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (X : Matrix κ κ R),
      HasLen v R ((κ → R) ⧸ LinearMap.range X.mulVecLin) (v (algebraMap R C X.det)))
    {A B D : Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup D]
    [Module R D] (ι : A →ₗ[R] B) (π : B →ₗ[R] D) (hι : Function.Injective ι)
    (hπ : Function.Surjective π) (hex : LinearMap.range ι = LinearMap.ker π) {a c : NNReal}
    (ha : HasLen v R A a) (hc : HasLen v R D c) : HasLen v R B (a * c) := by
  classical
  obtain ⟨m, α, ⟨eA⟩, hαa⟩ := ha
  obtain ⟨m', δ, ⟨eD⟩, hδc⟩ := hc
  set gA : Fin m → A := fun i => eA.symm (Pi.single i 1) with hgA
  set gD : Fin m' → D := fun j => eD.symm (Pi.single j 1) with hgD
  have hgA0 : ∀ i, α i • gA i = 0 := fun i => by
    simp only [hgA]
    rw [← map_smul, single_smul_self, map_zero]
  have hgD0 : ∀ j, δ j • gD j = 0 := fun j => by
    simp only [hgD]
    rw [← map_smul, single_smul_self, map_zero]
  have reprA : ∀ y : A, y = ∑ i, (Quotient.out (eA y i) : R) • gA i := fun y => by
    conv_lhs => rw [← eA.symm_apply_apply y, eq_sum_single α (eA y)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hgA, map_sum, map_smul]
  have reprD : ∀ y : D, y = ∑ j, (Quotient.out (eD y j) : R) • gD j := fun y => by
    conv_lhs => rw [← eD.symm_apply_apply y, eq_sum_single δ (eD y)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hgD, map_sum, map_smul]
  have memA : ∀ r : Fin m → R, ∑ i, r i • gA i = 0 → ∀ i, r i ∈ Ideal.span {α i} := by
    intro r hr i
    have h1 : eA (∑ i, r i • gA i) = 0 := by rw [hr, map_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hgA, map_sum, map_smul, LinearEquiv.apply_symm_apply] at h1
    have h3 := congrFun h1 i
    rw [Finset.sum_apply, Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne' hj]) (by simp)] at h3
    simpa [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] using h3
  have memD : ∀ r : Fin m' → R, ∑ j, r j • gD j = 0 → ∀ j, r j ∈ Ideal.span {δ j} := by
    intro r hr i
    have h1 : eD (∑ j, r j • gD j) = 0 := by rw [hr, map_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hgD, map_sum, map_smul, LinearEquiv.apply_symm_apply] at h1
    have h3 := congrFun h1 i
    rw [Finset.sum_apply, Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne' hj]) (by simp)] at h3
    simpa [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] using h3
  have hπι : ∀ y : A, π (ι y) = 0 := fun y => by
    have h1 : ι y ∈ LinearMap.range ι := ⟨y, rfl⟩
    rw [hex] at h1
    exact h1
  choose b hb using fun j => hπ (gD j)
  have hdb : ∀ j, ∃ y : A, ι y = δ j • b j := fun j => by
    have h1 : δ j • b j ∈ LinearMap.ker π := by rw [LinearMap.mem_ker, map_smul, hb, hgD0]
    rw [← hex] at h1
    exact h1
  choose aj haj using hdb
  set x : Fin m' → Fin m → R := fun j i => (Quotient.out (eA (aj j) i) : R) with hxdef
  have hx : ∀ j, aj j = ∑ i, x j i • gA i := fun j => reprA (aj j)
  set gen : Fin m ⊕ Fin m' → B := Sum.elim (fun i => ι (gA i)) b with hgen
  let Φ : (Fin m ⊕ Fin m' → R) →ₗ[R] B :=
    { toFun := fun p => ∑ k, p k • gen k
      map_add' := fun p q => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c p => by simp [Finset.smul_sum, smul_smul] }
  have hΦ : ∀ p, Φ p = ∑ i, p (Sum.inl i) • ι (gA i) + ∑ j, p (Sum.inr j) • b j := fun p => by
    show ∑ k, p k • gen k = _
    rw [Fintype.sum_sum_type]
    rfl
  let X : Matrix (Fin m ⊕ Fin m') (Fin m ⊕ Fin m') R :=
    Matrix.fromBlocks (Matrix.diagonal α) (Matrix.of fun i j => -x j i) 0 (Matrix.diagonal δ)
  have hdet : X.det = (∏ i, α i) * ∏ j, δ j := by
    simp [X, Matrix.det_fromBlocks_zero₂₁, Matrix.det_diagonal]
  have hXl : ∀ w i, X.mulVec w (Sum.inl i) = α i * w (Sum.inl i) - ∑ j, x j i * w (Sum.inr j) := by
    intro w i
    simp [X, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.diagonal_apply, Finset.sum_neg_distrib,
      sub_eq_add_neg]
  have hXr : ∀ w j, X.mulVec w (Sum.inr j) = δ j * w (Sum.inr j) := by
    intro w j
    simp [X, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.diagonal_apply]
  have hιx : ∀ j, ι (aj j) = ∑ i, x j i • ι (gA i) := fun j => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx j, map_sum]
    simp only [map_smul]
  have hΦX : ∀ w, Φ (X.mulVec w) = 0 := by
    intro w
    rw [hΦ]
    simp only [hXl, hXr, sub_smul, Finset.sum_sub_distrib]
    have e1 : ∀ i, (α i * w (Sum.inl i)) • ι (gA i) = 0 := by
      intro i
      rw [mul_comm, mul_smul, ← map_smul, hgA0, map_zero, smul_zero]
    have e2 : ∀ j, (δ j * w (Sum.inr j)) • b j = w (Sum.inr j) • ι (aj j) := by
      intro j
      rw [mul_comm, mul_smul, haj]
    have e3 : ∑ i, (∑ j, x j i * w (Sum.inr j)) • ι (gA i) = ∑ j, w (Sum.inr j) • ι (aj j) := by
      simp only [hιx, Finset.smul_sum, smul_smul, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm]
    simp only [e1, e2, Finset.sum_const_zero, zero_sub, e3, neg_add_cancel]
  have hker : LinearMap.ker Φ = LinearMap.range X.mulVecLin := by
    ext p
    constructor
    · intro hp
      rw [LinearMap.mem_ker, hΦ] at hp
      have hπs : ∑ j, p (Sum.inr j) • gD j = 0 := by
        have h1 := congrArg π hp
        set_option synthInstance.maxHeartbeats 100000 in
          simpa [map_add (f := _), map_sum, map_smul, hb, hπι] using h1
      choose t ht using fun j => Ideal.mem_span_singleton'.1 (memD _ hπs j)
      have hsb : ∑ j, p (Sum.inr j) • b j = ι (∑ i, (∑ j, t j * x j i) • gA i) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simp only [map_smul]
        have e4 : ∀ j, p (Sum.inr j) • b j = t j • ι (aj j) := by
          intro j
          rw [← ht j, mul_smul, haj]
        simp only [e4, hιx, Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]
      have hι0 : ι (∑ i, (p (Sum.inl i) + ∑ j, t j * x j i) • gA i) = 0 := by
        rw [← hp, hsb]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [add_smul, Finset.sum_add_distrib, map_add (f := _), map_sum, map_smul]
      have hA0 : ∑ i, (p (Sum.inl i) + ∑ j, t j * x j i) • gA i = 0 :=
        hι (hι0.trans (map_zero ι).symm)
      choose q hq using fun i => Ideal.mem_span_singleton'.1 (memA _ hA0 i)
      refine ⟨Sum.elim q t, ?_⟩
      funext k
      cases k with
      | inl i =>
        show X.mulVec (Sum.elim q t) (Sum.inl i) = p (Sum.inl i)
        rw [hXl]
        simp only [Sum.elim_inl, Sum.elim_inr]
        have hqi := hq i
        rw [show ∑ j, x j i * t j = ∑ j, t j * x j i from Finset.sum_congr rfl fun j _ => mul_comm _ _]
        linear_combination hqi
      | inr j =>
        show X.mulVec (Sum.elim q t) (Sum.inr j) = p (Sum.inr j)
        rw [hXr]
        simp only [Sum.elim_inr]
        rw [mul_comm]
        exact ht j
    · rintro ⟨w, rfl⟩
      exact hΦX w
  have hsurj : Function.Surjective Φ := by
    intro y
    set s : Fin m' → R := fun j => (Quotient.out (eD (π y) j) : R) with hs
    have hys : y - ∑ j, s j • b j ∈ LinearMap.range ι := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hex, LinearMap.mem_ker, map_sub, map_sum]
      simp only [map_smul, hb]
      rw [← reprD (π y), sub_self]
    obtain ⟨zA, hzA⟩ := hys
    refine ⟨Sum.elim (fun i => (Quotient.out (eA zA i) : R)) s, ?_⟩
    rw [hΦ]
    simp only [Sum.elim_inl, Sum.elim_inr]
    have e5 : ∑ i, (Quotient.out (eA zA i) : R) • ι (gA i) = ι zA := by
      conv_rhs => rw [reprA zA]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_smul]
    rw [e5, hzA, sub_add_cancel]
  let e1 : ((Fin m ⊕ Fin m' → R) ⧸ LinearMap.range X.mulVecLin) ≃ₗ[R] B :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (Φ.quotKerEquivOfSurjective hsurj)
  obtain ⟨k, cc, ⟨e2⟩, hcc⟩ := hS2 (Fin m ⊕ Fin m') X
  refine ⟨k, cc, ⟨e1.symm.trans e2⟩, ?_⟩
  rw [hcc, hdet, map_mul, map_mul, map_prod, map_prod, map_prod, map_prod, hαa, hδc]

end ReciprocityTheory.PGsh.Up
end
end

section -- merged from ReciprocityTheory.DualLattices.EigenLengthFrobeniusStatement
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section Defs

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}

def bt2 (H : HodgeTateDatum p g v R O σ cp) (U : UnramData p g v R O σ cp H) : Matrix (Fin g) (Ix g) R :=
  ∑ i, U.εL i * H.Bt * U.εT i

end Defs

def EigenLengthProductStatement : Prop :=
  ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → ∀ (g m : ℕ) (Ht Bt : Matrix (Fin g) (Ix g) R)
    (εT : Fin m → Matrix (Ix g) (Ix g) R) (εL : Fin m → Matrix (Fin g) (Fin g) R)
    (π : Equiv.Perm (Fin m)), (∀ i, π (π i) = i) →
    (∀ i j, εT i * εT j = if i = j then εT i else 0) → ∑ i, εT i = 1 →
    (∀ i j, εL i * εL j = if i = j then εL i else 0) → ∑ i, εL i = 1 →
    (∀ i, Ht * εT i = (εL (π i))ᵀ * Ht) → (∀ i, Bt * εT i = εL i * Bt) →
    ∀ X : Fin m → NNReal, (∀ i, HasLen v R (xModE Ht Bt εT εL π i) (X i)) →
      ∏ i, X i = v (algebraMap R C (fromRows Ht Bt).det)

def EigenLengthFrobeniusStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    p ≠ 2 → HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal),
    (∀ i, HasLen v R (xModE H.Ht (bt2 H U) U.εT U.εL U.cj i) (X i)) →
    ∏ i, X i = v (algebraMap R C cp) ^ g →
    ∀ i, X i ^ p ≤ X (U.φ i) * v (algebraMap R C (p : R)) ^ U.r (U.φ i)

end ReciprocityTheory.PGsh.Up
end
end

section -- merged from ReciprocityTheory.DualLattices.SubMemSpan
noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace OAdj

variable {B : BX R₀} {O : LAlg R₀} (A : OAdj B O) {R : LAlg R₀} (s : LHom O R)

lemma e_hcongr {x₁ x₂ z₁ z₂ : B.G R} (hx : x₁ = x₂) (hz : z₁ = z₂)
    {u₁ : B.P R (A.a.f s x₁) z₁} {u₂ : B.P R (A.a.f s x₂) z₂} (hu : HEq u₁ u₂) :
    HEq (A.e s x₁ z₁ u₁) (A.e s x₂ z₂ u₂) := by
  subst hx hz; cases eq_of_heq hu; rfl

lemma e_zero1 (z : B.G R) :
    HEq (A.e s 0 z (B.tr1 (map_zero (A.a.f s)).symm (B.zero1 z))) (B.zero1 (A.ab.f s z)) := by
  set w0 := B.tr1 (map_zero (A.a.f s)).symm (B.zero1 z) with hw0
  have hw : HEq w0 (B.zero1 z) := B.castFst_heq _ _
  have h1 := A.equiv_addFst s 0 0 z w0 w0
  have h2 : HEq (A.e s (0 + 0) z (B.tr1 (map_add (A.a.f s) 0 0).symm (B.add1 w0 w0)))
      (A.e s 0 z w0) := by
    refine A.e_hcongr s (add_zero 0) rfl ?_
    refine (B.castFst_heq _ _).trans ?_
    refine (B.addFst_hcongr (map_zero _) (map_zero _) rfl hw hw).trans ?_
    exact (B.zeroFst_add (B.zero1 z)).trans hw.symm
  have hid : B.S1mk (A.e s 0 z w0) + B.S1mk (A.e s 0 z w0) = B.S1mk (A.e s 0 z w0) :=
    Sigma.ext (add_zero (0 : B.G R)) ((heq_of_eq h1.symm).trans h2)
  exact (Sigma.ext_iff.1 (B.fibreFst_idem _ hid)).2

lemma e_zero2 (x : B.G R) : HEq (A.e s x 0 (B.zero2 (A.a.f s x))) (B.zero2 x) := by
  set w0 := B.zero2 (A.a.f s x) with hw0
  have h1 := A.equiv_addSnd s x 0 0 w0 w0
  have h2 : HEq (A.e s x (0 + 0) (B.add2 w0 w0)) (A.e s x 0 w0) :=
    A.e_hcongr s rfl (add_zero 0) (B.zeroSnd_add w0)
  have hz : A.ab.f s 0 + A.ab.f s 0 = A.ab.f s 0 := by rw [map_zero, add_zero]
  have hid : B.S2mk (A.e s x 0 w0) + B.S2mk (A.e s x 0 w0) = B.S2mk (A.e s x 0 w0) :=
    Sigma.ext hz ((B.castSnd_heq _ _).symm.trans ((heq_of_eq h1).symm.trans h2))
  exact (Sigma.ext_iff.1 (B.fibreSnd_idem _ hid)).2

lemma e_nsmul1 (x z : B.G R) (u : B.P R (A.a.f s x) z) (n : ℕ)
    (w : B.P R (A.a.f s (n • x)) z) (hw : HEq w (B.nsmul1 u n)) :
    HEq (A.e s (n • x) z w) (B.nsmul1 (A.e s x z u) n) := by
  induction n with
  | zero =>
    refine (A.e_hcongr s (zero_nsmul x) rfl
      (u₂ := B.tr1 (map_zero (A.a.f s)).symm (B.zero1 z)) ?_).trans ?_
    · exact hw.trans ((B.castFst_heq _ _).trans (B.castFst_heq _ _).symm)
    · exact (A.e_zero1 s z).trans (B.castFst_heq _ _).symm
  | succ n ih =>
    have hn : A.a.f s (n • x) = n • A.a.f s x := map_nsmul _ n x
    have h1 := ih (B.tr1 hn.symm (B.nsmul1 u n)) (B.castFst_heq _ _)
    refine (A.e_hcongr s (succ_nsmul x n) rfl
      (u₂ := B.tr1 (map_add (A.a.f s) (n • x) x).symm (B.add1 (B.tr1 hn.symm (B.nsmul1 u n)) u))
      ?_).trans ?_
    · refine hw.trans ((B.castFst_heq _ _).trans ?_)
      exact (B.addFst_hcongr hn.symm rfl rfl (B.castFst_heq _ _).symm HEq.rfl).trans (B.castFst_heq _ _).symm
    · rw [A.equiv_addFst]
      exact (B.addFst_hcongr rfl rfl rfl h1 HEq.rfl).trans (B.castFst_heq _ _).symm

lemma e_nsmul2 (x z : B.G R) (u : B.P R (A.a.f s x) z) (n : ℕ) :
    HEq (A.e s x (n • z) (B.nsmul2 u n)) (B.nsmul2 (A.e s x z u) n) := by
  induction n with
  | zero =>
    exact (A.e_hcongr s rfl (zero_nsmul z) (B.castSnd_heq _ _)).trans
      ((A.e_zero2 s x).trans (B.castSnd_heq _ _).symm)
  | succ n ih =>
    refine (A.e_hcongr s rfl (succ_nsmul z n) (B.castSnd_heq _ _)).trans ?_
    rw [A.equiv_addSnd]
    refine (B.castSnd_heq _ _).trans ?_
    exact (B.addSnd_hcongr rfl (map_nsmul _ n z) rfl ih HEq.rfl).trans (B.castSnd_heq _ _).symm

theorem pairing_of (N : ℕ) (x z : B.G R) (w : (R : Type u)ˣ) (hx : N • x = 0)
    (h : B.IsPairing N (A.a.f s x) z w) : B.IsPairing N x (A.ab.f s z) w := by
  obtain ⟨hax, hz, u, l₁, l₂, h1, h2, rfl⟩ := h
  have hbz : N • A.ab.f s z = 0 := by rw [← map_nsmul, hz, map_zero]
  refine ⟨hx, hbz, A.e s x z u, l₁, l₂, ?_, ?_, rfl⟩
  · have hn : A.a.f s (N • x) = N • A.a.f s x := map_nsmul _ N x
    have k1 := A.e_nsmul1 s x z u N (B.tr1 hn.symm (B.nsmul1 u N)) (B.castFst_heq _ _)
    have k2 : HEq (A.e s (N • x) z (B.tr1 hn.symm (B.nsmul1 u N)))
        (A.e s 0 z (B.tr1 (map_zero (A.a.f s)).symm (B.smul l₁ (B.zero1 z)))) := by
      refine A.e_hcongr s hx rfl ?_
      refine (B.castFst_heq _ _).trans ?_
      exact ((B.castFst_heq hax _).symm.trans (heq_of_eq h1)).trans (B.castFst_heq _ _).symm
    rw [B.castFst_smul, A.e_smul] at k2
    apply eq_of_heq
    refine (B.castFst_heq _ _).trans (k1.symm.trans (k2.trans ?_))
    exact B.smul_hcongr rfl rfl l₁ (A.e_zero1 s z)
  · have k1 := A.e_nsmul2 s x z u N
    have k2 : HEq (A.e s x (N • z) (B.nsmul2 u N))
        (A.e s x 0 (B.smul l₂ (B.zero2 (A.a.f s x)))) :=
      A.e_hcongr s rfl hz ((B.castSnd_heq hz _).symm.trans (heq_of_eq h2))
    rw [A.e_smul] at k2
    apply eq_of_heq
    refine (B.castSnd_heq _ _).trans (k1.symm.trans (k2.trans ?_))
    exact B.smul_hcongr rfl (map_zero _) l₂ (A.e_zero2 s x)

theorem pairing_iff (N : ℕ) (x z : B.G R) (w : (R : Type u)ˣ) (hx : N • x = 0) (hz : N • z = 0) :
    B.IsPairing N (A.a.f s x) z w ↔ B.IsPairing N x (A.ab.f s z) w := by
  refine ⟨A.pairing_of s N x z w hx, fun h => ?_⟩
  have hax : N • A.a.f s x = 0 := by rw [← map_nsmul, hx, map_zero]
  obtain ⟨w', hw'⟩ := B.pairing_exists N _ z hax hz
  rwa [B.pairing_unique N x _ _ _ (A.pairing_of s N x z w' hx hw') h] at hw'

end OAdj

namespace DualPair

variable {R : LAlg R₀} (Dp : DualPair R)

lemma π_η : Dp.π.1 Dp.η = 0 := by
  have h := Dp.η_mem
  rwa [Submodule.restrictScalars_mem, RingHom.mem_ker] at h

lemma sub_mem_span (d : (Dp.D : Type u)) : d - Dp.σ.1 (Dp.π.1 d) ∈ Ideal.span {Dp.η} := by
  rw [← Dp.ker_eq, RingHom.mem_ker, map_sub, Dp.sect, sub_self]

lemma mul_span (a b : (Dp.D : Type u)) (ha : a ∈ Ideal.span {Dp.η}) (hb : b ∈ Ideal.span {Dp.η}) :
    a * b = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hb
  calc c * Dp.η * (d * Dp.η) = c * d * (Dp.η * Dp.η) := by ring
    _ = 0 := by rw [Dp.η_sq, mul_zero]

def mr (r : (R : Type u)) : LHom Dp.D Dp.D :=
  ⟨{ toFun := fun d => Dp.σ.1 (Dp.π.1 d) + Dp.σ.1 r * (d - Dp.σ.1 (Dp.π.1 d))
     map_one' := by simp
     map_mul' := fun d e => by
       have hk := Dp.mul_span _ _ (Dp.sub_mem_span d) (Dp.sub_mem_span e)
       simp only [map_mul]
       linear_combination (Dp.σ.1 r - Dp.σ.1 r * Dp.σ.1 r) * hk
     map_zero' := by simp
     map_add' := fun d e => by simp only [map_add (f := _)]; ring
     commutes' := fun c => by simp },
   ⟨fun d hd => by
     have h1 := hd.map Dp.π.1
     have e : Dp.π.1 (Dp.σ.1 (Dp.π.1 d) + Dp.σ.1 r * (d - Dp.σ.1 (Dp.π.1 d))) = Dp.π.1 d := by
       simp [Dp.sect]
     refine Dp.π.2.map_nonunit d ?_
     convert h1 using 1
     exact e.symm⟩⟩

lemma mr_apply (r : (R : Type u)) (d : (Dp.D : Type u)) :
    (Dp.mr r).1 d = Dp.σ.1 (Dp.π.1 d) + Dp.σ.1 r * (d - Dp.σ.1 (Dp.π.1 d)) := rfl

lemma mr_π (r : (R : Type u)) (d : (Dp.D : Type u)) : Dp.π.1 ((Dp.mr r).1 d) = Dp.π.1 d := by
  simp [mr_apply, Dp.sect]

lemma mr_comp_σ (r : (R : Type u)) : (Dp.mr r).comp Dp.σ = Dp.σ :=
  Subtype.ext (AlgHom.ext fun t => by
    show (Dp.mr r).1 (Dp.σ.1 t) = Dp.σ.1 t
    simp [mr_apply, Dp.sect])

lemma mr_ση (r t : (R : Type u)) :
    (Dp.mr r).1 (Dp.σ.1 t * Dp.η) = Dp.σ.1 r * (Dp.σ.1 t * Dp.η) := by
  simp [mr_apply, Dp.π_η]

lemma mr_ker (r : (R : Type u)) :
    ∀ a ∈ Dp.π.ker, (Dp.mr r).1.toLinearMap a ∈ Dp.π.ker := by
  intro a ha
  rw [Submodule.restrictScalars_mem, RingHom.mem_ker] at ha ⊢
  rw [AlgHom.toLinearMap_apply, Dp.mr_π, ha]

end DualPair

lemma hext_tmul (B : BX R₀) {R : LAlg R₀} (h : B.gg →ₗ[R₀] (R : Type u)) (w : B.gg) (r : (R : Type u)) :
    hext B h (w ⊗ₜ r) = h w * r := by
  simp [hext]

theorem ht_ext (B : BX R₀) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ) (y : B.G R)
    (h : B.gg →ₗ[R₀] (R : Type u)) (hy : N • y = 0) (hH : B.IsHeight Dp N y h)
    (V : B.gg ⊗[R₀] (R : Type u)) :
    ∃ z : (Dp.D : Type u)ˣ,
      B.IsPairing N (B.tg Dp.π Dp.sqZero (LinearMap.lTensor B.gg Dp.ηmap V)) (B.map Dp.σ y) z ∧
        (z : (Dp.D : Type u)) = 1 + Dp.σ.1 (hext B h V) * Dp.η := by
  induction V using TensorProduct.induction_on with
  | zero =>
    have hY : N • B.map Dp.σ y = 0 := by rw [← map_nsmul, hy, map_zero]
    obtain ⟨z, hz⟩ := B.pairing_exists N (0 : B.G Dp.D) _ (smul_zero N) hY
    have h2 := B.isPairingValue_add_left N 0 0 _ z z hz hz
    rw [add_zero] at h2
    have hzz : z * z = z * 1 := by rw [mul_one]; exact (B.pairing_unique N _ _ _ _ hz h2).symm
    have h1 : z = 1 := mul_left_cancel hzz
    subst h1
    refine ⟨1, by simpa using hz, by simp⟩
  | tmul w r =>
    obtain ⟨z, hz, ez⟩ := hH w
    have k := B.pairing_map (Dp.mr r) N _ _ z hz
    have e1 : B.map (Dp.mr r) (B.tg Dp.π Dp.sqZero (w ⊗ₜ Dp.ηk)) =
        B.tg Dp.π Dp.sqZero (LinearMap.lTensor B.gg Dp.ηmap (w ⊗ₜ r)) := by
      rw [← B.tg_nat Dp.π Dp.π Dp.sqZero Dp.sqZero (Dp.mr r) (Dp.mr_ker r),
        LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]
      congr 2
      exact Subtype.ext (by simp [DualPair.ηk, DualPair.ηmap, DualPair.mr_apply, Dp.π_η, LinearMap.restrict_apply])
    have e2 : B.map (Dp.mr r) (B.map Dp.σ y) = B.map Dp.σ y := by
      rw [← B.map_comp, Dp.mr_comp_σ]
    rw [e1, e2] at k
    refine ⟨_, k, ?_⟩
    simp only [Units.coe_map, MonoidHom.coe_coe]
    rw [ez, map_add (f := _), map_one, Dp.mr_ση, hext_tmul, map_mul]
    ring
  | add V V' ihV ihV' =>
    obtain ⟨z, hz, ez⟩ := ihV
    obtain ⟨z', hz', ez'⟩ := ihV'
    refine ⟨z * z', ?_, ?_⟩
    · rw [map_add (f := _), map_add (f := _)]
      exact B.isPairingValue_add_left N _ _ _ z z' hz hz'
    · rw [Units.val_mul, ez, ez', map_add (f := _), map_add (f := _)]
      linear_combination (Dp.σ.1 (hext B h V) * Dp.σ.1 (hext B h V')) * Dp.η_sq

namespace OAdj

variable {B : BX R₀} {O : LAlg R₀} (A : OAdj B O) {R : LAlg R₀} (s : LHom O R)

theorem ht_a (Dp : DualPair R) (N : ℕ) (y : B.G R) (h : B.gg →ₗ[R₀] (R : Type u))
    (δ : B.gg →ₗ[R₀] B.gg ⊗[R₀] (R : Type u)) (hy : N • y = 0) (hH : B.IsHeight Dp N y h)
    (hδ : ∀ v, A.ab.f (Dp.σ.comp s) (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) =
      B.tg Dp.π Dp.sqZero (LinearMap.lTensor B.gg Dp.ηmap (δ v))) :
    B.IsHeight Dp N (A.a.f s y) (hext B h ∘ₗ δ) := by
  intro v
  obtain ⟨z, hz, ez⟩ := ht_ext B Dp N y h hy hH (δ v)
  rw [← hδ v] at hz
  obtain ⟨z0, hz0, -⟩ := hH v
  obtain ⟨hX, hY, -⟩ := hz0
  have k1 := B.pairing_sw N _ _ z hz
  have k2 := (A.pairing_iff (Dp.σ.comp s) N _ _ z⁻¹ hY hX).2 k1
  have k3 := B.pairing_sw N _ _ _ k2
  rw [inv_inv, A.a.nat] at k3
  exact ⟨z, k3, by rw [ez]; rfl⟩

end OAdj

theorem linHt (B : BX R₀) (O : LAlg R₀) : LinHtStatement B O :=
  fun A _ s Dp N y h δ hy hH hδ => A.ht_a s Dp N y h δ hy hH hδ

end ReciprocityTheory.PGsh
end
end
