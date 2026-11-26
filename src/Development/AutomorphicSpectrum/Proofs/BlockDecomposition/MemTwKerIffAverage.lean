module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.IsInvOne
public import Development.WeilBound.RepresentationTheoryGL.StandardBasisDerivatives.ArchimedeanBasisDerivatives.StBasDeriv
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdLeRevEqProdGe

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
noncomputable section

namespace GlobalTheory.CompanionTheory.TwistedAverage

open GlobalTheory.PRep

section Coset

variable {H V : Type} [Group H] [AddCommGroup V]

theorem sum_out_refine {N K : Subgroup H} (hNK : N ≤ K) [Fintype (H ⧸ N)] [Fintype (H ⧸ K)]
    [Fintype (K ⧸ N.subgroupOf K)] (f : H → V) (hf : ∀ x, ∀ k ∈ K, f (x * k) = f x) :
    ∑ q : H ⧸ N, f q.out = Fintype.card (K ⧸ N.subgroupOf K) • ∑ q : H ⧸ K, f q.out := by
  have h1 : ∀ q : H ⧸ N, f q.out = f ((Subgroup.quotientEquivProdOfLE hNK q).1).out := by
    intro q
    have hq : (Subgroup.quotientEquivProdOfLE hNK q).1 = (QuotientGroup.mk q.out : H ⧸ K) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [hq]
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K q.out
    rw [hh, hf _ _ h.2]
  calc ∑ q : H ⧸ N, f q.out
      = ∑ q : H ⧸ N, f ((Subgroup.quotientEquivProdOfLE hNK q).1).out :=
        Finset.sum_congr rfl fun q _ => h1 q
    _ = ∑ p : (H ⧸ K) × (K ⧸ N.subgroupOf K), f p.1.out :=
        Equiv.sum_comp (Subgroup.quotientEquivProdOfLE hNK) (fun p => f p.1.out)
    _ = Fintype.card (K ⧸ N.subgroupOf K) • ∑ q : H ⧸ K, f q.out := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ]
        rw [Finset.smul_sum]

theorem sum_out_mul_right (N : Subgroup H) [N.Normal] [Fintype (H ⧸ N)] (f : H → V)
    (hf : ∀ x, ∀ k ∈ N, f (x * k) = f x) (l : H) :
    ∑ q : H ⧸ N, f (q.out * l) = ∑ q : H ⧸ N, f q.out := by
  have h1 : ∀ q : H ⧸ N, f (q.out * l) = f (q * (QuotientGroup.mk l : H ⧸ N)).out := by
    intro q
    have hq : q * (QuotientGroup.mk l : H ⧸ N) = QuotientGroup.mk (q.out * l) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rw [hq]
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul N (q.out * l)
    rw [hh, hf _ _ h.2]
  calc ∑ q : H ⧸ N, f (q.out * l)
      = ∑ q : H ⧸ N, f (q * (QuotientGroup.mk l : H ⧸ N)).out :=
        Finset.sum_congr rfl fun q _ => h1 q
    _ = ∑ q : H ⧸ N, f q.out :=
        Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk l : H ⧸ N)) (fun q => f q.out)

end Coset

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def twOrbit (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (x : V) (t : L) : V :=
  (((θ t)⁻¹ : ℂˣ) : ℂ) • ρ (t : G) x

def stabKer (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (x : V) : Subgroup L where
  carrier := {l | ρ (l : G) x = x ∧ θ l = 1}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, by rw [map_mul, ha', hb', one_mul]⟩
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨?_, by rw [map_inv, ha', inv_one]⟩
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul]
    simp

theorem twOrbit_mul_right (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (x : V)
    (t k : L) (hk : k ∈ stabKer ρ L θ x) : twOrbit ρ L θ x (t * k) = twOrbit ρ L θ x t := by
  obtain ⟨h1, h2⟩ := hk
  simp only [twOrbit]
  rw [map_mul, h2, mul_one, Subgroup.coe_mul, map_mul, Module.End.mul_apply, h1]

theorem twOrbit_gen (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (w : V) (l t : L) :
    twOrbit ρ L θ (ρ (l : G) w - (θ l : ℂ) • w) t =
      (θ l : ℂ) • (twOrbit ρ L θ w (t * l) - twOrbit ρ L θ w t) := by
  simp only [twOrbit]
  have h : (θ l : ℂ) * (((θ (t * l))⁻¹ : ℂˣ) : ℂ) = (((θ t)⁻¹ : ℂˣ) : ℂ) := by
    rw [← Units.val_mul, map_mul, mul_inv, mul_comm (θ t)⁻¹, mul_inv_cancel_left]
  rw [smul_sub, smul_smul, h, Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_sub, map_smul,
    smul_sub, smul_smul, smul_smul, mul_comm]

theorem twOrbit_add (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (x y : V) (t : L) :
    twOrbit ρ L θ (x + y) t = twOrbit ρ L θ x t + twOrbit ρ L θ y t := by
  simp only [twOrbit, map_add (f := _), smul_add]

theorem twOrbit_smul (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (c : ℂ) (x : V)
    (t : L) : twOrbit ρ L θ (c • x) t = c • twOrbit ρ L θ x t := by
  simp only [twOrbit, map_smul]
  rw [smul_comm]

section Top

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem isOpen_stabKer {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (L : Subgroup G)
    (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L)) (x : V) :
    IsOpen (stabKer ρ L θ x : Set L) := by
  have h1 : IsOpen {l : L | ρ (l : G) x = x} := (hρ x).preimage continuous_subtype_val
  have h2 : (stabKer ρ L θ x : Set L) = {l : L | ρ (l : G) x = x} ∩ (θ.ker : Set L) := by
    ext l
    simp [stabKer, MonoidHom.mem_ker]
  rw [h2]
  exact h1.inter hθ

theorem finiteIndex_stabKer {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {L : Subgroup G}
    (hL : IsCompact (L : Set G)) (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L)) (x : V) :
    (stabKer ρ L θ x).FiniteIndex := by
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  haveI : Finite (L ⧸ stabKer ρ L θ x) :=
    Subgroup.quotient_finite_of_isOpen _ (isOpen_stabKer hρ L θ hθ x)
  exact Subgroup.finiteIndex_of_finite_quotient

theorem exists_sum_eq_zero {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {L : Subgroup G}
    (hL : IsCompact (L : Set G)) (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L)) {v : V}
    (hv : v ∈ twKer ρ L θ) :
    ∃ M : Subgroup L, M.FiniteIndex ∧ ∀ (N : Subgroup L) [N.Normal] [Fintype (L ⧸ N)], N ≤ M →
      ∑ q : L ⧸ N, twOrbit ρ L θ v q.out = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, w, rfl⟩ := hx
    refine ⟨stabKer ρ L θ w, finiteIndex_stabKer hρ hL θ hθ w, ?_⟩
    intro N _ _ hN
    have hf : ∀ x, ∀ k ∈ N, twOrbit ρ L θ w (x * k) = twOrbit ρ L θ w x :=
      fun x k hk => twOrbit_mul_right ρ L θ w x k (hN hk)
    simp only [twOrbit_gen]
    rw [← Finset.smul_sum, Finset.sum_sub_distrib,
      sum_out_mul_right N (twOrbit ρ L θ w) hf l, sub_self, smul_zero]
  | zero =>
    refine ⟨⊤, inferInstance, ?_⟩
    intro N _ _ _
    simp [twOrbit]
  | add x y _ _ hx hy =>
    obtain ⟨M₁, h₁, s₁⟩ := hx
    obtain ⟨M₂, h₂, s₂⟩ := hy
    refine ⟨M₁ ⊓ M₂, inferInstance, ?_⟩
    intro N _ _ hN
    simp only [twOrbit_add]
    rw [Finset.sum_add_distrib, s₁ N (hN.trans inf_le_left), s₂ N (hN.trans inf_le_right), add_zero]
  | smul c x _ hx =>
    obtain ⟨M, h, s⟩ := hx
    refine ⟨M, h, ?_⟩
    intro N _ _ hN
    simp only [twOrbit_smul]
    rw [← Finset.smul_sum, s N hN, smul_zero]

theorem mem_twKer_iff_average (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (L : Subgroup G)
    (hL : IsCompact (L : Set G)) (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L)) (v : V) :
    v ∈ twKer ρ L θ ↔ ∃ (K : Subgroup L) (T : Finset L), IsOpen (K : Set L) ∧
      (∀ x ∈ K, ρ (x : G) v = v) ∧ (∀ x ∈ K, θ x = 1) ∧
      (∀ x : L, ∃! t, t ∈ T ∧ t⁻¹ * x ∈ K) ∧
      ∑ t ∈ T, (((θ t)⁻¹ : ℂˣ) : ℂ) • ρ t v = 0 := by
  classical
  constructor
  · intro hv
    obtain ⟨M, hM, hsum⟩ := exists_sum_eq_zero hρ hL θ hθ hv
    haveI hK : (stabKer ρ L θ v).FiniteIndex := finiteIndex_stabKer hρ hL θ hθ v
    haveI : Fintype (L ⧸ stabKer ρ L θ v) := Fintype.ofFinite _
    refine ⟨stabKer ρ L θ v, (Finset.univ : Finset (L ⧸ stabKer ρ L θ v)).image Quotient.out,
      isOpen_stabKer hρ L θ hθ v,
      fun x hx => hx.1, fun x hx => hx.2, ?_, ?_⟩
    · intro x
      refine ⟨(QuotientGroup.mk x : L ⧸ stabKer ρ L θ v).out, ⟨Finset.mem_image_of_mem _
        (Finset.mem_univ _), ?_⟩, ?_⟩
      · exact QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
      · rintro t ⟨ht, hx⟩
        obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ht
        have : q = (QuotientGroup.mk x : L ⧸ stabKer ρ L θ v) := by
          rw [← QuotientGroup.out_eq' q]
          exact QuotientGroup.eq.2 hx
        rw [this]
    · rw [Finset.sum_image (fun a _ b _ h => Quotient.out_injective h)]
      set C : Subgroup L := (M ⊓ stabKer ρ L θ v).normalCore with hC
      haveI : C.Normal := Subgroup.normalCore_normal _
      haveI : C.FiniteIndex := inferInstance
      haveI : Fintype (L ⧸ C) := Fintype.ofFinite _
      have hCM : C ≤ M ⊓ stabKer ρ L θ v := Subgroup.normalCore_le _
      haveI : Finite (stabKer ρ L θ v ⧸ C.subgroupOf (stabKer ρ L θ v)) := inferInstance
      haveI : Fintype (stabKer ρ L θ v ⧸ C.subgroupOf (stabKer ρ L θ v)) := Fintype.ofFinite _
      have h0 := hsum C (hCM.trans inf_le_left)
      rw [sum_out_refine (hCM.trans inf_le_right) (twOrbit ρ L θ v)
        (fun x k hk => twOrbit_mul_right ρ L θ v x k hk)] at h0
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h0
      rcases h0 with h0 | h0
      · exact absurd h0 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
      · exact h0
  · rintro ⟨K, T, -, -, -, hT, hsum⟩
    have hne : T.Nonempty := by
      obtain ⟨t, ⟨ht, -⟩, -⟩ := hT 1
      exact ⟨t, ht⟩
    have hc : (T.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hne.card_pos.ne'
    have hmem : ∀ t : L, v - (((θ t)⁻¹ : ℂˣ) : ℂ) • ρ (t : G) v ∈ twKer ρ L θ := by
      intro t
      have hg : ρ (t : G) v - (θ t : ℂ) • v ∈ twKer ρ L θ := Submodule.subset_span ⟨t, v, rfl⟩
      have := (twKer ρ L θ).smul_mem (-(((θ t)⁻¹ : ℂˣ) : ℂ)) hg
      convert this using 1
      rw [smul_sub, smul_smul, neg_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, neg_smul,
        neg_smul, one_smul]
      abel
    have hs : (T.card : ℂ) • v = ∑ t ∈ T, (v - (((θ t)⁻¹ : ℂˣ) : ℂ) • ρ (t : G) v) := by
      rw [Finset.sum_sub_distrib, hsum, sub_zero, Finset.sum_const, Nat.cast_smul_eq_nsmul]
    have h1 : (T.card : ℂ) • v ∈ twKer ρ L θ := hs ▸ Submodule.sum_mem _ fun t _ => hmem t
    exact ((twKer ρ L θ).smul_mem_iff hc).1 h1

end Top

end GlobalTheory.CompanionTheory.TwistedAverage
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
open PositivityTheory.PfSWUS.Loc

namespace GlobalTheory.CompanionTheory.UnrDens

def barσ {R : Type} [CommRing R] (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) (k : ℕ) :
    R ⧸ lev ϖ k →+* R ⧸ lev ϖ k :=
  Ideal.Quotient.lift (lev ϖ k) ((Ideal.Quotient.mk (lev ϖ k)).comp σ) (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp only [RingHom.comp_apply, map_mul, map_pow, h]
    apply Ideal.Quotient.eq_zero_iff_mem.2
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

@[simp] theorem barσ_mk {R : Type} [CommRing R] (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) (k : ℕ) (a : R) :
    barσ σ ϖ h k (Ideal.Quotient.mk (lev ϖ k) a) = Ideal.Quotient.mk (lev ϖ k) (σ a) := rfl

structure ResAlg (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ) : Prop where
  inv : ∀ a, τ (τ a) = a
  fixedUnit : ∀ a, τ a = a → a ≠ 0 → IsUnit a
  basis : ∃ u : E, IsUnit (u - τ u) ∧ ∀ a, ∃ x y, τ x = x ∧ τ y = y ∧ a = x + y * u
  one_lt : 1 < q
  card : Nat.card E = q ^ 2
  eps : (ε = -1 ∧ IsField E) ∨ (ε = 1 ∧ ¬ IsField E)

variable {E : Type} [CommRing E] {τ : E →+* E}

structure HermSp (E : Type) [CommRing E] (τ : E →+* E) (V : Type) [AddCommGroup V] [Module E V] where
  h : V → V → E
  add_left : ∀ u v w, h (u + v) w = h u w + h v w
  smul_left : ∀ (a : E) v w, h (a • v) w = a * h v w
  symm : ∀ v w, h w v = τ (h v w)
  nondeg : ∀ v, (∀ w, h v w = 0) → v = 0

variable {V : Type} [AddCommGroup V] [Module E V]

namespace HermSp

variable (B : HermSp E τ V)

theorem zero_left (w : V) : B.h 0 w = 0 := by
  have h0 := B.smul_left 0 0 w
  rwa [zero_smul, zero_mul] at h0

theorem add_right (v u w : V) : B.h v (u + w) = B.h v u + B.h v w := by
  rw [B.symm (u + w) v, B.add_left, map_add (f := _), ← B.symm, ← B.symm]

theorem smul_right (a : E) (v w : V) : B.h v (a • w) = τ a * B.h v w := by
  rw [B.symm (a • w) v, B.smul_left, map_mul, ← B.symm]

theorem self_fixed (hτ : ∀ a, τ (τ a) = a) (v : V) : τ (B.h v v) = B.h v v := by
  exact (B.symm v v).symm

def perp (w : V) : Submodule E V where
  carrier := {v | B.h v w = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [B.add_left, ha, hb, add_zero]
  zero_mem' := B.zero_left w
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at *
    rw [B.smul_left, hx, mul_zero]

noncomputable def coef {w : V} (hw : IsUnit (B.h w w)) (z : V) : E := B.h z w * (hw.unit⁻¹ : Eˣ)

theorem coef_spec {w : V} (hw : IsUnit (B.h w w)) (z : V) : B.h (z - B.coef hw z • w) w = 0 := by
  have hu : ((hw.unit⁻¹ : Eˣ) : E) * B.h w w = 1 := by
    have h1 := hw.unit.inv_mul
    simpa using h1
  have hc : B.coef hw z * B.h w w = B.h z w := by
    unfold coef
    rw [mul_assoc, hu, mul_one]
  have e : B.h z w = B.h (z - B.coef hw z • w) w + B.h (B.coef hw z • w) w := by
    rw [← B.add_left, sub_add_cancel]
  rw [B.smul_left, hc] at e
  linear_combination -e

noncomputable def perpForm {w : V} (hw : IsUnit (B.h w w)) : HermSp E τ (B.perp w) where
  h a b := B.h a b
  add_left u v x := by simp [B.add_left]
  smul_left a v x := by simp [B.smul_left]
  symm v x := B.symm _ _
  nondeg := by
    intro v hv
    apply Subtype.ext
    apply B.nondeg
    intro z
    have h1 := hv ⟨z - B.coef hw z • w, B.coef_spec hw z⟩
    have hz : z = (z - B.coef hw z • w) + B.coef hw z • w := by abel
    have h0 : B.h (v : V) w = 0 := v.2
    rw [hz, B.add_right, B.smul_right, h0, mul_zero, add_zero]
    exact h1

@[simp] theorem perpForm_h {w : V} (hw : IsUnit (B.h w w)) (a b : B.perp w) :
    (B.perpForm hw).h a b = B.h a b := rfl

noncomputable def perpEquiv {w : V} (hw : IsUnit (B.h w w)) : E × B.perp w ≃ V where
  toFun p := p.1 • w + p.2
  invFun z := (B.coef hw z, ⟨z - B.coef hw z • w, B.coef_spec hw z⟩)
  left_inv := by
    rintro ⟨a, v⟩
    have h0 : B.h (v : V) w = 0 := v.2
    have hc : B.coef hw (a • w + (v : V)) = a := by
      unfold coef
      rw [B.add_left, B.smul_left, h0, add_zero, mul_assoc]
      have : B.h w w * ((hw.unit⁻¹ : Eˣ) : E) = 1 := by
        have := hw.unit.mul_inv
        simpa using this
      rw [this, mul_one]
    ext
    · exact hc
    · simp [hc]
  right_inv := by
    intro z
    simp

theorem perpEquiv_apply {w : V} (hw : IsUnit (B.h w w)) (p : E × B.perp w) :
    B.perpEquiv hw p = p.1 • w + (p.2 : V) := rfl

theorem norm_perp {w v : V} (hv : B.h v w = 0) (a : E) :
    B.h (a • w + v) (a • w + v) = a * τ a * B.h w w + B.h v v := by
  have hwv : B.h w v = 0 := by rw [B.symm v w, hv, map_zero]
  simp only [B.add_left, B.smul_left, B.add_right, B.smul_right, hv, hwv, mul_zero, add_zero]
  ring

end HermSp

def HermSp.ofMatrix (hτ : ∀ a, τ (τ a) = a) {m : ℕ} (S : Matrix (Fin m) (Fin m) E)
    (hS : cT τ S = S) (hd : IsUnit S.det) : HermSp E τ (Fin m → E) where
  h v w := dotProduct (fun i => τ (w i)) (S.mulVec v)
  add_left u v w := by rw [Matrix.mulVec_add, dotProduct_add]
  smul_left a v w := by rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  symm v w := by
    have hij : ∀ i j, τ (S j i) = S i j := fun i j => by
      have := congrFun (congrFun hS i) j
      simpa [cT] using this
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, hτ, hij]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  nondeg v hv := by
    have h0 : S.mulVec v = 0 := by
      funext i
      have := hv (Pi.single i 1)
      simpa [dotProduct, Pi.single_apply] using this
    have := congrArg (S⁻¹).mulVec h0
    have hu : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul _ hd
    simpa [Matrix.mulVec_mulVec, hu] using this

theorem gram_apply (hτ : ∀ a, τ (τ a) = a) {m n : ℕ} (S : Matrix (Fin m) (Fin m) E)
    (hS : cT τ S = S) (hd : IsUnit S.det) (x : Matrix (Fin m) (Fin n) E) (i j : Fin n) :
    (cT τ x * S * x) i j = (HermSp.ofMatrix hτ S hS hd).h (fun a => x a j) (fun a => x a i) := by
  show (cT τ x * S * x) i j = dotProduct (fun a => τ (x a i)) (S.mulVec (fun a => x a j))
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end GlobalTheory.CompanionTheory.UnrDens
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PfFacts
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem pf_facts : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A], Pf p A →
    (∃ F : A ≃+* A, ∀ x, F x = x ^ p) ∧ (∀ (x : A) (n : ℕ), x ^ n = 0 → x = 0) ∧
    (∀ (k : ℕ) (x : A), ∃ y, y ^ p ^ k = x) ∧ (∀ (k : ℕ) (x y : A), x ^ p ^ k = y ^ p ^ k → x = y) ∧
    ∀ r : ℕ → A, IsRt p r → (∀ k, ∃ c, r k = c * r (k + 1) * r (k + 1)) ∧ (∀ k, r k ^ p ^ k = r 0) ∧
      ∀ (N : ℕ) (x : A), r 0 ^ N * x = 0 → ∀ k, r k * x = 0 := by
  intro p _ A _ h
  have hp : p.Prime := Fact.out
  have hadd : ∀ x y : A, (x + y) ^ p = x ^ p + y ^ p := by
    intro x y
    obtain ⟨c, hc⟩ := exists_add_pow_prime_eq hp x y
    rw [hc, h.char]
    simp
  let F : A →+* A :=
    { toFun := fun x => x ^ p
      map_one' := one_pow p
      map_mul' := fun x y => mul_pow x y p
      map_zero' := zero_pow hp.ne_zero
      map_add' := hadd }
  have hk : ∀ k : ℕ, Function.Bijective fun x : A => x ^ p ^ k := by
    intro k
    induction k with
    | zero =>
      simp only [pow_zero, pow_one]
      exact Function.bijective_id
    | succ k ih =>
      have : (fun x : A => x ^ p ^ (k + 1)) = (fun x : A => x ^ p) ∘ (fun x : A => x ^ p ^ k) := by
        funext x
        simp only [Function.comp_apply]
        rw [pow_succ, pow_mul]
      rw [this]
      exact h.bij.comp ih
  have hinj : ∀ (k : ℕ) (x y : A), x ^ p ^ k = y ^ p ^ k → x = y := fun k x y e => (hk k).1 e
  have hred : ∀ (x : A) (n : ℕ), x ^ n = 0 → x = 0 := by
    intro x n e
    apply hinj n
    have hlt : n < p ^ n := Nat.lt_pow_self hp.one_lt
    rw [pow_eq_zero_of_le hlt.le e, zero_pow (pow_ne_zero n hp.ne_zero)]
  refine ⟨⟨RingEquiv.ofBijective F h.bij, fun x => rfl⟩, hred, fun k x => (hk k).2 x, hinj, ?_⟩
  intro r hr
  have hroot : ∀ k, r k ^ p ^ k = r 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', pow_mul, hr k, ih]
  refine ⟨?_, hroot, ?_⟩
  · intro k
    refine ⟨r (k + 1) ^ (p - 2), ?_⟩
    have h2 : p = (p - 2) + 1 + 1 := by have := hp.two_le; omega
    conv_lhs => rw [← hr k, h2]
    rw [pow_succ, pow_succ]
  · intro N x e k
    apply hred _ (p ^ k * N + 1)
    calc (r k * x) ^ (p ^ k * N + 1)
        = r k ^ (p ^ k * N + 1) * x ^ (p ^ k * N + 1) := mul_pow _ _ _
      _ = r k * x ^ (p ^ k * N) * (r 0 ^ N * x) := by
          rw [pow_succ (r k), pow_mul, hroot k, pow_succ x]
          ring
      _ = 0 := by rw [e, mul_zero]

end GlobalTheory.CompanionTheory.PerfectRing
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRingHomPowPrimePow
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Frobenius

theorem exists_ringHom_pow_prime_pow :
    ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A], (p : A) = 0 → ∀ k : ℕ,
      ∃ F : A →+* A, ∀ x, F x = x ^ p ^ k := by
  intro p hp A _ hpA k
  refine ⟨{ toFun := fun x => x ^ p ^ k
            map_one' := one_pow _
            map_mul' := fun x y => mul_pow x y _
            map_zero' := zero_pow (pow_ne_zero k hp.out.ne_zero)
            map_add' := fun x y => ?_ }, fun x => rfl⟩
  show (x + y) ^ p ^ k = x ^ p ^ k + y ^ p ^ k
  rw [add_pow_prime_pow_eq hp.out x y k, hpA]
  simp only [zero_mul, add_zero]

end GlobalTheory.CompanionTheory.Frobenius
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteSupport
open GlobalTheory.PRep

noncomputable section

namespace GlobalTheory.CompanionTheory.PRep.JacExact

section Finite

variable {L V W : Type} [Group L] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def avg (τ : Representation ℂ L V) (χ : L →* ℂˣ) (M : Subgroup L) [Fintype (L ⧸ M)] : V →ₗ[ℂ] V :=
  ∑ q : L ⧸ M, (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ) • τ (Quotient.out q)

theorem avg_apply (τ : Representation ℂ L V) (χ : L →* ℂˣ) (M : Subgroup L) [Fintype (L ⧸ M)] (x : V) :
    avg τ χ M x = ∑ q : L ⧸ M, (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ) • τ (Quotient.out q) x := by
  simp [avg, LinearMap.sum_apply]

theorem avg_translate (τ : Representation ℂ L V) (χ : L →* ℂˣ) (M : Subgroup L) [M.Normal]
    [Fintype (L ⧸ M)] (hχ : M ≤ χ.ker) (x : V) (hx : ∀ m ∈ M, τ m x = x) (n : L) :
    avg τ χ M (τ n x) = ((χ n : ℂˣ) : ℂ) • avg τ χ M x := by
  set F : L → V := fun t => (((χ t)⁻¹ : ℂˣ) : ℂ) • τ t x with hFdef
  have hF : ∀ a b : L, (QuotientGroup.mk a : L ⧸ M) = QuotientGroup.mk b → F a = F b := by
    intro a b hab
    have hm : a⁻¹ * b ∈ M := QuotientGroup.eq.1 hab
    have hb : b = a * (a⁻¹ * b) := by group
    have hc : χ (a⁻¹ * b) = 1 := hχ hm
    have ht : τ b x = τ a x := by
      rw [hb, map_mul, Module.End.mul_apply, hx _ hm]
    have hcb : χ b = χ a := by
      rw [hb, map_mul, hc, mul_one]
    simp only [hFdef, ht, hcb]
  have h1 : ∀ q : L ⧸ M, (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ) • τ (Quotient.out q) (τ n x)
      = ((χ n : ℂˣ) : ℂ) • F (Quotient.out (q * (QuotientGroup.mk n : L ⧸ M))) := by
    intro q
    have hq : (QuotientGroup.mk (Quotient.out q * n) : L ⧸ M)
        = QuotientGroup.mk (Quotient.out (q * (QuotientGroup.mk n : L ⧸ M))) := by
      rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rw [← hF _ _ hq]
    simp only [hFdef, map_mul, mul_inv, Units.val_mul, smul_smul, Module.End.mul_apply]
    congr 1
    have : ((χ n : ℂˣ) : ℂ) * (((χ n)⁻¹ : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ)
        = (((χ n : ℂˣ) : ℂ) * (((χ n)⁻¹ : ℂˣ) : ℂ)) * (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ) := by
          rw [this, one_mul]
      _ = _ := by ring
  rw [avg_apply, avg_apply, Finset.sum_congr rfl (fun q _ => h1 q), ← Finset.smul_sum]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk n : L ⧸ M))
    (fun q => F (Quotient.out q))

theorem mem_span_of_normal (ρ : Representation ℂ L V) (σ : Representation ℂ L W) (χ : L →* ℂˣ)
    (M : Subgroup L) [M.Normal] [Finite (L ⧸ M)] (hχ : M ≤ χ.ker)
    (f : V →ₗ[ℂ] W) (hf : Function.Injective f) (hfi : ∀ g v, f (ρ g v) = σ g (f v))
    (v : V) (hfv : f v ∈ Submodule.span ℂ
      {y | ∃ (n : L) (w : W), (∀ m ∈ M, σ m w = w) ∧ y = σ n w - ((χ n : ℂˣ) : ℂ) • w}) :
    v ∈ Submodule.span ℂ {y | ∃ (n : L) (u : V), y = ρ n u - ((χ n : ℂˣ) : ℂ) • u} := by
  haveI := Fintype.ofFinite (L ⧸ M)
  set S := Submodule.span ℂ {y | ∃ (n : L) (u : V), y = ρ n u - ((χ n : ℂˣ) : ℂ) • u} with hS
  have h1 : f (avg ρ χ M v) = avg σ χ M (f v) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [avg_apply, map_sum, map_smul, hfi]
  have h2 : avg σ χ M (f v) = 0 := by
    have hle : Submodule.span ℂ
        {y | ∃ (n : L) (w : W), (∀ m ∈ M, σ m w = w) ∧ y = σ n w - ((χ n : ℂˣ) : ℂ) • w}
        ≤ LinearMap.ker (avg σ χ M) := by
      refine Submodule.span_le.2 ?_
      rintro y ⟨n, w, hw, rfl⟩
      show avg σ χ M _ = 0
      rw [map_sub, avg_translate σ χ M hχ w hw, map_smul, sub_self]
    exact hle hfv
  have h3 : avg ρ χ M v = 0 := hf (by rw [h1, h2, map_zero])
  have h4 : ((Fintype.card (L ⧸ M) : ℕ) : ℂ) • v - avg ρ χ M v ∈ S := by
    have : ((Fintype.card (L ⧸ M) : ℕ) : ℂ) • v - avg ρ χ M v
        = ∑ q : L ⧸ M, (-(((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ)) •
            (ρ (Quotient.out q) v - ((χ (Quotient.out q) : ℂˣ) : ℂ) • v) := by
      have hq : ∀ q : L ⧸ M, (-(((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ)) •
            (ρ (Quotient.out q) v - ((χ (Quotient.out q) : ℂˣ) : ℂ) • v)
          = v - (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ) • ρ (Quotient.out q) v := by
        intro q
        rw [smul_sub, smul_smul, neg_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, neg_smul,
          neg_smul, one_smul]
        abel
      rw [Finset.sum_congr rfl (fun q _ => hq q), Finset.sum_sub_distrib, avg_apply]
      simp [Finset.card_univ, Nat.cast_smul_eq_nsmul]
    rw [this]
    exact Submodule.sum_mem _ fun q _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, rfl⟩)
  rw [h3, sub_zero] at h4
  have hc : ((Fintype.card (L ⧸ M) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact (Submodule.smul_mem_iff _ hc).1 h4

end Finite

section Top

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem exists_finite_support (σ : Representation ℂ G W) (N : Subgroup G) (θ : N →* ℂˣ) (x : W)
    (hx : x ∈ twKer σ N θ) :
    ∃ (s : Finset N) (t : Finset W), x ∈ Submodule.span ℂ
      {y | ∃ n ∈ s, ∃ w ∈ t, y = σ (n : G) w - ((θ n : ℂˣ) : ℂ) • w} := by
  classical
  unfold twKer at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨n, w, rfl⟩ := hy
    exact ⟨{n}, {w}, Submodule.subset_span ⟨n, by simp, w, by simp, rfl⟩⟩
  | zero => exact ⟨∅, ∅, Submodule.zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨s, t, h⟩ := ha
    obtain ⟨s', t', h'⟩ := hb
    refine ⟨s ∪ s', t ∪ t', Submodule.add_mem _ ?_ ?_⟩
    · refine Submodule.span_mono ?_ h
      rintro y ⟨n, hn, w, hw, rfl⟩
      exact ⟨n, Finset.mem_union_left _ hn, w, Finset.mem_union_left _ hw, rfl⟩
    · refine Submodule.span_mono ?_ h'
      rintro y ⟨n, hn, w, hw, rfl⟩
      exact ⟨n, Finset.mem_union_right _ hn, w, Finset.mem_union_right _ hw, rfl⟩
  | smul c a _ ha =>
    obtain ⟨s, t, h⟩ := ha
    exact ⟨s, t, Submodule.smul_mem _ _ h⟩

def stabIn (τ : Representation ℂ G V) (L : Subgroup G) (x : V) : Subgroup L where
  carrier := {l | τ (l : G) x = x}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Subgroup.coe_mul, map_mul, Module.End.mul_apply] at *
    rw [hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul]
    simp

theorem isOpen_stabIn [TopologicalSpace G] (τ : Representation ℂ G V) (hτ : IsSmooth τ)
    (L : Subgroup G) (x : V) : IsOpen (stabIn τ L x : Set L) :=
  (hτ x).preimage continuous_subtype_val

theorem exists_open_fixing [TopologicalSpace G] (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (L : Subgroup G) (O : Subgroup L)
    (hO : IsOpen (O : Set L)) (v : V) (t : Finset W) :
    ∃ M : Subgroup L, IsOpen (M : Set L) ∧ M ≤ O ∧ (∀ m ∈ M, ρ (m : G) v = v) ∧
      ∀ w ∈ t, ∀ m ∈ M, σ (m : G) w = w := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    refine ⟨O ⊓ stabIn ρ L v, ?_, inf_le_left, fun m hm => hm.2, by simp⟩
    rw [Subgroup.coe_inf]
    exact hO.inter (isOpen_stabIn ρ hρ L v)
  | insert a t _ ih =>
    obtain ⟨M, hM, hMO, hMv, hMt⟩ := ih
    refine ⟨M ⊓ stabIn σ L a, ?_, inf_le_left.trans hMO, fun m hm => hMv m hm.1, ?_⟩
    · rw [Subgroup.coe_inf]
      exact hM.inter (isOpen_stabIn σ hσ L a)
    · intro w hw m hm
      rcases Finset.mem_insert.1 hw with rfl | hw
      · exact hm.2
      · exact hMt w hw m hm.1

theorem twKer_reflect : ∀ {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W), IsSmooth ρ → IsSmooth σ →
    ∀ (N : Subgroup G) (θ : N →* ℂˣ), IsOpen (θ.ker : Set N) →
    (∀ s : Finset G, (↑s : Set G) ⊆ N → ∃ L : Subgroup G, L ≤ N ∧ (↑s : Set G) ⊆ L ∧
      IsCompact (L : Set G)) →
    ∀ (f : V →ₗ[ℂ] W), Function.Injective f → (∀ g v, f (ρ g v) = σ g (f v)) →
    ∀ v : V, f v ∈ twKer σ N θ → v ∈ twKer ρ N θ := by
  intro G V W _ _ _ _ _ _ _ ρ σ hρ hσ N θ hθ hN f hf hfi v hv
  classical
  obtain ⟨s, t, hst⟩ := exists_finite_support σ N θ (f v) hv
  obtain ⟨L, hLN, hsL, hLc⟩ := hN (s.image Subtype.val) (by
    intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
    obtain ⟨n, -, rfl⟩ := hx
    exact n.2)
  haveI : CompactSpace L := isCompact_iff_compactSpace.1 hLc
  let ι : L →* N := Subgroup.inclusion hLN
  have hι : Continuous ι := by
    exact Continuous.subtype_mk continuous_subtype_val _
  let χ : L →* ℂˣ := θ.comp ι
  have hχ : IsOpen (χ.ker : Set L) := by
    have : (χ.ker : Set L) = ι ⁻¹' (θ.ker : Set N) := by
      ext l
      simp [χ, MonoidHom.mem_ker]
    rw [this]
    exact hθ.preimage hι
  obtain ⟨M, hMo, hMχ, hMv, hMt⟩ := exists_open_fixing ρ σ hρ hσ L χ.ker hχ v t
  haveI : Finite (L ⧸ M) := Subgroup.quotient_finite_of_isOpen M hMo
  haveI : M.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let C : Subgroup L := M.normalCore
  haveI : C.Normal := Subgroup.normalCore_normal M
  haveI : C.FiniteIndex := inferInstance
  haveI : Finite (L ⧸ C) := inferInstance
  have hCM : C ≤ M := Subgroup.normalCore_le M
  have hmain := mem_span_of_normal (ρ.comp L.subtype) (σ.comp L.subtype) χ C (hCM.trans hMχ) f hf
    (fun g x => hfi g x) v (by
      refine Submodule.span_mono ?_ hst
      rintro y ⟨n, hn, w, hw, rfl⟩
      have hnL : (n : G) ∈ L := hsL (by
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
        exact ⟨n, hn, rfl⟩)
      refine ⟨⟨n, hnL⟩, w, fun m hm => hMt w hw m (hCM hm), ?_⟩
      rfl)
  refine Submodule.span_le.2 ?_ hmain
  rintro y ⟨n, u, rfl⟩
  exact Submodule.subset_span ⟨ι n, u, rfl⟩

end Top

end GlobalTheory.CompanionTheory.PRep.JacExact
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasDerivAtTwistHomotopyKernel
noncomputable section

open MvPolynomial Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw

namespace GlobalTheory.CompanionTheory.TwistHomotopy

variable {n : ℕ}

theorem hb_conjTranspose (p : Fin n × Fin n) : (hb p)ᴴ = hb p := by
  unfold hb
  split_ifs with h1 h2
  · simp
  · simp [conjTranspose_smul, conjTranspose_add, add_comm]
  · have e : star (((Real.sqrt 2 : ℂ))⁻¹ * Complex.I) = -(((Real.sqrt 2 : ℂ))⁻¹ * Complex.I) := by
      simp
    rw [conjTranspose_smul, conjTranspose_sub, e]
    simp [neg_smul, smul_sub]
    abel

end GlobalTheory.CompanionTheory.TwistHomotopy
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinCol
noncomputable section

open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.FSCrofton

def gW (d : ℕ) (α : Type) [Fintype α] (C : Fin d → α → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-∑ k, ∑ j, ‖C k j‖ ^ 2))

def zeroCnt {X : Type} (d : ℕ) {α : Type} [Fintype α] (A : Set X) (b : α → X → ℂ)
    (C : Fin d → α → ℂ) : ℝ≥0∞ :=
  (({z ∈ A | ∀ k, ∑ j, C k j * b j z = 0}.encard : ℕ∞) : ℝ≥0∞)

def fsLevi {β : Type} [Fintype β] {d : ℕ} (f : β → ℂ) (F : Matrix β (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun a c =>
    (((1 + ∑ j, ‖f j‖ ^ 2 : ℝ) : ℂ) * ∑ j, F j a * conj (F j c) -
        (∑ j, F j a * conj (f j)) * ∑ j, f j * conj (F j c)) /
      ((1 + ∑ j, ‖f j‖ ^ 2 : ℝ) : ℂ) ^ 2

def joinCol {d : ℕ} {α : Type} [DecidableEq α] (j₀ : α) (c : Fin d → ℂ)
    (C : Fin d → {j : α // j ≠ j₀} → ℂ) : Fin d → α → ℂ :=
  fun k j => if h : j = j₀ then c k else C k ⟨j, h⟩

end GlobalTheory.CompanionTheory.FSCrofton
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPQ
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPerfectRadical
namespace GlobalTheory.CompanionTheory.PerfClos

theorem exists_perfect_radical (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] (I : Ideal S)
    (hp : (p : S) = 0) :
    ∃ (T : Type) (_ : CommRing T) (i : S →+* T), (p : T) = 0 ∧
      Function.Bijective (fun t : T => t ^ p) ∧
      (∀ t : T, ∃ (k : ℕ) (x : S), t ^ p ^ k = i x) ∧
      ∀ x : S, i x = 0 ↔ x ∈ I.radical := by
  by_cases htop : I.radical = ⊤
  · haveI : Subsingleton (S ⧸ I.radical) := Ideal.Quotient.subsingleton_iff.mpr htop
    refine ⟨S ⧸ I.radical, inferInstance, Ideal.Quotient.mk I.radical, Subsingleton.elim _ _,
      ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨b, Subsingleton.elim _ _⟩⟩, fun t => ?_,
      fun x => Ideal.Quotient.eq_zero_iff_mem⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective t
    exact ⟨0, x, by simp⟩
  · haveI : Nontrivial (S ⧸ I.radical) := Ideal.Quotient.nontrivial_iff.mpr htop
    have hpQ : ((p : ℕ) : S ⧸ I.radical) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk I.radical), hp, map_zero]
    haveI : CharP (S ⧸ I.radical) p := by
      exact (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hpQ
    haveI : ExpChar (S ⧸ I.radical) p := ExpChar.prime (Fact.out : p.Prime)
    haveI : IsReduced (S ⧸ I.radical) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical I)
    refine ⟨PerfectClosure (S ⧸ I.radical) p, inferInstance,
      (PerfectClosure.of (S ⧸ I.radical) p).comp (Ideal.Quotient.mk I.radical), ?_, ?_, ?_, ?_⟩
    · exact CharP.cast_eq_zero _ p
    · exact PerfectRing.bijective_frobenius (R := PerfectClosure (S ⧸ I.radical) p) (p := p)
    · intro t
      obtain ⟨n, y, hy⟩ := IsPRadical.pow_mem (i := PerfectClosure.of (S ⧸ I.radical) p) (p := p) t
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨n, x, hy.symm⟩
    · intro x
      constructor
      · intro h
        have hk : Ideal.Quotient.mk I.radical x ∈ RingHom.ker (PerfectClosure.of (S ⧸ I.radical) p) := h
        obtain ⟨n, hn⟩ := mem_pNilradical.mp
          (IsPRadical.ker_le (i := PerfectClosure.of (S ⧸ I.radical) p) (p := p) hk)
        exact Ideal.Quotient.eq_zero_iff_mem.mp (IsReduced.eq_zero _ ⟨_, hn⟩)
      · intro h
        simp [Ideal.Quotient.eq_zero_iff_mem.mpr h]

end GlobalTheory.CompanionTheory.PerfClos
end

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfClos

theorem exists_PQ : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] (I : Ideal S), (p : S) = 0 →
    ∃ (T : Type) (_ : CommRing T) (i : S →+* T), PQ p i I := by
  intro p hpf S _ I hp
  obtain ⟨T, inst, i, hc, hb, hpow, hker⟩ := exists_perfect_radical p S I hp
  refine ⟨T, inst, i, ⟨⟨hc, hb⟩, hpow, fun x => ?_⟩⟩
  rw [hker x]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, Ideal.pow_mem_of_pow_mem I hn ?_⟩
    exact (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  · rintro ⟨k, hk⟩
    exact ⟨p ^ k, hk⟩

end GlobalTheory.CompanionTheory.PerfClos
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneTmulMemRangeIff
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.CovCmp

theorem one_tmul_mem_range_iff {A : Type} [CommRing A] (B' : Type) [CommRing B'] [Algebra A B']
    {K₁ K₀ : Type} [AddCommGroup K₁] [Module A K₁] [AddCommGroup K₀] [Module A K₀]
    (d : K₁ →ₗ[A] K₀) (z : K₀) :
    ((1 : B') ⊗ₜ[A] z) ∈ LinearMap.range (d.lTensor B') ↔
      (1 : B') ⊗ₜ[A] ((LinearMap.range d).mkQ z) = 0 := by
  have hex := lTensor_exact B' (LinearMap.exact_map_mkQ_range d)
    (Submodule.mkQ_surjective (LinearMap.range d))
  have := hex ((1 : B') ⊗ₜ[A] z)
  rw [LinearMap.lTensor_tmul] at this
  exact this.symm

theorem cov_of_solv : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (r : ℕ → A), (∀ (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), Solv B a c → ∃ (B₁ : Type) (_ : CommRing B₁) (_ : Algebra A B₁), Cov p r B₁ ∧ Solv B₁ a c) → Cov p r B := by
  intro p _ A _ B _ _ r h K₁ K₀ _ _ _ _ h₁ h₀ d hd z hz k
  have hB := (one_tmul_mem_range_iff B d z).mp hz
  obtain ⟨m, n, a, c, hs, hall⟩ := GlobalTheory.CompanionTheory.EqCrit.exists_system B ((LinearMap.range d).mkQ z) hB
  obtain ⟨B₁, i₁, i₂, hc, hs₁⟩ := h m n a c hs
  have h0 := hall B₁ hs₁
  exact hc K₁ K₀ h₁ h₀ d hd z ((one_tmul_mem_range_iff B₁ d z).mpr h0) k

end GlobalTheory.CompanionTheory.CovCmp
end
