module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleCechObj
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSubvarDrop
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechExact
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrictionBundle
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestrictTwist
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleNefPlusAmple
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepThreeOnWGen

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperQuotAdd
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace SnapperQuotientAdditivity

theorem altSum_eq {k : Type u} [Field k] (A B C : ℕ → Type v)
    [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)] [∀ i, FiniteDimensional k (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module k (B i)] [∀ i, FiniteDimensional k (B i)]
    [∀ i, AddCommGroup (C i)] [∀ i, Module k (C i)] [∀ i, FiniteDimensional k (C i)]
    (f : ∀ i, A i →ₗ[k] B i) (g : ∀ i, B i →ₗ[k] C i) (δ : ∀ i, C i →ₗ[k] A (i + 1))
    (h0 : Function.Injective (f 0)) (hfg : ∀ i, Function.Exact (f i) (g i))
    (hgδ : ∀ i, Function.Exact (g i) (δ i)) (hδf : ∀ i, Function.Exact (δ i) (f (i + 1))) (M : ℕ) :
    ∑ i ∈ Finset.range (M + 1), (-1 : ℤ) ^ i *
      ((Module.finrank k (A i) : ℤ) - Module.finrank k (B i) + Module.finrank k (C i)) =
      (-1 : ℤ) ^ M * Module.finrank k (LinearMap.range (δ M)) := by
  have hB : ∀ i, (Module.finrank k (B i) : ℤ) =
      Module.finrank k (LinearMap.range (f i)) + Module.finrank k (LinearMap.range (g i)) := by
    intro i
    rw [← LinearMap.finrank_range_add_finrank_ker (g i), LinearMap.exact_iff.1 (hfg i)]
    push_cast; ring
  have hC : ∀ i, (Module.finrank k (C i) : ℤ) =
      Module.finrank k (LinearMap.range (g i)) + Module.finrank k (LinearMap.range (δ i)) := by
    intro i
    rw [← LinearMap.finrank_range_add_finrank_ker (δ i), LinearMap.exact_iff.1 (hgδ i)]
    push_cast; ring
  have hA : ∀ i, (Module.finrank k (A (i + 1)) : ℤ) =
      Module.finrank k (LinearMap.range (δ i)) + Module.finrank k (LinearMap.range (f (i + 1))) := by
    intro i
    rw [← LinearMap.finrank_range_add_finrank_ker (f (i + 1)), LinearMap.exact_iff.1 (hδf i)]
    push_cast; ring
  have hA0 : (Module.finrank k (A 0) : ℤ) = Module.finrank k (LinearMap.range (f 0)) := by
    rw [← LinearMap.finrank_range_add_finrank_ker (f 0), LinearMap.ker_eq_bot.2 h0, finrank_bot]
    simp
  induction M with
  | zero => rw [Finset.sum_range_one, hA0, hB 0, hC 0]; ring
  | succ M ih => rw [Finset.sum_range_succ, ih, hA M, hB (M + 1), hC (M + 1)]; ring

section Top

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] (G : Cell U → Type v)
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] (ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J)

theorem cdeg_top (i : ℕ) : Cech.Cdeg G (fun _ => (⊤ : Submodule R _)) i = ⊤ := by
  ext s; simp [Cech.Cdeg]

theorem cocyDeg_top (i : ℕ) : Cech.cocyDeg G (fun _ => ⊤) ρ i = LinearMap.ker (Cech.d G ρ i) := by
  rw [Cech.cocyDeg, cdeg_top, inf_top_eq]

theorem bdryDeg_top (i : ℕ) : Cech.bdryDeg G (fun _ => ⊤) ρ i = Cech.bdry G ρ i := by
  cases i with
  | zero => rfl
  | succ i => rw [Cech.bdryDeg, Cech.bdry, cdeg_top, Submodule.map_top]

def hdegTopEquiv (i : ℕ) : Cech.Hdeg G (fun _ => ⊤) ρ i ≃ₗ[R] Cech.H G ρ i :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ (cocyDeg_top G ρ i)) (by
    ext z
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [bdryDeg_top] at hy
      exact hy
    · intro hz
      refine ⟨⟨z.1, (cocyDeg_top G ρ i).symm ▸ z.2⟩, ?_, rfl⟩
      rw [bdryDeg_top]; exact hz)

theorem hdeg_subsingleton {R' : Type*} [CommRing R'] [∀ I, Module R' (G I)] (deg : ∀ I, Submodule R' (G I))
    (ρ' : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R'] G J) (i : ℕ) [IsEmpty (Cech.Idx U i)] :
    Subsingleton (Cech.Hdeg G deg ρ' i) := by
  have : Subsingleton (Cech.cocyDeg G deg ρ' i) :=
    ⟨fun a b => Subtype.ext (funext fun I => isEmptyElim I)⟩
  refine ⟨fun a b => ?_⟩
  obtain ⟨z, rfl⟩ := Cech.Hdeg_mk_surjective a
  obtain ⟨z', rfl⟩ := Cech.Hdeg_mk_surjective b
  rw [Subsingleton.elim z z']

end Top

theorem idx_isEmpty {Ω : Type w} [Field Ω] {N : ℕ} (x : Fin (N + 1) → Ω) : IsEmpty (Cech.Idx (support x) (N + 1)) :=
  ⟨fun I => by
    have h1 := Finset.card_le_card I.1.2.2
    have h2 := Finset.card_le_univ (support x)
    have h3 := I.2
    simp only [Fintype.card_fin] at h2
    omega⟩

section Quot

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]

def quotInl (F₁ F₂ F₃ : SubSystem k x E) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I) (I : Chart x) :
    (F₂.sub I ⧸ SubSystem.quotSub F₂ F₃ I) →ₗ[k] (F₁.sub I ⧸ SubSystem.quotSub F₁ F₃ I) :=
  (SubSystem.quotSub F₂ F₃ I).mapQ (SubSystem.quotSub F₁ F₃ I)
    { toFun := fun y => ⟨y, h21 I y.2⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    (fun _ hy => hy)

def quotPr (F₁ F₂ F₃ : SubSystem k x E) (h32 : ∀ I, F₃.sub I ≤ F₂.sub I) (I : Chart x) :
    (F₁.sub I ⧸ SubSystem.quotSub F₁ F₃ I) →ₗ[k] (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) :=
  (SubSystem.quotSub F₁ F₃ I).mapQ (SubSystem.quotSub F₁ F₂ I) LinearMap.id (by intro _ hy; exact h32 I hy)

theorem quotRes_comp (F₁ F₂ : SubSystem k x E) (I J K : Chart x) (hIJ : I.1 ⊆ J.1) (hJK : J.1 ⊆ K.1) :
    (SubSystem.quotRes F₁ F₂ J K hJK).comp (SubSystem.quotRes F₁ F₂ I J hIJ) =
      SubSystem.quotRes F₁ F₂ I K (hIJ.trans hJK) :=
  Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)

theorem quotInl_comm (F₁ F₂ F₃ : SubSystem k x E) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I) (I J : Chart x) (h : I.1 ⊆ J.1)
    (m : F₂.sub I ⧸ SubSystem.quotSub F₂ F₃ I) :
    quotInl F₁ F₂ F₃ h21 J (SubSystem.quotRes F₂ F₃ I J h m) =
      SubSystem.quotRes F₁ F₃ I J h (quotInl F₁ F₂ F₃ h21 I m) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m; rfl

theorem quotPr_comm (F₁ F₂ F₃ : SubSystem k x E) (h32 : ∀ I, F₃.sub I ≤ F₂.sub I) (I J : Chart x) (h : I.1 ⊆ J.1)
    (m : F₁.sub I ⧸ SubSystem.quotSub F₁ F₃ I) :
    quotPr F₁ F₂ F₃ h32 J (SubSystem.quotRes F₁ F₃ I J h m) =
      SubSystem.quotRes F₁ F₂ I J h (quotPr F₁ F₂ F₃ h32 I m) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m; rfl

theorem quotInl_injective (F₁ F₂ F₃ : SubSystem k x E) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I) (I : Chart x) :
    Function.Injective (quotInl F₁ F₂ F₃ h21 I) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro m hm
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  have h' : (Submodule.Quotient.mk (⟨(y : E), h21 I y.2⟩ : F₁.sub I) :
      F₁.sub I ⧸ SubSystem.quotSub F₁ F₃ I) = 0 := hm
  rw [Submodule.Quotient.mk_eq_zero] at h'
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  exact h'

theorem quotPr_quotInl (F₁ F₂ F₃ : SubSystem k x E) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I)
    (h32 : ∀ I, F₃.sub I ≤ F₂.sub I) (I : Chart x) (m : F₂.sub I ⧸ SubSystem.quotSub F₂ F₃ I) :
    quotPr F₁ F₂ F₃ h32 I (quotInl F₁ F₂ F₃ h21 I m) = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  show (Submodule.Quotient.mk (⟨(y : E), h21 I y.2⟩ : F₁.sub I) : F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact y.2

theorem exists_quotInl (F₁ F₂ F₃ : SubSystem k x E) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I)
    (h32 : ∀ I, F₃.sub I ≤ F₂.sub I) (I : Chart x) (m : F₁.sub I ⧸ SubSystem.quotSub F₁ F₃ I)
    (hm : quotPr F₁ F₂ F₃ h32 I m = 0) : ∃ y, quotInl F₁ F₂ F₃ h21 I y = m := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  have h' : (Submodule.Quotient.mk z : F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) = 0 := hm
  rw [Submodule.Quotient.mk_eq_zero] at h'
  exact ⟨Submodule.Quotient.mk ⟨z, h'⟩, rfl⟩

theorem quotPr_surjective (F₁ F₂ F₃ : SubSystem k x E) (h32 : ∀ I, F₃.sub I ≤ F₂.sub I) (I : Chart x) :
    Function.Surjective (quotPr F₁ F₂ F₃ h32 I) := by
  intro m
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  exact ⟨Submodule.Quotient.mk z, rfl⟩

theorem finrank_quotH (F₁ F₂ : SubSystem k x E) (i : ℕ) :
    Module.finrank k (SubSystem.quotH F₁ F₂ i) =
      Module.finrank k (Cech.Hdeg (fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) (fun _ => ⊤)
        (SubSystem.quotRes F₁ F₂) i) :=
  (hdegTopEquiv _ _ i).finrank_eq.symm

end Quot

end SnapperQuotientAdditivity


set_option maxHeartbeats 1000000 in
open SnapperQuotientAdditivity in
theorem SnapperQuotAdd.proof (hfin : SnapperSubquotFinite.Statement.{u, v, w}) :
    SnapperQuotAdd.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x E _ _ _ _ F₁ F₂ F₃ hfg h21 h32
  have h31 : ∀ I, F₃.sub I ≤ F₁.sub I := fun I => (h32 I).trans (h21 I)
  have hdd := CechDSq.proof (N + 1) (support x) k
    (fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁.toSubSystem F₃.toSubSystem I)
    (SubSystem.quotRes F₁.toSubSystem F₃.toSubSystem) (quotRes_comp F₁.toSubSystem F₃.toSubSystem)
  have L := Cech.longExact (R := k) (U := support x)
    (A := fun I : Chart x => F₂.sub I ⧸ SubSystem.quotSub F₂.toSubSystem F₃.toSubSystem I)
    (B := fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁.toSubSystem F₃.toSubSystem I)
    (C := fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁.toSubSystem F₂.toSubSystem I)
    (ρA := SubSystem.quotRes F₂.toSubSystem F₃.toSubSystem)
    (ρB := SubSystem.quotRes F₁.toSubSystem F₃.toSubSystem)
    (ρC := SubSystem.quotRes F₁.toSubSystem F₂.toSubSystem)
    (dA := fun _ => ⊤) (dB := fun _ => ⊤) (dC := fun _ => ⊤)
    (φ := quotInl F₁.toSubSystem F₂.toSubSystem F₃.toSubSystem h21)
    (ψ := quotPr F₁.toSubSystem F₂.toSubSystem F₃.toSubSystem h32)
  have L1 := L (quotInl_comm _ _ _ h21)
  have L2 := L1 (quotPr_comm _ _ _ h32)
  have L3 := L2 (fun _ _ _ => Submodule.mem_top) (fun _ _ _ => Submodule.mem_top)
  have L4 := L3 (quotInl_injective _ _ _ h21)
  have L5 := L4 (quotPr_quotInl _ _ _ h21 h32)
  have L6 := L5 (fun I m _ hm => (exists_quotInl _ _ _ h21 h32 I m hm).imp fun y hy => ⟨Submodule.mem_top, hy⟩)
  have L7 := L6 (fun I m _ => (quotPr_surjective _ _ _ h32 I m).imp fun y hy => ⟨Submodule.mem_top, hy⟩)
  have L8 := L7 (fun _ _ _ _ _ => Submodule.mem_top)
  have liftZP_newton := L8 hdd
  have h0 := liftZP_newton.1
  have hex := liftZP_newton.2
  choose δ hgδ hδf using fun i => (hex i).2
  have fin : ∀ (G₁ G₂ : SubFamily k x E), (∀ I, G₁.sub I ≤ F₁.sub I) → (∀ I, G₂.sub I ≤ G₁.sub I) → ∀ i,
      FiniteDimensional k (Cech.Hdeg (fun I : Chart x => G₁.sub I ⧸ SubSystem.quotSub G₁.toSubSystem G₂.toSubSystem I)
        (fun _ => ⊤) (SubSystem.quotRes G₁.toSubSystem G₂.toSubSystem) i) := by
    intro G₁ G₂ h1 h2 i
    have : FiniteDimensional k (Cech.H (fun I : Chart x => G₁.sub I ⧸ SubSystem.quotSub G₁.toSubSystem G₂.toSubSystem I)
        (SubSystem.quotRes G₁.toSubSystem G₂.toSubSystem) i) := hfin k Ω N x E F₁ G₁ G₂ hfg h1 h2 i
    exact (hdegTopEquiv _ _ i).symm.finiteDimensional
  have := fin F₂ F₃ h21 h32
  have := fin F₁ F₃ (fun _ => le_rfl) h31
  have := fin F₁ F₂ (fun _ => le_rfl) h21
  have key := altSum_eq _ _ _ _ _ δ h0 (fun i => (hex i).1) hgδ hδf N
  have := idx_isEmpty x
  have hsub := hdeg_subsingleton (fun I : Chart x => F₂.sub I ⧸ SubSystem.quotSub F₂.toSubSystem F₃.toSubSystem I)
    (fun _ => (⊤ : Submodule k _)) (SubSystem.quotRes F₂.toSubSystem F₃.toSubSystem) (N + 1)
  have hδN : Module.finrank k (LinearMap.range (δ N)) = 0 := by
    have hz : Module.finrank k (Cech.Hdeg (fun I : Chart x => F₂.sub I ⧸ SubSystem.quotSub F₂.toSubSystem F₃.toSubSystem I)
        (fun _ => (⊤ : Submodule k _)) (SubSystem.quotRes F₂.toSubSystem F₃.toSubSystem) (N + 1)) = 0 :=
      Module.finrank_zero_of_subsingleton
    exact Nat.eq_zero_of_le_zero ((Submodule.finrank_le (LinearMap.range (δ N))).trans hz.le)
  rw [hδN] at key
  simp only [Nat.cast_zero, mul_zero, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] at key
  simp only [eulerCharQuot, finrank_quotH]
  linarith

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestriction
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem zero_mem_ampleChart {S : Type u} [CommRing S] {E : Type w} [Field E] [Algebra S E] {M : ℕ}
    {z : Fin (M + 1) → E} {H : SubSystem S z E} {σ : E} {I : Chart z} :
    (0 : E) ∈ ampleChart H 1 σ I :=
  ⟨0, by rw [zero_mul]; exact Submodule.zero_mem _⟩

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}

theorem exists_restrictData_isVeryAmpleBy (hsp : primeOf (S := k) x ≤ primeOf (S := k) y)
    (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (I₀ : Chart y) (Nb : LineBundle k x) {r : ℕ}
    (h : Fin (r + 1) → Ω) (hV : IsVeryAmpleBy Nb.toSubSystem h) :
    ∃ (Q' : LineBundle k y) (ρ : Ω → K'), RestrictData Nb.toSubSystem hxy Q'.toSubSystem ρ ∧
      IsVeryAmpleBy Q'.toSubSystem (ρ ∘ h) ∧ dimCl k y = dimCl k (ρ ∘ h) := by
  classical
  obtain ⟨l₀, hg0, hgl, hg⟩ := exists_redGood hsp hxy hV I₀
  obtain ⟨Q', hQ⟩ := exists_lineBundle_redSys hsp hxy hV hg0 hg (mem_sub_of_isVeryAmpleBy hV l₀)
  set g := h l₀ with hgdef
  set ρ : Ω → K' := fun q => redAt k x y (q / g) with hρ
  have hloc : ∀ {j : Fin (r + 1)} (_ : redAt k x y (h j / g) ≠ 0) {c : Ω},
      c ∈ ampleRing Nb.toSubSystem 1 (h j) →
        c ∈ locAt k x y ∧ redAt k x y c ∈ ampleBase (S := k) (ρ ∘ h) j := fun {j} hr {c} hc =>
    redAt_mem_ampleBase hsp hg0 hgl hr (hV.closed j (ne_zero_of_redAt_div hsp (hgl j) hr) hc)
  have hvery : IsVeryAmpleBy Q'.toSubSystem (ρ ∘ h) := by
    refine ⟨fun l => ?_, fun I => ?_, fun j hj => ?_, fun j hj => ?_⟩
    · refine (Submodule.mem_iInf _).mpr fun I => ?_
      rw [Submodule.restrictScalars_mem, hQ]
      exact Submodule.subset_span ⟨h l, mem_sub_of_isVeryAmpleBy hV l _, rfl⟩
    · rw [hQ, redSys_sub_eq hsp hxy hV hg]; rfl
    ·
      have hσ := hgl j
      have hσr : redAt k x y (h j / g) ≠ 0 := hj
      obtain ⟨n, a', b', J, ha', hb', hsum, hbJ⟩ :=
        hV.affine j (ne_zero_of_redAt_div hsp hσ hσr)
      intro a ha
      have hE : ∀ kk, ∃ E : ℕ, redAt k x y (b' kk) ^ (E + 1) * a ∈ ampleBase (S := k) (ρ ∘ h) j := by
        intro kk
        by_cases hbr : redAt k x y (b' kk) = 0
        · refine ⟨0, ?_⟩
          rw [hbr, zero_pow (Nat.succ_ne_zero 0), zero_mul]; exact zero_mem _
        · have hbl := (hloc hσr (hb' kk)).1
          have hJ := subset_support_of_redAt_ne_zero hsp hxy hg hσ hσr I₀ hbl hbr (hbJ kk)
          let Jy : Chart y := ⟨(J kk).1, (J kk).2.1, hJ⟩
          obtain ⟨e, he, hea⟩ :=
            exists_lift_ampleChart hsp hxy hg Q' hQ hσ hσr Jy (Set.mem_iInter.mp ha Jy)
          have hel := (redAt_mem_ampleChart hsp hxy hg Q' hQ hσ hσr Jy he).1
          obtain ⟨E, hEm⟩ := res_exists_pow_mul_mem_ampleRing Nb (hb' kk) (hbJ kk) (J := J kk) he
          have hm := hloc hσr hEm
          rw [(locAt_mul hsp (locAt_pow hsp hbl E).1 hel).2, (locAt_pow hsp hbl E).2, hea] at hm
          refine ⟨E, ?_⟩
          have : redAt k x y (b' kk) ^ (E + 1) * a =
              redAt k x y (b' kk) * (redAt k x y (b' kk) ^ E * a) := by ring
          rw [this]
          exact mul_mem (hloc hσr (hb' kk)).2 hm.2
      choose E hE using hE
      let T := Finset.univ.sup E + 1
      let β : Fin n → ampleBase (S := k) (ρ ∘ h) j :=
        fun kk => ⟨redAt k x y (b' kk), (hloc hσr (hb' kk)).2⟩
      let α : Fin n → ampleBase (S := k) (ρ ∘ h) j :=
        fun kk => ⟨redAt k x y (a' kk), (hloc hσr (ha' kk)).2⟩
      have hsum' : ∑ kk, α kk * β kk = 1 := by
        apply Subtype.ext
        rw [AddSubmonoidClass.coe_finsetSum, OneMemClass.coe_one]
        have h2 := (locAt_sum hsp Finset.univ (fun kk => a' kk * b' kk) fun kk _ =>
          (locAt_mul hsp (hloc hσr (ha' kk)).1 (hloc hσr (hb' kk)).1).1).2
        rw [hsum, (locAt_one hsp).2] at h2
        refine Eq.trans (Finset.sum_congr rfl fun kk _ => ?_) h2.symm
        rw [(locAt_mul hsp (hloc hσr (ha' kk)).1 (hloc hσr (hb' kk)).1).2]
        rfl
      have hspan : Ideal.span (Set.range β) = ⊤ := by
        rw [Ideal.eq_top_iff_one, ← hsum']
        exact Ideal.sum_mem _ fun kk _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨kk, rfl⟩)
      have hT := Ideal.span_pow_eq_top (Set.range β) hspan T
      let 𝔞 : Ideal (ampleBase (S := k) (ρ ∘ h) j) :=
        { carrier := {c | (c : K') * a ∈ ampleBase (S := k) (ρ ∘ h) j}
          add_mem' := fun {u v} hu hv => by
            simp only [Set.mem_ofPred_eq, AddMemClass.coe_add, add_mul] at hu hv ⊢
            exact add_mem hu hv
          zero_mem' := by
            simp only [Set.mem_ofPred_eq, ZeroMemClass.coe_zero, zero_mul]; exact zero_mem _
          smul_mem' := fun c u hu => by
            simp only [Set.mem_ofPred_eq, smul_eq_mul, MulMemClass.coe_mul, mul_assoc] at hu ⊢
            exact mul_mem c.2 hu }
      have hle : Ideal.span ((fun c => c ^ T) '' Set.range β) ≤ 𝔞 := by
        rw [Ideal.span_le]
        rintro _ ⟨_, ⟨kk, rfl⟩, rfl⟩
        show ((β kk ^ T : ampleBase (S := k) (ρ ∘ h) j) : K') * a ∈ ampleBase (S := k) (ρ ∘ h) j
        have hk : E kk + 1 ≤ T := Nat.succ_le_succ (Finset.le_sup (Finset.mem_univ kk))
        rw [SubmonoidClass.coe_pow, ← Nat.sub_add_cancel hk, pow_add, mul_assoc]
        exact mul_mem (pow_mem (β kk).2 _) (hE kk)
      have h1 : (1 : ampleBase (S := k) (ρ ∘ h) j) ∈ 𝔞 := hle (by rw [hT]; exact Submodule.mem_top)
      have h1' : ((1 : ampleBase (S := k) (ρ ∘ h) j) : K') * a ∈ ampleBase (S := k) (ρ ∘ h) j := h1
      rwa [OneMemClass.coe_one, one_mul] at h1'
    ·
      have hσ := hgl j
      have hσr : redAt k x y (h j / g) ≠ 0 := hj
      obtain ⟨n, a', b', J, ha', hb', hsum, hbJ⟩ :=
        hV.affine j (ne_zero_of_redAt_div hsp hσ hσr)
      have hred : ∀ {c : Ω}, c ∈ ampleRing Nb.toSubSystem 1 (h j) →
          redAt k x y c ∈ ampleRing Q'.toSubSystem 1 ((ρ ∘ h) j) := fun hc =>
        Set.mem_iInter.mpr fun I => (redAt_mem_ampleChart hsp hxy hg Q' hQ hσ hσr I
          (Set.mem_iInter.mp hc (liftChart hxy I))).2
      have hsupp : ∀ kk, redAt k x y (b' kk) ≠ 0 → (J kk).1 ⊆ support y := fun kk hbr =>
        subset_support_of_redAt_ne_zero hsp hxy hg hσ hσr I₀ (hloc hσr (hb' kk)).1 hbr (hbJ kk)
      refine ⟨n, fun kk => redAt k x y (a' kk),
        fun kk => if redAt k x y (b' kk) = 0 then 0 else redAt k x y (b' kk),
        fun kk => if hb : redAt k x y (b' kk) = 0 then I₀ else ⟨(J kk).1, (J kk).2.1, hsupp kk hb⟩,
        fun kk => hred (ha' kk), fun kk => ?_, ?_, fun kk I => ?_⟩
      · dsimp only
        split_ifs with hb
        · exact Set.mem_iInter.mpr fun I => zero_mem_ampleChart
        · exact hred (hb' kk)
      · have h2 := (locAt_sum hsp Finset.univ (fun kk => a' kk * b' kk) fun kk _ =>
          (locAt_mul hsp (hloc hσr (ha' kk)).1 (hloc hσr (hb' kk)).1).1).2
        rw [hsum, (locAt_one hsp).2] at h2
        refine Eq.trans (Finset.sum_congr rfl fun kk _ => ?_) h2.symm
        rw [(locAt_mul hsp (hloc hσr (ha' kk)).1 (hloc hσr (hb' kk)).1).2]
        dsimp only
        split_ifs with hb
        · rw [hb, mul_zero]
        · rfl
      · dsimp only
        by_cases hb : redAt k x y (b' kk) = 0
        · rw [if_pos hb, dite_eq_left hb]
          exact ⟨1, by rw [pow_one, zero_mul]; exact zero_mem_ampleChart⟩
        · rw [if_neg hb, dite_eq_right hb]
          obtain ⟨e, he⟩ := hbJ kk (liftChart hxy I)
          have hbl := (hloc hσr (hb' kk)).1
          have hJ := hsupp kk hb
          have hf := (res_isHomogeneous_prod_X (S := k) I.1).pow (J kk).1.card
          have hs : ((∏ l ∈ (J kk).1, (X l : Poly k N)) ^ I.1.card).IsHomogeneous
              (I.1.card * (J kk).1.card) := by
            rw [mul_comm]; exact (res_isHomogeneous_prod_X (S := k) (J kk).1).pow I.1.card
          have hsy : aeval y ((∏ l ∈ (J kk).1, (X l : Poly k N)) ^ I.1.card) ≠ 0 := by
            rw [map_pow, res_aeval_prod_X]
            exact pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun i hi => (mem_support y).mp (hJ hi))
          have ht : xProd (liftChart hxy I) ^ (J kk).1.card / xProd (J kk) ^ (liftChart hxy I).1.card =
              aeval x ((∏ l ∈ I.1, (X l : Poly k N)) ^ (J kk).1.card) /
                aeval x ((∏ l ∈ (J kk).1, (X l : Poly k N)) ^ I.1.card) := by
            rw [map_pow, map_pow, res_aeval_prod_X, res_aeval_prod_X]; rfl
          obtain ⟨-, h2⟩ := redAt_mem_ampleChart hsp hxy hg Q' hQ hσ hσr I he
          rw [ht, (locAt_mul hsp (locAt_pow hsp hbl e).1 (mem_locAt hf hs hsy)).2,
            (locAt_pow hsp hbl e).2, redAt_eq hsp hf hs hsy, map_pow, map_pow, res_aeval_prod_X,
            res_aeval_prod_X] at h2
          exact ⟨e, h2⟩

  have hdim : funField (k := k) y = funField (k := k) (ρ ∘ h) := by
    obtain ⟨i₀, hi₀⟩ := I₀.2.1
    have hy₀ : y i₀ ≠ 0 := (mem_support y).mp (I₀.2.2 hi₀)
    have haeval : ∀ p : Poly k N, aeval (fun l => y l / y i₀) p ∈ funField (k := k) y := fun p =>
      MvPolynomial.induction_on (motive := fun p => aeval (fun l => y l / y i₀) p ∈ funField (k := k) y) p
        (fun c => by rw [aeval_C]; exact IntermediateField.algebraMap_mem _ c)
        (fun p q hp hq => by rw [map_add]; exact add_mem hp hq)
        (fun p l hp => by
          rw [map_mul, aeval_X]
          exact mul_mem hp (IntermediateField.subset_adjoin _ _ ⟨i₀, l, hy₀, rfl⟩))
    have hredF : ∀ {c : Ω}, c ∈ locAt k x y → redAt k x y c ∈ funField (k := k) y := by
      rintro _ ⟨f, s, e, hf, hs, hsy, rfl⟩
      rw [redAt_eq hsp hf hs hsy, ← div_div_div_cancel_right₀ (pow_ne_zero e hy₀),
        ← aeval_div_of_isHomogeneous hf i₀, ← aeval_div_of_isHomogeneous hs i₀]
      exact div_mem (haeval f) (haeval s)
    apply le_antisymm
    · have hg1' : redAt k x y (g / g) ≠ 0 := by
        rw [div_self hg0, (locAt_one hsp).2]; exact one_ne_zero
      obtain ⟨n, a', b', J, ha', hb', hsum, hbJ⟩ := hV.affine l₀ hg0
      have h2 := (locAt_sum hsp Finset.univ (fun kk => a' kk * b' kk) fun kk _ =>
          (locAt_mul hsp (hloc hg1' (ha' kk)).1 (hloc hg1' (hb' kk)).1).1).2
      rw [hsum, (locAt_one hsp).2] at h2
      have hne : ∑ kk, redAt k x y (a' kk * b' kk) ≠ 0 := by rw [← h2]; exact one_ne_zero
      obtain ⟨kk, -, hkk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      rw [(locAt_mul hsp (hloc hg1' (ha' kk)).1 (hloc hg1' (hb' kk)).1).2] at hkk
      have hbr : redAt k x y (b' kk) ≠ 0 := right_ne_zero_of_mul hkk
      have hbl := (hloc hg1' (hb' kk)).1
      have hJ := subset_support_of_redAt_ne_zero hsp hxy hg (hgl l₀) hg1' I₀ hbl hbr (hbJ kk)
      obtain ⟨c, hc⟩ := (J kk).2.1
      have hyc : y c ≠ 0 := (mem_support y).mp (hJ hc)
      have hBF : ampleBase (S := k) (ρ ∘ h) l₀ ≤ (funField (k := k) (ρ ∘ h)).toSubalgebra := by
        refine Algebra.adjoin_le ?_
        rintro _ ⟨l, rfl⟩
        exact IntermediateField.subset_adjoin _ _ ⟨l₀, l, hg1', rfl⟩
      have hbF : redAt k x y (b' kk) ∈ funField (k := k) (ρ ∘ h) := hBF (hloc hg1' (hb' kk)).2
      have hratio : ∀ m, y m / y c ∈ funField (k := k) (ρ ∘ h) := by
        intro m
        have hmc : x m / x c ∈ chartRing k x (J kk) :=
          ⟨X m, X c, 1, X_mem_monos hc, isHomogeneous_X k m, isHomogeneous_X k c, by simp⟩
        obtain ⟨E, hE⟩ := res_exists_pow_mul_mem_ampleRing Nb (hb' kk) (hbJ kk)
          (res_chartRing_sub_ampleChart hmc)
        have hm := hloc hg1' hE
        have hsy : aeval y (X c : Poly k N) ≠ 0 := by rw [aeval_X]; exact hyc
        have hmcl : x m / x c ∈ locAt k x y := by
          have := mem_locAt (x := x) (isHomogeneous_X k m) (isHomogeneous_X k c) hsy
          simpa only [aeval_X] using this
        have hmcr : redAt k x y (x m / x c) = y m / y c := by
          have := redAt_eq hsp (isHomogeneous_X k m) (isHomogeneous_X k c) hsy
          simpa only [aeval_X] using this
        rw [(locAt_mul hsp (locAt_pow hsp hbl E).1 hmcl).2, (locAt_pow hsp hbl E).2, hmcr] at hm
        have hF := hBF hm.2
        have hbE : redAt k x y (b' kk) ^ E ≠ 0 := pow_ne_zero _ hbr
        have : y m / y c = (redAt k x y (b' kk) ^ E * (y m / y c)) / redAt k x y (b' kk) ^ E := by
          field_simp
        rw [this]
        exact div_mem hF (pow_mem hbF E)
      rw [funField, IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, i', hi, rfl⟩
      rw [← div_div_div_cancel_right₀ hyc (y i') (y i)]
      exact div_mem (hratio i') (hratio i)
    · rw [funField, IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, i', -, rfl⟩
      exact div_mem (hredF (hgl i')) (hredF (hgl i))
  refine ⟨Q', ρ, restrictData_redSys hsp hxy hg Q' hQ, hvery, ?_⟩
  rw [dimCl, dimCl, hdim]

theorem Restriction.proof : Restriction.Statement.{u, w} := by
  intro k _ Ω _ _ N x Nb r h hV pp _ _ _ j hj _ K' _ _ ψ _ hxy
  have hsp := primeOf_le_primeOf_of_algHom hj ψ
  have hyj : (fun i => ψ (ratio hj i)) j ≠ 0 := by
    show ψ (ratio hj j) ≠ 0
    rw [algHom_ratio_self]; exact one_ne_zero
  exact exists_restrictData_isVeryAmpleBy hsp hxy (singleChart hyj) Nb h hV

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHFreeEmbedSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

def KHFreeEmbed.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (a : (Σ k, ι k) → ℤ),
    (∀ (n : ℕ) (f : CombC S (negSet a) n),
      KH.cechD S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n (embed S a n f) =
        embed S a (n + 1) (combD S (negSet a) n f)) ∧
    (∀ (c d : K → ℤ), blockSum a = c + d → ∀ (n : ℕ) (f : CombC S (negSet a) n),
      embed S a n f ∈ KH.cechCc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n) ∧
    ((∀ p, 0 ≤ a p) → ∃ m ∈ KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (blockSum a),
      ∀ I : ∀ k, Finset (ι k), monoFrac S I a = LocalizedModule.mk m 1)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ZChartLocalSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def ZChartLocal.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (G : SubFamily S x E) (H : LineBundle S x) (r : ℕ) (h : Fin (r + 1) → Ω),
    (∀ l, h l ∈ H.secs) → ∀ (J : Chart h) (j : Fin (r + 1)), j ∈ J.1 →
    ∀ (b : Ω), b ∈ ampleRing H.toSubSystem 1 (h j) → ∀ K : Chart x,
      (∀ I : Chart x, ∃ e : ℕ,
        b ^ e * (xProd I ^ K.1.card / xProd K ^ I.1.card) ∈ ampleChart H.toSubSystem 1 (h j) I) →
      ∀ j₀ ∈ K.1, ∀ I I' : Chart x, I'.1 = insert j₀ I.1 →
        ∀ z ∈ secsOnZChart G.toSubSystem H.toSubSystem h I' J,
          ∃ e : ℕ, b ^ e • z ∈ secsOnZChart G.toSubSystem H.toSubSystem h I J

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsRestrictGenerated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def RestrictGenerated.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (K' : Type w) [Field K'] [Algebra S K'] (y : Fin (N + 1) → K') (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    (pp : Ideal (Poly S N)), primeOf (S := S) x ≤ pp → primeOf (S := S) y = pp →
    ∀ (Q : LineBundle S x) (Q' : LineBundle S y) (r : Ω → K'),
      RestrictData Q.toSubSystem hxy Q'.toSubSystem r → Q'.toSubSystem.Generated →
      ∀ I : Chart x, Q.toSubSystem.sub I ≤
        Submodule.span (chartRing S x I) {z | ∃ s : Chart x → Ω, (∀ I', s I' ∈ Q.toSubSystem.sub I') ∧
          (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ (Q.toSubSystem.twist (idealSys x pp)).sub I₂) ∧
          z = s I} ⊔ (Q.toSubSystem.twist (idealSys x pp)).sub I

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperQuotFiltSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SnapperQuotFilt.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F₁ F₂ : SubFamily k x E), (∀ I, (F₁.sub I).FG) → (∀ I, F₂.sub I ≤ F₁.sub I) →
    ∀ J : Ideal (Poly k N), (∀ f ∈ J, ∀ d : ℕ, homogeneousComponent d f ∈ J) → primeOf (S := k) x ≤ J →
    (∀ I, (F₁.toSubSystem.twist (idealSys x J)).sub I ≤ F₂.sub I) →
    ∃ (r : ℕ) (G : ℕ → SubFamily k x E) (pp : Fin r → Ideal (Poly k N)) (a : Fin r → ℤ),
      (∀ m I, ((G m).sub I).FG) ∧ (G 0).toSubSystem = F₂.toSubSystem ∧
      (G r).toSubSystem = F₁.toSubSystem ∧ (∀ m < r, ∀ I, (G m).sub I ≤ (G (m + 1)).sub I) ∧
      (∀ m, (pp m).IsPrime ∧ (∀ f ∈ pp m, ∀ d : ℕ, homogeneousComponent d f ∈ pp m) ∧ J ≤ pp m) ∧
      ∀ (m : Fin r) (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ),
        Nonempty (QuotIso
          (((G (m + 1)).toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
          (((G m).toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
          (((twistSys k x (a m)).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
          ((((twistSys k x (a m)).twist (idealSys x (pp m))).twistPows t (fun j => (L j).toSubSystem) n).twist
            (twistSys k x c)))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefRestrict
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

section Helpers

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem tensorSub_single (L : SubSystem S x Ω) (T : Finset (Fin 1)) :
    tensorSub ![L] T = if (0 : Fin 1) ∈ T then L else twistSys S x 0 := by
  have hf : List.finRange 1 = [0] := rfl
  split_ifs with h
  · simp [tensorSub, hf, h, twistSys_zero_twist]
  · simp [tensorSub, hf, h]

end Helpers

theorem NefRestrict.proof (hRT : RestrictTwist.Statement.{u, w})
    (hRL : RestrLenRestrict.Statement.{u, w}) : NefRestrict.Statement.{u, w} := by
  intro k _ Ω _ _ N x K' _ _ y hxy hle M M' r hr hnef pp _ hpp
  have hx : IsSubvar x pp 1 := ⟨hpp.isPrime, hpp.homog, hle.trans hpp.le, hpp.relevant, hpp.dim⟩
  obtain ⟨r₀, hr₀⟩ := hRT.1 k Ω N x K' y hxy hle 0
  have hM := hRL k Ω N x K' y hxy hle pp 1 hpp M M' r hr
  have hO := hRL k Ω N x K' y hxy hle pp 1 hpp (twistBundle k x 0) (twistBundle k y 0) r₀ hr₀
  have heq : interSum pp ![M'.toSubSystem] =ᶠ[atTop] interSum pp ![M.toSubSystem] := by
    filter_upwards [hM, hO] with c hMc hOc
    unfold interSum
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [tensorSub_single, tensorSub_single]
    split_ifs
    · rw [hMc]
    · exact congrArg _ hOc
  have hnum : interNum pp ![M'.toSubSystem] = interNum pp ![M.toSubSystem] := by
    unfold interNum limUnder
    rw [Filter.map_congr heq]
  rw [hnum]
  exact hnef pp bot_le hx

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PInterNumRestrict
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace InterNumRestrict

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {K' : Type w} [Field K'] [Algebra k K'] {y : Fin (N + 1) → K'} {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}

theorem inr_foldl_restrict {n : ℕ} (L : Fin n → LineBundle k x) (L' : Fin n → LineBundle k y)
    (rr : Fin n → Ω → K') (hL : ∀ i, RestrictData (L i).toSubSystem hxy (L' i).toSubSystem (rr i)) :
    ∀ (l : List (Fin n)) (Q : LineBundle k x) (Q' : LineBundle k y) (r : Ω → K'),
      RestrictData Q.toSubSystem hxy Q'.toSubSystem r →
      ∃ (P : LineBundle k x) (P' : LineBundle k y) (s : Ω → K'),
        l.foldl (fun F i => F.twist (L i).toSubSystem) Q.toSubSystem = P.toSubSystem ∧
        l.foldl (fun F i => F.twist (L' i).toSubSystem) Q'.toSubSystem = P'.toSubSystem ∧
        RestrictData P.toSubSystem hxy P'.toSubSystem s := by
  intro l
  induction l with
  | nil =>
    intro Q Q' r h
    exact ⟨Q, Q', r, rfl, rfl, h⟩
  | cons i l ih =>
    intro Q Q' r h
    have htwist : ∃ s : Ω → K',
        RestrictData (Q.toSubSystem.twist (L i).toSubSystem) hxy
          (Q'.toSubSystem.twist (L' i).toSubSystem) s :=
      RestrictTwist.restrictData_twist (Q₁ := Q) (Q₂ := L i)
        (Q₁' := Q') (Q₂' := L' i) (hxy := hxy) (r₁ := r) (r₂ := rr i) h (hL i)
    obtain ⟨s, hs⟩ := htwist
    exact ih (Q.tensorProd (L i)) (Q'.tensorProd (L' i)) s hs

theorem proof (hRL : RestrLenRestrict.Statement.{u, w}) : InterNumRestrict.Statement.{u, w} := by
  intro k _ Ω _ _ N x K' _ _ y hxy hle pp n hsub L L' rr hL
  have hT : ∀ T : Finset (Fin n), ∀ᶠ c : ℕ in atTop,
      restrLen pp ((tensorSub (fun i => (L' i).toSubSystem) T).twist (twistSys k y (c : ℤ))) =
        restrLen pp ((tensorSub (fun i => (L i).toSubSystem) T).twist (twistSys k x (c : ℤ))) := by
    intro T
    obtain ⟨P, P', s, hP, hP', hs⟩ := inr_foldl_restrict L L' rr hL
      ((List.finRange n).filter (· ∈ T)) (twistBundle k x 0) (twistBundle k y 0)
      (RestrictTwist.twistRes k x y 0) (RestrictTwist.restrictData_twistSys hxy hle 0)
    have e1 : tensorSub (fun i => (L i).toSubSystem) T = P.toSubSystem := hP
    have e2 : tensorSub (fun i => (L' i).toSubSystem) T = P'.toSubSystem := hP'
    rw [e1, e2]
    exact hRL k Ω N x K' y hxy hle pp n hsub P P' s hs
  have hall : ∀ᶠ c : ℕ in atTop, interSum pp (fun i => (L' i).toSubSystem) c =
      interSum pp (fun i => (L i).toSubSystem) c := by
    filter_upwards [Filter.eventually_all.2 hT] with c hc
    unfold interSum
    exact Finset.sum_congr rfl fun T _ => by rw [hc T]
  unfold interNum limUnder
  rw [Filter.map_congr hall]

end InterNumRestrict

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepTwoReduce
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

theorem Cech.H_subsingleton {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type v}
    [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] (ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J)
    (h : ∀ I, Subsingleton (G I)) (i : ℕ) : Subsingleton (Cech.H G ρ i) := by
  have h2 : Subsingleton (Cech.Cochain G i) := by
    unfold Cech.Cochain; infer_instance
  unfold Cech.H
  refine Submodule.Quotient.subsingleton_iff.mpr (eq_top_iff.mpr fun z _ => ?_)
  have hz : z = 0 := Subtype.ext (h2.elim _ _)
  rw [hz]
  exact Submodule.zero_mem _

section Helpers

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]


omit [IsScalarTower S Ω E] in
theorem tildeSys_twist_mono {M M' : FinGradedSub (S := S) (x := x) E} (h : ∀ c, M.piece c ≤ M'.piece c)
    (Q : SubSystem S x Ω) (I : Chart x) :
    ((M.tildeSys 0).twist Q).sub I ≤ ((M'.tildeSys 0).twist Q).sub I := by
  refine Submodule.span_mono ?_
  rintro _ ⟨q, hq, y, hy, rfl⟩
  refine ⟨q, hq, y, ?_, rfl⟩
  change y ∈ M'.tilde 0 I
  change y ∈ M.tilde 0 I at hy
  refine Submodule.span_mono ?_ hy
  rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
  exact ⟨m, s, a, e, hs, hse, h a hm, hae, rfl⟩

theorem quotH_self_subsingleton (F : SubSystem S x E) (i : ℕ) :
    Subsingleton (SubSystem.quotH F F i) := by
  have h1 : ∀ I, Subsingleton (F.sub I ⧸ SubSystem.quotSub F F I) := fun I =>
    Submodule.Quotient.subsingleton_iff.mpr (eq_top_iff.mpr fun y _ => y.2)
  unfold SubSystem.quotH
  exact Cech.H_subsingleton _ h1 i

end Helpers

theorem StepTwo.Reduce.proof (hF : StepTwo.Filt.Statement.{u, v, w}) (hT : QuotTrans.Statement.{u, v, w})
    (hP : StepTwo.Piece.Statement.{u, v, w}) : StepTwo.Reduce.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ M₁ M₂ h21 J hJ
  obtain ⟨n, Nf, g, deg, pr, h0, hlast, hk⟩ := hF S Ω N x E M₁ M₂ h21 J hJ
  refine ⟨n, pr, fun i => -deg i, fun i => ⟨(hk i).1, (hk i).2.1, (hk i).2.2.1, (hk i).2.2.2.1⟩, ?_⟩
  intro Q c hQ
  have key : ∀ (m : ℕ) (hm : m < n + 1), (∀ a, (Nf 0).piece a ≤ (Nf ⟨m, hm⟩).piece a) ∧
      Subsingleton (SubSystem.quotH (((Nf ⟨m, hm⟩).tildeSys 0).twist (Q.twist (twistSys S x c)))
        (((Nf 0).tildeSys 0).twist (Q.twist (twistSys S x c))) 1) := by
    intro m
    induction m with
    | zero => intro _; exact ⟨fun _ => le_rfl, quotH_self_subsingleton _ 1⟩
    | succ m ih =>
      intro hm
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      obtain ⟨hpr, hhom, hprx, -, hg, hsup, hann⟩ := hk ⟨m, by omega⟩
      have hstep := hP S Ω N x E _ _ (g ⟨m, by omega⟩) (deg ⟨m, by omega⟩) (pr ⟨m, by omega⟩) hpr hhom
        hprx hg hsup hann Q c (fun hrel => by rw [sub_eq_add_neg]; exact hQ ⟨m, by omega⟩ hrel)
      have hle : ∀ a, (Nf ⟨m, by omega⟩).piece a ≤ (Nf ⟨m + 1, hm⟩).piece a := fun a => by
        rw [show (⟨m + 1, hm⟩ : Fin (n + 1)) = Fin.succ ⟨m, by omega⟩ from rfl, hsup a]
        exact le_sup_left
      exact ⟨fun a => (ih1 a).trans (hle a), hT S Ω N x E _ _ _ (tildeSys_twist_mono ih1 _)
        (tildeSys_twist_mono hle _) ih2 hstep⟩
  obtain ⟨-, h⟩ := key n (Nat.lt_succ_self n)
  rw [show (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n from rfl, hlast, h0] at h
  exact h

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleEmbedNumbers
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

theorem VeryAmpleEmbed.Numbers.proof (hSecs : VeryAmpleSecs.Statement.{u, w})
    (hHilb : VeryAmpleHilbert.Statement.{u, w}) : VeryAmpleEmbed.Numbers.Statement.{u, w} := by
  intro k _ Ω _ _ N y Q r h hV n hZ
  exact ⟨VeryAmpleDim.proof k Ω N y n Q r h hZ hV,
    VeryAmpleDegree.proof VeryAmpleDim.proof hSecs hHilb k Ω N y n Q r h hZ hV⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThreeOnW
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem StepThree.OnW.proof (hL : StepThree.OnW.Lift.Statement.{u, w})
    (hG : StepThree.OnW.Gen.Statement.{u, w}) : StepThree.OnW.Statement.{u, w} := by
  intro k _ Ω _ _ N x T hK pp hpp
  obtain ⟨c₁, h₁⟩ := hL k Ω N x T hK pp hpp
  obtain ⟨c₂, h₂⟩ := hG k Ω N x T hK pp hpp
  refine ⟨max c₁ c₂, fun b c hb hc I => ?_⟩
  refine (h₂ b c hb (le_of_max_le_right hc) I).trans (sup_le ?_ le_sup_right)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨s, hs, hcomp, rfl⟩
  obtain ⟨t, ht, hts⟩ := h₁ b c hb (le_of_max_le_left hc) s hs hcomp
  have he : s I = t - (t - s I) := by abel
  rw [SetLike.mem_coe, he]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.subset_span (SetLike.mem_coe.mpr ht)))
    (Submodule.mem_sup_right (hts I))

end

end GroundTheory.Heights₂.Heights.Kleiman
end
