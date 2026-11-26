module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryMovesSelfDualLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridTopVertexFramePointTransportLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthonormalBasisSplitSupportedAdelicPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthonormalBasisDefiniteHermitianSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthonormalBasisDefiniteHermitianSpace
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefiniteFrame

theorem exists_unitary_frame : ∀ (D : D7) (V : HSp D), V.SigOK → (∀ τ, V.sig τ = (V.rank, 0)) →
    ∃ fr : GL (Fin V.rank) D.host.E, Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 := by
  intro D V hs hp
  obtain ⟨b, hli, horth⟩ := GlobalTheory.DefiniteOrthonormal.landherrHasse D V hs hp
  have hsp : Submodule.span D.host.E (Set.range b) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli]
    simp [V.rank_eq]
  let B : Module.Basis (Fin V.rank) D.host.E V.V := Module.Basis.mk hli (by rw [hsp])
  have hB : ∀ a, B a = b a := fun a => by simp [B]
  let M : Matrix (Fin V.rank) (Fin V.rank) D.host.E := V.frame.toMatrix B
  let M' : Matrix (Fin V.rank) (Fin V.rank) D.host.E := B.toMatrix V.frame
  let fr : GL (Fin V.rank) D.host.E :=
    ⟨M, M', Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩
  refine ⟨fr, ?_⟩
  ext a c
  have key : V.hT (b a) (b c) = ∑ i, ∑ j, star (M i a) * V.gram i j * M j c := by
    rw [← hB a, ← hB c]
    conv_lhs => rw [← V.frame.sum_repr (B a), ← V.frame.sum_repr (B c)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, Finset.mul_sum, M, Module.Basis.toMatrix_apply, Formalism.BasicNotions.HSpace.gram]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [RingHom.id_apply]
    ring
  have lhs : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1) a c
      = ∑ i, ∑ j, star (M i a) * V.gram i j * M j c := by
    simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    rfl
  rw [lhs, ← key, horth, Matrix.one_apply]

end GlobalTheory.DefiniteFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthonormalBasisDefiniteHermitianSpaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthonormalBasis_definite_hermitianSpace : ∀ (D : D7) (V : HSp D), V.SigOK → (∀ τ, V.sig τ = (V.rank, 0)) →
    ∃ fr : GL (Fin V.rank) D.host.E, Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 := by
  first | exact @GlobalTheory.DefiniteFrame.exists_unitary_frame | exact GlobalTheory.DefiniteFrame.exists_unitary_frame | (intros; apply GlobalTheory.DefiniteFrame.exists_unitary_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentSupportHermitianDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatSmulLe
namespace GlobalTheory.NatMultipleIntegralSmulBound

open NumberField

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ m : ℕ, 0 < m ∧ ∃ b : RingOfIntegers E, (b : E) = (m : E) * a := by
  have ha : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hint⟩ := ha.exists_integral_multiple
  refine ⟨y.natAbs * y.natAbs, Nat.mul_pos (Int.natAbs_pos.2 hy) (Int.natAbs_pos.2 hy),
    ⟨y • (y • a), (mem_integralClosure_iff ℤ E).2 (hint.smul y)⟩, ?_⟩
  show y • (y • a) = ((y.natAbs * y.natAbs : ℕ) : E) * a
  rw [smul_smul, zsmul_eq_mul, ← Int.cast_natCast, Int.natAbs_mul_self]

theorem exists_nat_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L' : Submodule (RingOfIntegers E) (Fin n → E))
    (h : Submodule.span E (↑L' : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ c : ℕ, 0 < c ∧ (c : E) • x ∈ L' := by
  have key : ∀ x ∈ Submodule.span E (↑L' : Set (Fin n → E)), ∃ c : ℕ, 0 < c ∧ (c : E) • x ∈ L' := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
    | zero => exact ⟨1, one_pos, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, hcx⟩ := hx
      obtain ⟨d, hd, hdy⟩ := hy
      refine ⟨c * d, Nat.mul_pos hc hd, ?_⟩
      have e : ((c * d : ℕ) : E) • (x + y) = d • ((c : E) • x) + c • ((d : E) • y) := by
        rw [smul_add, ← Nat.cast_smul_eq_nsmul E d, ← Nat.cast_smul_eq_nsmul E c, smul_smul, smul_smul,
          Nat.cast_mul, mul_comm (d : E)]
      rw [e]
      exact L'.add_mem (L'.nsmul_mem hcx d) (L'.nsmul_mem hdy c)
    | smul e x _ hx =>
      obtain ⟨c, hc, hcx⟩ := hx
      obtain ⟨m, hm, b, hb⟩ := exists_nat_mul_integral e
      refine ⟨m * c, Nat.mul_pos hm hc, ?_⟩
      have e' : ((m * c : ℕ) : E) • (e • x) = (b : E) • ((c : E) • x) := by
        rw [hb, smul_smul, smul_smul, Nat.cast_mul]
        congr 1
        ring
      have hb' : (b : E) • ((c : E) • x) = b • ((c : E) • x) := algebraMap_smul E b _
      rw [e', hb']
      exact L'.smul_mem b hcx
  exact key x (h ▸ Submodule.mem_top)

theorem exists_nat_smul_le {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L L' : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.FG L)
    (h : Submodule.span E (↑L' : Set (Fin n → E)) = ⊤) :
    ∃ (c : ℕ), (0 : ℕ) < c ∧ ∀ x ∈ L, (↑c : E) • x ∈ L' := by
  classical
  obtain ⟨s, rfl⟩ := hL
  have hs : ∃ c : ℕ, 0 < c ∧ ∀ x ∈ s, (c : E) • x ∈ L' := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_pos, by simp⟩
    | @insert a s _ ih =>
      obtain ⟨c, hc, hcs⟩ := ih
      obtain ⟨d, hd, hda⟩ := exists_nat_smul_mem L' h a
      refine ⟨c * d, Nat.mul_pos hc hd, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · have e : ((c * d : ℕ) : E) • x = c • ((d : E) • x) := by
          rw [← Nat.cast_smul_eq_nsmul E c, smul_smul, Nat.cast_mul]
        rw [e]
        exact L'.nsmul_mem hda c
      · have e : ((c * d : ℕ) : E) • x = d • ((c : E) • x) := by
          rw [← Nat.cast_smul_eq_nsmul E d, smul_smul, Nat.cast_mul, mul_comm]
        rw [e]
        exact L'.nsmul_mem (hcs x hx) d
  obtain ⟨c, hc, hcs⟩ := hs
  refine ⟨c, hc, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact hcs x hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact L'.add_mem hx hy
  | smul b x _ hx =>
    rw [Nat.cast_smul_eq_nsmul] at hx ⊢
    rw [smul_comm]
    exact L'.smul_mem b hx

end GlobalTheory.NatMultipleIntegralSmulBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentSupportHermitianDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FunObj.StdReps

section General

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem exists_nat_smul_mem (L L' : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG)
    (hsp : Submodule.span E (L' : Set (Fin n → E)) = ⊤) :
    ∃ c : ℕ, 0 < c ∧ ∀ x ∈ L, (c : E) • x ∈ L' := by
  first
  | exact @_root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le
  | exact _root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le
  | (apply _root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le ..)

theorem fg_colLat (B : GL (Fin n) E) : (colLat B).FG :=
  Submodule.fg_span (Set.finite_range _)

theorem span_colLat (B : GL (Fin n) E) : Submodule.span E (colLat B : Set (Fin n → E)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x = ∑ j, ((B⁻¹).1 *ᵥ x) j • (fun a : Fin n => (B : Matrix (Fin n) (Fin n) E) a j) := by
    have e : x = B.1 *ᵥ ((B⁻¹).1 *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    conv_lhs => rw [e]
    funext a
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hx]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact Submodule.subset_span ⟨j, rfl⟩

end General

variable {D : D7}

def stabGL {R : Type} [CommRing R] {m : ℕ} (H : Set (Fin m → R)) : Subgroup (GL (Fin m) R) where
  carrier := {g | ∀ v, v ∈ H ↔ g.1 *ᵥ v ∈ H}
  one_mem' := fun v => by rw [Units.val_one, Matrix.one_mulVec]
  mul_mem' := fun {a b} ha hb v => by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hb v).trans (ha _)
  inv_mem' := fun {a} ha v => by
    have := ha ((a⁻¹).1 *ᵥ v)
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this
    exact this.symm

def stabG (V : HSp D) (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Subgroup (GA D V) :=
  (stabGL (Formalism.L2.Herm.hatL (F := D.host.F) M : Set (Fin V.rank → Formalism.IndefR.Lev.EAf D))).comap (Formalism.IndefR.Lev.finE V)


set_option maxHeartbeats 1000000 in
theorem mulVec_mem_of_finCong (V : HSp D) (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (c : ℕ) (hc : 0 < c)
    (h1 : ∀ x ∈ M, (c : D.host.E) • x ∈ GlobalTheory.Member.latC V)
    (h2 : ∀ x ∈ GlobalTheory.Member.latC V, (c : D.host.E) • x ∈ M) (a : GA D V) (ha : GlobalTheory.Member.FinCong V (c * c) a) :
    ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) M,
      (Formalism.IndefR.Lev.finE V a).1 *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) M := by
  have hl := (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  have hcong : ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.Member.latC V),
      ∃ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.Member.latC V),
        (Formalism.IndefR.Lev.finE V a).1 *ᵥ z - z = (c * c) • y := by
    unfold GlobalTheory.Member.FinCong at ha
    rw [hl] at ha
    exact GlobalTheory.PrincInLevel.cong_swap _ _ _ ha
  intro z hz
  obtain ⟨y, hy, e⟩ := hcong _ (GlobalTheory.LevSplit.hatL_smul _ _ c h1 z hz)
  have hcE : IsUnit (c : D.host.E) := (Nat.cast_ne_zero.2 hc.ne').isUnit
  have hu : IsUnit (c : Formalism.IndefR.Lev.EAf D) := by
    have := hcE.map (eToEAf D)
    rwa [map_natCast] at this
  have e2 : (Formalism.IndefR.Lev.finE V a).1 *ᵥ z - z = (c : Formalism.IndefR.Lev.EAf D) • y := by
    refine (hu.smul_left_cancel).1 ?_
    rw [smul_sub, ← Matrix.mulVec_smul, e, ← Nat.cast_smul_eq_nsmul (Formalism.IndefR.Lev.EAf D), Nat.cast_mul, mul_smul]
  rw [sub_eq_iff_eq_add'] at e2
  rw [e2]
  exact Submodule.add_mem _ hz (GlobalTheory.LevSplit.hatL_smul _ _ c h2 y hy)


set_option maxHeartbeats 1000000 in
theorem mem_stabG_of_finCong (V : HSp D) (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (c : ℕ) (hc : 0 < c)
    (h1 : ∀ x ∈ M, (c : D.host.E) • x ∈ GlobalTheory.Member.latC V)
    (h2 : ∀ x ∈ GlobalTheory.Member.latC V, (c : D.host.E) • x ∈ M) (a : GA D V) (ha : GlobalTheory.Member.FinCong V (c * c) a) :
    a ∈ stabG V M := by
  intro v
  refine ⟨mulVec_mem_of_finCong V M c hc h1 h2 a ha v, fun hv => ?_⟩
  have := mulVec_mem_of_finCong V M c hc h1 h2 a⁻¹ (GlobalTheory.Member.PrincLevel.finCong_inv ha) _ hv
  rwa [map_inv, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this


set_option maxHeartbeats 4000000 in
theorem exists_rep_std : ∀ (D : D7) (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (S : Finset ℕ), (∀ q ∈ S, q.Prime) →
    ∀ x : GA D V, x ∈ GfC V →
    ∃ (γ : GL (Fin V.rank) D.host.E) (h k : GA D V),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1 * V.gram * γ.1 = V.gram ∧ h ∈ GfC V ∧
      (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V h ∧ ∀ w ∈ P, Off S w) ∧
      k ∈ GfC V ∧ (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
        (Formalism.IndefR.Lev.finE V k).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) ∧
      (Formalism.IndefR.Lev.finE V x).1 = γ.1.map (eToEAf D) * (Formalism.IndefR.Lev.finE V h).1 * (Formalism.IndefR.Lev.finE V k).1 := by
  intro D V fr S hS x hx
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨c1, hc1, h1⟩ := exists_nat_smul_mem (colLat fr) (GlobalTheory.Member.latC V) (fg_colLat fr) hsp
  obtain ⟨c2, hc2, h2⟩ := exists_nat_smul_mem (GlobalTheory.Member.latC V) (colLat fr) hfg (span_colLat fr)
  have h1' : ∀ y ∈ colLat fr, ((c1 * c2 : ℕ) : D.host.E) • y ∈ GlobalTheory.Member.latC V := fun y hy => by
    rw [Nat.cast_mul, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul D.host.E c2]
    exact (GlobalTheory.Member.latC V).toAddSubmonoid.nsmul_mem (h1 y hy) c2
  have h2' : ∀ y ∈ GlobalTheory.Member.latC V, ((c1 * c2 : ℕ) : D.host.E) • y ∈ colLat fr := fun y hy => by
    rw [Nat.cast_mul, mul_smul, Nat.cast_smul_eq_nsmul D.host.E c1]
    exact (colLat fr).toAddSubmonoid.nsmul_mem (h2 y hy) c1
  have hc : 0 < c1 * c2 := Nat.mul_pos hc1 hc2
  let J' : Subgroup (Formalism.IndefR.Bridge.Gf V) := (GfC V ⊓ stabG V (colLat fr)).map (finHom V).rangeRestrict
  have hK : ∀ k ∈ GfC V, GlobalTheory.Member.FinCong V ((c1 * c2) * (c1 * c2)) k → Formalism.IndefR.FWT.fin V k ∈ J' :=
    fun k hk hck => ⟨k, ⟨hk, mem_stabG_of_finCong V (colLat fr) _ hc h1' h2' k hck⟩, rfl⟩
  have hbad : 0 < ∏ q ∈ S, q := Finset.prod_pos fun q hq => (hS q hq).pos
  obtain ⟨h, ⟨hh, hs⟩, γ, k, e⟩ :=
    GlobalTheory.SplitReps.exists_split_rep V (Nat.mul_pos hc hc) hK hbad (Formalism.IndefR.FWT.fin V x)
  obtain ⟨k0, ⟨hk0, hk0s⟩, hk0e⟩ := Subgroup.mem_map.1 k.2
  obtain ⟨-, e0, P, he0, hP, hsupp⟩ := GlobalTheory.SplitReps.splitOffBad_of_suppSplit V _ h hh hs
  obtain ⟨γE, hU, hγ⟩ := γ.2
  have hm : matHom V γ.1 = Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γE := hγ.symm
  have hfγ : finHom V γ.1 = Formalism.UG.bc (inclR (F := D.host.F) (Af D.host.F)) γE := by
    rw [finHom, MonoidHom.comp_apply, hm]
    exact GlobalTheory.HLatMove.bc_map_bc_inclR _ _
  have ef : finHom V x = finHom V γ.1 * finHom V h * finHom V k0 := by
    have := congrArg Subtype.val e
    rw [← hk0e] at this
    exact this
  refine ⟨γE, h, k0, hU, hh, ⟨P, e0, he0, hsupp, fun w hw q hq hqw => hP w hw ?_⟩, hk0, hk0s, ?_⟩
  · obtain ⟨m, hm'⟩ := Finset.dvd_prod_of_mem (fun q : ℕ => q) hq
    rw [hm', Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hqw
  · have eE : Formalism.IndefR.Lev.finE V x = Formalism.IndefR.Lev.finE V γ.1 * Formalism.IndefR.Lev.finE V h * Formalism.IndefR.Lev.finE V k0 := by
      simp only [Formalism.IndefR.Lev.finE, MonoidHom.comp_apply, ef, map_mul]
    have eγ : (Formalism.IndefR.Lev.finE V γ.1).1 = γE.1.map (eToEAf D) := by
      simp only [Formalism.IndefR.Lev.finE, MonoidHom.comp_apply, hfγ]
      ext i j
      rfl
    rw [eE, Units.val_mul, Units.val_mul, eγ]

end GlobalTheory.FunObj.StdReps
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentSupportHermitianDecompositionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_support_hermitian_decomposition : ∀ (D : D7) (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (S : Finset ℕ), (∀ q ∈ S, q.Prime) →
    ∀ x : GA D V, x ∈ GfC V →
    ∃ (γ : GL (Fin V.rank) D.host.E) (h k : GA D V),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1 * V.gram * γ.1 = V.gram ∧ h ∈ GfC V ∧
      (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V h ∧ ∀ w ∈ P, Off S w) ∧
      k ∈ GfC V ∧ (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
        (Formalism.IndefR.Lev.finE V k).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) ∧
      (Formalism.IndefR.Lev.finE V x).1 = γ.1.map (eToEAf D) * (Formalism.IndefR.Lev.finE V h).1 * (Formalism.IndefR.Lev.finE V k).1 := by
  first | exact @GlobalTheory.FunObj.StdReps.exists_rep_std | exact GlobalTheory.FunObj.StdReps.exists_rep_std | (intros; apply GlobalTheory.FunObj.StdReps.exists_rep_std <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthonormalBasisSplitSupportedAdelicPoint
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FunObj.StdVertex


set_option maxHeartbeats 6000000 in
theorem exists_std_vertex : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), V.SigOK →
    (∀ τ, V.sig τ = (V.rank, 0)) → IsSelfDualC V Λ → ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) →
    ∃ (fr : GL (Fin V.rank) D.host.E) (u : GfC V),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 ∧
      (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V u.1 ∧ ∀ w ∈ P, Off S w) ∧
      ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
        (Formalism.IndefR.Lev.finE V u.1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  intro D V Λ hsig hpos hΛ S hS
  obtain ⟨fr0, hfr0⟩ := GlobalTheory.T.exists_orthonormalBasis_definite_hermitianSpace D V hsig hpos
  obtain ⟨x, hxx⟩ := GlobalTheory.T.exists_finiteAdelicUnitary_moves_selfDualLattice D V fr0 Λ hfr0 hΛ
  have hx : x ∈ GfC V := hxx.1
  have hxL := hxx.2
  obtain ⟨γ, h, k, hr⟩ := GlobalTheory.T.idempotent_support_hermitian_decomposition D V fr0 S hS x hx
  have hγ := hr.1
  have hh := hr.2.1
  have hsupp := hr.2.2.1
  have hkL := hr.2.2.2.2.1
  have hxe := hr.2.2.2.2.2
  obtain ⟨u, hur⟩ := GlobalTheory.T.rationalUnitary_conj_splitSupported_finiteAdelicPoint D V S γ h hγ hh hsupp
  have hu : u ∈ GfC V := hur.1
  have hue := hur.2.2
  refine ⟨γ * fr0, ⟨u, hu⟩, ?_, hur.2.1, ?_⟩
  · have e1 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (γ * fr0).1 =
        Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr0.1 * Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1 := by
      simp only [Formalism.UG.cT, Units.val_mul, Matrix.map_mul, Matrix.transpose_mul]
    rw [e1, Units.val_mul]
    calc _ = Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr0.1 *
          (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1 * V.gram * γ.1) * fr0.1 := by
            simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hγ, hfr0]
  · intro v
    have hγγ : γ.1.map (eToEAf D) * (γ⁻¹).1.map (eToEAf D) = 1 := by
      rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    have hKK : (Formalism.IndefR.Lev.finE V k).1 * ((Formalism.IndefR.Lev.finE V k)⁻¹).1 = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h1 : ∀ w, w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr0) ↔
        ((Formalism.IndefR.Lev.finE V k)⁻¹).1 *ᵥ w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr0) := fun w => by
      rw [hkL (((Formalism.IndefR.Lev.finE V k)⁻¹).1 *ᵥ w), Matrix.mulVec_mulVec, hKK, Matrix.one_mulVec]
    have key : (Formalism.IndefR.Lev.finE V x).1 *ᵥ (((Formalism.IndefR.Lev.finE V k)⁻¹).1 *ᵥ ((γ⁻¹).1.map (eToEAf D) *ᵥ v)) =
        (Formalism.IndefR.Lev.finE V u).1 *ᵥ v := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hxe, hue]
      congr 1
      calc _ = γ.1.map (eToEAf D) * (Formalism.IndefR.Lev.finE V h).1 *
            ((Formalism.IndefR.Lev.finE V k).1 * ((Formalism.IndefR.Lev.finE V k)⁻¹).1) * (γ⁻¹).1.map (eToEAf D) := by
              simp only [Matrix.mul_assoc]
        _ = _ := by rw [hKK, Matrix.mul_one]
    have s1 := GlobalTheory.T.mem_completedLattice_columnLattice_mul_iff D γ fr0 v
    have s2 := h1 ((γ⁻¹).1.map (eToEAf D) *ᵥ v)
    have s3 := hxL (((Formalism.IndefR.Lev.finE V k)⁻¹).1 *ᵥ ((γ⁻¹).1.map (eToEAf D) *ᵥ v))
    rw [key] at s3
    exact s1.trans (s2.trans s3)

end GlobalTheory.FunObj.StdVertex
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthonormalBasisSplitSupportedAdelicPointStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthonormalBasis_splitSupported_adelicPoint : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), V.SigOK →
    (∀ τ, V.sig τ = (V.rank, 0)) → IsSelfDualC V Λ → ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) →
    ∃ (fr : GL (Fin V.rank) D.host.E) (u : GfC V),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 ∧
      (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V u.1 ∧ ∀ w ∈ P, Off S w) ∧
      ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
        (Formalism.IndefR.Lev.finE V u.1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  first | exact @GlobalTheory.FunObj.StdVertex.exists_std_vertex | exact GlobalTheory.FunObj.StdVertex.exists_std_vertex | (intros; apply GlobalTheory.FunObj.StdVertex.exists_std_vertex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridTopVertexFramePointTransportLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridTopVertex_frame_point_transport_lattice : ∀ (D : D7) (T : Type) (L : LevCh D T) (sc : Consts) (G : GridData L sc) (S : Finset ℕ)
    (fr₀ : GL (Fin (G.V (.grid D.R.m D.R.m)).rank) D.host.E) (u₀ : FinPt G (.grid D.R.m D.R.m)),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr₀.1 * (G.V (.grid D.R.m D.R.m)).gram * fr₀.1 = 1 →
    (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e _ u₀.1 ∧ ∀ w ∈ P, Off S w) →
    (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr₀) ↔
        (Formalism.IndefR.Lev.finE (G.V (.grid D.R.m D.R.m)) u₀.1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.grid D.R.m D.R.m))) →
    ∃ (fr : GL (Fin (G.V (.top D.R.m)).rank) D.host.E) (u : FinPt G (.top D.R.m)),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * (G.V (.top D.R.m)).gram * fr.1 = 1 ∧
      (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e _ u.1 ∧ ∀ w ∈ P, Off S w) ∧
      (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
        (Formalism.IndefR.Lev.finE (G.V (.top D.R.m)) u.1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.top D.R.m))) ∧
      (∀ i (k : Fin (G.V (.grid D.R.m D.R.m)).rank), fr.1 i (Formalism.L2.Col.Br.iC G.sp.topDec.rank.symm k) =
        (frameMat _ _ G.sp.topDec.ι * fr₀.1) i k) ∧
      (∀ i, fr.1 i (Formalism.L2.Col.Br.iL G.sp.topDec.rank.symm) = G.sp.topDec.a i 0) ∧
      HMul.hMul (mt (G.V (.top D.R.m)) u.1) (topEmb G) = HMul.hMul (topEmb G) (mt (G.V (.grid D.R.m D.R.m)) u₀.1) ∧
      mt (G.V (.top D.R.m)) u.1 *ᵥ topVec G = topVec G := by
  first | exact @GlobalTheory.FunObj.top_transport | exact GlobalTheory.FunObj.top_transport | (intros; apply GlobalTheory.FunObj.top_transport <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterUnramifiedOffFinitePrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterUnramifiedOffFinitePrimes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnrOff

theorem natCast_not_mem {D : D7} {S : Finset ℕ} {w : Pl D.host.E} (hw : Off S w) {N : ℕ} (hN : 0 < N)
    (hS : N.primeFactors ⊆ S) : ((N : 𝓞 D.host.E)) ∉ w.asIdeal := by
  intro h
  rw [← Nat.prod_factorization_pow_eq_self hN.ne', Nat.cast_finsuppProd] at h
  obtain ⟨p, hp, hpw⟩ := (Ideal.IsPrime.prod_mem_iff (hp := w.isPrime)).1 h
  dsimp only at hpw
  rw [Nat.cast_pow] at hpw
  exact hw p (hS (Nat.support_factorization N ▸ hp)) (w.isPrime.mem_of_pow_mem _ hpw)

theorem infPart_idem {D : D7} {e : AE D} (he : Formalism.L2.Theta.IsSplitIdem D e) : infPart D e = 0 := by
  obtain ⟨hee, hec, v, ε, ⟨α, hε, -, -⟩, hs⟩ := he
  have h1 : e = e * algebraMap (AF D.host.F) (AE D) ε := by
    rw [← hs, mul_add, hee, hec, add_zero]
  have h2 : infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
    subst hε
    have e1 : (algebraMap (AF D.host.F) (AE D)) (pairA D.host.F 0 α) = (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
    rw [e1]
    simp only [infPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
    exact TensorProduct.zero_tmul _ _
  rw [h1, map_mul, h2, mul_zero]

theorem intAE_one {D : D7} : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D := by
  apply AddSubgroup.subset_closure
  exact ⟨1, fun w => by rw [map_one]; exact one_mem _, 1, by simp [Algebra.TensorProduct.one_def]⟩

theorem intAE_mul {D : D7} {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  induction hx using AddSubgroup.closure_induction with
  | mem x h =>
    obtain ⟨a, ha, s, rfl⟩ := h
    induction hy using AddSubgroup.closure_induction with
    | mem y h' =>
      obtain ⟨b, hb, t, rfl⟩ := h'
      refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, s * t, ?_⟩
      · rw [map_mul]; exact mul_mem (ha w) (hb w)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]; push_cast; rfl
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
    | neg y _ h1 => rw [mul_neg]; exact neg_mem h1
  | zero => rw [zero_mul]; exact zero_mem _
  | add x z _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | neg x _ h1 => rw [neg_mul]; exact neg_mem h1

theorem unr_off : ∀ (D : D7) (c : (AE D)ˣ →* Circle), Continuous c →
    ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime) ∧ ∀ w : Pl D.host.E, Off S w → ∀ e, Formalism.L2.NTheta.IsIdemAt e w → UnrIdem c e := by
  intro D c hc
  obtain ⟨N, hN, hN1, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D c hc
  refine ⟨N.primeFactors, fun q hq => Nat.prime_of_mem_primeFactors hq, ?_⟩
  intro w hw e he x hx h1 h2
  have hNw := natCast_not_mem hw hN le_rfl
  have hN0 : ((N : 𝓞 D.host.E)) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hg : finPart D (e * incA D (((N : 𝓞 D.host.E) : D.host.E))⁻¹) ∈ intAE D :=
    not_not.1 ((he.2 _ hN0).not.1 hNw)
  have hNE : (((N : 𝓞 D.host.E) : D.host.E)) ≠ 0 := by exact_mod_cast hN.ne'
  have hi : (N : AE D) * incA D (((N : 𝓞 D.host.E) : D.host.E))⁻¹ = 1 := by
    rw [show (N : AE D) = incA D (((N : 𝓞 D.host.E) : D.host.E)) by simp, ← map_mul, mul_inv_cancel₀ hNE, map_one]
  have key : (x : AE D) - 1 = (N : AE D) * (e * incA D (((N : 𝓞 D.host.E) : D.host.E))⁻¹ * ((x : AE D) - 1)) := by
    linear_combination (-1 : AE D) * hx - (e * ((x : AE D) - 1)) * hi
  refine hN1 x ⟨?_, h1, h2⟩ ⟨finPart D (e * incA D (((N : 𝓞 D.host.E) : D.host.E))⁻¹) * (finPart D (x : AE D) - 1),
    intAE_mul hg (sub_mem h1 intAE_one), ?_⟩
  · have h0 := infPart_idem he.1
    have := congrArg (infPart D) hx
    simp only [RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_sub, RingHom.map_one, h0, zero_mul, zero_add, sub_zero] at this
    exact this.symm
  · have := congrArg (finPart D) key
    simp only [RingHom.map_sub, RingHom.map_one, RingHom.map_mul, map_natCast] at this
    rw [nsmul_eq_mul]
    refine this.trans ?_
    simp only [RingHom.map_mul, map_natCast]

end GlobalTheory.UnrOff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterUnramifiedOffFinitePrimesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_unramified_off_finite_primes : ∀ (D : D7) (c : (AE D)ˣ →* Circle), Continuous c →
    ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime) ∧ ∀ w : Pl D.host.E, Off S w → ∀ e, Formalism.L2.NTheta.IsIdemAt e w → UnrIdem c e := by
  first | exact @GlobalTheory.UnrOff.unr_off | exact GlobalTheory.UnrOff.unr_off | (intros; apply GlobalTheory.UnrOff.unr_off <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePrimeSetAvoidingGridPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePrimeSetAvoidingGridPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FunObj

theorem exists_primeFactor_mem_of_natCast_mem {D : D7} (w : Pl D.host.E) {M : ℕ} (hM : M ≠ 0)
    (h : (M : 𝓞 D.host.E) ∈ w.asIdeal) : ∃ p ∈ M.primeFactors, (p : 𝓞 D.host.E) ∈ w.asIdeal := by
  have e := Nat.prod_factorization_pow_eq_self hM
  rw [← e, Finsupp.prod, Nat.cast_prod] at h
  obtain ⟨p, hp, hmem⟩ := (Ideal.IsPrime.prod_mem_iff (hp := w.isPrime)).1 h
  refine ⟨p, by simpa [Nat.support_factorization] using hp, ?_⟩
  rw [Nat.cast_pow] at hmem
  exact w.isPrime.mem_of_pow_mem _ hmem

theorem natCast_mem_of_under_eq {D : D7} (w : Pl D.host.E) {v : Pl D.host.F} (h : w.under (𝓞 D.host.F) = v) (n : ℕ)
    (hn : (n : 𝓞 D.host.F) ∈ v.asIdeal) : (n : 𝓞 D.host.E) ∈ w.asIdeal := by
  subst h
  have : (n : 𝓞 D.host.F) ∈ w.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := hn
  rw [Ideal.mem_comap, map_natCast] at this
  exact this

theorem exists_std_primes : ∀ (D : D7) (T : Type) (L : LevCh D T) (sc : Consts) (G : GridData L sc) (U : Set T), U.Finite →
    ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime) ∧ ∀ w : Pl D.host.E, Off S w → w.under (𝓞 D.host.F) ∉ G.pl.S0 ∧
      (∀ t ∈ U, ∀ w' ∈ L.Q t, w.under (𝓞 D.host.F) ≠ w'.under (𝓞 D.host.F)) ∧
      ((D.host.QS * D.host.q * D.host.d * D.host.g 0 * D.host.g 1 * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  intro D T L sc G U hU
  set N : ℕ := D.host.QS * D.host.q * D.host.d * D.host.g 0 * D.host.g 1 * Ideal.absNorm D.host.ccK with hN
  set A : ℕ := ∏ v ∈ G.pl.S0, Ideal.absNorm v.asIdeal with hA
  set B : ℕ := ∏ t ∈ hU.toFinset, ∏ w' ∈ L.Q t, Ideal.absNorm (w'.under (𝓞 D.host.F)).asIdeal with hB
  have hN0 : N ≠ 0 := by
    have h1 := D.host.hyp.1.ne_zero
    have h2 := D.host.hyp.2.1.ne_zero
    have h3 := (D.host.g_prime 0).ne_zero
    have h4 := (D.host.g_prime 1).ne_zero
    have h5 : Ideal.absNorm D.host.ccK ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
    have h0 : D.host.QS ≠ 0 := D.host.QS_pos.ne'
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h0 h1) h2) h3) h4) h5
  have hA0 : A ≠ 0 := by
    rw [hA, Finset.prod_ne_zero_iff]
    intro v _
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hB0 : B ≠ 0 := by
    rw [hB, Finset.prod_ne_zero_iff]
    intro t _
    rw [Finset.prod_ne_zero_iff]
    intro w' _
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact (w'.under (𝓞 D.host.F)).ne_bot
  have hM0 : N * A * B ≠ 0 := mul_ne_zero (mul_ne_zero hN0 hA0) hB0
  refine ⟨(N * A * B).primeFactors, fun p hp => Nat.prime_of_mem_primeFactors hp, ?_⟩
  intro w hw
  have key : ∀ n : ℕ, n ∣ N * A * B → (n : 𝓞 D.host.E) ∉ w.asIdeal := by
    intro n hn hmem
    obtain ⟨k, hk⟩ := hn
    have hM : ((N * A * B : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
      rw [hk, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hmem
    obtain ⟨p, hp, hpm⟩ := exists_primeFactor_mem_of_natCast_mem w hM0 hM
    exact hw p hp hpm
  refine ⟨fun hv => ?_, fun t ht w' hw' heq => ?_, key N (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)⟩
  · apply key (Ideal.absNorm (w.under (𝓞 D.host.F)).asIdeal)
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hv) _) _
    · exact natCast_mem_of_under_eq w rfl _ (Ideal.absNorm_mem _)
  · apply key (Ideal.absNorm (w'.under (𝓞 D.host.F)).asIdeal)
    · exact dvd_mul_of_dvd_right ((Finset.dvd_prod_of_mem (fun w'' : Pl D.host.E => Ideal.absNorm (w''.under (𝓞 D.host.F)).asIdeal) hw').trans
        (Finset.dvd_prod_of_mem (fun t => ∏ w'' ∈ L.Q t, Ideal.absNorm (w''.under (𝓞 D.host.F)).asIdeal)
          (hU.mem_toFinset.2 ht))) _
    · exact natCast_mem_of_under_eq w heq _ (Ideal.absNorm_mem _)

end GlobalTheory.FunObj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePrimeSetAvoidingGridPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_primeSet_avoiding_gridPlaces : ∀ (D : D7) (T : Type) (L : LevCh D T) (sc : Consts) (G : GridData L sc) (U : Set T), U.Finite →
    ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime) ∧ ∀ w : Pl D.host.E, Off S w → w.under (𝓞 D.host.F) ∉ G.pl.S0 ∧
      (∀ t ∈ U, ∀ w' ∈ L.Q t, w.under (𝓞 D.host.F) ≠ w'.under (𝓞 D.host.F)) ∧
      ((D.host.QS * D.host.q * D.host.d * D.host.g 0 * D.host.g 1 * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  first | exact @GlobalTheory.FunObj.exists_std_primes | exact GlobalTheory.FunObj.exists_std_primes | (intros; apply GlobalTheory.FunObj.exists_std_primes <;> assumption)
end
end

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FunObj

theorem defNode_isV {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (μ0 : T) (hL : L.Is μ0)
    (X : Node) (hX : DefNode D.R.m X) : (G.node X).IsV (X.rank D) 0 := by
  rcases X with ⟨i, j⟩ | i | j
  · obtain ⟨hi, rfl⟩ := hX
    rcases i with _ | i
    · have h := colY_isV D T L μ0 hL D.R.m le_rfl
      rw [Nat.sub_self, Nat.zero_div] at h
      exact h
    · have h := G.isV (X := .grid (i + 1) D.R.m) ⟨hi, le_rfl⟩ (fun j h => by cases h)
      simp only [Node.neg, Nat.sub_self, Nat.zero_div] at h
      exact h
  · exact absurd hX id
  · exact G.isV (X := .top j) hX (fun j' h => by cases h)

theorem unrIdem_mul {D : D7} {a b : (AE D)ˣ →* Circle} {e : AE D} (ha : UnrIdem a e) (hb : UnrIdem b e) :
    UnrIdem (a * b) e := fun x h1 h2 h3 => by
  rw [MonoidHom.mul_apply, ha x h1 h2 h3, hb x h1 h2 h3, one_mul]

theorem off_mono {D : D7} {S S' : Finset ℕ} (h : S ⊆ S') {w : Pl D.host.E} (hw : Off S' w) : Off S w :=
  fun q hq => hw q (h hq)


set_option maxHeartbeats 2000000 in
theorem exists_std {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (μ0 : T) (hL : L.Is μ0)
    (U : Set T) (hU : U.Finite) : Nonempty (Std G U) := by
  classical
  obtain ⟨S₁, hS₁p, hS₁⟩ := GlobalTheory.T.exists_finite_primeSet_avoiding_gridPlaces D T L sc G U hU
  have key : ∀ c : (AE D)ˣ →* Circle, ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime) ∧
      (Continuous c → ∀ w : Pl D.host.E, Off S w → ∀ e, Formalism.L2.NTheta.IsIdemAt e w → UnrIdem c e) := fun c => by
    by_cases hc : Continuous c
    · obtain ⟨S, h1, h2⟩ := GlobalTheory.T.character_unramified_off_finite_primes D c hc
      exact ⟨S, h1, fun _ => h2⟩
    · exact ⟨∅, by simp, fun h => absurd h hc⟩
  choose Sc hScp hSc using key
  set S : Finset ℕ := S₁ ∪ (Finset.range (D.R.m + 1)).biUnion (fun j => Sc (L.mu0 j)) ∪
    hU.toFinset.biUnion (fun t => Sc (L.xi t)) with hSdef
  have hSp : ∀ q ∈ S, q.Prime := by
    intro q hq
    simp only [hSdef, Finset.mem_union, Finset.mem_biUnion] at hq
    rcases hq with (hq | ⟨j, -, hq⟩) | ⟨t, -, hq⟩
    · exact hS₁p q hq
    · exact hScp _ q hq
    · exact hScp _ q hq
  have hsub1 : S₁ ⊆ S := fun q hq => by simp [hSdef, hq]
  have hsubμ : ∀ j, j ≤ D.R.m → Sc (L.mu0 j) ⊆ S := fun j hj q hq => by
    simp only [hSdef, Finset.mem_union, Finset.mem_biUnion, Finset.mem_range]
    exact Or.inl (Or.inr ⟨j, by omega, hq⟩)
  have hsubξ : ∀ t ∈ U, Sc (L.xi t) ⊆ S := fun t ht q hq => by
    simp only [hSdef, Finset.mem_union, Finset.mem_biUnion, Set.Finite.mem_toFinset]
    exact Or.inr ⟨t, ht, hq⟩
  have hcμ : ∀ j, 1 ≤ j → j ≤ D.R.m → Continuous (L.mu0 j) := fun j h1 h2 => by
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact (hL.mu0 ⟨k, by omega⟩).1.1
  have hV : ∀ X, DefNode D.R.m X → ∃ (fr : GL (Fin (G.V X).rank) D.host.E) (u : FinPt G X),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * (G.V X).gram * fr.1 = 1 ∧
      (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e _ u.1 ∧ ∀ w ∈ P, Off S w) ∧
      ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
        (Formalism.IndefR.Lev.finE (G.V X) u.1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ X) := by
    intro X hX
    have h := defNode_isV G μ0 hL X hX
    exact GlobalTheory.T.exists_orthonormalBasis_splitSupported_adelicPoint D (G.V X) (G.Λ X) h.sigOK (fun τ => by rw [h.sig τ, h.rank, Nat.sub_zero]) h.sd S hSp
  choose fr0 u0 h0 using hV
  have hmm : DefNode D.R.m (.grid D.R.m D.R.m) := ⟨le_rfl, rfl⟩
  obtain ⟨frT, uT, hT1, hT2, hT3, hT4, hT5, hT6, hT7⟩ :=
    GlobalTheory.T.gridTopVertex_frame_point_transport_lattice D T L sc G S (fr0 _ hmm) (u0 _ hmm) (h0 _ hmm).1 (h0 _ hmm).2.1 (h0 _ hmm).2.2
  have hne : (Node.grid D.R.m D.R.m) ≠ Node.top D.R.m := fun h => by cases h
  obtain ⟨fr, frt, hfr⟩ : ∃ fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E, fr (.top D.R.m) = frT ∧
      ∀ X (hX : DefNode D.R.m X), X ≠ .top D.R.m → fr X = fr0 X hX :=
    ⟨Function.update (fun X => if h : DefNode D.R.m X then fr0 X h else 1) (.top D.R.m) frT,
      Function.update_self _ _ _, fun X hX hXt => by rw [Function.update_of_ne hXt, dite_eq_left hX]⟩
  obtain ⟨u, ut, hu⟩ : ∃ u : ∀ X : Node, FinPt G X, u (.top D.R.m) = uT ∧
      ∀ X (hX : DefNode D.R.m X), X ≠ .top D.R.m → u X = u0 X hX :=
    ⟨Function.update (fun X => if h : DefNode D.R.m X then u0 X h else 1) (.top D.R.m) uT,
      Function.update_self _ _ _, fun X hX hXt => by rw [Function.update_of_ne hXt, dite_eq_left hX]⟩
  have frmm := hfr _ hmm hne
  have hu_mm := hu _ hmm hne
  refine ⟨⟨S, hSp, ?_, ?_, fr, ?_, u, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact fun w hw => hS₁ w (off_mono hsub1 hw)
  · intro w hw e he t ht j h1 h2
    exact unrIdem_mul (hSc _ (hcμ j h1 h2) w (off_mono (hsubμ j h2) hw) e he)
      (hSc _ (hL.xi t).1.1 w (off_mono (hsubξ t ht) hw) e he)
  · intro X hX
    by_cases hXt : X = .top D.R.m
    · subst hXt; rw [frt]; exact hT1
    · have := hfr X hX hXt
      rw [this]; exact (h0 X hX).1
  · intro X hX
    by_cases hXt : X = .top D.R.m
    · subst hXt; rw [ut]; exact hT2
    · have := hu X hX hXt
      rw [this]; exact (h0 X hX).2.1
  · intro X hX
    by_cases hXt : X = .top D.R.m
    · subst hXt; rw [frt, ut]; exact hT3
    · have e1 := hfr X hX hXt
      have e2 := hu X hX hXt
      rw [e1, e2]; exact (h0 X hX).2.2
  · intro i k; rw [frt, frmm]; exact hT4 i k
  · intro i; rw [frt]; exact hT5 i
  · rw [ut, hu_mm]; exact hT6
  · rw [ut]; exact hT7

end GlobalTheory.FunObj
