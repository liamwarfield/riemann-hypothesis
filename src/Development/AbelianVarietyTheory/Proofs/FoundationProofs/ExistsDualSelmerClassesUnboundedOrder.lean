module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisCocycleIntegralAfterScaling
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCochainsGlueGlobal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GreenbergWilesDualSelmerLowerBoundModPrimePow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardPrimePowTorsionSelmerClassesModPrimePowBound
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardPrimePowTorsionSelmerClassesModPrimePowBound
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.TorsBound

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem natCast_ne_zero' : ((l : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero

theorem norm_mul_pow_le_iff (k j : ℕ) (a : Qbar l) :
    ‖((l : ℕ) : Qbar l) ^ k * a‖ ≤ ‖((l : ℕ) : Qbar l) ^ (k + j)‖ ↔ ‖a‖ ≤ ‖((l : ℕ) : Qbar l) ^ j‖ := by
  rw [norm_mul, pow_add, norm_mul]
  have : 0 < ‖((l : ℕ) : Qbar l) ^ k‖ := norm_pos_iff.2 (pow_ne_zero _ natCast_ne_zero')
  exact mul_le_mul_iff_of_pos_left this

theorem cv_of_smul {k m : ℕ} {a b w w' : Fin 2 → Qbar l} (h : ((l : ℕ) : Qbar l) ^ k • (a - b) = w - w')
    (hw : Cv (k + m) w w') : Cv m a b := fun i => by
  have e := congrFun h i
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e
  have := hw i
  unfold Cg at this ⊢
  rw [← e] at this
  exact (norm_mul_pow_le_iff k m _).1 this

theorem cv_smul {k m : ℕ} {a b w w' : Fin 2 → Qbar l} (h : ((l : ℕ) : Qbar l) ^ k • (a - b) = w - w')
    (hab : Cv m a b) : Cv (k + m) w w' := fun i => by
  have e := congrFun h i
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e
  have := hab i
  unfold Cg at this ⊢
  rw [← e]
  exact (norm_mul_pow_le_iff k m _).2 this

theorem mem_of_mul (c : Coef l) (k : ℕ) {a : Qbar l} (ha : ((l : ℕ) : Qbar l) ^ k * a ∈ c.O) (hn : ‖a‖ ≤ 1) :
    a ∈ c.O :=
  mem_coefO_of_memE_norm_le_one l c a ⟨k, ha⟩ hn

theorem exists_cls (c : Coef l) (m : ℕ) : ∃ (T : Type) (_ : Fintype T) (cls : (Fin 2 → c.O) → T),
    ∀ x y, cls x = cls y → ∀ j, ‖((x j : c.O) : Qbar l) - (y j : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ m‖ := by
  have hl0 : ((l : ℕ) : c.O) ^ m ≠ 0 := pow_ne_zero _ (by
    intro h
    have h' : (((l : ℕ) : c.O) : PadicAlgCl l) = 0 := by rw [h]; rfl
    exact natCast_ne_zero' (by simpa using h'))
  haveI hfin := (UpperTheory.V.X.So.levFacts l c.O _ hl0 (c.O ⧸ Ideal.span {((l : ℕ) : c.O) ^ m})
    ⟨LinearEquiv.refl _ _⟩).1
  refine ⟨Fin 2 → c.O ⧸ Ideal.span {((l : ℕ) : c.O) ^ m}, Fintype.ofFinite _,
    fun x j => Ideal.Quotient.mk _ (x j), ?_⟩
  intro x y h j
  have h1 := congrFun h j
  simp only at h1
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h1
  obtain ⟨w, hw⟩ := h1
  have e : ((x j : c.O) : Qbar l) - (y j : Qbar l) = ((l : ℕ) : Qbar l) ^ m * (w : Qbar l) := by
    have := congrArg (fun z : c.O => (z : Qbar l)) hw
    simpa using this
  rw [e, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_le_one_of_mem_coefO c w)

def cobd (V : R2 Ω l) (s : G ℚ Ω) : (Fin 2 → Qbar l) →ₗ[Qbar l] (Fin 2 → Qbar l) :=
  Matrix.mulVecLin (mat V s) - LinearMap.id

theorem cobd_apply (V : R2 Ω l) (s : G ℚ Ω) (y : Fin 2 → Qbar l) : cobd V s y = mat V s *ᵥ y - y := rfl

theorem cobd_mul (V : R2 Ω l) (s t : G ℚ Ω) (y : Fin 2 → Qbar l) :
    cobd V (s * t) y = cobd V s y + mat V s *ᵥ cobd V t y := by
  simp only [cobd_apply, mat_mul', ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
  abel

end GlobalTheory.Ord2.TorsBound

namespace GlobalTheory.Ord2.TorsBound

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def lift (V : R2 Ω l) (m k : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l) (x : Fin 2 → Qbar l) (s : G ℚ Ω) : Fin 2 → Qbar l :=
  (((l : ℕ) : Qbar l) ^ k)⁻¹ • (z s - cobd V s ((((l : ℕ) : Qbar l) ^ m)⁻¹ • x))

theorem smul_lift (V : R2 Ω l) (m k : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l) (x : Fin 2 → Qbar l) (s : G ℚ Ω) :
    ((l : ℕ) : Qbar l) ^ k • lift V m k z x s = z s - cobd V s ((((l : ℕ) : Qbar l) ^ m)⁻¹ • x) :=
  smul_inv_smul₀ (pow_ne_zero _ natCast_ne_zero') _

theorem smul_diff (V : R2 Ω l) (m : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l) (x : Fin 2 → Qbar l) (s : G ℚ Ω) :
    ((l : ℕ) : Qbar l) ^ m • (z s - cobd V s ((((l : ℕ) : Qbar l) ^ m)⁻¹ • x)) =
      ((l : ℕ) : Qbar l) ^ m • z s - cobd V s x := by
  rw [smul_sub, ← map_smul, smul_inv_smul₀ (pow_ne_zero _ natCast_ne_zero')]

variable (c : Coef l) (V : R2 Ω l) (m k : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l) (x : Fin 2 → Qbar l)

theorem lift_mem (hVO : ∀ s i j, mat V s i j ∈ c.O) (hz : ∀ s i, z s i ∈ c.O) (hx : ∀ i, x i ∈ c.O)
    (hxc : ∀ s, Cv (m + k) (((l : ℕ) : Qbar l) ^ m • z s) (cobd V s x)) (s : G ℚ Ω) (j : Fin 2) :
    lift V m k z x s j ∈ c.O := by
  have hL : ((l : ℕ) : Qbar l) ∈ c.O := by
    have : ((l : ℕ) : Qbar l) = algebraMap ℤ_[l] (Qbar l) (l : ℤ_[l]) := by simp
    rw [this]; exact c.O.algebraMap_mem _
  have hD : ‖(z s - cobd V s ((((l : ℕ) : Qbar l) ^ m)⁻¹ • x)) j‖ ≤ ‖((l : ℕ) : Qbar l) ^ k‖ := by
    have e := congrFun (smul_diff V m z x s) j
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e
    apply (norm_mul_pow_le_iff m k _).1
    simp only [Pi.sub_apply]
    rw [e]
    have := hxc s j
    unfold Cg at this
    simpa using this
  have e2 := congrFun (smul_lift V m k z x s) j
  simp only [Pi.smul_apply, smul_eq_mul] at e2
  have hn : ‖lift V m k z x s j‖ ≤ 1 := by
    have := (norm_mul_pow_le_iff k 0 (lift V m k z x s j)).1 (by rw [e2, add_zero]; exact hD)
    simpa using this
  refine mem_of_mul c (m + k) ?_ hn
  have e3 := congrFun (smul_diff V m z x s) j
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e3
  rw [pow_add, mul_assoc, e2]
  simp only [Pi.sub_apply] at e3 ⊢
  rw [mul_sub] at e3 ⊢
  rw [e3, cobd_apply]
  refine c.O.sub_mem (c.O.mul_mem (c.O.pow_mem hL _) (hz s j)) (c.O.sub_mem ?_ (hx j))
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact c.O.add_mem (c.O.mul_mem (hVO _ _ _) (hx _)) (c.O.mul_mem (hVO _ _ _) (hx _))

theorem lift_coc (hz : ∀ s t, Cv (m + k) (z (s * t)) (z s + mat V s *ᵥ z t)) (s t : G ℚ Ω) :
    Cv m (lift V m k z x (s * t)) (lift V m k z x s + mat V s *ᵥ lift V m k z x t) := by
  refine cv_of_smul (k := k) (w := z (s * t)) (w' := z s + mat V s *ᵥ z t) ?_ (by rw [add_comm]; exact hz s t)
  rw [smul_sub, smul_add, ← Matrix.mulVec_smul, smul_lift, smul_lift, smul_lift, cobd_mul, Matrix.mulVec_sub]
  abel

theorem lift_ker (a : G ℚ Ω) (ha : mat V a = 1) (hz : Cv (m + k) (z a) 0) : Cv m (lift V m k z x a) 0 := by
  refine cv_of_smul (k := k) (w := z a) (w' := 0) ?_ (by rw [add_comm]; exact hz)
  rw [sub_zero, sub_zero, smul_lift, cobd_apply, ha, Matrix.one_mulVec, sub_self, sub_zero]

theorem cob_of_lift (hVO : ∀ s i j, mat V s i j ∈ c.O) (z' : G ℚ Ω → Fin 2 → Qbar l) (x' : Fin 2 → Qbar l)
    (hx : ∀ i, x i ∈ c.O) (hx' : ∀ i, x' i ∈ c.O) (hd : ∀ j, ‖x j - x' j‖ ≤ ‖((l : ℕ) : Qbar l) ^ m‖)
    (h : Cob1 c m V ⊤ (lift V m k z x - lift V m k z' x')) : Cob1 c (m + k) V ⊤ (z - z') := by
  obtain ⟨v, hvO, hv⟩ := h
  set d : Fin 2 → Qbar l := (((l : ℕ) : Qbar l) ^ m)⁻¹ • (x - x') with hd'
  have hL : ((l : ℕ) : Qbar l) ∈ c.O := by
    have : ((l : ℕ) : Qbar l) = algebraMap ℤ_[l] (Qbar l) (l : ℤ_[l]) := by simp
    rw [this]; exact c.O.algebraMap_mem _
  have hdO : ∀ j, d j ∈ c.O := by
    intro j
    have e : ((l : ℕ) : Qbar l) ^ m * d j = x j - x' j := by
      simp only [hd', Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ natCast_ne_zero'), one_mul]
    refine mem_of_mul c m (by rw [e]; exact c.O.sub_mem (hx j) (hx' j)) ?_
    have := (norm_mul_pow_le_iff m 0 (d j)).1 (by rw [e, add_zero]; exact hd j)
    simpa using this
  refine ⟨d + ((l : ℕ) : Qbar l) ^ k • v, fun j => c.O.add_mem (hdO j) ?_, fun s _ => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]; exact c.O.mul_mem (c.O.pow_mem hL _) (hvO j)
  have hs := hv s (Subgroup.mem_top s)
  rw [add_comm m k]
  refine cv_smul (a := (lift V m k z x - lift V m k z' x') s) (b := mat V s *ᵥ v - v) ?_ hs
  have e1 : (((l : ℕ) : Qbar l) ^ m)⁻¹ • x = (((l : ℕ) : Qbar l) ^ m)⁻¹ • x' + d := by
    rw [hd', smul_sub]; abel
  have e2 := smul_lift V m k z x s
  have e3 := smul_lift V m k z' x' s
  rw [e1, map_add (f := _)] at e2
  simp only [Pi.sub_apply, smul_sub]
  rw [e2, e3, ← cobd_apply V s (d + _), map_add (f := _), cobd_apply V s (_ • v), Matrix.mulVec_smul]
  abel

end GlobalTheory.Ord2.TorsBound

namespace GlobalTheory.Ord2.TorsBound

open GlobalTheory.Ord2.GwCount

theorem tors_bound : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → (∀ n : ℕ, ∃ B : ℕ, ∀ (N : ℕ) (z : Fin N → G ℚ Ω → Fin 2 → Qbar l), (∀ i, Coc1 c n (dual1 W) ⊤ (z i) ∧ ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z i a) 0) → (∀ i j, i ≠ j → ¬ Cob1 c n (dual1 W) ⊤ (z i - z j)) → N ≤ B) → ∀ m : ℕ, ∃ B : ℕ, ∀ (n N : ℕ) (z : Fin N → G ℚ Ω → Fin 2 → Qbar l), (∀ i, GwCount.SelN c n S A (dual1 W) (z i)) → (∀ i j, i ≠ j → ¬ Cob1 c n (dual1 W) ⊤ (z i - z j)) → (∀ i, Cob1 c n (dual1 W) ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z i s)) → N ≤ B := by
  intro l _ Ω _ _ _ e S A W hW c hWc hyp m
  choose Bf hBf using hyp
  have hVc : Continuous fun s => mat (dual1 W) s := continuous_mat_dual1 W hW.cont hW.det2
  have hVO : ∀ s i j, mat (dual1 W) s i j ∈ c.O := CupCob.dual_representation_integral c W hW.det2 hWc
  have hDI : ∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ (dual1 W).ker := by
    intro w hw B hB σ hσ
    have h1 : W σ = 1 := hW.unr w hw B hB hσ
    have hm : mat W σ = 1 := by simp [mat, h1]
    have he : eps l σ = 1 := eps_eq_one_of_mem_Ine (fun h => hw (hW.above w h)) hB hσ
    show dual1 W σ = 1
    apply Units.ext
    show mat (dual1 W) σ = 1
    rw [mat_dual1_eq' W hW.det2, hm, he, Matrix.det_one, mul_one, one_smul]
  have hVK : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, mat (dual1 W) a = 1 := by
    intro a ha
    have hker : (toGS Ω (S : Set Pl)).ker = NS Ω (S : Set Pl) := QuotientGroup.ker_mk' _
    rw [hker] at ha
    have hU : Unr (dual1 W) (0 : G ℚ Ω → Fin 2 → Qbar l) := fun w _ =>
      ⟨placeOf Ω w, isPlaceOver_placeOf Ω w, 0, fun s _ => by simp⟩
    exact (vanish_NS hW.above (dual1 W) hVc (Submodule.zero_mem _) hU hDI a ha).1
  obtain ⟨T, _, cls, hcls⟩ := exists_cls c m
  refine ⟨max ((Finset.range m).sup Bf) (Fintype.card T * Bf m), ?_⟩
  intro n N z hz hnc hcob
  by_cases hnm : n < m
  · exact (hBf n N z (fun i => ⟨(hz i).1, (hz i).2.1⟩) hnc).trans
      ((Finset.le_sup (f := Bf) (Finset.mem_range.2 hnm)).trans (le_max_left _ _))
  push_neg at hnm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  refine le_trans ?_ (le_max_right _ _)
  choose x hxO hx using hcob
  by_contra hlt
  push_neg at hlt
  let f : Fin N → T := fun i => cls (fun j => ⟨x i j, hxO i j⟩)
  classical
  obtain ⟨t, ht⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card f (by rw [Fintype.card_fin]; exact hlt)
  set F := Finset.univ.filter (fun i => f i = t) with hF
  let emb : Fin F.card → Fin N := fun k => (F.equivFin.symm k : Fin N)
  have hemb : ∀ a, f (emb a) = t := fun a => (Finset.mem_filter.1 (F.equivFin.symm a).2).2
  have hinj : Function.Injective emb := fun a b h => F.equivFin.symm.injective (Subtype.ext h)
  have hzc : ∀ i, Continuous (z i) := fun i => by
    have := (hz i).1.1
    rw [Subgroup.coe_top] at this
    exact continuousOn_univ.1 this
  have key := hBf m F.card (fun a => lift (dual1 W) m k (z (emb a)) (x (emb a))) ?_ ?_
  · omega
  · intro a
    refine ⟨⟨?_, fun s j => lift_mem c (dual1 W) m k _ _ hVO (hz (emb a)).1.2.1 (hxO (emb a))
      (fun s => hx (emb a) s (Subgroup.mem_top s)) s j,
      fun s _ t _ => lift_coc (dual1 W) m k _ _ (fun s t => (hz (emb a)).1.2.2 s (Subgroup.mem_top s) t
        (Subgroup.mem_top t)) s t⟩, fun b hb => lift_ker (dual1 W) m k _ _ b (hVK b hb) ((hz (emb a)).2.1 b hb)⟩
    apply Continuous.continuousOn
    show Continuous fun s => (((l : ℕ) : Qbar l) ^ k)⁻¹ • (z (emb a) s - (mat (dual1 W) s *ᵥ ((((l : ℕ) : Qbar l) ^ m)⁻¹ • x (emb a)) - (((l : ℕ) : Qbar l) ^ m)⁻¹ • x (emb a)))
    exact ((hzc _).sub ((hVc.matrix_mulVec continuous_const).sub continuous_const)).const_smul ((((l : ℕ) : Qbar l) ^ k)⁻¹)
  · intro a b hab hcob
    refine hnc (emb a) (emb b) (fun h => hab (hinj h)) ?_
    refine cob_of_lift c (dual1 W) m k (z (emb a)) (x (emb a)) hVO (z (emb b)) (x (emb b)) (hxO _) (hxO _) ?_ hcob
    have := hcls _ _ ((hemb a).trans (hemb b).symm)
    simpa using this

end GlobalTheory.Ord2.TorsBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardPrimePowTorsionSelmerClassesModPrimePowBoundStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_primePowTorsion_selmerClassesModPrimePow_bounded : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → (∀ n : ℕ, ∃ B : ℕ, ∀ (N : ℕ) (z : Fin N → G ℚ Ω → Fin 2 → Qbar l), (∀ i, Coc1 c n (dual1 W) ⊤ (z i) ∧ ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z i a) 0) → (∀ i j, i ≠ j → ¬ Cob1 c n (dual1 W) ⊤ (z i - z j)) → N ≤ B) → ∀ m : ℕ, ∃ B : ℕ, ∀ (n N : ℕ) (z : Fin N → G ℚ Ω → Fin 2 → Qbar l), (∀ i, GwCount.SelN c n S A (dual1 W) (z i)) → (∀ i j, i ≠ j → ¬ Cob1 c n (dual1 W) ⊤ (z i - z j)) → (∀ i, Cob1 c n (dual1 W) ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z i s)) → N ≤ B := by
  first | exact @GlobalTheory.Ord2.TorsBound.tors_bound | exact GlobalTheory.Ord2.TorsBound.tors_bound | (intros; apply GlobalTheory.Ord2.TorsBound.tors_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualCocyclesModPrimePowUnramifiedOutsideSBou
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualCocyclesModPrimePowUnramifiedOutsideSBou
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.GwFin

open GlobalTheory.Ord2.TwistTriv

variable {l : ℕ} [Fact l.Prime]

def mulR (c : Coef l) (n : ℕ) (a : c.O) : Red c n →+ Red c n :=
  QuotientAddGroup.map (nbhd c n) (nbhd c n) (AddMonoidHom.mulLeft a) (by
    intro x hx
    show ‖((a * x : c.O) : Qbar l)‖ ≤ _
    rw [MulMemClass.coe_mul, norm_mul]
    calc _ ≤ 1 * ‖(x : Qbar l)‖ := mul_le_mul_of_nonneg_right (norm_le_one c a) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hx)

theorem mulR_red (c : Coef l) (n : ℕ) (a x : c.O) : mulR c n a (red c n x) = red c n (a * x) := rfl

def redV (c : Coef l) (n : ℕ) (x : Fin 2 → c.O) : Fin 2 → Red c n := fun i => red c n (x i)

theorem redV_surjective (c : Coef l) (n : ℕ) : Function.Surjective (redV c n) := by
  intro m
  choose x hx using fun i => red_surjective c n (m i)
  exact ⟨x, funext hx⟩

theorem redV_add (c : Coef l) (n : ℕ) (x y : Fin 2 → c.O) :
    redV c n (x + y) = redV c n x + redV c n y := by
  funext i; simp [redV]

def act (c : Coef l) (n : ℕ) (B : Matrix (Fin 2) (Fin 2) c.O) :
    (Fin 2 → Red c n) →+ (Fin 2 → Red c n) where
  toFun m i := ∑ j, mulR c n (B i j) (m j)
  map_zero' := by funext i; simp
  map_add' m m' := by funext i; simp [Finset.sum_add_distrib]

theorem act_redV (c : Coef l) (n : ℕ) (B : Matrix (Fin 2) (Fin 2) c.O) (x : Fin 2 → c.O) :
    act c n B (redV c n x) = redV c n (B *ᵥ x) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [act, AddMonoidHom.coe_mk, ZeroHom.coe_mk, redV, mulR_red, Matrix.mulVec, dotProduct,
    map_sum]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

def Vo (c : Coef l) (V : R2 Ω l) (hD : ∀ s i j, mat V s i j ∈ c.O) (s : G ℚ Ω) :
    Matrix (Fin 2) (Fin 2) c.O :=
  fun i j => ⟨mat V s i j, hD s i j⟩

theorem Vo_mulVec_coe (c : Coef l) (V : R2 Ω l) (hD : ∀ s i j, mat V s i j ∈ c.O) (s : G ℚ Ω)
    (x : Fin 2 → c.O) (i : Fin 2) :
    ((Vo c V hD s *ᵥ x) i : Qbar l) = (mat V s *ᵥ fun j => (x j : Qbar l)) i := by
  simp [Matrix.mulVec, dotProduct, Vo]

theorem Vo_mul (c : Coef l) (V : R2 Ω l) (hD : ∀ s i j, mat V s i j ∈ c.O) (s t : G ℚ Ω) :
    Vo c V hD (s * t) = Vo c V hD s * Vo c V hD t := by
  ext i j
  simp [Vo, mat, Matrix.mul_apply]

theorem Vo_eq_one (c : Coef l) (V : R2 Ω l) (hD : ∀ s i j, mat V s i j ∈ c.O) {s : G ℚ Ω}
    (h : V s = 1) : Vo c V hD s = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Vo, mat, h]

def repG (c : Coef l) (n : ℕ) (V : R2 Ω l) (hD : ∀ s i j, mat V s i j ∈ c.O) :
    Representation (ZMod (l ^ n)) (G ℚ Ω) (Fin 2 → Red c n) where
  toFun s := (act c n (Vo c V hD s)).toZModLinearMap (l ^ n)
  map_one' := by
    apply LinearMap.ext; intro m
    obtain ⟨x, rfl⟩ := redV_surjective c n m
    show act c n (Vo c V hD 1) (redV c n x) = redV c n x
    rw [act_redV, Vo_eq_one c V hD (map_one V), Matrix.one_mulVec]
  map_mul' s t := by
    apply LinearMap.ext; intro m
    obtain ⟨x, rfl⟩ := redV_surjective c n m
    show act c n (Vo c V hD (s * t)) (redV c n x) =
      act c n (Vo c V hD s) (act c n (Vo c V hD t) (redV c n x))
    rw [act_redV, act_redV, act_redV, Vo_mul, Matrix.mulVec_mulVec]

theorem repG_apply (c : Coef l) (n : ℕ) (V : R2 Ω l) (hD : ∀ s i j, mat V s i j ∈ c.O) (s : G ℚ Ω)
    (m : Fin 2 → Red c n) : repG c n V hD s m = act c n (Vo c V hD s) m := rfl

variable [IsAlgClosure ℚ Ω] (S : Finset Pl)

def repS (c : Coef l) (n : ℕ) (V : R2 Ω l) (hD : ∀ s i j, mat V s i j ∈ c.O)
    (hK : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, V a = 1) :
    Representation (ZMod (l ^ n)) (GS Ω (S : Set Pl)) (Fin 2 → Red c n) :=
  QuotientGroup.lift (NS Ω (S : Set Pl)) (repG c n V hD) (by
    intro a ha
    rw [MonoidHom.mem_ker]
    apply LinearMap.ext; intro m
    obtain ⟨x, rfl⟩ := redV_surjective c n m
    show act c n (Vo c V hD a) (redV c n x) = redV c n x
    rw [Vo_eq_one c V hD (hK a (by rw [toGS, QuotientGroup.ker_mk']; exact ha)), act_redV,
      Matrix.one_mulVec])

theorem repS_mk (c : Coef l) (n : ℕ) (V : R2 Ω l) (hD : ∀ s i j, mat V s i j ∈ c.O)
    (hK : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, V a = 1) (g : G ℚ Ω) :
    repS S c n V hD hK (QuotientGroup.mk g) = repG c n V hD g := rfl

end GlobalTheory.Ord2.GwFin

namespace GlobalTheory.Ord2.GwFin

open GlobalTheory.Ord2.TwistTriv

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl)

theorem contAction_repS (c : Coef l) (n : ℕ) (V : R2 Ω l) (hD : ∀ s i j, mat V s i j ∈ c.O)
    (hK : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, V a = 1) (hc : Continuous V) :
    ReciprocityTheory.Gal.ContAction (repS S c n V hD hK) := by
  unfold ReciprocityTheory.Gal.ContAction
  refine continuous_prod_of_discrete_right.2 fun m => ?_
  rw [(QuotientGroup.isQuotientMap_mk (NS Ω (S : Set Pl))).continuous_iff]
  obtain ⟨x, rfl⟩ := redV_surjective c n m
  have e : ((fun q => repS S c n V hD hK q (redV c n x)) ∘
      (QuotientGroup.mk : G ℚ Ω → GS Ω (S : Set Pl))) = fun g => redV c n (Vo c V hD g *ᵥ x) := by
    funext g; exact act_redV c n _ x
  rw [e]
  refine continuous_pi fun i => continuous_red_comp c n (fun g => (Vo c V hD g *ᵥ x) i) ?_
  simp only [Vo_mulVec_coe]
  have hm : Continuous fun g => mat V g := Units.continuous_val.comp hc
  exact (continuous_apply i).comp (hm.matrix_mulVec continuous_const)

def zr (c : Coef l) (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l) (hz : ∀ s k, z s k ∈ c.O) (s : G ℚ Ω) :
    Fin 2 → Red c n :=
  redV c n fun k => ⟨z s k, hz s k⟩

theorem zr_eq_iff (c : Coef l) (n : ℕ) (z z' : G ℚ Ω → Fin 2 → Qbar l) (hz : ∀ s k, z s k ∈ c.O)
    (hz' : ∀ s k, z' s k ∈ c.O) (s : G ℚ Ω) :
    zr c n z hz s = zr c n z' hz' s ↔ Cv n (z s) (z' s) := by
  simp only [zr, redV, funext_iff, red_eq_iff, Cv]

theorem zr_eq_zero (c : Coef l) (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l) (hz : ∀ s k, z s k ∈ c.O)
    (a : G ℚ Ω) (h : Cv n (z a) 0) : zr c n z hz a = 0 := by
  funext k
  show red c n ⟨z a k, hz a k⟩ = 0
  rw [red_eq_zero_iff, mem_nbhd]
  have := h k
  simpa [Cg] using this

theorem zr_mul (c : Coef l) (n : ℕ) (V : R2 Ω l) (hD : ∀ s i j, mat V s i j ∈ c.O)
    (z : G ℚ Ω → Fin 2 → Qbar l) (hz : ∀ s k, z s k ∈ c.O)
    (hcoc : ∀ s t, Cv n (z (s * t)) (z s + mat V s *ᵥ z t)) (s t : G ℚ Ω) :
    zr c n z hz (s * t) = zr c n z hz s + repG c n V hD s (zr c n z hz t) := by
  rw [repG_apply, zr, zr, zr, act_redV, ← redV_add]
  funext k
  simp only [redV]
  rw [red_eq_iff, Pi.add_apply, AddMemClass.coe_add, Vo_mulVec_coe]
  have h := hcoc s t k
  simpa only [Pi.add_apply] using h

def zbar (c : Coef l) (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l) (hz : ∀ s k, z s k ∈ c.O)
    (q : GS Ω (S : Set Pl)) : Fin 2 → Red c n :=
  zr c n z hz q.out

theorem zbar_mk (c : Coef l) (n : ℕ) (V : R2 Ω l) (hD : ∀ s i j, mat V s i j ∈ c.O)
    (z : G ℚ Ω → Fin 2 → Qbar l) (hz : ∀ s k, z s k ∈ c.O)
    (hcoc : ∀ s t, Cv n (z (s * t)) (z s + mat V s *ᵥ z t))
    (hker : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) (g : G ℚ Ω) :
    zbar S c n z hz (QuotientGroup.mk g) = zr c n z hz g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (NS Ω (S : Set Pl)) g
  unfold zbar
  rw [hh, zr_mul c n V hD z hz hcoc,
    zr_eq_zero c n z hz (h : G ℚ Ω) (hker _ (by rw [toGS, QuotientGroup.ker_mk']; exact h.2)), map_zero,
    add_zero]

theorem zbar_mem (c : Coef l) (n : ℕ) (V : R2 Ω l) (hD : ∀ s i j, mat V s i j ∈ c.O)
    (hK : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, V a = 1)
    (z : G ℚ Ω → Fin 2 → Qbar l) (hz : ∀ s k, z s k ∈ c.O) (hzc : Continuous z)
    (hcoc : ∀ s t, Cv n (z (s * t)) (z s + mat V s *ᵥ z t))
    (hker : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) :
    zbar S c n z hz ∈ Z1 (repS S c n V hD hK) := by
  refine ⟨?_, fun q₁ q₂ => ?_⟩
  · rw [(QuotientGroup.isQuotientMap_mk (NS Ω (S : Set Pl))).continuous_iff]
    have e : zbar S c n z hz ∘ (QuotientGroup.mk : G ℚ Ω → GS Ω (S : Set Pl)) = zr c n z hz := by
      funext g; exact zbar_mk S c n V hD z hz hcoc hker g
    rw [e]
    exact continuous_pi fun k => continuous_red_comp c n (fun g => (⟨z g k, hz g k⟩ : c.O))
      ((continuous_apply k).comp hzc)
  · induction q₁ using QuotientGroup.induction_on with | H g => ?_
    induction q₂ using QuotientGroup.induction_on with | H h => ?_
    rw [← QuotientGroup.mk_mul, zbar_mk S c n V hD z hz hcoc hker, zbar_mk S c n V hD z hz hcoc hker,
      zbar_mk S c n V hD z hz hcoc hker, repS_mk, zr_mul c n V hD z hz hcoc]

end GlobalTheory.Ord2.GwFin

namespace GlobalTheory.Ord2.GwFin

open GlobalTheory.Ord2.TwistTriv

theorem finite_cocycles_of_finite_h1 {R : Type*} [CommRing R] {H : Type*} [Group H] [TopologicalSpace H]
    {Q : Type*} [AddCommGroup Q] [Module R Q] [TopologicalSpace Q] [IsTopologicalAddGroup Q]
    [ContinuousConstSMul R Q] [Finite Q] (σ : Representation R H Q) [Finite (H1 σ)] :
    Finite (Z1 σ) := by
  haveI : Finite ((B1 σ).comap (Z1 σ).subtype) := by
    haveI : Finite (B1 σ) := by
      haveI : Finite (Set.range (d0 σ)) := Set.finite_range _
      exact Finite.of_injective (fun x : B1 σ => (⟨x.1, x.2⟩ : Set.range (d0 σ)))
        (fun x y h => Subtype.ext (congrArg Subtype.val h))
    exact Finite.of_injective (fun x : (B1 σ).comap (Z1 σ).subtype => (⟨x.1.1, x.2⟩ : B1 σ))
      (fun x y h => by
        apply Subtype.ext; apply Subtype.ext
        have := congrArg Subtype.val h
        simpa using this)
  let P := (B1 σ).comap (Z1 σ).subtype
  let s := Function.surjInv (Submodule.Quotient.mk_surjective P)
  have hs : ∀ x : Z1 σ, x - s (Submodule.Quotient.mk x) ∈ P := fun x =>
    (Submodule.Quotient.eq P).1 (Function.surjInv_eq (Submodule.Quotient.mk_surjective P) _).symm
  refine Finite.of_injective (fun x : Z1 σ => ((Submodule.Quotient.mk x : Z1 σ ⧸ P), (⟨_, hs x⟩ : P))) ?_
  intro x y h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rw [h1] at h2
  simpa using h2

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl)

theorem finite_cocycles_restricted_rep (hL : GlobalTheory.Mem.LiteralAutomorphy.LitCoh) (c : Coef l) (n : ℕ) (V : R2 Ω l)
    (hD : ∀ s i j, mat V s i j ∈ c.O) (hK : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, V a = 1)
    (hc : Continuous V) (hS : ContainsAbove S l) : Finite (Z1 (repS S c n V hD hK)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · haveI : Subsingleton (Red c 0) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨x, rfl⟩ := red_surjective c 0 a
      obtain ⟨y, rfl⟩ := red_surjective c 0 b
      rw [red_eq_iff]
      unfold Cg
      rw [pow_zero, norm_one]
      have hxy : ‖(x : Qbar l) - y‖ ≤ max ‖(x : Qbar l)‖ ‖-(y : Qbar l)‖ := by
        rw [sub_eq_add_neg]; exact IsUltrametricDist.norm_add_le_max _ _
      rw [norm_neg] at hxy
      exact hxy.trans (max_le (norm_le_one c x) (norm_le_one c y))
    infer_instance
  · haveI := (hL.gf ℚ Ω l n (Fin 2 → Red c n) S (repS S c n V hD hK) hn hS
      (contAction_repS S c n V hD hK hc)).2.1
    exact finite_cocycles_of_finite_h1 _

theorem card_dualCocyclesModPrimePow_unramifiedOutsideS_bounded : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → ∀ n : ℕ, ∃ B : ℕ, ∀ (N : ℕ) (z : Fin N → G ℚ Ω → Fin 2 → Qbar l), (∀ i, Coc1 c n (dual1 W) ⊤ (z i) ∧ ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z i a) 0) → (∀ i j, i ≠ j → ¬ Cob1 c n (dual1 W) ⊤ (z i - z j)) → N ≤ B := by
  intro hL l _ Ω _ _ _ e S A W hN c hW n
  have hD := galoisRepRankTwoTateDual_matrix_mem_coefRing_of_normalForm l Ω e S A W hN c hW
  have hK := galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramified l Ω e S A W hN
  have hc := DualCont.continuous_galoisRepRankTwoTateDual l Ω e S A W hN
  haveI := finite_cocycles_restricted_rep S hL c n (dual1 W) hD hK hc hN.above
  refine ⟨Nat.card (Z1 (repS S c n (dual1 W) hD hK)), fun N z hz hne => ?_⟩
  have hint : ∀ i s k, z i s k ∈ c.O := fun i => (hz i).1.2.1
  have hcont : ∀ i, Continuous (z i) := fun i => by
    have h := (hz i).1.1
    rwa [Subgroup.coe_top, continuousOn_univ] at h
  have hcoc : ∀ i s t, Cv n (z i (s * t)) (z i s + mat (dual1 W) s *ᵥ z i t) :=
    fun i s t => (hz i).1.2.2 s (Subgroup.mem_top s) t (Subgroup.mem_top t)
  let f : Fin N → Z1 (repS S c n (dual1 W) hD hK) := fun i =>
    ⟨zbar S c n (z i) (hint i),
      zbar_mem S c n (dual1 W) hD hK (z i) (hint i) (hcont i) (hcoc i) (hz i).2⟩
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hij'
    apply hne i j hij'
    refine ⟨0, fun _ => zero_mem _, fun s _ => ?_⟩
    have h1 := congrArg (fun y : Z1 (repS S c n (dual1 W) hD hK) => y.1 (QuotientGroup.mk s)) hij
    simp only [f, zbar_mk S c n (dual1 W) hD (z i) (hint i) (hcoc i) (hz i).2,
      zbar_mk S c n (dual1 W) hD (z j) (hint j) (hcoc j) (hz j).2] at h1
    have h2 := (zr_eq_iff c n (z i) (z j) (hint i) (hint j) s).1 h1
    intro k
    have h3 := h2 k
    simpa [Cg] using h3
  simpa using Nat.card_le_card_of_injective f hf

end GlobalTheory.Ord2.GwFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualCocyclesModPrimePowUnramifiedOutsideSBouStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_dualCocyclesModPrimePow_unramifiedOutsideS_bounded_alt : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → ∀ n : ℕ, ∃ B : ℕ, ∀ (N : ℕ) (z : Fin N → G ℚ Ω → Fin 2 → Qbar l), (∀ i, Coc1 c n (dual1 W) ⊤ (z i) ∧ ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z i a) 0) → (∀ i j, i ≠ j → ¬ Cob1 c n (dual1 W) ⊤ (z i - z j)) → N ≤ B := by
  first | exact @GlobalTheory.Ord2.GwFin.card_dualCocyclesModPrimePow_unramifiedOutsideS_bounded | exact GlobalTheory.Ord2.GwFin.card_dualCocyclesModPrimePow_unramifiedOutsideS_bounded | (intros; apply GlobalTheory.Ord2.GwFin.card_dualCocyclesModPrimePow_unramifiedOutsideS_bounded <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CocycleVanishesOnKerToGSOfInertiaCoboundary
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CocycleVanishesOnKerToGSOfInertiaCoboundary
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.GwCount

theorem cocycle_zero_on_ker_toGS : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (Y : G ℚ Ω → Fin 2 → Qbar l), Nf e S A W → Y ∈ Z1 (Loc.colRep W) → (∀ q : Pl, q ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ x : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, Y s = mat W s *ᵥ x - x) → ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Y a = 0 := by
  intro l _ Ω _ _ _ e S A W Y hN hY hc a ha
  have hcoc : ∀ g h, Y (g * h) = Y g + mat W g *ᵥ Y h := fun g h => ((mem_Z1_iff_cocycle _ _).1 hY).2 g h
  have hcont : Continuous Y := ((mem_Z1_iff_cocycle _ _).1 hY).1
  have h1 : Y 1 = 0 := by
    have := hcoc 1 1
    simpa [mat] using this
  let H : Subgroup (G ℚ Ω) :=
    { carrier := {g | Y g = 0 ∧ W g = 1}
      one_mem' := ⟨h1, map_one W⟩
      mul_mem' := fun {g h} hg hh => ⟨by rw [hcoc, hg.1, hh.1]; simp, by rw [map_mul, hg.2, hh.2, one_mul]⟩
      inv_mem' := fun {g} hg => by
        refine ⟨?_, by rw [map_inv, hg.2, inv_one]⟩
        have := hcoc g g⁻¹
        rw [mul_inv_cancel, h1, hg.1] at this
        simpa [mat, hg.2] using this.symm }
  have hH : ∀ g, g ∈ H ↔ Y g = 0 ∧ W g = 1 := fun g => Iff.rfl
  haveI : H.Normal := ⟨fun g hg h => by
    rw [hH] at hg ⊢
    refine ⟨?_, by rw [map_mul, map_mul, hg.2, mul_one, ← map_mul, mul_inv_cancel, map_one]⟩
    have e1 : Y (g * h⁻¹) = Y h⁻¹ := by
      rw [hcoc, hg.1]; simp [mat, hg.2]
    rw [mul_assoc, hcoc, e1, ← hcoc, mul_inv_cancel, h1]⟩
  have hcl : IsClosed (H : Set (G ℚ Ω)) :=
    (isClosed_singleton.preimage hcont).inter (isClosed_singleton.preimage hN.cont)
  have hle : Subgroup.normalClosure
      (⋃ v ∈ (S : Set Pl)ᶜ, ⋃ B ∈ {B : ValuationSubring Ω | IsPlaceOver B v}, Inertia (F := ℚ) B) ≤ H := by
    apply Subgroup.normalClosure_le_normal
    intro τ hτ
    simp only [Set.mem_iUnion] at hτ
    obtain ⟨v, hv, B, hB, hτ⟩ := hτ
    have hv' : v ∉ S := by simpa using hv
    have hτ' : τ ∈ Ine (F := ℚ) B := hτ
    have hW : W τ = 1 := hN.unr v hv' B hB hτ'
    obtain ⟨x, hx⟩ := hc v hv' B hB
    refine (hH τ).2 ⟨?_, hW⟩
    rw [hx τ hτ']
    simp [mat, hW]
  have ha' : a ∈ NS Ω (S : Set Pl) := by
    rwa [toGS, QuotientGroup.ker_mk'] at ha
  exact ((hH a).1 (Subgroup.topologicalClosure_minimal _ hle hcl ha')).1

end GlobalTheory.Ord2.GwCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CocycleVanishesOnKerToGSOfInertiaCoboundaryStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_vanishes_on_ker_toGS_of_inertia_coboundary : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (Y : G ℚ Ω → Fin 2 → Qbar l), Nf e S A W → Y ∈ Z1 (Loc.colRep W) → (∀ q : Pl, q ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ x : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, Y s = mat W s *ᵥ x - x) → ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Y a = 0 := by
  first | exact @GlobalTheory.Ord2.GwCount.cocycle_zero_on_ker_toGS | exact GlobalTheory.Ord2.GwCount.cocycle_zero_on_ker_toGS | (intros; apply GlobalTheory.Ord2.GwCount.cocycle_zero_on_ker_toGS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NotCongruentZeroIntCastMulPrimePow
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NotCongruentZeroIntCastMulPrimePow
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.IntNorm

theorem norm_intCast_qbar (l : ℕ) [Fact l.Prime] (d : ℤ) :
    ‖(d : Qbar l)‖ = ‖(d : ℚ_[l])‖ := by
  have h : (d : Qbar l) = ((d : ℚ_[l]) : PadicAlgCl l) := by simp
  rw [h, PadicAlgCl.norm_extends]

theorem norm_l_qbar (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹ := by
  have h : ((l : ℕ) : Qbar l) = (((l : ℕ) : ℚ_[l]) : PadicAlgCl l) := by simp
  rw [h, PadicAlgCl.norm_extends, Padic.norm_p]

theorem not_cg_int_mul_pow (l : ℕ) [Fact l.Prime] (t k : ℕ) (d : ℤ) (hd : d ≠ 0)
    (hlt : |d| < (l : ℤ) ^ t) : ¬ Cg (t + k) ((d : Qbar l) * ((l : ℕ) : Qbar l) ^ k) 0 := by
  intro h
  unfold Cg at h
  rw [sub_zero, norm_mul, norm_pow, norm_pow, pow_add] at h
  have hlpos : (0 : ℝ) < ‖((l : ℕ) : Qbar l)‖ := by
    rw [norm_l_qbar]; have := (Fact.out : l.Prime).pos; positivity
  have hk : (0 : ℝ) < ‖((l : ℕ) : Qbar l)‖ ^ k := pow_pos hlpos k
  have h1 : ‖(d : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l)‖ ^ t := le_of_mul_le_mul_right h hk
  rw [norm_intCast_qbar, norm_l_qbar] at h1
  have h2 : ‖(d : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(t : ℤ)) := by
    rw [zpow_neg, zpow_natCast, ← inv_pow]; exact h1
  have h3 : ((l : ℤ) ^ t) ∣ d := (Padic.norm_int_le_pow_iff_dvd d t).mp h2
  have h4 : ((l : ℤ) ^ t) ≤ |d| := by
    have := Int.le_of_dvd (abs_pos.mpr hd) ((dvd_abs _ _).mpr h3)
    exact this
  omega

end GlobalTheory.Ord2.IntNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NotCongruentZeroIntCastMulPrimePowStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_congruent_zero_intCast_mul_prime_pow : ∀ (l : ℕ) [Fact l.Prime] (t k : ℕ) (d : ℤ), d ≠ 0 → |d| < (l : ℤ) ^ t → ¬ Cg (t + k) ((d : Qbar l) * ((l : ℕ) : Qbar l) ^ k) 0 := by
  first | exact @GlobalTheory.Ord2.IntNorm.not_cg_int_mul_pow | exact GlobalTheory.Ord2.IntNorm.not_cg_int_mul_pow | (intros; apply GlobalTheory.Ord2.IntNorm.not_cg_int_mul_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonzeroClassBoundedTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOfMemSpan
namespace GlobalTheory.NormBoundOfSpan

theorem norm_le_of_mem_span {K E ι : Type} [NormedField K] [AddCommGroup E] [Module K E]
    (φ : ι → E →ₗ[K] K) :
    ∀ f ∈ Submodule.span K (Set.range φ), ∃ (C : ℝ), (0 : ℝ) ≤ C ∧ ∀ (p : E) (r : ℝ),
      (0 : ℝ) ≤ r → (∀ (j : ι), ‖(φ j : E → K) p‖ ≤ r) → ‖(f : E → K) p‖ ≤ C * r := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨1, zero_le_one, fun p r _ h => by simpa using h j⟩
  | zero => exact ⟨0, le_rfl, fun p r _ _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨C, hC, h1⟩ := hx
    obtain ⟨D, hD, h2⟩ := hy
    refine ⟨C + D, add_nonneg hC hD, fun p r hr h => ?_⟩
    rw [LinearMap.add_apply, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (h1 p r hr h) (h2 p r hr h))
  | smul a x _ hx =>
    obtain ⟨C, hC, h1⟩ := hx
    refine ⟨‖a‖ * C, mul_nonneg (norm_nonneg a) hC, fun p r hr h => ?_⟩
    rw [LinearMap.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h1 p r hr h) (norm_nonneg a)

end GlobalTheory.NormBoundOfSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonzeroClassBoundedTorsion
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.GwCount

theorem exists_bound_of_mem_span {K E ι : Type} [NormedField K] [AddCommGroup E] [Module K E] (φ : ι → E →ₗ[K] K)
    (f : E →ₗ[K] K) (hf : f ∈ Submodule.span K (Set.range φ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : E) (r : ℝ), 0 ≤ r → (∀ j, ‖φ j p‖ ≤ r) → ‖f p‖ ≤ C * r := by
  first
  | exact @_root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span
  | exact _root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span
  | (apply _root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span ..)

theorem exists_bound_multiplier {K Γ : Type} [NormedField K] (M : Γ → Matrix (Fin 2) (Fin 2) K) (Y : Γ → Fin 2 → K)
    (hY : ¬ ∃ x : Fin 2 → K, ∀ s, Y s = M s *ᵥ x - x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : K) (x : Fin 2 → K) (r : ℝ), 0 ≤ r →
      (∀ s i, ‖(a • Y s) i - (M s *ᵥ x - x) i‖ ≤ r) → ‖a‖ ≤ C * r := by
  let φ : Γ × Fin 2 → (K × (Fin 2 → K)) →ₗ[K] K := fun j =>
    (LinearMap.proj j.2).comp (((LinearMap.fst K K (Fin 2 → K)).smulRight (Y j.1)) -
      ((Matrix.toLin' (M j.1) - LinearMap.id).comp (LinearMap.snd K K (Fin 2 → K))))
  have hφ : ∀ s i a x, φ (s, i) (a, x) = (a • Y s) i - (M s *ᵥ x - x) i := by
    intro s i a x
    simp only [φ, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smulRight_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, LinearMap.id_apply, Matrix.toLin'_apply, LinearMap.proj_apply, Pi.sub_apply]
  have hker : ⨅ j, LinearMap.ker (φ j) ≤ LinearMap.ker (LinearMap.fst K K (Fin 2 → K)) := by
    rintro ⟨a, x⟩ h
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at h
    simp only [LinearMap.mem_ker, LinearMap.fst_apply]
    by_contra ha
    refine hY ⟨a⁻¹ • x, fun s => ?_⟩
    have h1 : a • Y s = M s *ᵥ x - x := by
      funext i
      have := h (s, i)
      rw [hφ] at this
      exact sub_eq_zero.1 this
    rw [Matrix.mulVec_smul, ← smul_sub, ← h1, smul_smul, inv_mul_cancel₀ ha, one_smul]
  obtain ⟨C, hC, h⟩ := exists_bound_of_mem_span φ _ (FiniteDimensional.mem_span_of_iInf_ker_le_ker hker)
  exact ⟨C, hC, fun a x r hr hb => h (a, x) r hr fun j => by rw [show j = (j.1, j.2) from rfl, hφ]; exact hb _ _⟩

theorem closed_multiplier : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (Y : G ℚ Ω → Fin 2 → Qbar l), (∀ s i j, mat W s i j ∈ c.O) → Y ∈ Z1 (Loc.colRep W) → (∀ s i, Y s i ∈ c.O) → Y ∉ ReciprocityTheory.Gal.B1 (Loc.colRep W) → ∃ k0 : ℕ, ∀ (n : ℕ) (a : Qbar l), a ∈ c.O → Cob1 c n W ⊤ (fun s => a • Y s) → Cg n (a * ((l : ℕ) : Qbar l) ^ k0) 0 := by
  intro l hl Ω _ _ _ W c Y _ _ _ hY
  obtain ⟨C, hC, h⟩ := exists_bound_multiplier (mat W) Y (by
    rintro ⟨x, hx⟩
    refine hY ⟨x, ?_⟩
    funext s
    rw [hx s]
    simp [ReciprocityTheory.Gal.d0, Loc.colRep, Matrix.toLin'_apply])
  have hlt : ‖((l : ℕ) : Qbar l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']
    exact Padic.norm_p_lt_one
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < (C + 1)⁻¹ by positivity) hlt
  refine ⟨k, fun n a _ ⟨x, _, hx⟩ => ?_⟩
  have h1 := h a x _ (norm_nonneg _) fun s i => hx s (Subgroup.mem_top s) i
  unfold Cg
  rw [sub_zero, norm_mul, norm_pow _ k]
  have h2 : C * ‖((l : ℕ) : Qbar l)‖ ^ k ≤ 1 := by
    calc C * ‖((l : ℕ) : Qbar l)‖ ^ k ≤ (C + 1) * (C + 1)⁻¹ :=
          mul_le_mul (by linarith) hk.le (by positivity) (by positivity)
      _ = 1 := mul_inv_cancel₀ (by positivity)
  calc ‖a‖ * ‖((l : ℕ) : Qbar l)‖ ^ k ≤ C * ‖((l : ℕ) : Qbar l) ^ n‖ * ‖((l : ℕ) : Qbar l)‖ ^ k :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = ‖((l : ℕ) : Qbar l) ^ n‖ * (C * ‖((l : ℕ) : Qbar l)‖ ^ k) := by ring
    _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) h2

end GlobalTheory.Ord2.GwCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonzeroClassBoundedTorsionStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzero_class_bounded_torsion : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (Y : G ℚ Ω → Fin 2 → Qbar l), (∀ s i j, mat W s i j ∈ c.O) → Y ∈ Z1 (Loc.colRep W) → (∀ s i, Y s i ∈ c.O) → Y ∉ ReciprocityTheory.Gal.B1 (Loc.colRep W) → ∃ k0 : ℕ, ∀ (n : ℕ) (a : Qbar l), a ∈ c.O → Cob1 c n W ⊤ (fun s => a • Y s) → Cg n (a * ((l : ℕ) : Qbar l) ^ k0) 0 := by
  first | exact @GlobalTheory.Ord2.GwCount.closed_multiplier | exact GlobalTheory.Ord2.GwCount.closed_multiplier | (intros; apply GlobalTheory.Ord2.GwCount.closed_multiplier <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualSelmerClassesUnboundedOrder
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.GwCount

theorem dual_classes_unbounded : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ¬ GrZero W A → ∃ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) ∧ ∀ m : ℕ, ∃ (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l), Coc1 c n (dual1 W) ⊤ z ∧ (∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) ∧ (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ Cob1 c n (dual1 W) (Ine (F := ℚ) B) z) ∧ (∃ x ∈ c.O, ∀ s ∈ Dec (F := ℚ) A, Cg n (z s 1) (mat (dual1 W) s 1 1 * x - x)) ∧ ¬ Cob1 c n (dual1 W) ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z s) := by
  intro hL l _ Ω _ _ _ e S A W hN hG
  obtain ⟨y, hyZ, hyU, hyG, hyB⟩ : ∃ y ∈ Z1 (Loc.colRep W), Unr W y ∧ Gr W A y ∧
      y ∉ ReciprocityTheory.Gal.B1 (Loc.colRep W) := by
    unfold GrZero at hG; push_neg at hG; exact hG
  have hcol : ∀ s (x : Fin 2 → Qbar l), Loc.colRep W s x = mat W s *ᵥ x := fun s x => by
    simp [Loc.colRep, Matrix.toLin'_apply]
  obtain ⟨c0, hc0⟩ := hN.int
  obtain ⟨c, k, hle, hYi, hYu, -, hYg⟩ := GlobalTheory.T.galois_cocycle_integral_after_scaling l Ω S W c0 y hN.cont hc0 hN.unr hyZ hyU A
  have hW : ∀ s i j, mat W s i j ∈ c.O := fun s i j => hle (hc0 s i j)
  obtain ⟨Y, hY⟩ : ∃ Y : G ℚ Ω → Fin 2 → Qbar l, Y = fun s => ((l : ℕ) : Qbar l) ^ k • y s := ⟨_, rfl⟩
  have hYs : ∀ s, Y s = ((l : ℕ) : Qbar l) ^ k • y s := fun s => by rw [hY]
  have hYZ : Y ∈ Z1 (Loc.colRep W) := by
    have : Y = ((l : ℕ) : Qbar l) ^ k • y := by rw [hY]; rfl
    rw [this]; exact (Z1 _).smul_mem _ hyZ
  have hYcoc : ∀ s t, Y (s * t) = Y s + mat W s *ᵥ Y t := fun s t => by
    rw [hYZ.2 s t, hcol]
  have hYI : ∀ s i, Y s i ∈ c.O := fun s i => by
    rw [hYs, Pi.smul_apply, smul_eq_mul]; exact hYi s i
  have hl0 : ((l : ℕ) : Qbar l) ^ k ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hYB : Y ∉ ReciprocityTheory.Gal.B1 (Loc.colRep W) := by
    intro h; apply hyB
    rw [mem_coboundaries1] at h ⊢
    obtain ⟨x, hx⟩ := h
    refine ⟨(((l : ℕ) : Qbar l) ^ k)⁻¹ • x, fun g => ?_⟩
    have h1 := hx g
    rw [hYs] at h1
    rw [map_smul, ← smul_sub, ← h1, smul_smul, inv_mul_cancel₀ hl0, one_smul]
  obtain ⟨k0, hk0⟩ := GlobalTheory.T.nonzero_class_bounded_torsion l Ω W c Y hW hYZ hYI hYB
  have hY0 : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Y a = 0 := by
    refine GlobalTheory.T.cocycle_vanishes_on_ker_toGS_of_inertia_coboundary l Ω e S A W Y hN hYZ fun q hq B hB => ?_
    have hlq : ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal := fun h => hq (hN.above q h)
    obtain ⟨x, -, hx⟩ := hYu q hlq B hB
    exact ⟨x, fun s hs => by rw [hYs]; exact hx s hs⟩
  refine ⟨c, hW, fun m => ?_⟩
  obtain ⟨C, hC⟩ := GlobalTheory.T.greenbergWiles_dualSelmer_lower_bound_mod_prime_pow hL l Ω e S A W hN c hW
  obtain ⟨B, hB⟩ := GlobalTheory.T.card_primePowTorsion_selmerClassesModPrimePow_bounded l Ω e S A W hN c hW (GlobalTheory.T.card_dualCocyclesModPrimePow_unramifiedOutsideS_bounded_alt hL l Ω e S A W hN c hW) m
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = C * B + 1 := ⟨_, rfl⟩
  have hlt : C * B < l ^ t := by
    have := Nat.lt_pow_self (Fact.out : l.Prime).one_lt (n := t)
    omega
  have hCv : ∀ {n : ℕ} (a b : Fin 2 → Qbar l), a = b → Cv n a b := fun a b h i => by
    subst h; simp [Cg]
  let yF : Fin (l ^ t) → G ℚ Ω → Fin 2 → Qbar l := fun j s => ((j : ℕ) : Qbar l) • Y s
  have hjO : ∀ j : Fin (l ^ t), ((j : ℕ) : Qbar l) ∈ c.O := fun j => natCast_mem _ _
  have hsel : ∀ j, GwCount.SelN c (t + k0) S A W (yF j) := by
    intro j
    refine ⟨⟨?_, fun s i => ?_, fun s _ r _ => hCv _ _ ?_⟩, fun a ha => hCv _ _ ?_, fun q _ hlq => ?_, ?_⟩
    · exact (hYZ.1.const_smul ((j : ℕ) : Qbar l)).continuousOn
    · simp only [yF, Pi.smul_apply, smul_eq_mul]; exact mul_mem (hjO j) (hYI s i)
    · simp only [yF]; rw [hYcoc, smul_add, Matrix.mulVec_smul]
    · simp only [yF]; rw [hY0 a ha, smul_zero]
    · obtain ⟨x, hxO, hx⟩ := hYu q hlq (placeOf Ω q) (isPlaceOver_placeOf Ω q)
      refine ⟨placeOf Ω q, isPlaceOver_placeOf Ω q, ((j : ℕ) : Qbar l) • x, fun i => ?_, fun s hs => hCv _ _ ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_mem (hjO j) (hxO i)
      · simp only [yF]; rw [hYs, hx s hs, Matrix.mulVec_smul, smul_sub]
    · obtain ⟨x, hxO, hx⟩ := hYg hyG
      refine ⟨((j : ℕ) : Qbar l) * x, mul_mem (hjO j) hxO, fun s hs => ?_⟩
      have h1 : yF j s 1 = ((j : ℕ) : Qbar l) * (mat W s 1 1 * x - x) := by
        simp only [yF, Pi.smul_apply, smul_eq_mul]; rw [hYs, Pi.smul_apply, smul_eq_mul, hx s hs]
      have h2 : ((j : ℕ) : Qbar l) * (mat W s 1 1 * x - x) = mat W s 1 1 * (((j : ℕ) : Qbar l) * x) - ((j : ℕ) : Qbar l) * x := by ring
      rw [h1, h2]; simp [Cg]
  have hne : ∀ i j, i ≠ j → ¬ Cob1 c (t + k0) W ⊤ (yF i - yF j) := by
    intro i j hij h
    have e1 : yF i - yF j = fun s => ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : Qbar l) • Y s := by
      funext s; simp only [yF, Pi.sub_apply]; push_cast; rw [sub_smul]
    rw [e1] at h
    have hd := hk0 (t + k0) _ (intCast_mem _ _) h
    refine GlobalTheory.T.not_congruent_zero_intCast_mul_prime_pow l t k0 (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ?_ ?_ hd
    · intro h0; apply hij; ext; omega
    · have hi := i.2; have hj := j.2
      have : ((l ^ t : ℕ) : ℤ) = (l : ℤ) ^ t := by push_cast; rfl
      rw [← this, abs_lt]; constructor <;> omega
  obtain ⟨N', z, hNC, hzS, hzne⟩ := hC (t + k0) (by omega) (l ^ t) yF hsel hne
  have hex : ∃ i, ¬ Cob1 c (t + k0) (dual1 W) ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z i s) := by
    by_contra h
    push_neg at h
    have h1 := hB (t + k0) N' z hzS hzne h
    have h2 : C * N' ≤ C * B := Nat.mul_le_mul_left C h1
    omega
  obtain ⟨i, hi⟩ := hex
  obtain ⟨h1, h2, h3, h4⟩ := hzS i
  exact ⟨t + k0, z i, h1, h2, h3, h4, hi⟩

end GlobalTheory.Ord2.GwCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualSelmerClassesUnboundedOrderStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
theorem _root_.GlobalTheory.T.exists_dualSelmer_classes_unbounded_order : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ¬ GrZero W A → ∃ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) ∧ ∀ m : ℕ, ∃ (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l), Coc1 c n (dual1 W) ⊤ z ∧ (∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) ∧ (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ Cob1 c n (dual1 W) (Ine (F := ℚ) B) z) ∧ (∃ x ∈ c.O, ∀ s ∈ Dec (F := ℚ) A, Cg n (z s 1) (mat (dual1 W) s 1 1 * x - x)) ∧ ¬ Cob1 c n (dual1 W) ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z s) := by
  first | exact @GlobalTheory.Ord2.GwCount.dual_classes_unbounded | exact GlobalTheory.Ord2.GwCount.dual_classes_unbounded | (intros; apply GlobalTheory.Ord2.GwCount.dual_classes_unbounded <;> assumption)
end
