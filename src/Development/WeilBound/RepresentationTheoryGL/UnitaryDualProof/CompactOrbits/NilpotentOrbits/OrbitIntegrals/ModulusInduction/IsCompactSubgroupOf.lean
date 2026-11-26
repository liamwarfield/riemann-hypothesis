module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ZNClosed

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusInduction.PieceCount
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusInduction.MemOrbitIff
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusInduction.IsClosedGzS
noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.T.Nil.Orb.BStep

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem totDisc : TotallyDisconnectedSpace k := by
  have := GlobalTheory.SplitWeil.t2Space k
  have : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  infer_instance

def SpT (k : Type) [Field k] (n : ℕ) : Type := Sp k n

instance : TopologicalSpace (SpT k n) := inferInstanceAs (TopologicalSpace (Sp k n))

theorem t2Sp : T2Space (SpT k n) := by
  have := GlobalTheory.SplitWeil.t2Space k
  have : T2Space (Matrix (Fin n) (Fin n) k) := inferInstanceAs (T2Space (Fin n → Fin n → k))
  exact inferInstanceAs (T2Space (Matrix (Fin n) (Fin n) k × (Fin n → k)))

theorem lcSp : LocallyCompactSpace (SpT k n) := by
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) k) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → k))
  exact inferInstanceAs (LocallyCompactSpace (Matrix (Fin n) (Fin n) k × (Fin n → k)))

theorem tdSp : TotallyDisconnectedSpace (SpT k n) := by
  have : TotallyDisconnectedSpace k := totDisc
  have : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  exact inferInstanceAs (TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k × (Fin n → k)))

instance actGL : MulAction (GL (Fin n) k) (SpT k n) where
  smul g p := (act g p : Sp k n)
  one_smul := act_one (k := k)
  mul_smul := act_mul (k := k)

theorem contSMul : ContinuousSMul (GL (Fin n) k) (SpT k n) := by
  refine ⟨?_⟩
  show Continuous fun p : GL (Fin n) k × (Matrix (Fin n) (Fin n) k × (Fin n → k)) => act p.1 p.2
  unfold act
  refine Continuous.prodMk ?_ ?_
  · exact ((Units.continuous_val.comp continuous_fst).matrix_mul
      (continuous_fst.comp continuous_snd)).matrix_mul (Units.continuous_coe_inv.comp continuous_fst)
  · exact (Units.continuous_val.comp continuous_fst).matrix_mulVec (continuous_snd.comp continuous_snd)

theorem isClosed_GzS (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : IsClosed (GzS Z : Set (GL (Fin n) k)) := by
  have := GlobalTheory.SplitWeil.t2Space k
  have : T2Space (Matrix (Fin n) (Fin n) k) := inferInstanceAs (T2Space (Fin n → Fin n → k))
  have e : (GzS Z : Set (GL (Fin n) k)) =
      ⋂ a ∈ (Z : Set (Matrix (Fin n) (Fin n) k)), {g : GL (Fin n) k | a * g.val = g.val * a} := by
    ext g
    simp [GzS, Gz]
  rw [e]
  exact isClosed_biInter fun a _ => isClosed_eq (continuous_const.matrix_mul Units.continuous_val)
    (Units.continuous_val.matrix_mul continuous_const)

theorem lcH (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : LocallyCompactSpace (GzS Z) :=
  (isClosed_GzS Z).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem tdGL : TotallyDisconnectedSpace (GL (Fin n) k) := by
  have : TotallyDisconnectedSpace k := totDisc
  have : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  refine ⟨fun t _ ht => ?_⟩
  have h := isTotallyDisconnected_of_totallyDisconnectedSpace (Units.val '' t) (Units.val '' t)
    subset_rfl (ht.image _ Units.continuous_val.continuousOn)
  intro x hx y hy
  exact Units.val_injective (h ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)

theorem tdH (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : TotallyDisconnectedSpace (GzS Z) := by
  have := tdGL (k := k) (n := n)
  infer_instance

theorem scH (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : SigmaCompactSpace (GzS Z) := by
  have := lcH Z
  have := GlobalTheory.SplitWeil.secondCountable k
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → k))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) k)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  have : SecondCountableTopology (GL (Fin n) k) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  have : SecondCountableTopology (GzS Z) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  exact sigmaCompactSpace_of_locallyCompact_secondCountable

theorem contSMulH (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : ContinuousSMul (GzS Z) (SpT k n) := by
  have := contSMul (k := k) (n := n)
  refine ⟨?_⟩
  show Continuous fun p : GzS Z × SpT k n => (p.1 : GL (Fin n) k) • p.2
  exact (continuous_subtype_val.comp continuous_fst).smul continuous_snd

theorem isOpen_UU : IsOpen (UU : Set (Sp k n)) := by
  have := GlobalTheory.SplitWeil.t2Space k
  exact isOpen_compl_singleton.preimage continuous_snd


open scoped Pointwise in
theorem relIndex_ne_zero {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {J A : Subgroup H}
    (hJ : IsCompact (J : Set H)) (hA : IsOpen (A : Set H)) : A.relIndex J ≠ 0 := by
  letI : SMul J (Set J) := ⟨fun g s => (fun x => g * x) '' s⟩
  have : CompactSpace J := isCompact_iff_compactSpace.mp hJ
  have hA' : IsOpen ((A.subgroupOf J : Subgroup J) : Set J) := by
    rw [Subgroup.coe_subgroupOf]
    exact hA.preimage continuous_subtype_val
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun g : J => g • ((A.subgroupOf J : Subgroup J) : Set J))
    (fun g => by
      rw [← Set.image_smul]
      exact (Homeomorph.mulLeft g).isOpenMap _ hA')
    (fun x _ => Set.mem_iUnion.2 ⟨x, ⟨1, (A.subgroupOf J).one_mem, mul_one x⟩⟩)
  have hc : ⋃ i ∈ t, (fun g : J => g) i • ((A.subgroupOf J : Subgroup J) : Set J) = Set.univ :=
    Set.eq_univ_of_univ_subset ht
  have := Subgroup.finiteIndex_of_leftCoset_cover_const hc
  exact Subgroup.finiteIndex_iff.mp this

end PositivityTheory.RgUd.T.Nil.Orb.BStep
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusInduction.TraceMulEqZero
noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.T.Nil.Orb.BStep

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

set_option linter.unusedSectionVars false

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem qZ_add (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x y : Matrix (Fin n) (Fin n) k) :
    qZ Z (x + y) = qZ Z x + qZ Z y := by
  funext i; simp [qZ, mul_add, trace_add]

theorem qZ_sub (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x y : Matrix (Fin n) (Fin n) k) :
    qZ Z (x - y) = qZ Z x - qZ Z y := by
  funext i; simp [qZ, mul_sub, trace_sub]

theorem qZ_smul (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (r : k) (x : Matrix (Fin n) (Fin n) k) :
    qZ Z (r • x) = r • qZ Z x := by
  funext i
  simp only [qZ, Pi.smul_apply, Matrix.mul_smul, trace_smul]

theorem piZ_congr (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {x y : Matrix (Fin n) (Fin n) k}
    (h : qZ Z x = qZ Z y) : piZ Z x = piZ Z y := by
  unfold piZ; rw [h]

theorem piZ_mem (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x : Matrix (Fin n) (Fin n) k) : piZ Z x ∈ Z := by
  unfold piZ
  split
  · rename_i h; exact h.choose_spec.1
  · exact Z.zero_mem

theorem qZ_conj (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (h : GL (Fin n) k) (hh : h ∈ Gz Z)
    (x : Matrix (Fin n) (Fin n) k) : qZ Z (h.val * x * h⁻¹.val) = qZ Z x := by
  funext i
  simp only [qZ]
  have hb := hh _ ((Module.finBasis k Z) i).2
  have e1 : (((Module.finBasis k Z) i : Z) : Matrix (Fin n) (Fin n) k) * (h.val * x * h⁻¹.val)
      = h.val * ((((Module.finBasis k Z) i : Z) : Matrix (Fin n) (Fin n) k) * x) * h⁻¹.val := by
    simp only [← mul_assoc, hb]
  rw [e1, trace_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]

theorem conj_of_mem (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (h : GL (Fin n) k) (hh : h ∈ Gz Z)
    {c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z) : h.val * c * h⁻¹.val = c := by
  rw [← hh c hc, mul_assoc, Units.mul_inv, mul_one]

theorem sig_act (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (t : kˣ) (h : GL (Fin n) k) (hh : h ∈ Gz Z)
    (q : Sp k n) : sig Z t (act h q) = act h (sig Z t q) := by
  have h1 : piZ Z (h.val * q.1 * h⁻¹.val) = piZ Z q.1 := piZ_congr Z (qZ_conj Z h hh q.1)
  have h2 : h.val * piZ Z q.1 * h⁻¹.val = piZ Z q.1 := conj_of_mem Z h hh (piZ_mem Z q.1)
  simp only [sig, act]
  refine Prod.ext ?_ rfl
  show piZ Z (h.val * q.1 * h⁻¹.val) + (t : k) • (h.val * q.1 * h⁻¹.val - piZ Z (h.val * q.1 * h⁻¹.val))
    = h.val * (piZ Z q.1 + (t : k) • (q.1 - piZ Z q.1)) * h⁻¹.val
  rw [h1, mul_add, add_mul, h2, Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul, h2]

theorem reg_in (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) {c : Matrix (Fin n) (Fin n) k}
    (hc : c ∈ Z) : ∃ g ∈ Z, c * g * c = c := by
  obtain ⟨hcomm, hred⟩ := hZ
  haveI := hred
  have hint : IsIntegral k c := Algebra.IsIntegral.isIntegral c
  have hp0 : minpoly k c ≠ 0 := minpoly.ne_zero hint
  obtain ⟨q, hpq, hnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd (minpoly k c) hp0 0
  have hq0 : q.coeff 0 ≠ 0 := by
    intro h0
    apply hnd
    rw [map_zero, sub_zero, Polynomial.X_dvd_iff]
    exact h0
  have haZ : Polynomial.aeval c q.divX ∈ Z :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 hc) (Polynomial.aeval_mem_adjoin_singleton k c)
  have hev : q.coeff 0 • c ^ Polynomial.rootMultiplicity 0 (minpoly k c)
      + c ^ Polynomial.rootMultiplicity 0 (minpoly k c) * c * Polynomial.aeval c q.divX = 0 := by
    have h1 := minpoly.aeval k c
    rw [hpq, ← Polynomial.X_mul_divX_add q] at h1
    simp only [map_mul, map_pow, map_sub, map_add (f := _), Polynomial.aeval_X, Polynomial.aeval_C, map_zero,
      sub_zero] at h1
    rw [mul_add, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, ← mul_assoc] at h1
    rw [add_comm]
    exact h1
  generalize Polynomial.rootMultiplicity 0 (minpoly k c) = m at hev
  generalize Polynomial.aeval c q.divX = a at hev haZ
  generalize q.coeff 0 = s at hev hq0
  have h2 : c ^ m * c * a = -(s • c ^ m) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hev
  have hgZ : (-(s⁻¹) • a) ∈ Z := Z.smul_mem haZ _
  have hmu : c ^ m * (1 - c * (-(s⁻¹) • a)) = 0 := by
    rw [mul_sub, mul_one, Matrix.mul_smul, Matrix.mul_smul, ← mul_assoc, h2, smul_neg, neg_smul,
      neg_neg, smul_smul, inv_mul_cancel₀ hq0, one_smul, sub_self]
  generalize -(s⁻¹) • a = g at hgZ hmu
  have hcg : Commute c g := hcomm c hc g hgZ
  have hcomm' : Commute c (1 - c * g) := (Commute.one_right c).sub_right ((Commute.refl c).mul_right hcg)
  have hpow : (c * (1 - c * g)) ^ (m + 1) = 0 := by
    rw [hcomm'.mul_pow, pow_succ', pow_succ', mul_assoc, ← mul_assoc (c ^ m), hmu, zero_mul, mul_zero]
  have hdZ : c * (1 - c * g) ∈ Z := Z.mul_mem hc (Z.sub_mem Z.one_mem (Z.mul_mem hc hgZ))
  have hnil : IsNilpotent (⟨c * (1 - c * g), hdZ⟩ : Z) :=
    ⟨m + 1, Subtype.ext (by simpa using hpow)⟩
  have hd0 : c * (1 - c * g) = 0 := congrArg Subtype.val hnil.eq_zero
  refine ⟨g, hgZ, ?_⟩
  rw [mul_sub, mul_one, sub_eq_zero] at hd0
  have hcg' : c * g = g * c := hcg
  rw [mul_assoc, ← hcg']
  exact hd0.symm

theorem idem_zero [CharZero k] (e : Matrix (Fin n) (Fin n) k) (he : e * e = e) (ht : trace e = 0) : e = 0 := by
  have hf : IsIdempotentElem (Matrix.toLin' e) := by
    show Matrix.toLin' e * Matrix.toLin' e = Matrix.toLin' e
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, he]
  have ht' : LinearMap.trace k _ (Matrix.toLin' e) = 0 := by
    rw [LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin n)), LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin']
    exact ht
  have h0 := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hf ht'
  exact (LinearEquiv.map_eq_zero_iff _).1 h0

theorem trace_mul_eq_zero (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {c : Matrix (Fin n) (Fin n) k}
    (hq : qZ Z c = 0) {b : Matrix (Fin n) (Fin n) k} (hb : b ∈ Z) : trace (b * c) = 0 := by
  have hsum := (Module.finBasis k Z).sum_repr ⟨b, hb⟩
  have hb' : b = ∑ i, ((Module.finBasis k Z).repr ⟨b, hb⟩ i) •
      (((Module.finBasis k Z) i : Z) : Matrix (Fin n) (Fin n) k) := by
    have h1 := congrArg Subtype.val hsum
    push_cast at h1
    exact h1.symm
  rw [hb', Finset.sum_mul, trace_sum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Matrix.smul_mul, trace_smul]
  have h2 := congrFun hq i
  simp only [qZ, Pi.zero_apply] at h2
  rw [h2, smul_zero]

theorem qZ_inj [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z)
    {c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z) (hq : qZ Z c = 0) : c = 0 := by
  obtain ⟨g, hg, hcgc⟩ := reg_in Z hZ hc
  have hgc : g * c = c * g := hZ.1 g hg c hc
  have hidem : (c * g) * (c * g) = c * g := by
    rw [← mul_assoc, hcgc]
  have htr : trace (c * g) = 0 := by
    rw [trace_mul_comm]
    exact trace_mul_eq_zero Z hq hg
  have he0 := idem_zero (c * g) hidem htr
  rw [← hcgc, he0, zero_mul]

theorem exists_qZ [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z)
    (x : Matrix (Fin n) (Fin n) k) : ∃ c ∈ Z, qZ Z c = qZ Z x := by
  let φ : Z →ₗ[k] (Fin (Module.finrank k Z) → k) :=
    { toFun := fun c => qZ Z c.1
      map_add' := fun a b => qZ_add Z a.1 b.1
      map_smul' := fun r a => qZ_smul Z r a.1 }
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    exact Subtype.ext (qZ_inj Z hZ a.2 ha)
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  obtain ⟨a, ha⟩ := hsurj (qZ Z x)
  exact ⟨a.1, a.2, ha⟩

theorem piZ_spec [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z)
    (x : Matrix (Fin n) (Fin n) k) : qZ Z (piZ Z x) = qZ Z x := by
  unfold piZ
  rw [dite_eq_left (exists_qZ Z hZ x)]
  exact (exists_qZ Z hZ x).choose_spec.2

theorem piZ_eq [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z)
    {x c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z) (h : qZ Z c = qZ Z x) : piZ Z x = c := by
  have := qZ_inj Z hZ (Z.sub_mem (piZ_mem Z x) hc) (by rw [qZ_sub, piZ_spec Z hZ, h, sub_self])
  exact sub_eq_zero.mp this

def piL [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) :
    Matrix (Fin n) (Fin n) k →ₗ[k] Matrix (Fin n) (Fin n) k where
  toFun := piZ Z
  map_add' x y := by
    refine piZ_eq Z hZ (Z.add_mem (piZ_mem Z x) (piZ_mem Z y)) ?_
    rw [qZ_add, qZ_add, piZ_spec Z hZ, piZ_spec Z hZ]
  map_smul' r x := by
    refine piZ_eq Z hZ (Z.smul_mem (piZ_mem Z x) r) ?_
    rw [qZ_smul, qZ_smul, piZ_spec Z hZ]; rfl

theorem continuous_piZ [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) :
    Continuous (piZ Z (n := n)) := by
  have hrep : ∀ x : Matrix (Fin n) (Fin n) k,
      piZ Z x = ∑ i, ∑ j, x i j • piZ Z (Matrix.single i j (1 : k)) := by
    intro x
    have h := congrArg (piL Z hZ) (Matrix.matrix_eq_sum_single x)
    have hs : ∀ i j, Matrix.single i j (x i j) = x i j • Matrix.single i j (1 : k) := by
      intro i j
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hs, map_sum, map_smul] at h
    exact h
  have hfun : piZ Z (n := n) = fun x => ∑ i, ∑ j, x i j • piZ Z (Matrix.single i j (1 : k)) := funext hrep
  rw [hfun]
  fun_prop

theorem sig_inv_sig [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (t : kˣ)
    (q : Sp k n) : sig Z t⁻¹ (sig Z t q) = q := by
  obtain ⟨x, v⟩ := q
  have hP : piZ Z (piZ Z x + (t : k) • (x - piZ Z x)) = piZ Z x := by
    refine piZ_eq Z hZ (piZ_mem Z x) ?_
    rw [qZ_add, qZ_smul, qZ_sub, piZ_spec Z hZ, sub_self, smul_zero, add_zero]
  simp only [sig]
  refine Prod.ext ?_ rfl
  show piZ Z (piZ Z x + (t : k) • (x - piZ Z x)) + ((t⁻¹ : kˣ) : k) • (piZ Z x + (t : k) • (x - piZ Z x) - piZ Z (piZ Z x + (t : k) • (x - piZ Z x))) = x
  rw [hP, add_sub_cancel_left, smul_smul, Units.inv_mul, one_smul, add_sub_cancel]

theorem continuous_sig [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (t : kˣ) :
    Continuous (sig Z t) := by
  have hc := continuous_piZ Z hZ
  unfold sig
  fun_prop

end PositivityTheory.RgUd.T.Nil.Orb.BStep
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusInduction.Imports
namespace PositivityTheory.RgUd.T.Nil.Orb.BStep

open scoped Pointwise

theorem count {G X : Type*} [Group G] [MulAction G X] (J A : Subgroup G) (hAJ : A ≤ J)
    (hn : ∀ j ∈ J, ∀ a ∈ A, j * a * j⁻¹ ∈ A) (y : X) :
    Nat.card ((fun j : G => j • ((fun a : G => a • y) '' (A : Set G))) '' (J : Set G)) *
      (A ⊓ MulAction.stabilizer G y).relIndex (J ⊓ MulAction.stabilizer G y) = A.relIndex J := by
  classical
  set P : Set X := (fun a : G => a • y) '' (A : Set G) with hP
  set S := MulAction.stabilizer G y with hS
  have hsmul : ∀ u : J, u • P = (u : G) • P := fun u => rfl
  have himg : ((fun j : G => j • P) '' (J : Set G)) = MulAction.orbit J P := by
    ext Q
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, j.2, rfl⟩
  have hAP : ∀ u ∈ A, u • P = P := by
    intro u hu
    ext x
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨u * a, A.mul_mem hu ha, mul_smul u a y⟩
    · rintro ⟨a, ha, rfl⟩
      refine ⟨(u⁻¹ * a) • y, ⟨u⁻¹ * a, A.mul_mem (A.inv_mem hu) ha, rfl⟩, ?_⟩
      simp [mul_smul]
  have hSP : ∀ s ∈ J, s ∈ S → s • P = P := by
    intro s hsJ hsS
    have hsy : s • y = y := hsS
    ext x
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨s * a * s⁻¹, hn s hsJ a ha, ?_⟩
      show (s * a * s⁻¹) • y = s • a • y
      conv_lhs => rw [← hsy]
      simp [mul_smul]
    · rintro ⟨a, ha, rfl⟩
      have h1 : s⁻¹ * a * s⁻¹⁻¹ ∈ A := hn s⁻¹ (J.inv_mem hsJ) a ha
      rw [inv_inv] at h1
      refine ⟨(s⁻¹ * a * s) • y, ⟨_, h1, rfl⟩, ?_⟩
      show s • (s⁻¹ * a * s) • y = a • y
      rw [mul_smul, mul_smul, hsy, smul_inv_smul]
  have hstab : MulAction.stabilizer J P = A.subgroupOf J ⊔ S.subgroupOf J := by
    apply le_antisymm
    · intro u hu
      have hu' : (u : G) • P = P := hu
      have hy : (u : G) • y ∈ P := by
        rw [← hu']
        exact Set.smul_mem_smul_set ⟨1, A.one_mem, one_smul G y⟩
      obtain ⟨a, ha, hay⟩ := hy
      have hay' : a • y = (u : G) • y := hay
      have haJ : a ∈ J := hAJ ha
      have hs : a⁻¹ * (u : G) ∈ S := by
        show (a⁻¹ * (u : G)) • y = y
        rw [mul_smul, ← hay', inv_smul_smul]
      have e : u = (⟨a, haJ⟩ : J) * ⟨a⁻¹ * u, J.mul_mem (J.inv_mem haJ) u.2⟩ := by
        ext
        simp
      rw [e]
      exact Subgroup.mul_mem_sup (show (⟨a, haJ⟩ : J) ∈ A.subgroupOf J from ha)
        (show (⟨a⁻¹ * u, J.mul_mem (J.inv_mem haJ) u.2⟩ : J) ∈ S.subgroupOf J from hs)
    · refine sup_le ?_ ?_
      · intro u hu
        show u • P = P
        rw [hsmul]
        exact hAP u hu
      · intro u hu
        show u • P = P
        rw [hsmul]
        exact hSP u u.2 hu
  have hnorm : (A.subgroupOf J).Normal := ⟨fun a ha g => by
    show ((g * a * g⁻¹ : J) : G) ∈ A
    simpa using hn g g.2 a ha⟩
  have hcard : Nat.card ((fun j : G => j • P) '' (J : Set G)) = (A.subgroupOf J ⊔ S.subgroupOf J).index := by
    rw [himg, ← hstab, MulAction.index_stabilizer]
    rfl
  have hb : (A ⊓ S).relIndex (J ⊓ S) = (A.subgroupOf J).relIndex (S.subgroupOf J) := by
    rw [← Subgroup.inf_subgroupOf_right S J, Subgroup.relIndex_subgroupOf inf_le_right]
    have h1 := Subgroup.relIndex_inf_mul_relIndex A S (J ⊓ S)
    rw [(Subgroup.relIndex_eq_one).2 inf_le_right, mul_one] at h1
    rw [← h1, show S ⊓ (J ⊓ S) = J ⊓ S from inf_of_le_right inf_le_right, inf_comm J S]
  have hm := Subgroup.relIndex_mul_index (le_sup_left : A.subgroupOf J ≤ A.subgroupOf J ⊔ S.subgroupOf J)
  rw [Subgroup.relIndex_sup_left] at hm
  rw [hcard, hb, mul_comm, hm]
  rfl

end PositivityTheory.RgUd.T.Nil.Orb.BStep
end

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker MulAction

open scoped Pointwise

namespace PositivityTheory.RgUd.T.Nil.Orb.BStep

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

set_option linter.unusedSectionVars false

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

attribute [local instance] t2Sp lcSp tdSp contSMul lcH tdH scH contSMulH

theorem act_inv_act (h : GL (Fin n) k) (q : Sp k n) : act h⁻¹ (act h q) = q := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_snd_ne (h : GL (Fin n) k) {q : Sp k n} (hq : q.2 ≠ 0) : (act h q).2 ≠ 0 := by
  intro h0
  apply hq
  rw [← act_inv_act h q]
  show ((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ (act h q).2 = 0
  rw [h0, mulVec_zero]

def toT (p : Sp k n) : SpT k n := p

theorem smulH_eq (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (h : GzS Z) (q : SpT k n) :
    h • q = (act (h : GL (Fin n) k) q : Sp k n) := rfl

theorem mem_orbit_iff' (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {p q : Sp k n} :
    toT q ∈ orbit (GzS Z) (toT p) ↔ q ∈ orb Z p := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, g.2, ?_⟩
    dsimp only at hg
    rw [smulH_eq] at hg
    exact hg
  · rintro ⟨g, hg, hgq⟩
    have hg' : g ∈ GzS Z := hg
    refine ⟨⟨g, hg'⟩, ?_⟩
    show (⟨g, hg'⟩ : GzS Z) • toT p = toT q
    rw [smulH_eq]
    exact hgq

theorem lift_on_C' {U₁ C O : Set (Sp k n)} (hO : U₁ ∩ C = O) {P : Set (SpT k n)} (hP : ∀ x, toT x ∈ P → x ∈ O)
    {F : Sp k n → ℂ} (hF : F ∈ supportedIn U₁) (hFO : ∀ x ∈ O, F x = P.indicator 1 (toT x)) :
    ∀ x ∈ C, F x = P.indicator 1 (toT x) := by
  intro x hx
  by_cases hxU : x ∈ U₁
  · exact hFO x (by rw [← hO]; exact ⟨hxU, hx⟩)
  · have hF0 : F x = 0 := by
      by_contra hne
      exact hxU ((mem_supportedIn.1 hF).2 hne)
    have hxP : toT x ∉ P := by
      intro hP'
      have hxO := hP x hP'
      rw [← hO] at hxO
      exact hxU hxO.1
    rw [hF0, Set.indicator_of_notMem hxP]

theorem xi_eq {ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} {C : Set (Sp k n)} (hξC : SuppU ξ C) {a b : Sp k n → ℂ}
    (ha : a ∈ supportedIn UU) (hb : b ∈ supportedIn UU) (h : ∀ q ∈ C, a q = b q) : ξ a = ξ b := by
  have := hξC (a - b) (Submodule.sub_mem _ ha hb) (fun q hq => by simp [h q hq])
  rwa [map_sub, sub_eq_zero] at this

def sigH [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (t : kˣ) : Sp k n ≃ₜ Sp k n where
  toFun := sig Z t
  invFun := sig Z t⁻¹
  left_inv := sig_inv_sig Z hZ t
  right_inv q := by simpa using sig_inv_sig Z hZ t⁻¹ q
  continuous_toFun := continuous_sig Z hZ t
  continuous_invFun := continuous_sig Z hZ t⁻¹

theorem comp_sig_mem [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (t : kˣ)
    {f : Sp k n → ℂ} (hf : f ∈ supportedIn UU) : (fun q => f (sig Z t q)) ∈ supportedIn UU := by
  rw [mem_supportedIn, GroundTheory.Automorphic.mem_locallyConstantCompactSupport] at hf ⊢
  obtain ⟨⟨hlc, hcs⟩, hsu⟩ := hf
  refine ⟨⟨hlc.comp_continuous (continuous_sig Z hZ t), hcs.comp_homeomorph (sigH Z hZ t)⟩, ?_⟩
  intro q hq
  have h1 : (sig Z t q).2 ≠ 0 := hsu (show sig Z t q ∈ Function.support f from hq)
  exact h1

theorem comp_act_mem (h : GL (Fin n) k) {f : Sp k n → ℂ} {V : Set (Sp k n)} (hf : f ∈ supportedIn V) :
    (fun q => f (act h q)) ∈ supportedIn ((fun q => act h⁻¹ q) '' V) := by
  have hc : ∀ g : GL (Fin n) k, Continuous (fun q : Sp k n => act g q) := by
    intro g
    unfold act
    fun_prop
  let e : Sp k n ≃ₜ Sp k n :=
    { toFun := fun q => act h q
      invFun := fun q => act h⁻¹ q
      left_inv := fun q => act_inv_act h q
      right_inv := fun q => by simpa using act_inv_act h⁻¹ q
      continuous_toFun := hc h
      continuous_invFun := hc h⁻¹ }
  rw [mem_supportedIn, GroundTheory.Automorphic.mem_locallyConstantCompactSupport] at hf ⊢
  obtain ⟨⟨hlc, hcs⟩, hsu⟩ := hf
  refine ⟨⟨hlc.comp_continuous (hc h), hcs.comp_homeomorph e⟩, ?_⟩
  intro q hq
  exact ⟨act h q, hsu hq, act_inv_act h q⟩

theorem comp_act_memUU (h : GL (Fin n) k) {f : Sp k n → ℂ} (hf : f ∈ supportedIn UU) :
    (fun q => f (act h q)) ∈ supportedIn UU := by
  refine supportedIn_mono ?_ (comp_act_mem h hf)
  rintro _ ⟨q, hq, rfl⟩
  exact act_snd_ne h⁻¹ hq

end PositivityTheory.RgUd.T.Nil.Orb.BStep
end
end

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker MulAction

open scoped Pointwise

namespace PositivityTheory.RgUd.T.Nil.Orb.BStep

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

attribute [local instance] t2Sp lcSp tdSp contSMul lcH tdH scH contSMulH

theorem piece_count (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (hξ : Inv Z ξ)
    {C U₁ : Set (Sp k n)} (hC : IsClosed C) (hU₁ : IsOpen U₁) (hU₁UU : U₁ ⊆ UU) {p : Sp k n}
    (hCinv : ∀ h ∈ Gz Z, ∀ q ∈ C, act h q ∈ C)
    (hO : U₁ ∩ C = orb Z p) (hξC : SuppU ξ C)
    {J A : Subgroup (GzS Z)} (hJc : IsCompact (J : Set (GzS Z))) (hAo : IsOpen (A : Set (GzS Z))) (hAJ : A ≤ J)
    (hn : ∀ j ∈ J, ∀ a ∈ A, j * a * j⁻¹ ∈ A)
    {fJ fA : Sp k n → ℂ} (hfJ : fJ ∈ supportedIn U₁) (hfA : fA ∈ supportedIn U₁)
    (hfJO : ∀ x ∈ orb Z p, fJ x = (orbitPiece J (toT p)).indicator 1 (toT x))
    (hfAO : ∀ x ∈ orb Z p, fA x = (orbitPiece A (toT p)).indicator 1 (toT x)) :
    ξ fJ * ((A ⊓ stabilizer (GzS Z) (toT p)).relIndex (J ⊓ stabilizer (GzS Z) (toT p)) : ℂ) =
      (A.relIndex J : ℂ) * ξ fA := by
  classical
  have hOorb : orbit (GzS Z) (toT p) = orb Z p := Set.ext fun q => mem_orbit_iff' Z (p := p) (q := q)
  have hO' : ((U₁ : Set (SpT k n)) ∩ C) = orbit (GzS Z) (toT p) := by rw [hOorb]; exact hO
  have hOl : IsLocallyClosed (orbit (GzS Z) (toT p)) := ⟨U₁, C, hU₁, hC, hO'.symm⟩
  obtain ⟨𝒮, -, h𝒮, hsum⟩ := exists_finset_orbitPiece (X := SpT k n) hOl hJc hAo hAJ hn (mem_orbit_self (toT p))
  choose! j hjJ hjS using h𝒮
  have hPsub : ∀ B : Subgroup (GzS Z), ∀ x, toT x ∈ orbitPiece B (toT p) → x ∈ orb Z p := by
    intro B x hx
    exact (mem_orbit_iff' Z).1 (orbitPiece_subset_orbit (mem_orbit_self (toT p)) hx)
  have hfAUU : fA ∈ supportedIn UU := supportedIn_mono hU₁UU hfA
  have htr : ∀ S ∈ 𝒮, ξ (fun q => fA (act (((j S)⁻¹ : GzS Z) : GL (Fin n) k) q)) = ξ fA := by
    intro S _
    exact hξ _ ((j S)⁻¹).2 fA (supportedIn_mono (Set.subset_univ _) hfA)
  have hsumξ : ξ fJ = ∑ S ∈ 𝒮, ξ (fun q => fA (act (((j S)⁻¹ : GzS Z) : GL (Fin n) k) q)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum]
    refine xi_eq hξC (supportedIn_mono hU₁UU hfJ)
      (Submodule.sum_mem _ fun S _ => comp_act_memUU ((j S)⁻¹ : GzS Z).1 hfAUU) fun x hx => ?_
    rw [lift_on_C' hO (hPsub J) hfJ hfJO x hx, hsum (toT x), Finset.sum_apply]
    refine Finset.sum_congr rfl fun S hS => ?_
    have hx' : act (((j S)⁻¹ : GzS Z) : GL (Fin n) k) x ∈ C := hCinv _ ((j S)⁻¹).2 x hx
    rw [lift_on_C' hO (hPsub A) hfA hfAO _ hx']
    conv_lhs => rw [hjS S hS]
    by_cases hxS : toT (act (((j S)⁻¹ : GzS Z) : GL (Fin n) k) x) ∈ orbitPiece A (toT p)
    · rw [Set.indicator_of_mem (Set.mem_smul_set_iff_inv_smul_mem.2 (show (j S)⁻¹ • toT x ∈ _ from hxS)),
        Set.indicator_of_mem hxS]
      rfl
    · rw [Set.indicator_of_notMem (fun h' => hxS (Set.mem_smul_set_iff_inv_smul_mem.1 h')),
        Set.indicator_of_notMem hxS]
  have hcard : ξ fJ = (𝒮.card : ℂ) * ξ fA := by
    rw [hsumξ, Finset.sum_congr rfl htr, Finset.sum_const, nsmul_eq_mul]
  have hset : ((𝒮 : Set (Set (SpT k n)))) =
      (fun i : GzS Z => i • orbitPiece A (toT p)) '' (J : Set (GzS Z)) := by
    ext P
    constructor
    · intro hP
      exact ⟨j P, hjJ P hP, (hjS P hP).symm⟩
    · rintro ⟨i, hi, rfl⟩
      have hx : i • toT p ∈ orbitPiece J (toT p) := ⟨i, hi, rfl⟩
      have h1 := hsum (i • toT p)
      rw [Set.indicator_of_mem hx] at h1
      obtain ⟨S, hS, hiS⟩ : ∃ S ∈ 𝒮, i • toT p ∈ S := by
        by_contra hcon
        push Not at hcon
        rw [Finset.sum_eq_zero (fun S hS => Set.indicator_of_notMem (hcon S hS) _)] at h1
        exact one_ne_zero h1
      have e1 : i • orbitPiece A (toT p) = orbitPiece A (i • toT p) :=
        smul_orbitPiece (hn i hi) (fun a ha => by simpa using hn i⁻¹ (J.inv_mem hi) a ha) _
      have e2 : S = orbitPiece A (j S • toT p) := (hjS S hS).trans
        (smul_orbitPiece (hn _ (hjJ S hS)) (fun a ha => by simpa using hn _ (J.inv_mem (hjJ S hS)) a ha) _)
      have e3 : orbitPiece A (i • toT p) = orbitPiece A (j S • toT p) :=
        orbitPiece_eq_of_mem (e2 ▸ hiS)
      show i • orbitPiece A (toT p) ∈ (𝒮 : Set (Set (SpT k n)))
      rw [Finset.mem_coe, e1, e3, ← e2]
      exact hS
  have hc := count J A hAJ hn (toT p)
  change Nat.card ((fun i : GzS Z => i • orbitPiece A (toT p)) '' (J : Set (GzS Z))) * _ = _ at hc
  rw [← hset, Nat.card_coe_set_eq, Set.ncard_coe_finset] at hc
  rw [hcard, mul_assoc, mul_comm (ξ fA), ← mul_assoc]
  exact_mod_cast congrArg (fun N : ℕ => (N : ℂ) * ξ fA) hc

end PositivityTheory.RgUd.T.Nil.Orb.BStep
end
end

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker MulAction

open scoped Pointwise

namespace PositivityTheory.RgUd.T.Nil.Orb.BStep

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

set_option linter.unusedSectionVars false

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

attribute [local instance] t2Sp lcSp tdSp contSMul lcH tdH scH contSMulH

theorem stab_subgroupOf {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (p : Sp k n) :
    (stab Z p).subgroupOf (GzS Z) = stabilizer (GzS Z) (toT p) := by
  ext x
  simp only [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨x.2, h⟩

theorem inf_subgroupOf' {G : Type*} [Group G] (A B G' : Subgroup G) :
    (A ⊓ B).subgroupOf G' = A.subgroupOf G' ⊓ B.subgroupOf G' := by
  ext x
  simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]

theorem relIndex_H {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (p : Sp k n)
    {K L : Subgroup (GL (Fin n) k)} (hKG : K ≤ GzS Z) :
    ((L ⊓ stab Z p).relIndex (K ⊓ stab Z p) = ((L.subgroupOf (GzS Z)) ⊓ stabilizer (GzS Z) (toT p)).relIndex
      ((K.subgroupOf (GzS Z)) ⊓ stabilizer (GzS Z) (toT p))) ∧
    L.relIndex K = (L.subgroupOf (GzS Z)).relIndex (K.subgroupOf (GzS Z)) := by
  refine ⟨?_, (Subgroup.relIndex_subgroupOf hKG).symm⟩
  rw [← stab_subgroupOf, ← inf_subgroupOf', ← inf_subgroupOf',
    Subgroup.relIndex_subgroupOf (inf_le_left.trans hKG)]

theorem isCompact_subgroupOf {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {K : Subgroup (GL (Fin n) k)}
    (hKG : K ≤ GzS Z) (hKc : IsCompact (K : Set (GL (Fin n) k))) : IsCompact ((K.subgroupOf (GzS Z) : Subgroup (GzS Z)) : Set (GzS Z)) := by
  rw [Subtype.isCompact_iff]
  convert hKc using 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hKG hx⟩, hx, rfl⟩

end PositivityTheory.RgUd.T.Nil.Orb.BStep
