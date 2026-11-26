module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeTailLoc
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleCechObj
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSubvarDrop
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepThreeOnWGen
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPolyOfDiffs

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeTail
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Cocycles

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} (M : FinGradedSub (S := S) (x := x) Ω)

def FinGradedSub.cellCone (I : StdCell N) : LocMod S N M.coneSub I.1 →ₗ[Poly S N] ConeLaurent S x :=
  if h : I.1 ⊆ support x then locCone M I.1 h else 0

theorem FinGradedSub.cellCone_of_subset {I : StdCell N} (h : I.1 ⊆ support x) :
    M.cellCone I = locCone M I.1 h := dif_pos h

theorem Cech.sgn_mul_self {n : ℕ} (J : Finset (Fin n)) (j : Fin n) : Cech.sgn J j * Cech.sgn J j = 1 := by
  rw [Cech.sgn, ← mul_pow, neg_one_mul, neg_neg, one_pow]

theorem FinGradedSub.cellCone_cocycle {z : Cech.Cochain (locSys S N M.coneSub) 0}
    (hz : Cech.d (locSys S N M.coneSub) locResS 0 z = 0)
    (K K' : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0)
    (hK : K.1.1 ⊆ support x) (hK' : K'.1.1 ⊆ support x) :
    M.cellCone K.1 (z K) = M.cellCone K'.1 (z K') := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp K.2
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp K'.2
  by_cases hab : a = b
  · have : K = K' := Subtype.ext (Subtype.ext (ha.trans (hab ▸ hb.symm)))
    subst this; rfl
  let Kp : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 1 :=
    ⟨⟨{a, b}, Finset.insert_nonempty _ _, Finset.subset_univ _⟩, Finset.card_pair hab⟩
  have hKp : Kp.1.1 ⊆ support x := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hK (by rw [ha]; exact Finset.mem_singleton_self _)
    · exact hK' (by rw [hb]; exact hi)
  have hfa : ∀ j : Kp.1.1, (j : Fin (N + 1)) = a → Cech.face Kp j = K' := by
    intro j hj
    apply Subtype.ext; apply Subtype.ext
    change ({a, b} : Finset (Fin (N + 1))).erase j = K'.1.1
    rw [hj, hb, Finset.erase_insert (Finset.notMem_singleton.mpr hab)]
  have hfb : ∀ j : Kp.1.1, (j : Fin (N + 1)) = b → Cech.face Kp j = K := by
    intro j hj
    apply Subtype.ext; apply Subtype.ext
    change ({a, b} : Finset (Fin (N + 1))).erase j = K.1.1
    rw [hj, ha, Finset.pair_comm, Finset.erase_insert (Finset.notMem_singleton.mpr (Ne.symm hab))]
  have h0 := congrArg (M.cellCone Kp.1) (congrFun hz Kp)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Cech.d_apply, map_sum, Pi.zero_apply, map_zero] at h0
  have hterm : ∀ j : Kp.1.1, M.cellCone Kp.1 (Cech.sgn Kp.1.1 j • locResS (Cech.face Kp j).1 Kp.1
      (Cech.face_subset Kp j) (z (Cech.face Kp j))) =
      Cech.sgn Kp.1.1 j • M.cellCone (Cech.face Kp j).1 (z (Cech.face Kp j)) := by
    intro j
    rw [map_zsmul, M.cellCone_of_subset hKp, M.cellCone_of_subset ((Cech.face_subset Kp j).trans hKp)]
    congr 1
    exact locCone_locRes M (Cech.face_subset Kp j) hKp _
  rw [Finset.sum_congr rfl fun j _ => hterm j] at h0
  rw [Fintype.sum_eq_add (⟨a, Finset.mem_insert_self a {b}⟩ : Kp.1.1)
    (⟨b, Finset.mem_insert_of_mem (Finset.mem_singleton_self b)⟩ : Kp.1.1)
    (fun h => hab (congrArg Subtype.val h)) (fun j hj => ?_)] at h0
  · rw [hfa ⟨a, Finset.mem_insert_self a {b}⟩ rfl,
      hfb ⟨b, Finset.mem_insert_of_mem (Finset.mem_singleton_self b)⟩ rfl] at h0
    have hs : Cech.sgn Kp.1.1 b = -Cech.sgn Kp.1.1 a := by
      have := Cech.sum_sgn_of_card_two (J := Kp.1.1) Kp.2
      rw [show Kp.1.1 = {a, b} from rfl, Finset.sum_pair hab] at this
      linarith
    change Cech.sgn Kp.1.1 a • M.cellCone K'.1 (z K') + Cech.sgn Kp.1.1 b • M.cellCone K.1 (z K) = 0 at h0
    rw [hs, neg_smul, ← sub_eq_add_neg, ← smul_sub] at h0
    have h1 := congrArg (Cech.sgn Kp.1.1 a • ·) h0
    simp only [smul_smul, Cech.sgn_mul_self, one_smul, smul_zero] at h1
    exact (sub_eq_zero.mp h1).symm
  · exfalso
    rcases Finset.mem_insert.mp j.2 with h | h
    · exact hj.1 (Subtype.ext h)
    · exact hj.2 (Subtype.ext (Finset.mem_singleton.mp h))

theorem FinGradedSub.cocycle_eq_coneSingle {c : ℤ} {z : Cech.Cochain (locSys S N M.coneSub) 0}
    (hz : z ∈ Cech.cocyDeg (locSys S N M.coneSub) (degLoc M.coneGraded c) locResS 0)
    (K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0) (hK : K.1.1 ⊆ support x) :
    ∃ v ∈ (M.tildeSys c).secs, M.cellCone K.1 (z K) = coneSingle S x c v := by
  obtain ⟨v, -, hzv⟩ := locCone_degLoc M c K.1 hK (hz.2 K (Set.mem_univ _))
  rw [← M.cellCone_of_subset hK] at hzv
  refine ⟨v, ?_, hzv⟩
  rw [SubSystem.secs, Submodule.mem_iInf]
  intro J
  obtain ⟨i, hi⟩ := J.2.1
  let Ki : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 :=
    ⟨⟨{i}, Finset.singleton_nonempty i, Finset.subset_univ _⟩, Finset.card_singleton i⟩
  have hKi : Ki.1.1 ⊆ support x := Finset.singleton_subset_iff.mpr (J.2.2 hi)
  obtain ⟨v', hv', hzv'⟩ := locCone_degLoc M c Ki.1 hKi (hz.2 Ki (Set.mem_univ _))
  rw [← M.cellCone_of_subset hKi, ← M.cellCone_cocycle (LinearMap.mem_ker.mp hz.1) K Ki hK hKi, hzv] at hzv'
  have hvv : v = v' := by
    have := congrArg (coeffAt S x c) hzv'
    rwa [coeffAt_coneSingle_same, coeffAt_coneSingle_same] at this
  rw [hvv]
  exact (M.tildeSys c).mono _ J (Finset.singleton_subset_iff.mpr hi) v' hv'

theorem FinGradedSub.exists_cocycle_of_mem_secs {c : ℤ} {v : Ω} (hv : v ∈ (M.tildeSys c).secs) :
    ∃ z ∈ Cech.cocyDeg (locSys S N M.coneSub) (degLoc M.coneGraded c) locResS 0,
      ∀ K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0, K.1.1 ⊆ support x →
        M.cellCone K.1 (z K) = coneSingle S x c v := by
  classical
  rw [SubSystem.secs, Submodule.mem_iInf] at hv
  have hl : ∀ (I : StdCell N) (h : I.1 ⊆ support x), ∃ z ∈ degLoc M.coneGraded c I,
      locCone M I.1 h z = coneSingle S x c v :=
    fun I h => exists_locCone_eq M c I h (hv ⟨I.1, I.2.1, h⟩)
  choose w hw hwv using hl
  let u : ∀ I : StdCell N, LocMod S N M.coneSub I.1 := fun I =>
    if h : I.1 ⊆ support x then w I h else 0
  have hcompat : ∀ (I J : StdCell N) (h : I.1 ⊆ J.1), locResS I J h (u I) = u J := by
    intro I J h
    by_cases hJ : J.1 ⊆ support x
    · apply locCone_injective M J.1 hJ
      have hI : I.1 ⊆ support x := h.trans hJ
      simp only [u, dif_pos hJ, dif_pos hI]
      rw [hwv J hJ]
      exact (locCone_locRes M h hJ (w I hI)).trans (hwv I hI)
    · obtain ⟨i, hiJ, hi⟩ : ∃ i ∈ J.1, x i = 0 := by
        by_contra hne
        push Not at hne
        exact hJ fun i hi => (mem_support x).mpr (hne i hi)
      have := locMod_subsingleton M hiJ hi
      exact Subsingleton.elim _ _
  refine ⟨fun K => u K.1, ⟨LinearMap.mem_ker.mpr (Cech.d_zero_of_compat u hcompat), fun K _ => ?_⟩,
    fun K hK => ?_⟩
  · change u K.1 ∈ degLoc M.coneGraded c K.1
    by_cases hK : K.1.1 ⊆ support x
    · simp only [u, dif_pos hK]; exact hw K.1 hK
    · simp only [u, dif_neg hK]; exact zero_mem _
  · change M.cellCone K.1 (u K.1) = _
    simp only [u, dif_pos hK, M.cellCone_of_subset hK]
    exact hwv K.1 hK

end Cocycles

theorem TildeTail.proof (h : SerreTail.Statement.{u, w}) : TildeTail.Statement.{u, w} := by
  classical
  intro S _ _ Ω _ _ N x M hx c₁
  obtain ⟨i₀, hi₀⟩ : ∃ i, x i ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hx (funext hne)
  let K₀ : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 :=
    ⟨⟨{i₀}, Finset.singleton_nonempty i₀, Finset.subset_univ _⟩, Finset.card_singleton i₀⟩
  have hK₀ : K₀.1.1 ⊆ support x := Finset.singleton_subset_iff.mpr ((mem_support x).mpr hi₀)

  let Ψ : Cech.Cochain (locSys S N M.coneSub) 0 →ₗ[Poly S N] ConeLaurent S x :=
    (M.cellCone K₀.1).comp (LinearMap.proj (R := Poly S N)
      (φ := fun K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 => LocMod S N M.coneSub K.1.1) K₀)
  have hΨ : ∀ z, Ψ z = M.cellCone K₀.1 (z K₀) := fun z => rfl
  obtain ⟨t, ht, hspan⟩ := h S N M.coneSub M.coneGraded M.coneSub_finite c₁

  let G : Submodule S (Cech.Cochain (locSys S N M.coneSub) 0) :=
    { carrier := {z | ∀ d, coeffAt S x d (Ψ z) ∈ (M.tildeSys d).secs ∧ (d < c₁ → coeffAt S x d (Ψ z) = 0)}
      add_mem' := fun {a b} ha hb d => by
        rw [map_add (f := _), map_add (f := _)]
        exact ⟨add_mem (ha d).1 (hb d).1, fun hd => by rw [(ha d).2 hd, (hb d).2 hd, add_zero]⟩
      zero_mem' := fun d => by rw [map_zero, map_zero]; exact ⟨zero_mem _, fun _ => rfl⟩
      smul_mem' := fun s z hz d => by
        rw [LinearMap.map_smul_of_tower, map_smul]
        exact ⟨Submodule.smul_mem _ s (hz d).1, fun hd => by rw [(hz d).2 hd, smul_zero]⟩ }
  have hG : H0tail M.coneGraded c₁ ≤ G := by
    refine iSup₂_le fun c hc z hz => ?_
    show ∀ d, coeffAt S x d (Ψ z) ∈ (M.tildeSys d).secs ∧ (d < c₁ → coeffAt S x d (Ψ z) = 0)
    intro d
    obtain ⟨v, hv, hzv⟩ := M.cocycle_eq_coneSingle hz K₀ hK₀
    rw [hΨ, hzv]
    by_cases hcd : c = d
    · subst hcd
      rw [coeffAt_coneSingle_same]
      exact ⟨hv, fun h => absurd hc (not_le.mpr h)⟩
    · rw [coeffAt_coneSingle_ne hcd]
      exact ⟨zero_mem _, fun _ => rfl⟩
  have hgood : ∀ z ∈ t, ∀ d, coeffAt S x d (Ψ z) ∈ (M.tildeSys d).secs ∧
      (d < c₁ → coeffAt S x d (Ψ z) = 0) := fun z hz => hG (ht z hz)

  let D : Finset ℤ := (t.biUnion fun z => coneSupp (Ψ z)).filter (c₁ ≤ ·)
  let e := (t ×ˢ D).equivFin.symm
  refine ⟨(t ×ˢ D).card, fun j => (e j).1.2, fun j => coeffAt S x (e j).1.2 (Ψ (e j).1.1),
    fun j => ?_, fun c hc y hy => ?_⟩
  · have hm := Finset.mem_product.mp (e j).2
    exact ⟨(Finset.mem_filter.mp hm.2).2, (hgood _ hm.1 _).1⟩
  obtain ⟨z, hz, hzy⟩ := M.exists_cocycle_of_mem_secs hy
  have hzt : z ∈ H0tail M.coneGraded c₁ :=
    (le_iSup₂ (f := fun c (_ : c₁ ≤ c) =>
      Cech.cocyDeg (locSys S N M.coneSub) (degLoc M.coneGraded c) locResS 0) c hc) hz
  let Sp : ℤ → Submodule S Ω := fun d => Submodule.span S {w | ∃ (j : Fin (t ×ˢ D).card) (f : Poly S N)
    (k : ℕ), f.IsHomogeneous k ∧ (k : ℤ) + (e j).1.2 = d ∧ w = aeval x f * coeffAt S x (e j).1.2 (Ψ (e j).1.1)}
  have hmulSp : ∀ (f : Poly S N) (k : ℕ), f.IsHomogeneous k → ∀ d, ∀ u ∈ Sp (d - k),
      aeval x f * u ∈ Sp d := by
    intro f k hf d u hu
    refine Submodule.span_induction (p := fun u _ => aeval x f * u ∈ Sp d) ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨j, g, k', hg, hgk, rfl⟩
      exact Submodule.subset_span ⟨j, f * g, k + k', hf.mul hg, by push_cast; omega,
        by rw [map_mul, mul_assoc]⟩
    · rw [mul_zero]; exact zero_mem _
    · intro a b _ _ ha hb; rw [mul_add]; exact add_mem ha hb
    · intro s a _ ha; rw [mul_smul_comm]; exact Submodule.smul_mem _ s ha
  have key : ∀ w ∈ Submodule.span (Poly S N) (t : Set (Cech.Cochain (locSys S N M.coneSub) 0)),
      ∀ d, coeffAt S x d (Ψ w) ∈ Sp d := by
    intro w hw
    refine Submodule.span_induction (p := fun w _ => ∀ d, coeffAt S x d (Ψ w) ∈ Sp d) ?_ ?_ ?_ ?_ hw
    · intro z' hz' d
      by_cases h0 : coeffAt S x d (Ψ z') = 0
      · rw [h0]; exact zero_mem _
      · have hd : c₁ ≤ d := by
          by_contra hlt
          exact h0 ((hgood z' hz' d).2 (not_le.mp hlt))
        have hmem : (z', d) ∈ t ×ˢ D := Finset.mem_product.mpr ⟨hz', Finset.mem_filter.mpr
          ⟨Finset.mem_biUnion.mpr ⟨z', hz', mem_coneSupp.mpr h0⟩, hd⟩⟩
        refine Submodule.subset_span ⟨e.symm ⟨(z', d), hmem⟩, 1, 0, isHomogeneous_one _ _, ?_, ?_⟩
        · simp
        · simp
    · intro d; rw [map_zero, map_zero]; exact zero_mem _
    · intro a b _ _ ha hb d; rw [map_add (f := _), map_add (f := _)]; exact add_mem (ha d) (hb d)
    · intro p a _ ha d
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_smul, ← sum_homogeneousComponent p, Finset.sum_smul, map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [coeffAt_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous k p)]
      exact hmulSp _ k (homogeneousComponent_isHomogeneous k p) d _ (ha (d - k))
  have hyc := key z (hspan hzt) c
  rwa [hΨ, hzy K₀ hK₀, coeffAt_coneSingle_same] at hyc

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleZColumnsSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def VeryAmpleZColumns.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (G : SubFamily S x E) (H : LineBundle S x) (r : ℕ) (h : Fin (r + 1) → Ω),
    IsVeryAmpleBy H.toSubSystem h → ∀ I : Chart x,
      (∀ J J' : Chart h, J.1 ⊆ J'.1 →
        secsOnZChart G.toSubSystem H.toSubSystem h I J ≤ secsOnZChart G.toSubSystem H.toSubSystem h I J') ∧
      Cech.AugExact S (secsOnZChart G.toSubSystem H.toSubSystem h I) ((G.sub I).restrictScalars S)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CechDoubleSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def CechDouble.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] (N r : ℕ) (x : Fin (N + 1) → Ω) (h : Fin (r + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module S E]
    (A : Chart x → Submodule S E) (B : Chart h → Submodule S E) (M : Chart x → Chart h → Submodule S E),
    (∀ (I I' : Chart x) (J : Chart h), I.1 ⊆ I'.1 → M I J ≤ M I' J) →
    (∀ (I : Chart x) (J J' : Chart h), J.1 ⊆ J'.1 → M I J ≤ M I J') →
    (∀ I, Cech.AugExact S (M I) (A I)) → (∀ J, Cech.AugExact S (fun I => M I J) (B J)) →
    ∀ n : ℕ, Nonempty (Cech.Hdeg (fun _ : Chart x => E) A (Cech.idRes S E (support x)) n ≃ₗ[S]
      Cech.Hdeg (fun _ : Chart h => E) B (Cech.idRes S E (support h)) n)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

theorem SnapperFinite.proof (hE : Extension.Statement.{u, v, w}) (hEL : Extension.Statement.{u, w, w})
    (hT : TwistTilde.Statement.{u, v, w}) (hTL : TwistTilde.Statement.{u, w, w})
    (hS : TildeShift.Statement.{u, v, w}) (hF : TildeFiniteE.Statement.{u, v, w}) :
    SnapperFinite.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x E _ _ _ _ F hF0 t L n c i

  have hpow : ∀ (Lb : LineBundle k x) (m : ℕ), ∃ Q : FinGradedSub (S := k) (x := x) Ω,
      Lb.toSubSystem.pow m = Q.tildeSys 0 := by
    intro Lb m
    induction m with
    | zero =>
      refine ⟨coordGraded k x, ?_⟩
      change twistSys k x 0 = _
      rw [← coordGraded_tildeSys_twist (twistSys k x 0), SubSystem.twist_twistSys_zero]
    | succ m ih =>
      obtain ⟨Q, hQ⟩ := ih
      obtain ⟨QL, -, hQL⟩ := hEL k Ω N x Ω Lb.toSubFamily Lb.fg
      obtain ⟨P, -, hP⟩ := hTL k Ω N x Ω Q QL
      refine ⟨P, ?_⟩
      have hL : Lb.toSubSystem = QL.tildeSys 0 := SubSystem.ext_sub fun I => (hQL I).symm
      change (Lb.toSubSystem.pow m).twist Lb.toSubSystem = _
      rw [hQ, hL]
      exact SubSystem.ext_sub hP

  have hpows : ∀ (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ),
      ∃ P : FinGradedSub (S := k) (x := x) E,
        F.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n = P.tildeSys 0 := by
    intro t
    induction t with
    | zero =>
      intro L n
      obtain ⟨M, -, hM⟩ := hE k Ω N x E F hF0
      exact ⟨M, SubSystem.ext_sub fun I => (hM I).symm⟩
    | succ t ih =>
      intro L n
      obtain ⟨P, hP⟩ := ih (fun j => L j.castSucc) (fun j => n j.castSucc)
      obtain ⟨Q, hQ⟩ := hpow (L (Fin.last t)) (n (Fin.last t))
      obtain ⟨P', -, hP'⟩ := hT k Ω N x E P Q
      refine ⟨P', ?_⟩
      change (F.toSubSystem.twistPows t (fun j => (L j.castSucc).toSubSystem)
        (fun j => n j.castSucc)).twist ((L (Fin.last t)).toSubSystem.pow (n (Fin.last t))) = _
      rw [hP, hQ]
      exact SubSystem.ext_sub hP'
  obtain ⟨P, hP⟩ := hpows t L n
  rw [hP, ← hS k Ω N x E P c]
  exact hF k Ω N x E P i c

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperDevissage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w u₁ v₁ w₁

namespace Cech

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u₁} [CommRing R]
  {G : Cell U → Type v₁} [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)]
  {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
  {G' : Cell U → Type w₁} [∀ I, AddCommGroup (G' I)] [∀ I, Module R (G' I)]
  {ρ' : ∀ I J : Cell U, I.1 ⊆ J.1 → G' I →ₗ[R] G' J}

def mapH (φ : ∀ I, G I →ₗ[R] G' I) (hφ : ∀ I J h m, φ J (ρ I J h m) = ρ' I J h (φ I m)) (i : ℕ) :
    H G ρ i →ₗ[R] H G' ρ' i :=
  Submodule.mapQ _ _ ((mapC φ i).restrict (p := LinearMap.ker (d G ρ i)) (q := LinearMap.ker (d G' ρ' i))
      (fun s hs => by
        change d G' ρ' i (mapC φ i s) = 0
        rw [← mapC_d φ hφ, show d G ρ i s = 0 from hs, map_zero]))
    (by
      intro s hs
      cases i with
      | zero =>
        change (s : Cochain G 0) ∈ (⊥ : Submodule R _) at hs
        rw [Submodule.mem_bot] at hs
        change (mapC φ 0 s : Cochain G' 0) ∈ (⊥ : Submodule R _)
        rw [hs, map_zero]; exact Submodule.zero_mem _
      | succ i =>
        obtain ⟨t, hts⟩ := hs
        refine ⟨mapC φ i t, ?_⟩
        change d G' ρ' i (mapC φ i t) = mapC φ (i + 1) s
        rw [← mapC_d φ hφ, hts]
        rfl)

def hEquivOfEquiv (φ : ∀ I, G I ≃ₗ[R] G' I) (hφ : ∀ I J h m, φ J (ρ I J h m) = ρ' I J h (φ I m)) (i : ℕ) :
    H G ρ i ≃ₗ[R] H G' ρ' i :=
  have hψ : ∀ I J h m, (φ J).symm (ρ' I J h m) = ρ I J h ((φ I).symm m) := fun I J h m => by
    rw [LinearEquiv.symm_apply_eq, hφ, LinearEquiv.apply_symm_apply]
  LinearEquiv.ofLinearMap (mapH (fun I => (φ I).toLinearMap) hφ i)
    (mapH (fun I => (φ I).symm.toLinearMap) hψ i)
    (by
      refine Submodule.linearMap_qext _ (LinearMap.ext fun z => ?_)
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      congr 1
      exact Subtype.ext (funext fun I => (φ I.1).apply_symm_apply _))
    (by
      refine Submodule.linearMap_qext _ (LinearMap.ext fun z => ?_)
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      congr 1
      exact Subtype.ext (funext fun I => (φ I.1).symm_apply_apply _))

end Cech

section Zero

variable (k : Type u) [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} (x : Fin (N + 1) → Ω)
  (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]

def zeroFamily : SubFamily k x E where
  sub _ := ⊥
  mono _ _ _ _ hy := hy
  mem_iff I J h y := by
    simp only [Submodule.mem_bot]
    constructor
    · rintro rfl
      exact ⟨1, by simp, by simp⟩
    · rintro ⟨a, ha, hay⟩
      obtain ⟨b, hb⟩ := ha.exists_right_inv
      have hne : (a : Ω) ≠ 0 := by
        intro h0
        have h1 := congrArg (fun z : chartRing k x J => (z : Ω)) hb
        change (a : Ω) * _ = 1 at h1
        rw [h0, zero_mul] at h1
        exact zero_ne_one h1
      exact (smul_eq_zero.mp hay).resolve_left hne

end Zero

section Lemmas

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]


omit [Module k E] [IsScalarTower k Ω E] in
theorem twist_sub_eq_bot {F : SubSystem k x E} (hF : ∀ I, F.sub I = ⊥) (Q : SubSystem k x Ω) (I : Chart x) :
    (F.twist Q).sub I = ⊥ := by
  refine Submodule.span_eq_bot.mpr ?_
  rintro _ ⟨q, -, y, hy, rfl⟩
  rw [hF I, Submodule.mem_bot] at hy
  rw [hy, smul_zero]


omit [Module k E] [IsScalarTower k Ω E] in
theorem twistPows_sub_eq_bot {F : SubSystem k x E} (hF : ∀ I, F.sub I = ⊥) :
    ∀ (t : ℕ) (L : Fin t → SubSystem k x Ω) (n : Fin t → ℕ) (I : Chart x), (F.twistPows t L n).sub I = ⊥
  | 0, _, _, I => hF I
  | t + 1, _, _, I => twist_sub_eq_bot (fun I => twistPows_sub_eq_bot hF t _ _ I) _ I


omit [Module k E] [IsScalarTower k Ω E] in
theorem twist_idealSys_primeOf_sub (F : SubSystem k x E) (I : Chart x) :
    (F.twist (idealSys x (primeOf (S := k) x))).sub I = ⊥ := by
  refine Submodule.span_eq_bot.mpr ?_
  rintro _ ⟨q, hq, y, -, rfl⟩
  have hq0 : q = 0 := by
    have h0 : idealMod (primeOf (S := k) x) I = ⊥ := by
      refine Submodule.span_eq_bot.mpr ?_
      rintro _ ⟨f, s, e, hf, _, hfe, _, rfl⟩
      rw [(mem_primeOf_of_isHomogeneous x hfe).mp hf, zero_div]
    have hq' : q ∈ (⊥ : Submodule (chartRing k x I) Ω) := h0 ▸ hq
    exact (Submodule.mem_bot _).mp hq'
  rw [hq0, zero_smul]

theorem eulerCharQuot_of_bot (F₁ F₂ : SubSystem k x E) (h : ∀ I, F₂.sub I = ⊥) :
    eulerCharQuot k F₁ F₂ = eulerChar k F₁ := by
  have hq : ∀ I, SubSystem.quotSub F₁ F₂ I = ⊥ := fun I => by
    refine (Submodule.eq_bot_iff _).mpr fun y hy => Subtype.ext ?_
    have hy' : (y : E) ∈ F₂.sub I := hy
    rw [h I, Submodule.mem_bot] at hy'
    exact hy'
  let φ : ∀ I, F₁.sub I ≃ₗ[k] (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) := fun I =>
    (Submodule.quotEquivOfEqBot _ (hq I)).symm
  have hφ : ∀ I J h m, φ J (F₁.res I J h m) = SubSystem.quotRes F₁ F₂ I J h (φ I m) := fun _ _ _ _ => rfl
  unfold eulerCharQuot eulerChar
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  exact ((Cech.hEquivOfEquiv φ hφ i).finrank_eq).symm

end Lemmas

theorem SnapperDevissage.proof (hQ : SnapperQuotDevissage.Statement.{u, v, w}) :
    SnapperDevissage.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x E _ _ _ _ F hF
  obtain ⟨r, pp, a, hpp, heq⟩ := hQ k Ω N x E F (zeroFamily k x E) hF (fun _ => bot_le)
    (primeOf (S := k) x) (fun f hf d => homogeneousComponent_mem_primeOf x hf d) le_rfl
    (fun I => (twist_idealSys_primeOf_sub F.toSubSystem I).le)
  refine ⟨r, pp, a, hpp, fun t L n c => ?_⟩
  rw [← heq t L n c]
  exact (eulerCharQuot_of_bot _ _ fun I =>
    twist_sub_eq_bot (twistPows_sub_eq_bot (fun _ => rfl) t _ n) _ I).symm

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperDiffPoly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

namespace SnapperDiffPoly

def numPt {t : ℕ} (n : Fin t → ℕ) (c : ℤ) : Fin (t + 1) → ℚ :=
  Fin.snoc (α := fun _ => ℚ) (fun j => (n j : ℚ)) (c : ℚ)

theorem eval_aeval_eq {K : Type} (x : K → ℚ) (σ : K → MvPolynomial K ℚ) (P : MvPolynomial K ℚ) :
    eval x (aeval σ P) = eval (fun k => eval x (σ k)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => rw [map_add (f := _), map_add (f := _), hp, hr, map_add (f := _)]
  | mul_X p j hp => simp only [map_mul, hp, aeval_X, eval_X]

theorem numPt_succ {t : ℕ} (n : Fin t → ℕ) (c : ℤ) :
    numPt n (c + 1) = numPt n c + Pi.single (Fin.last t) 1 := by
  funext k
  induction k using Fin.lastCases with
  | last => simp [numPt]
  | cast i => simp [numPt, Fin.castSucc_ne_last]

theorem numPt_update {t : ℕ} (n : Fin t → ℕ) (c : ℤ) (j : Fin t) :
    numPt (Function.update n j (n j + 1)) c = numPt n c + Pi.single j.castSucc 1 := by
  funext k
  induction k using Fin.lastCases with
  | last => simp [numPt, (Fin.castSucc_ne_last j).symm]
  | cast i =>
    by_cases h : i = j
    · subst h; simp [numPt]
    · simp [numPt, h, Function.update_apply]

theorem exists_fwd_antideriv {K : Type} [DecidableEq K] (D : ℕ) (k : K) (q : MvPolynomial K ℚ)
    (hq : q = 0 ∨ q.totalDegree < D) : ∃ P : MvPolynomial K ℚ, P.totalDegree ≤ D ∧
      ∀ x : K → ℚ, eval (x + Pi.single k 1) P - eval x P = eval x q := by
  rcases hq with rfl | hq
  · exact ⟨0, by simp, fun x => by simp⟩
  obtain ⟨P₀, hd, he⟩ := FieldNumbers.PolyOfDiffs.exists_antideriv k q
  refine ⟨aeval (fun i => X i - C ((Pi.single k (1 : ℚ) : K → ℚ) i)) P₀, ?_, fun x => ?_⟩
  · refine (FieldNumbers.PolyOfDiffs.totalDegree_aeval_le _ (fun i => ?_) P₀).trans (by omega)
    refine (totalDegree_sub _ _).trans ?_
    simp [totalDegree_X, totalDegree_C]
  · have h1 : (fun i => eval (x + Pi.single k 1) (X i - C ((Pi.single k (1 : ℚ) : K → ℚ) i))) = x := by
      funext i; simp
    have h2 : (fun i => eval x (X i - C ((Pi.single k (1 : ℚ) : K → ℚ) i))) = x - Pi.single k 1 := by
      funext i; simp
    rw [eval_aeval_eq, eval_aeval_eq, h1, h2, he x]

theorem isNumPolyLT_comp {t D : ℕ} {F G : (Fin t → ℕ) → ℤ → ℚ} (σ : Fin (t + 1) → MvPolynomial (Fin (t + 1)) ℚ)
    (hσ : ∀ i, (σ i).totalDegree ≤ 1) (a : (Fin t → ℕ) → ℤ → (Fin t → ℕ)) (b : (Fin t → ℕ) → ℤ → ℤ)
    (hab : ∀ n c, (fun i => eval (numPt n c) (σ i)) = numPt (a n c) (b n c))
    (hG : ∀ n c, G n c = F (a n c) (b n c)) (hF : IsNumPolyLT t D F) : IsNumPolyLT t D G := by
  obtain ⟨Q, hQ, hE⟩ := hF
  refine ⟨aeval σ Q, ?_, fun n c => ?_⟩
  · rcases hQ with rfl | hQ
    · left; simp
    · exact Or.inr ((FieldNumbers.PolyOfDiffs.totalDegree_aeval_le σ hσ Q).trans_lt hQ)
  · rw [hG, hE]
    change _ = eval (numPt n c) (aeval σ Q)
    rw [eval_aeval_eq, hab]
    rfl

theorem isNumPolyLT_shear {t D : ℕ} (ν : Fin t → ℤ) {F : (Fin t → ℕ) → ℤ → ℚ} (hF : IsNumPolyLT t D F) :
    IsNumPolyLT t D (fun n c => F n (c + ∑ i, ν i * (n i : ℤ))) := by
  refine isNumPolyLT_comp (Fin.snoc (α := fun _ => MvPolynomial (Fin (t + 1)) ℚ) (fun i => X i.castSucc)
    (X (Fin.last t) + ∑ i, C (ν i : ℚ) * X i.castSucc)) (fun k => ?_) (fun n _ => n)
    (fun n c => c + ∑ i, ν i * (n i : ℤ)) (fun n c => ?_) (fun n c => rfl) hF
  · induction k using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      refine (totalDegree_add _ _).trans (max_le (by rw [totalDegree_X]) ?_)
      refine totalDegree_finsetSum_le fun i _ => (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, totalDegree_X]
    | cast i => simp [totalDegree_X]
  · funext k
    induction k using Fin.lastCases with
    | last => simp [numPt]
    | cast i => simp [numPt]

theorem unit_steps {t D : ℕ} (g : (Fin t → ℕ) → ℤ → ℚ)
    (hc : IsNumPolyLT t D (fun n c => g n (c + 1) - g n c))
    (hj : ∀ j, IsNumPolyLT t D (fun n c => g (Function.update n j (n j + 1)) c - g n c)) :
    IsNumPolyLT t (D + 1) g := by
  classical
  obtain ⟨Qc, hQc, hcE⟩ := hc
  choose Q hQ hjE using hj
  obtain ⟨Pc, hPcd, hPc⟩ := exists_fwd_antideriv D (Fin.last t) Qc hQc
  choose P hPd hP using fun j : Fin t => exists_fwd_antideriv D j.castSucc (Q j) (hQ j)

  have hcol : ∀ c : ℤ, g 0 c - g 0 0 = eval (numPt 0 c) Pc - eval (numPt 0 0) Pc := by
    have step : ∀ c : ℤ, g 0 (c + 1) - g 0 c = eval (numPt 0 (c + 1)) Pc - eval (numPt 0 c) Pc := by
      intro c
      have h1 : g 0 (c + 1) - g 0 c = eval (numPt 0 c) Qc := hcE 0 c
      rw [h1, numPt_succ, hPc]
    intro c
    induction c using Int.induction_on with
    | zero => simp
    | succ i ih => have := step i; linarith
    | pred i ih =>
      have := step (-(i : ℤ) - 1)
      rw [sub_add_cancel] at this
      linarith

  have hrow : ∀ (i : Fin t) (v : Fin t → ℕ) (c : ℤ) (m : ℕ),
      g (Function.update v i m) c - g (Function.update v i 0) c =
        eval (numPt (Function.update v i m) c) (P i) - eval (numPt (Function.update v i 0) c) (P i) := by
    intro i v c m
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 : g (Function.update (Function.update v i m) i (Function.update v i m i + 1)) c -
          g (Function.update v i m) c = eval (numPt (Function.update v i m) c) (Q i) := hjE i _ c
      have h2 := hP i (numPt (Function.update v i m) c)
      rw [← numPt_update] at h2
      simp only [Function.update_self, Function.update_idem] at h1 h2
      linarith

  let tr : Finset (Fin t) → (Fin t → ℕ) → (Fin t → ℕ) := fun s n i => if i ∈ s then n i else 0
  let σ : Finset (Fin t) → Fin (t + 1) → MvPolynomial (Fin (t + 1)) ℚ := fun s =>
    Fin.snoc (α := fun _ => MvPolynomial (Fin (t + 1)) ℚ) (fun i => if i ∈ s then X i.castSucc else 0)
      (X (Fin.last t))
  have hσd : ∀ s k, (σ s k).totalDegree ≤ 1 := by
    intro s k
    induction k using Fin.lastCases with
    | last => simp [σ, totalDegree_X]
    | cast i => simp only [σ, Fin.snoc_castSucc]; split_ifs <;> simp [totalDegree_X]
  have hσe : ∀ s n c, (fun k => eval (numPt n c) (σ s k)) = numPt (tr s n) c := by
    intro s n c
    funext k
    induction k using Fin.lastCases with
    | last => simp [σ, numPt]
    | cast i => simp only [σ, tr, numPt, Fin.snoc_castSucc]; split_ifs <;> simp
  have key : ∀ s : Finset (Fin t), ∃ Γ : MvPolynomial (Fin (t + 1)) ℚ, Γ.totalDegree ≤ D ∧
      ∀ n c, g (tr s n) c = eval (numPt n c) Γ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨aeval (σ ∅) Pc + C (g 0 0 - eval (numPt 0 0) Pc), ?_, fun n c => ?_⟩
      · refine (totalDegree_add _ _).trans (max_le ?_ (by rw [totalDegree_C]; exact Nat.zero_le _))
        exact (FieldNumbers.PolyOfDiffs.totalDegree_aeval_le _ (hσd ∅) _).trans hPcd
      · have h0 : tr ∅ n = 0 := by funext i; simp [tr]
        rw [map_add (f := _), eval_C, eval_aeval_eq, hσe, h0]
        linarith [hcol c]
    | insert i s hi ih =>
      obtain ⟨Γ, hΓd, hΓ⟩ := ih
      refine ⟨Γ + (aeval (σ (insert i s)) (P i) - aeval (σ s) (P i)), ?_, fun n c => ?_⟩
      · refine (totalDegree_add _ _).trans (max_le hΓd ((totalDegree_sub _ _).trans (max_le ?_ ?_)))
        · exact (FieldNumbers.PolyOfDiffs.totalDegree_aeval_le _ (hσd _) _).trans (hPd i)
        · exact (FieldNumbers.PolyOfDiffs.totalDegree_aeval_le _ (hσd _) _).trans (hPd i)
      · have e1 : tr (insert i s) n = Function.update (tr s n) i (n i) := by
          funext k
          by_cases hk : k = i
          · subst hk; simp [tr]
          · simp [tr, hk]
        have e2 : tr s n = Function.update (tr s n) i 0 := by
          funext k
          by_cases hk : k = i
          · subst hk; simp [tr, hi]
          · simp [hk]
        have h := hrow i (tr s n) c (n i)
        rw [← e1, ← e2] at h
        rw [map_add (f := _), map_sub, eval_aeval_eq, eval_aeval_eq, hσe, hσe, ← hΓ n c]
        linarith
  obtain ⟨Γ, hΓd, hΓ⟩ := key Finset.univ
  refine ⟨Γ, Or.inr (by omega), fun n c => ?_⟩
  have h := hΓ n c
  have hu : tr Finset.univ n = n := by funext i; simp [tr]
  rw [hu] at h
  exact h

end SnapperDiffPoly

theorem SnapperDiffPoly.proof : SnapperDiffPoly.Statement := by
  intro t D f μ hc hj
  classical
  let L : (Fin t → ℕ) → ℤ := fun n => ∑ i, μ i * (n i : ℤ)
  have hL : ∀ n j, L (Function.update n j (n j + 1)) = L n + μ j := by
    intro n j
    simp only [L]
    have : ∀ i, μ i * ((Function.update n j (n j + 1) i : ℕ) : ℤ) =
        μ i * (n i : ℤ) + if i = j then μ j else 0 := by
      intro i
      by_cases h : i = j
      · subst h; simp; ring
      · simp [h]
    rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp
  let g : (Fin t → ℕ) → ℤ → ℚ := fun n c => f n (c + L n)
  have hgc : IsNumPolyLT t D (fun n c => g n (c + 1) - g n c) := by
    obtain ⟨Q, hQ, hE⟩ := SnapperDiffPoly.isNumPolyLT_shear μ hc
    refine ⟨Q, hQ, fun n c => ?_⟩
    rw [← hE n c]
    simp only [g, L]
    rw [add_right_comm]
  have hgj : ∀ j, IsNumPolyLT t D (fun n c => g (Function.update n j (n j + 1)) c - g n c) := by
    intro j
    obtain ⟨Q, hQ, hE⟩ := SnapperDiffPoly.isNumPolyLT_shear μ (hj j)
    refine ⟨Q, hQ, fun n c => ?_⟩
    rw [← hE n c]
    simp only [g]
    rw [hL n j, ← add_assoc]
  obtain ⟨Q, hQ, hE⟩ := SnapperDiffPoly.isNumPolyLT_shear (-μ) (SnapperDiffPoly.unit_steps g hgc hgj)
  refine ⟨Q, hQ, fun n c => ?_⟩
  rw [← hE n c]
  simp only [g, L, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  congr 1
  ring

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHFreeBadFiniteSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

def KHFreeBadFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (e : K → ℤ),
    {a : (Σ k, ι k) → ℤ | blockSum a = e ∧ ∀ k, negSet a k = ∅ ∨ negSet a k = Finset.univ}.Finite

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHFreeIndepSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

def KHFreeIndep.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (n : ℕ) (A : Finset ((Σ k, ι k) → ℤ))
    (f : ∀ a : (Σ k, ι k) → ℤ, CombC S (negSet a) n),
    ∑ a ∈ A, embed S a n (f a) = 0 → ∀ a ∈ A, f a = 0

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CutZeroNotLeSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def CutZeroNotLe.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (e : ℕ) (pp : Ideal (Poly k N)) (L : LineBundle k x) (s : Ω), IsSubvar x pp e →
    s ∈ L.secs → (∃ I, s ∉ (L.twist (idealSys x pp)).sub I) →
    ∃ f ∈ zeroIdeal L.toSubSystem s, f ∉ pp

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHFreeDecompSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

def KHFreeDecomp.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (c d : K → ℤ) (n : ℕ),
    ∀ φ ∈ KH.cechCc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n,
      ∃ (A : Finset ((Σ k, ι k) → ℤ)) (f : ∀ a : (Σ k, ι k) → ℤ, CombC S (negSet a) n),
        (∀ a ∈ A, blockSum a = c + d) ∧ φ = ∑ a ∈ A, embed S a n (f a)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHCombCyclicSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

def KHCombCyclic.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (J : ∀ k, Finset (ι k)) (n : ℕ),
    (∀ k, J k = ∅ ∨ J k = Finset.univ) →
      combD S J n (singOne S J n) = 0 ∧
        ∀ f : CombC S J n, combD S J n f = 0 → ∃ s : S, f - s • singOne S J n ∈ combB S J n

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CutNonemptySt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def CutNonempty.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (L : LineBundle k x) (s : Ω), IsSubvar x pp (n + 1) →
    IsVeryAmple L.toSubSystem → s ∈ L.secs → (∃ I, s ∉ (L.twist (idealSys x pp)).sub I) →
    ∃ qq ∈ (pp ⊔ zeroIdeal L.toSubSystem s).minimalPrimes, ∃ j, (X j : Poly k N) ∉ qq

end

end GroundTheory.Heights₂.Heights.Kleiman
end
