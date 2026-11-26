module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepThreeOnWGen
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSubvarDrop
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleCechObj
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDropFiltStep
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSurjectiveClosed

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleEmbedSections
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section VeryAmpleEmbedSectionsProof

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {y : Fin (N + 1) → Ω}

theorem vaes_ampleBase_le_chartRing {r : ℕ} {h : Fin (r + 1) → Ω} {j : Fin (r + 1)} (hj : h j ≠ 0) :
    ampleBase (S := k) h j ≤ chartRing k h (singleChart hj) :=
  Algebra.adjoin_le (by rintro _ ⟨l, rfl⟩; exact (ratio (S := k) hj l).2)

theorem vaes_mem_pow_of_forall (Q : LineBundle k y) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hv : IsVeryAmpleBy Q.toSubSystem h) (I : Chart y) {m : ℕ} {s : Ω}
    (hs : ∀ j, h j ≠ 0 → ∃ e : ℕ, s * h j ^ e ∈ (Q.toSubSystem.pow (m + e)).sub I) :
    s ∈ (Q.toSubSystem.pow m).sub I := by
  have hs' : ∀ j, h j ≠ 0 → ∃ e : ℕ, s * h j ^ e ∈ Q.toSubSystem.sub I ^ (m + e) := fun j hj => by
    obtain ⟨e, he⟩ := hs j hj
    exact ⟨e, by rw [← SubSystem.pow_sub_eq_pow Q.toSubSystem]; exact he⟩
  rw [SubSystem.pow_sub_eq_pow Q.toSubSystem]
  clear hs
  obtain ⟨P', hPP'⟩ := Q.invertible I
  set P := Q.toSubSystem.sub I with hP
  let c : Ideal (chartRing k y I) := (P ^ m).comap (LinearMap.toSpanSingleton _ Ω s)
  have hc : ∀ a, a ∈ c ↔ (a : Ω) * s ∈ P ^ m := fun a => by
    change a • s ∈ P ^ m ↔ _; rw [chartRing_smul_def]
  have key : ∀ j, ∀ q ∈ P', ∀ a : chartRing k y I, (a : Ω) = h j * q → a ∈ c.radical := by
    intro j q hq a ha
    by_cases hj : h j = 0
    · have : a = 0 := Subtype.ext (by rw [ha, hj, zero_mul]; rfl)
      rw [this]; exact Ideal.zero_mem _
    obtain ⟨e, he⟩ := hs' j hj
    refine ⟨e, (hc _).mpr ?_⟩
    have hmem := Submodule.mul_mem_mul he (Submodule.pow_mem_pow P' hq e)
    rw [pow_add, mul_assoc, ← mul_pow, hPP', one_pow, mul_one] at hmem
    rw [Subalgebra.coe_pow, ha]
    convert hmem using 1
    ring
  let M : Submodule (chartRing k y I) Ω := Submodule.map (Algebra.linearMap (chartRing k y I) Ω) c.radical
  have hle : P * P' ≤ M := by
    refine Submodule.mul_le.mpr fun p hp q hq => ?_
    rw [hP, ← hv.generates I] at hp
    induction hp using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      have h1 : h j * q ∈ P * P' := Submodule.mul_mem_mul
        (by rw [hP, ← hv.generates I]; exact Submodule.subset_span ⟨j, rfl⟩) hq
      rw [hPP'] at h1
      obtain ⟨a, ha⟩ := Submodule.mem_one.mp h1
      exact ⟨a, key j q hq a ha, ha⟩
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add u v _ _ hu hv => rw [add_mul]; exact Submodule.add_mem _ hu hv
    | smul a u _ hu => rw [smul_mul_assoc]; exact Submodule.smul_mem _ a hu
  have h1 : (1 : Ω) ∈ M := hle (by rw [hPP']; exact Submodule.one_le.mp le_rfl)
  obtain ⟨a, ha, ha1⟩ := h1
  have : a = 1 := Subtype.ext ha1
  have ha' : (1 : chartRing k y I) ∈ c.radical := this ▸ ha
  rw [← Ideal.eq_top_iff_one, Ideal.radical_eq_top, Ideal.eq_top_iff_one, hc] at ha'
  simpa using ha'

end VeryAmpleEmbedSectionsProof

theorem VeryAmpleEmbed.Sections.proof : VeryAmpleEmbed.Sections.Statement.{u, w} := by
  intro k _ Ω _ _ N y Q r h _ hv m
  apply le_antisymm
  · intro s hs
    refine (Submodule.mem_iInf _).mpr fun J => ?_
    obtain ⟨j, hjJ⟩ := J.2.1
    have hj : h j ≠ 0 := (mem_support h).mp (J.2.2 hjJ)
    have hsI : ∀ I, s ∈ (Q.toSubSystem.pow m).sub I := fun I =>
      (Submodule.restrictScalars_mem k _ _).mp ((Submodule.mem_iInf _).mp hs I)
    have hb : s / h j ^ m ∈ ampleRing Q.toSubSystem 1 (h j) := Set.mem_iInter.mpr fun I =>
      ⟨m, by rw [one_mul, div_mul_cancel₀ _ (pow_ne_zero _ hj)]; exact hsI I⟩
    have hbc := vaes_ampleBase_le_chartRing hj (hv.closed j hj hb)
    have hmem : s ∈ twistMod k h (m : ℤ) (singleChart hj) := by
      rw [twistMod_eq_span _ _ (Finset.mem_singleton_self j), Submodule.mem_span_singleton]
      exact ⟨⟨_, hbc⟩, by rw [chartRing_smul_def, zpow_natCast, div_mul_cancel₀ _ (pow_ne_zero _ hj)]⟩
    exact (Submodule.restrictScalars_mem k _ _).mpr ((twistSys k h (m : ℤ)).mono (singleChart hj) J
      (Finset.singleton_subset_iff.mpr hjJ) s hmem)
  · intro s hs
    refine (Submodule.mem_iInf _).mpr fun I => (Submodule.restrictScalars_mem k _ _).mpr ?_
    refine vaes_mem_pow_of_forall Q hv I fun j hj => ?_
    have hsj : s ∈ twistMod k h (m : ℤ) (singleChart hj) :=
      (Submodule.restrictScalars_mem k _ _).mp ((Submodule.mem_iInf _).mp hs _)
    obtain ⟨g, t, e, ht, hte, hg, hgt⟩ := exists_rep_of_mem_twistMod h m hj hsj
    have ht' : t ∈ Submonoid.closure {(X j : MvPolynomial (Fin (r + 1)) k)} := by
      have : ((fun i => (X i : MvPolynomial (Fin (r + 1)) k)) ''
          ((({j} : Finset (Fin (r + 1))) : Set (Fin (r + 1))))) = {X j} := by simp
      rw [← this]; exact ht
    obtain ⟨d, rfl⟩ := Submonoid.mem_closure_singleton.mp ht'
    have hde : e = d := hte.inj_right (isHomogeneous_X_pow j d) (by
      rw [X_pow_eq_monomial, Ne, monomial_eq_zero]; exact one_ne_zero)
    subst hde
    refine ⟨e, ?_⟩
    have := aeval_mem_pow Q.toSubSystem hv.mem_secs I hg
    rwa [hgt, map_pow, aeval_X, add_comm] at this

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PMulQuotEq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace Cech

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R]
  {G : Cell U → Type v} [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)]
  {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
  {G' : Cell U → Type w} [∀ I, AddCommGroup (G' I)] [∀ I, Module R (G' I)]
  {ρ' : ∀ I J : Cell U, I.1 ⊆ J.1 → G' I →ₗ[R] G' J}

def mapCEquiv (e : ∀ I, G I ≃ₗ[R] G' I) (i : ℕ) : Cochain G i ≃ₗ[R] Cochain G' i :=
  LinearEquiv.piCongrRight fun I : Idx U i => e I.1

theorem mapCEquiv_d (e : ∀ I, G I ≃ₗ[R] G' I) (he : ∀ I J h m, e J (ρ I J h m) = ρ' I J h (e I m))
    (i : ℕ) (s : Cochain G i) : mapCEquiv e (i + 1) (d G ρ i s) = d G' ρ' i (mapCEquiv e i s) :=
  mapC_d (fun I => (e I).toLinearMap) he i s

theorem mem_bdry_iff (e : ∀ I, G I ≃ₗ[R] G' I) (he : ∀ I J h m, e J (ρ I J h m) = ρ' I J h (e I m))
    (i : ℕ) (s : Cochain G i) : s ∈ bdry G ρ i ↔ mapCEquiv e i s ∈ bdry G' ρ' i := by
  cases i with
  | zero =>
    change s ∈ (⊥ : Submodule R _) ↔ mapCEquiv e 0 s ∈ (⊥ : Submodule R _)
    rw [Submodule.mem_bot, Submodule.mem_bot, LinearEquiv.map_eq_zero_iff]
  | succ i =>
    change s ∈ LinearMap.range (d G ρ i) ↔ mapCEquiv e (i + 1) s ∈ LinearMap.range (d G' ρ' i)
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨mapCEquiv e i t, (mapCEquiv_d e he i t).symm⟩
    · rintro ⟨t', ht'⟩
      refine ⟨(mapCEquiv e i).symm t', (mapCEquiv e (i + 1)).injective ?_⟩
      rw [mapCEquiv_d e he, LinearEquiv.apply_symm_apply, ht']

theorem mem_ker_iff (e : ∀ I, G I ≃ₗ[R] G' I) (he : ∀ I J h m, e J (ρ I J h m) = ρ' I J h (e I m))
    (i : ℕ) (s : Cochain G i) : s ∈ LinearMap.ker (d G ρ i) ↔ mapCEquiv e i s ∈ LinearMap.ker (d G' ρ' i) := by
  rw [LinearMap.mem_ker, LinearMap.mem_ker, ← mapCEquiv_d e he, LinearEquiv.map_eq_zero_iff]

def kerEquiv (e : ∀ I, G I ≃ₗ[R] G' I) (he : ∀ I J h m, e J (ρ I J h m) = ρ' I J h (e I m)) (i : ℕ) :
    LinearMap.ker (d G ρ i) ≃ₗ[R] LinearMap.ker (d G' ρ' i) :=
  LinearEquiv.ofSubmodules (mapCEquiv e i) _ _ (by
    ext z
    rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, mem_ker_iff e he,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply])

def equivH (e : ∀ I, G I ≃ₗ[R] G' I) (he : ∀ I J h m, e J (ρ I J h m) = ρ' I J h (e I m)) (i : ℕ) :
    H G ρ i ≃ₗ[R] H G' ρ' i :=
  Submodule.Quotient.equiv _ _ (kerEquiv e he i) (by
    ext z
    rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, Submodule.mem_comap,
      Submodule.mem_comap, Submodule.subtype_apply, Submodule.subtype_apply, mem_bdry_iff e he]
    congr! 1
    change mapCEquiv e i ((mapCEquiv e i).symm (z : Cochain G' i)) = z
    exact LinearEquiv.apply_symm_apply _ _)

end Cech

section Mul

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {F₁ F₂ G₁ G₂ : SubSystem k x Ω} {s : Ω}

def mulSubMap (h₁ : ∀ I, ∀ y ∈ F₁.sub I, s * y ∈ G₁.sub I) (I : Chart x) : F₁.sub I →ₗ[k] G₁.sub I where
  toFun y := ⟨s * y, h₁ I y y.2⟩
  map_add' a b := Subtype.ext (mul_add s (a : Ω) b)
  map_smul' c y := Subtype.ext (by
    change s * ((c • y : F₁.sub I) : Ω) = ((c • (⟨s * y, h₁ I y y.2⟩ : G₁.sub I) : G₁.sub I) : Ω)
    rw [Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower, mul_smul_comm])

def mulQuotMap (h₁ : ∀ I, ∀ y ∈ F₁.sub I, s * y ∈ G₁.sub I)
    (h₃ : ∀ I, ∀ y ∈ F₁.sub I, (s * y ∈ G₂.sub I ↔ y ∈ F₂.sub I)) (I : Chart x) :
    (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) →ₗ[k] (G₁.sub I ⧸ SubSystem.quotSub G₁ G₂ I) :=
  (SubSystem.quotSub F₁ F₂ I).mapQ (SubSystem.quotSub G₁ G₂ I) (mulSubMap h₁ I)
    (fun y hy => (h₃ I y y.2).mpr hy)

theorem mulQuotMap_bijective (h₁ : ∀ I, ∀ y ∈ F₁.sub I, s * y ∈ G₁.sub I)
    (h₂ : ∀ I, ∀ z ∈ G₁.sub I, ∃ y ∈ F₁.sub I, z - s * y ∈ G₂.sub I)
    (h₃ : ∀ I, ∀ y ∈ F₁.sub I, (s * y ∈ G₂.sub I ↔ y ∈ F₂.sub I)) (I : Chart x) :
    Function.Bijective (mulQuotMap h₁ h₃ I) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro m hm
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [LinearMap.mem_ker] at hm
    change Submodule.Quotient.mk (mulSubMap h₁ I y) = 0 at hm
    rw [Submodule.Quotient.mk_eq_zero] at hm
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact (h₃ I y y.2).mp hm
  · intro m
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    obtain ⟨y, hy, hz⟩ := h₂ I z z.2
    refine ⟨Submodule.Quotient.mk ⟨y, hy⟩, ?_⟩
    change Submodule.Quotient.mk (mulSubMap h₁ I ⟨y, hy⟩) = Submodule.Quotient.mk z
    rw [Submodule.Quotient.eq]
    change ((mulSubMap h₁ I ⟨y, hy⟩ - z : G₁.sub I) : Ω) ∈ G₂.sub I
    rw [Submodule.coe_sub, ← neg_sub]
    exact (G₂.sub I).neg_mem hz

end Mul

theorem MulQuotEq.proof : MulQuotEq.Statement.{u, w} := by
  intro k _ Ω _ _ N x F₁ F₂ G₁ G₂ s h₁ h₂ h₃
  let e : ∀ I, (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) ≃ₗ[k] (G₁.sub I ⧸ SubSystem.quotSub G₁ G₂ I) :=
    fun I => LinearEquiv.ofBijective (mulQuotMap h₁ h₃ I) (mulQuotMap_bijective h₁ h₂ h₃ I)
  have he : ∀ I J h m, e J (SubSystem.quotRes F₁ F₂ I J h m) = SubSystem.quotRes G₁ G₂ I J h (e I m) := by
    intro I J h m
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rfl
  unfold eulerCharQuot
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  exact ((Cech.equivH e he i).finrank_eq).symm

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ZColumnsCechPartition
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

namespace Cech.Partition

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V]
  [Module R V]

def onSet {i : ℕ} (s : Cech.Cochain (fun _ : Cell U => V) i) (A : Finset (Fin n)) : V :=
  if h : A.card = i + 1 ∧ A ⊆ U then
    s ⟨⟨A, Finset.card_pos.mp (h.1 ▸ Nat.succ_pos i), h.2⟩, h.1⟩
  else 0

theorem onSet_idx {i : ℕ} (s : Cech.Cochain (fun _ : Cell U => V) i) (I : Cech.Idx U i) :
    onSet s I.1.1 = s I := by
  unfold onSet
  rw [dite_eq_left ⟨I.2, I.1.2.2⟩]

theorem d_eq {i : ℕ} (s : Cech.Cochain (fun _ : Cell U => V) i) (K : Cech.Idx U (i + 1)) :
    Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) i s K =
      ∑ j ∈ K.1.1, Cech.sgn K.1.1 j • onSet s (K.1.1.erase j) := by
  rw [Cech.d_apply, ← Finset.sum_coe_sort K.1.1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← onSet_idx s (Cech.face K j)]
  rfl

def coneY {i : ℕ} (k : Fin n) (z : Cech.Cochain (fun _ : Cell U => V) (i + 1)) (A : Finset (Fin n)) : V :=
  if k ∈ A then 0 else Cech.sgn (insert k A) k • onSet z (insert k A)

theorem cone_d {i : ℕ} {z : Cech.Cochain (fun _ : Cell U => V) (i + 1)}
    (hz : Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) (i + 1) z = 0) {k : Fin n} (hk : k ∈ U)
    (K : Cech.Idx U (i + 1)) :
    ∑ j ∈ K.1.1, Cech.sgn K.1.1 j • coneY k z (K.1.1.erase j) = z K := by
  have hcoc : ∀ L : Finset (Fin n), L ⊆ U → L.card = i + 1 + 1 + 1 →
      ∑ j ∈ L, Cech.sgn L j • onSet z (L.erase j) = 0 := by
    intro L hLU hL
    have h := congrFun hz ⟨⟨L, Finset.card_pos.mp (by omega), hLU⟩, hL⟩
    rw [d_eq] at h
    exact h
  rw [← onSet_idx z K]
  have hK : K.1.1.card = i + 1 + 1 := K.2
  have hKU : K.1.1 ⊆ U := K.1.2.2
  generalize K.1.1 = Kf at hK hKU ⊢
  by_cases h : k ∈ Kf
  · rw [Finset.sum_eq_single k]
    · rw [coneY, if_neg (Finset.notMem_erase k Kf), Finset.insert_erase h, smul_smul,
        Cech.Cone.sgn_mul_self, one_smul]
    · intro j hj hne
      rw [coneY, if_pos (Finset.mem_erase.mpr ⟨Ne.symm hne, h⟩), smul_zero]
    · exact fun h' => absurd h h'
  · have hc := hcoc (insert k Kf) (Finset.insert_subset hk hKU)
      (by rw [Finset.card_insert_of_notMem h, hK])
    rw [Finset.sum_insert h, Finset.erase_insert h] at hc
    have hb := eq_neg_iff_add_eq_zero.mpr ((add_comm _ _).trans hc)
    have hs : ∑ j ∈ Kf, Cech.sgn Kf j • coneY k z (Kf.erase j) =
        -(Cech.sgn (insert k Kf) k •
          ∑ j ∈ Kf, Cech.sgn (insert k Kf) j • onSet z ((insert k Kf).erase j)) := by
      rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hne : k ≠ j := fun e => h (e ▸ hj)
      have hni : k ∉ Kf.erase j := fun hm => h (Finset.mem_of_mem_erase hm)
      rw [Finset.erase_insert_of_ne hne, coneY, if_neg hni, smul_smul, smul_smul,
        Cech.Cone.sgn_key h hj, neg_smul]
    rw [hs, hb, smul_neg, neg_neg, smul_smul, Cech.Cone.sgn_mul_self, one_smul]

theorem exact_of_partition {A : Type w} [Semiring A] [Module A V] (M : Cell U → Submodule R V)
    {i : ℕ} (z : Cech.Cochain (fun _ : Cell U => V) (i + 1))
    (hz : Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) (i + 1) z = 0)
    (a : Fin n → A) (ha : ∑ k ∈ U, a k = 1)
    (hmem : ∀ (K : Cech.Idx U i) (k : Fin n), k ∈ U → k ∉ K.1.1 →
      a k • onSet z (insert k K.1.1) ∈ M K.1) :
    ∃ t ∈ Cech.Cdeg (fun _ : Cell U => V) M i,
      Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) i t = z := by
  refine ⟨fun K => ∑ k ∈ U, a k • coneY k z K.1.1, fun K _ => ?_, ?_⟩
  · refine Submodule.sum_mem _ fun k hk => ?_
    unfold coneY
    split_ifs with h
    · rw [smul_zero]; exact zero_mem _
    · rw [smul_comm]; exact zsmul_mem (hmem K k hk h) _
  · funext K
    rw [d_eq]
    have hY : ∀ j ∈ K.1.1, onSet (fun I => ∑ k ∈ U, a k • coneY k z I.1.1 :
        Cech.Cochain (fun _ : Cell U => V) i) (K.1.1.erase j) =
          ∑ k ∈ U, a k • coneY k z (K.1.1.erase j) := by
      intro j hj
      unfold onSet
      rw [dite_eq_left ⟨by rw [Finset.card_erase_of_mem hj, K.2]; rfl,
        (Finset.erase_subset _ _).trans K.1.2.2⟩]
    rw [Finset.sum_congr rfl fun j hj => by rw [hY j hj]]
    calc ∑ j ∈ K.1.1, Cech.sgn K.1.1 j • ∑ k ∈ U, a k • coneY k z (K.1.1.erase j)
        = ∑ k ∈ U, a k • ∑ j ∈ K.1.1, Cech.sgn K.1.1 j • coneY k z (K.1.1.erase j) := by
          simp_rw [Finset.smul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => smul_comm _ _ _
      _ = ∑ k ∈ U, a k • z K := Finset.sum_congr rfl fun k hk => by rw [cone_d hz hk K]
      _ = z K := by rw [← Finset.sum_smul, ha, one_smul]

theorem onSet_pair {z : Cech.Cochain (fun _ : Cell U => V) 0}
    (hz : Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) 0 z = 0)
    {a b : Fin n} (haU : a ∈ U) (hbU : b ∈ U) (hab : a < b) : onSet z {a} = onSet z {b} := by
  have hcard : ({a, b} : Finset (Fin n)).card = 0 + 1 + 1 := Finset.card_pair hab.ne
  have h := congrFun hz ⟨⟨{a, b}, Finset.insert_nonempty _ _,
    Finset.insert_subset haU (Finset.singleton_subset_iff.mpr hbU)⟩, hcard⟩
  rw [d_eq] at h
  change ∑ j ∈ ({a, b} : Finset (Fin n)), Cech.sgn {a, b} j • onSet z (({a, b} : Finset _).erase j)
    = 0 at h
  have ha : a ∉ ({b} : Finset (Fin n)) := Finset.notMem_singleton.mpr hab.ne
  rw [Finset.sum_pair hab.ne, Finset.erase_insert ha, Finset.erase_insert_of_ne hab.ne,
    Finset.erase_singleton, Cech.Cone.sgn_insert ha, Cech.Cone.sgn_insert ha, if_neg (lt_irrefl _),
    if_pos hab] at h
  have e1 : Cech.sgn ({b} : Finset (Fin n)) a = 1 := by
    simp [Cech.sgn, Finset.filter_singleton, lt_asymm hab]
  have e2 : Cech.sgn ({b} : Finset (Fin n)) b = 1 := by
    simp [Cech.sgn, Finset.filter_singleton]
  rw [e1, e2, insert_empty_eq] at h
  rw [one_mul, one_smul, one_mul, neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h
  exact h.symm

theorem const {z : Cech.Cochain (fun _ : Cell U => V) 0}
    (hz : Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) 0 z = 0)
    (I K : Cech.Idx U 0) : z I = z K := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp I.2
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp K.2
  have haU : a ∈ U := I.1.2.2 (by rw [ha]; exact Finset.mem_singleton_self a)
  have hbU : b ∈ U := K.1.2.2 (by rw [hb]; exact Finset.mem_singleton_self b)
  rw [← onSet_idx z I, ← onSet_idx z K, ha, hb]
  rcases lt_trichotomy a b with h | rfl | h
  · exact onSet_pair hz haU hbU h
  · rfl
  · exact (onSet_pair hz hbU haU h).symm

end Cech.Partition

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutDimLower
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section CutDimLowerAux

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem exists_monos_mul_mem_twistMod_all (L : LineBundle S x) (I : Chart x) (y : Ω)
    (hy : ∀ δ ∈ L.sub I, y * δ ∈ chartRing S x I) :
    ∃ U ∈ monos (S := S) I.1, ∃ dU : ℕ, U.IsHomogeneous dU ∧
      ∀ (K : Chart x), ∀ δ ∈ L.sub K, aeval x U * (y * δ) ∈ twistMod S x (dU : ℤ) K := by
  classical
  have hyU := mul_mem_chartRing_union L.toSubFamily I
  choose G hG using fun K => L.fg K
  have hgen : ∀ p : Σ K : Chart x, (G K : Set Ω),
      y * (p.2 : Ω) ∈ chartRing S x (chartUnion I p.1) := fun p =>
    hyU p.1 y hy _ (L.mono p.1 (chartUnion I p.1)
      (show p.1.1 ⊆ (chartUnion I p.1).1 from Finset.subset_union_right) _
      (by rw [← hG p.1]; exact Submodule.subset_span p.2.2))
  choose u hu d hd hud using fun p : (Σ K : Chart x, (G K : Set Ω)) =>
    exists_monos_mul_mem_twistMod (S := S) I p.1 (y * (p.2 : Ω)) (hgen p)
  obtain ⟨U, hUdef⟩ : ∃ U : Poly S N, U = ∏ p, u p := ⟨_, rfl⟩
  obtain ⟨dU, hdUdef⟩ : ∃ dU : ℕ, dU = ∑ p, d p := ⟨_, rfl⟩
  have hUm : U ∈ monos (S := S) I.1 := hUdef ▸ prod_mem fun p _ => hu p
  have hUh : U.IsHomogeneous dU := hUdef ▸ hdUdef ▸ IsHomogeneous.prod _ _ _ fun p _ => hd p
  have key : ∀ p : Σ K : Chart x, (G K : Set Ω),
      aeval x U * (y * (p.2 : Ω)) ∈ twistMod S x (dU : ℤ) p.1 := by
    intro p
    have hsplit : U = u p * ∏ q ∈ Finset.univ.erase p, u q := by
      rw [hUdef, Finset.mul_prod_erase _ _ (Finset.mem_univ p)]
    have hdsplit : dU = d p + ∑ q ∈ Finset.univ.erase p, d q := by
      rw [hdUdef, Finset.add_sum_erase _ _ (Finset.mem_univ p)]
    have h2 := aeval_mem_twistMod (x := x)
      (IsHomogeneous.prod _ _ _ fun q _ => hd q : (∏ q ∈ Finset.univ.erase p, u q).IsHomogeneous _) p.1
    have h3 := twistMod_mul_mem (hud p) h2
    rw [hsplit, hdsplit, map_mul, Nat.cast_add]
    convert h3 using 1
    ring
  refine ⟨U, hUm, dU, hUh, fun K δ hδ => ?_⟩
  rw [← hG K] at hδ
  induction hδ using Submodule.span_induction with
  | mem δ hδ => exact key ⟨K, ⟨δ, hδ⟩⟩
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add, mul_add]; exact add_mem ha hb
  | smul a b _ hb =>
    rw [chartRing_smul_def, show aeval x U * (y * ((a : Ω) * b)) = (a : Ω) * (aeval x U * (y * b)) by ring,
      ← chartRing_smul_def]
    exact Submodule.smul_mem _ a hb

end CutDimLowerAux

theorem CutDimLower.proof : CutDimLower.Statement.{u, w} := by
  classical
  intro k _ Ω _ _ N x n pp L s qq hW hs hqq hjq
  obtain ⟨j, hj⟩ := hjq
  have hpp : pp.IsPrime := hW.isPrime
  have hqp : qq.IsPrime := hqq.1.1
  have hle : pp ⊔ zeroIdeal L.toSubSystem s ≤ qq := hqq.1.2
  have hppq : pp ≤ qq := le_sup_left.trans hle
  have hZq : zeroIdeal L.toSubSystem s ≤ qq := le_sup_right.trans hle

  have hvan : ∀ {F : Poly k N} {e : ℕ}, F.IsHomogeneous e → aeval x F = 0 → F ∈ pp := fun hF h0 =>
    hW.le ((mem_primeOf_of_isHomogeneous x hF).mpr h0)
  have hxj : x j ≠ 0 := by
    intro h0
    exact hj (hppq (hvan (isHomogeneous_X k j) (by rw [aeval_X, h0])))
  set J : Chart x := singleChart hxj with hJdef
  have hjJ : j ∈ J.1 := Finset.mem_singleton_self j
  have hmono : ∀ {t : Poly k N}, t ∈ monos (S := k) J.1 → t ∉ qq := fun ht =>
    monos_not_mem (fun i hi => by rw [Finset.mem_singleton.mp hi]; exact hj) ht

  have hone : (1 : Ω) ∉ idealMod (x := x) qq J := by
    intro h1
    obtain ⟨g, t, e, hg, ht, hge, hte, h1⟩ := idealMod_mem_form qq J h1
    have ht0 := eval_ne_zero_of_mem_monos J ht
    have hgt : aeval x g = aeval x t := by
      rw [eq_div_iff ht0, one_mul] at h1; exact h1.symm
    have hd : g - t ∈ qq := hppq (hvan (hge.sub hte) (by rw [map_sub, hgt, sub_self]))
    exact hmono ht (by simpa using sub_mem hg hd)

  obtain ⟨Q', hQ'⟩ := L.invertible J
  have hLQ : ∀ l ∈ L.sub J, ∀ q ∈ Q', l * q ∈ chartRing k x J := by
    intro l hl q hq
    have h := Submodule.mul_mem_mul hl hq
    rw [hQ', Submodule.mem_one] at h
    obtain ⟨y, hy⟩ := h
    rw [← hy]
    exact y.2
  obtain ⟨l, hl, q, hq, hu⟩ : ∃ l ∈ L.sub J, ∃ q ∈ Q', l * q ∉ idealMod (x := x) qq J := by
    by_contra hcon
    push Not at hcon
    have h1 : L.sub J * Q' ≤ idealMod (x := x) qq J := Submodule.mul_le.mpr fun l hl q hq => hcon l hl q hq
    rw [hQ'] at h1
    exact hone (h1 (Submodule.mem_one.mpr ⟨1, map_one _⟩))

  have hsJ : s ∈ L.sub J := (Submodule.mem_iInf _).mp hs J
  obtain ⟨f, t0, e, ht0, hf, ht0e, ha⟩ := hLQ s hsJ q hq
  have ht00 := eval_ne_zero_of_mem_monos J ht0
  have hfz : s * q * aeval x t0 = aeval x f := (eq_div_iff ht00).mp ha

  obtain ⟨U, hUm, dU, hUh, hUK⟩ := exists_monos_mul_mem_twistMod_all L J q
    (fun δ hδ => by rw [mul_comm]; exact hLQ δ hδ q hq)
  have hfU : f * U ∈ zeroIdeal L.toSubSystem s := by
    refine Ideal.subset_span ⟨e + dU, hf.mul hUh, fun K δ hδ => ?_⟩
    refine ⟨aeval x t0 * (aeval x U * (q * δ)), ?_, ?_⟩
    · rw [Nat.cast_add]
      exact twistMod_mul_mem (aeval_mem_twistMod ht0e K) (hUK K δ hδ)
    · rw [map_mul, ← hfz]; ring
  have hfq : f ∈ qq := (hqp.mem_or_mem (hZq hfU)).resolve_right (hmono hUm)

  obtain ⟨U', t2, eU, ht2, hU'h, ht2e, hUdef⟩ := hLQ l hl q hq
  have hU'q : U' ∉ qq := fun h => hu (hUdef ▸ Submodule.subset_span ⟨U', t2, eU, h, ht2, hU'h, ht2e, rfl⟩)
  have ht20 := eval_ne_zero_of_mem_monos J ht2
  have hU'v : aeval x U' = l * q * aeval x t2 := ((eq_div_iff ht20).mp hUdef).symm
  have hgen : ∀ h ∈ {f' : Poly k N | ∃ c : ℕ, f'.IsHomogeneous c ∧ ∀ (I : Chart x), ∀ δ ∈ L.toSubSystem.sub I,
      ∃ o ∈ twistMod k x (c : ℤ) I, aeval x f' * δ = s * o},
      ∃ t : Poly k N, t ∉ qq ∧ t * h ∈ pp ⊔ Ideal.span {f} := by
    rintro h ⟨c, hc, hh⟩
    obtain ⟨o, ho, hho⟩ := hh J l hl
    rw [twistMod_eq_span (c : ℤ) J hjJ, Submodule.mem_span_singleton] at ho
    obtain ⟨b, rfl⟩ := ho
    obtain ⟨B, t1, eb, ht1, hB, ht1e, hb⟩ := b.2
    have ht10 := eval_ne_zero_of_mem_monos J ht1
    have hBv : aeval x B = (b : Ω) * aeval x t1 := ((eq_div_iff ht10).mp hb).symm
    rw [chartRing_smul_def, zpow_natCast] at hho
    have hF1 : (U' * h * t0 * t1).IsHomogeneous (eU + c + e + eb) := ((hU'h.mul hc).mul ht0e).mul ht1e
    have hF2 : (f * (B * X j ^ c * t2)).IsHomogeneous (eU + c + e + eb) := by
      have := hf.mul ((hB.mul (isHomogeneous_X_pow j c)).mul ht2e)
      rwa [show e + (eb + c + eU) = eU + c + e + eb by ring] at this
    have hFv : aeval x (U' * h * t0 * t1 - f * (B * X j ^ c * t2)) = 0 := by
      simp only [map_sub, map_mul, map_pow, aeval_X]
      rw [hU'v, hBv, ← hfz]
      linear_combination (q * aeval x t2 * aeval x t0 * aeval x t1) * hho
    refine ⟨U' * t0 * t1, ?_, ?_⟩
    · intro hmem
      rcases hqp.mem_or_mem hmem with h1 | h1
      · rcases hqp.mem_or_mem h1 with h2 | h2
        · exact hU'q h2
        · exact hmono ht0 h2
      · exact hmono ht1 h1
    · have hsplit : U' * t0 * t1 * h =
          (U' * h * t0 * t1 - f * (B * X j ^ c * t2)) + f * (B * X j ^ c * t2) := by ring
      rw [hsplit]
      exact add_mem (Ideal.mem_sup_left (hvan (hF1.sub hF2) hFv))
        (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f)))

  have hmin : qq ∈ (pp ⊔ Ideal.span {f}).minimalPrimes := by
    refine ⟨⟨hqp, sup_le hppq ((Ideal.span_singleton_le_iff_mem qq).mpr hfq)⟩, ?_⟩
    rintro r ⟨hr, hfr⟩ hrq
    refine hqq.2 ⟨hr, sup_le (le_sup_left.trans hfr) (Ideal.span_le.mpr ?_)⟩ hrq
    intro h hh
    obtain ⟨t, htq, hth⟩ := hgen h hh
    exact (hr.mem_or_mem (hfr hth)).resolve_left fun h' => htq (hrq h')

  have hQ := Ideal.map_height_le_one_of_mem_minimalPrimes hmin
  have := hpp
  have : (qq.map (Ideal.Quotient.mk pp)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have key := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient k
    (qq.map (Ideal.Quotient.mk pp))
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hppq), hW.dim] at key
  have hnn : (0 : WithBot ℕ∞) ≤ ringKrullDim (Poly k N ⧸ qq) := ringKrullDim_nonneg_of_nontrivial
  generalize ringKrullDim (Poly k N ⧸ qq) = D at key hnn ⊢
  generalize (qq.map (Ideal.Quotient.mk pp)).height = H at key hQ
  induction D using WithBot.recBotCoe with
  | bot => exact absurd hnn (by simp)
  | coe d =>
    have key' : H + d = ((n + 1 + 1 : ℕ) : ℕ∞) := by exact_mod_cast key
    suffices ((n + 1 : ℕ) : ℕ∞) ≤ d by exact_mod_cast this
    induction d using ENat.recTopCoe with
    | top => exact le_top
    | coe m =>
      induction H using ENat.recTopCoe with
      | top => simp at hQ
      | coe h =>
        have h1 : h ≤ 1 := by exact_mod_cast hQ
        have h2 : h + m = n + 1 + 1 := by exact_mod_cast key'
        exact_mod_cast (by omega : n + 1 ≤ m)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCycleSplitFiltStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace CycleSplit.Filt.Step

theorem length_ne_top_of_smul_eq_zero {S : Type u} [CommRing S] {T : Type w} [AddCommGroup T] [Module S T]
    [Module.Finite S T] (𝔪 : Ideal S) [𝔪.IsMaximal] (h : ∀ a ∈ 𝔪, ∀ t : T, a • t = 0) :
    Module.length S T ≠ ⊤ := by
  let := Ideal.Quotient.field 𝔪
  have hT : Module.IsTorsionBySet S T 𝔪 := by
    intro t a
    exact h a a.2 t
  let : Module (S ⧸ 𝔪) T := hT.module
  have : IsScalarTower S (S ⧸ 𝔪) T := hT.isScalarTower
  have : Module.Finite (S ⧸ 𝔪) T := Module.Finite.of_restrictScalars_finite S (S ⧸ 𝔪) T
  rw [Module.length_eq_of_surjective (R := S ⧸ 𝔪) (M := T) Ideal.Quotient.mk_surjective]
  exact Module.length_ne_top

theorem proof (hSC : SurjectiveClosed.Statement.{u, w}) (hFS : FiniteSections.Statement.{u, w}) :
    CycleSplit.Filt.Step.Statement.{u, w} := by
  classical
  intro S _ _ Ω _ _ N x 𝔪 h𝔪 K pp g e hKh hK h𝔪K hg hpph hpp Q
  obtain ⟨c₀, hc₀⟩ := hSC S Ω N x Q pp hpph
  filter_upwards [eventually_ge_atTop (c₀ + e).toNat] with c hc
  have hce : c₀ ≤ (c : ℤ) - e := by
    have := Int.toNat_le.mp hc
    omega
  set F : SubSystem S x Ω := Q.twist (twistSys S x (c : ℤ)) with hF
  set F' : SubSystem S x Ω := Q.twist (twistSys S x ((c : ℤ) - e)) with hF'
  have hF'eq : F' = F.twist (twistSys S x (-(e : ℤ))) := by
    rw [hF', hF, SubSystem.twist_assoc, twistSys_twist_eq_add, sub_eq_add_neg]
  have hsub : ∀ (J : Ideal (Poly S N)) (I : Chart x),
      (F.twist (idealSys x J)).sub I = idealMod J I * F.sub I :=
    fun J I ↦ SubSystem.twist_sub_eq_mul_of_line _ _ I
  have hF's : ∀ I, F'.sub I = twistMod S x (-(e : ℤ)) I * F.sub I := fun I ↦ by
    rw [hF'eq]; exact SubSystem.twist_sub_eq_mul_of_line _ _ I
  have hF'p : ∀ I, (F'.twist (idealSys x pp)).sub I =
      idealMod pp I * (twistMod S x (-(e : ℤ)) I * F.sub I) := fun I ↦ by
    rw [SubSystem.twist_sub_eq_mul_of_line, hF's]; rfl
  have hinv : ∀ I, ∃ Q' : Submodule (chartRing S x I) Ω, F.sub I * Q' = 1 :=
    fun I ↦ (Q.tensorProd (twistBundle S x (c : ℤ))).invertible I

  have hgK' : ∀ I : Chart x, ∀ y ∈ F'.sub I,
      aeval x g * y ∈ (F.twist (idealSys x (K ⊔ Ideal.span {g}))).sub I := by
    intro I y hy
    obtain ⟨i, hi⟩ := I.2.1
    rw [hF's, twistMod_eq_span _ I hi] at hy
    obtain ⟨q, hq, rfl⟩ := Submodule.mem_span_singleton_mul.mp hy
    rw [hsub]
    have hγ : aeval x g / x i ^ e ∈ idealMod (K ⊔ Ideal.span {g}) I :=
      Submodule.subset_span ⟨g, X i ^ e, e, Ideal.mem_sup_right (Ideal.mem_span_singleton_self g),
        pow_mem (X_mem_monos hi) e, hg, isHomogeneous_X_pow i e, by simp⟩
    have h1 : aeval x g * (x i ^ (-(e : ℤ)) * q) = aeval x g / x i ^ e * q := by
      rw [← mul_assoc, zpow_neg, zpow_natCast, div_eq_mul_inv]
    rw [h1]
    exact Submodule.mul_mem_mul hγ hq
  have hU : ∀ I (y : Ω), y ∈ F'.sub I → aeval x g * y ∈ (F.twist (idealSys x K)).sub I →
      y ∈ (F'.twist (idealSys x pp)).sub I := by
    intro I y hy hgy
    obtain ⟨i, hi⟩ := I.2.1
    obtain ⟨Q', hQ'⟩ := hinv I
    rw [hF's] at hy
    rw [hsub] at hgy
    rw [hF'p]
    exact SectionCount.Drop.Filt.Step.mem_chart_of_mul_mem hK hpp hg I hi _ Q' hQ' hy hgy
  have hC : ∀ I (y : Ω), y ∈ (F'.twist (idealSys x pp)).sub I →
      aeval x g * y ∈ (F.twist (idealSys x K)).sub I := by
    intro I y hy
    obtain ⟨i, hi⟩ := I.2.1
    rw [hF'p] at hy
    rw [hsub]
    exact SectionCount.Drop.Filt.Step.mul_mem_chart hpp hg I hi _ hy
  have hE : ∀ s ∈ (F.twist (idealSys x (K ⊔ Ideal.span {g}))).secs, ∀ I,
      ∃ y ∈ F'.sub I, s - aeval x g * y ∈ (F.twist (idealSys x K)).sub I := by
    intro s hs I
    obtain ⟨i, hi⟩ := I.2.1
    have hsI := SectionCount.Drop.Filt.Step.mem_secs_iff'.mp hs I
    rw [hsub] at hsI
    rw [hF's, hsub]
    exact SectionCount.Drop.Filt.Step.exists_chart hKh hg I hi _ hsI

  have hWV : ∀ z, z ∈ (F.twist (idealSys x K)).secs →
      z ∈ (F.twist (idealSys x (K ⊔ Ideal.span {g}))).secs := by
    intro z hz
    refine SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ ?_
    have h1 := SectionCount.Drop.Filt.Step.mem_secs_iff'.mp hz I
    rw [hsub] at h1 ⊢
    have hle : idealMod K I ≤ idealMod (K ⊔ Ideal.span {g}) I := by
      refine Submodule.span_mono ?_
      rintro _ ⟨f, s, d, hf, hs, hfd, hsd, rfl⟩
      exact ⟨f, s, d, Ideal.mem_sup_left hf, hs, hfd, hsd, rfl⟩
    exact (Submodule.mul_le.mpr fun m hm n hn ↦ Submodule.mul_mem_mul (hle hm) hn) h1
  have hVH : ∀ z, z ∈ (F.twist (idealSys x (K ⊔ Ideal.span {g}))).secs → z ∈ F.secs := fun z hz ↦
    SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ SurjectiveClosed.twist_idealSys_le F _ I (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp hz I)
  have hgsec : ∀ y ∈ F'.secs, aeval x g * y ∈ (F.twist (idealSys x (K ⊔ Ideal.span {g}))).secs :=
    fun y hy ↦ SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ hgK' I y (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp hy I)

  have hlift : ∀ s ∈ (F.twist (idealSys x (K ⊔ Ideal.span {g}))).secs,
      ∃ t ∈ F'.secs, s - aeval x g * t ∈ (F.twist (idealSys x K)).secs := by
    intro s hs
    choose y hy hys using hE s hs
    have hcomp : ∀ (I₁ I₂ : Chart x), I₁.1 ⊆ I₂.1 →
        y I₁ - y I₂ ∈ (F'.twist (idealSys x pp)).sub I₂ := by
      intro I₁ I₂ h
      refine hU I₂ _ (sub_mem (F'.mono I₁ I₂ h _ (hy I₁)) (hy I₂)) ?_
      have h1 := sub_mem (hys I₂) ((F.twist (idealSys x K)).mono I₁ I₂ h _ (hys I₁))
      convert h1 using 1
      ring
    obtain ⟨t, ht, htI⟩ := hc₀ _ hce y hy hcomp
    refine ⟨t, ht, SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ ?_⟩
    have h1 := add_mem (hys I) (hC I _ (neg_mem (htI I)))
    convert h1 using 1
    ring

  set H := F.secs with hH
  set H' := F'.secs with hH'
  set A := ((F.twist (idealSys x K)).secs).comap H.subtype with hA
  set B := ((F.twist (idealSys x (K ⊔ Ideal.span {g}))).secs).comap H.subtype with hB
  set P := ((F'.twist (idealSys x pp)).secs).comap H'.subtype with hP
  have hAB : A ≤ B := fun z hz ↦ Submodule.mem_comap.mpr (hWV _ (Submodule.mem_comap.mp hz))
  let μ0 : H' →ₗ[S] H := (LinearMap.mulLeft S (aeval x g)).restrict (p := H') (q := H)
    (fun y hy ↦ hVH _ (hgsec y hy))
  let μ : H' →ₗ[S] H ⧸ A := A.mkQ ∘ₗ μ0
  have hμ : ∀ y : H', y ∈ P ↔ μ y = 0 := by
    intro y
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, Submodule.mem_comap]
    change (y : Ω) ∈ _ ↔ aeval x g * (y : Ω) ∈ _
    constructor
    · intro h
      exact SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ hC I _ (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp h I)
    · intro h
      exact SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ hU I _ (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp y.2 I) (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp h I)
  let μb : (H' ⧸ P) →ₗ[S] H ⧸ A := P.liftQ μ (fun y hy ↦ (hμ y).mp hy)
  have hinj : Function.Injective μb := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ (fun y hy ↦ (hμ y).mpr hy)
  let π : (H ⧸ A) →ₗ[S] H ⧸ B := Submodule.factor hAB
  have hsurj : Function.Surjective π := by
    intro z
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective B z
    exact ⟨A.mkQ m, rfl⟩
  have hex : Function.Exact μb π := by
    intro z
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective A z
    change B.mkQ m = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    constructor
    · intro hm
      obtain ⟨t, ht, hst⟩ := hlift _ hm
      change (m : Ω) - aeval x g * t ∈ _ at hst
      refine ⟨P.mkQ ⟨t, ht⟩, ?_⟩
      change A.mkQ (μ0 ⟨t, ht⟩) = A.mkQ m
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap]
      change aeval x g * t - (m : Ω) ∈ _
      have h1 := neg_mem hst
      convert h1 using 1
      ring
    · rintro ⟨w, hw⟩
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective P w
      change A.mkQ (μ0 y) = A.mkQ m at hw
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap] at hw
      change aeval x g * (y : Ω) - m ∈ _ at hw
      change (m : Ω) ∈ _
      have h1 := sub_mem (hgsec _ y.2) (hWV _ hw)
      convert h1 using 1
      ring
  have hlen := Module.length_eq_add_of_exact μb π hinj hsurj hex

  have hfin : Module.length S (H ⧸ A) ≠ ⊤ := by
    by_cases hx : x = 0
    · have hE0 : IsEmpty (Chart x) := ⟨fun I ↦ by
        obtain ⟨i, hi⟩ := I.2.1
        exact (mem_support x).mp (I.2.2 hi) (by simp [hx])⟩
      have hAt : A = ⊤ := eq_top_iff.mpr fun m _ ↦
        Submodule.mem_comap.mpr (SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ isEmptyElim I)
      have : Subsingleton (H ⧸ A) := Submodule.Quotient.subsingleton_iff.mpr hAt
      rw [Module.length_eq_zero]
      exact ENat.zero_ne_top
    · have : Module.Finite S H := (hFS S Ω N x (Q.tensorProd (twistBundle S x (c : ℤ))) hx).1
      have := h𝔪
      refine length_ne_top_of_smul_eq_zero 𝔪 fun a ha z ↦ ?_
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective A z
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      change a • (m : Ω) ∈ _
      refine SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ ?_
      rw [hsub, Algebra.smul_def]
      refine Submodule.mul_mem_mul ?_ (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp m.2 I)
      exact Submodule.subset_span ⟨C a, 1, 0, h𝔪K (Ideal.mem_map_of_mem _ ha), one_mem _,
        isHomogeneous_C _ _, isHomogeneous_one _ _, by simp⟩
  have hB' : Module.length S (H ⧸ B) ≠ ⊤ := fun h ↦ hfin (by rw [hlen, h, add_top])
  have hP' : Module.length S (H' ⧸ P) ≠ ⊤ := fun h ↦ hfin (by rw [hlen, h, top_add])
  change ((Module.length S (H ⧸ A)).toNat : ℤ) =
    ((Module.length S (H ⧸ B)).toNat : ℤ) + ((Module.length S (H' ⧸ P)).toNat : ℤ)
  rw [hlen, ENat.toNat_add hP' hB']
  push_cast
  ring

end CycleSplit.Filt.Step

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleProductPos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem VeryAmpleProductPos.proof (hR : GenericPointSectionInput.Statement.{u, w}) (hP : PointDegreePos.Statement.{u, w})
    (hC : CutComponent.Statement.{u, w}) (hM : CutMultPos.Statement.{u}) :
    VeryAmpleProductPos.Statement.{u, w} := by
  intro k _ Ω _ _ N x e
  induction e with
  | zero =>
    intro pp L hW _
    have h0 : (fun i => (L i).toSubSystem) = (![] : Fin 0 → SubSystem k x Ω) :=
      funext fun i => i.elim0
    rw [h0, (hR k Ω N x).2.2.2.2 pp hW]
    exact_mod_cast hP k Ω N x pp hW
  | succ n ih =>
    intro pp L hW hL
    obtain ⟨s, hs, hsI⟩ := exists_sec_not_mem (L (Fin.last n)) (hL _) hW
    have hsplit : (fun i => (L i).toSubSystem) = Fin.snoc (α := fun _ => SubSystem k x Ω)
        (fun i : Fin n => (L (Fin.castSucc i)).toSubSystem) (L (Fin.last n)).toSubSystem :=
      (Fin.snoc_init_self _).symm
    rw [hsplit, (hR k Ω N x).2.2.2.1 n pp (fun i => L (Fin.castSucc i)) (L (Fin.last n)) s hW hs hsI]
    obtain ⟨q₀, hq₀, hq₀W⟩ := hC k Ω N x n pp (L (Fin.last n)) s hW (hL _) hs hsI

    have hterm : ∀ qq (h : qq ∈ (pp ⊔ zeroIdeal (L (Fin.last n)).toSubSystem s).minimalPrimes),
        IsSubvar x qq n → haveI : qq.IsPrime := h.1.1
        0 < (((cutMult (pp ⊔ zeroIdeal (L (Fin.last n)).toSubSystem s) qq).toNat : ℤ) *
          interNum qq (fun i => (L (Fin.castSucc i)).toSubSystem)) := by
      intro qq h hqW
      have hm := hM k N _ qq h
      exact mul_pos (by exact_mod_cast ENat.toNat_pos hm.1.ne' hm.2.ne) (ih qq _ hqW fun i => hL _)
    refine lt_of_lt_of_le ?_ (single_le_finsum q₀ ?_ ?_)
    · rw [dite_eq_left ⟨hq₀, hq₀W⟩]
      exact hterm q₀ hq₀ hq₀W
    · refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _
        (pp ⊔ zeroIdeal (L (Fin.last n)).toSubSystem s)).subset fun qq hqq => ?_
      by_contra hn
      exact hqq (dif_neg fun h => hn h.1)
    · intro qq
      split_ifs with h
      · exact (hterm qq h.1 h.2).le
      · exact le_rfl

end

end GroundTheory.Heights₂.Heights.Kleiman
end
