module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PHilbertPoint
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropFiltStepSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperCutObj

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.FiniteHZeroOfExact
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w v₁ v₂ v₃

namespace Cech

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R]
  {A : Cell U → Type v₁} [∀ I, AddCommGroup (A I)] [∀ I, Module R (A I)]
  {B : Cell U → Type v₂} [∀ I, AddCommGroup (B I)] [∀ I, Module R (B I)]
  {C : Cell U → Type v₃} [∀ I, AddCommGroup (C I)] [∀ I, Module R (C I)]


set_option maxHeartbeats 1000000 in
theorem finite_H_zero_of_exact [IsNoetherianRing R]
    (ρA : ∀ I J : Cell U, I.1 ⊆ J.1 → A I →ₗ[R] A J) (ρB : ∀ I J : Cell U, I.1 ⊆ J.1 → B I →ₗ[R] B J)
    (ρC : ∀ I J : Cell U, I.1 ⊆ J.1 → C I →ₗ[R] C J)
    (hρB : ∀ (I J K : Cell U) (h : I.1 ⊆ J.1) (h' : J.1 ⊆ K.1) (m : B I),
      ρB J K h' (ρB I J h m) = ρB I K (h.trans h') m)
    (ι : ∀ I, A I →ₗ[R] B I) (q : ∀ I, B I →ₗ[R] C I)
    (hι : ∀ I J h m, ι J (ρA I J h m) = ρB I J h (ι I m))
    (hq : ∀ I J h m, q J (ρB I J h m) = ρC I J h (q I m))
    (hinj : ∀ I, Function.Injective (ι I)) (hsurj : ∀ I, Function.Surjective (q I))
    (hex : ∀ I b, q I b = 0 ↔ ∃ a, ι I a = b)
    (hB : Module.Finite R (H B ρB 0)) (hA : Module.Finite R (H A ρA 1)) :
    Module.Finite R (H C ρC 0) := by
  have := hA
  have hιd := mapC_d (R := R) (G := A) (G' := B) ι hι
  have hqd := mapC_d (R := R) (G := B) (G' := C) q hq
  have hιinj : ∀ i, Function.Injective (mapC (R := R) (G := A) (G' := B) ι i) := fun i a b hab =>
    _root_.funext fun I => hinj I.1 (congrFun hab I)
  have hq0 : ∀ i (c : Cochain B i), mapC (R := R) (G := B) (G' := C) q i c = 0 ↔
      ∃ a, mapC (R := R) (G := A) (G' := B) ι i a = c := fun i c => by
    constructor
    · intro h
      choose a ha using fun I => (hex I.1 (c I)).mp (congrFun h I)
      exact ⟨a, _root_.funext ha⟩
    · rintro ⟨a, rfl⟩
      exact _root_.funext fun I => (hex I.1 _).mpr ⟨a I, rfl⟩

  obtain ⟨P, hP⟩ : ∃ P : Submodule R (Cochain B 0), ∀ w, w ∈ P ↔
      mapC (R := R) (G := B) (G' := C) q 1 (d B ρB 0 w) = 0 :=
    ⟨LinearMap.ker ((mapC (R := R) (G := B) (G' := C) q 1).comp (d B ρB 0)), fun _ => LinearMap.mem_ker⟩

  obtain ⟨θ, hθ0, hθs⟩ : ∃ θ : P →ₗ[R] H C ρC 0,
      (∀ p, θ p = 0 ↔ mapC (R := R) (G := B) (G' := C) q 0 p.1 = 0) ∧ Function.Surjective θ := by
    have hk : ∀ p : P, mapC (R := R) (G := B) (G' := C) q 0 p.1 ∈ LinearMap.ker (d C ρC 0) := fun p => by
      rw [LinearMap.mem_ker, ← hqd 0]; exact (hP p.1).mp p.2
    refine ⟨(Submodule.mkQ _).comp (LinearMap.codRestrict _
      ((mapC (R := R) (G := B) (G' := C) q 0).comp P.subtype) hk), fun p => ?_, fun h => ?_⟩
    · change Submodule.Quotient.mk _ = 0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact Submodule.mem_bot R
    · obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ h
      choose w hw using fun I : Idx U 0 => hsurj I.1 (c.1 I)
      have hmw : mapC (R := R) (G := B) (G' := C) q 0 w = c.1 := _root_.funext hw
      refine ⟨⟨w, (hP w).mpr (by rw [hqd 0, hmw]; exact c.2)⟩, ?_⟩
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk c
      congr 1
      exact Subtype.ext hmw

  have hdP : ∀ p : P, d B ρB 0 p.1 ∈ LinearMap.range (mapC (R := R) (G := A) (G' := B) ι 1) := fun p =>
    LinearMap.mem_range.mpr ((hq0 1 _).mp ((hP p.1).mp p.2))
  obtain ⟨g, hg⟩ : ∃ g : P →ₗ[R] Cochain A 1,
      ∀ p, mapC (R := R) (G := A) (G' := B) ι 1 (g p) = d B ρB 0 p.1 :=
    ⟨(LinearEquiv.ofInjective _ (hιinj 1)).symm.toLinearMap.comp
        (LinearMap.codRestrict _ ((d B ρB 0).comp P.subtype) hdP),
      fun p => congrArg Subtype.val ((LinearEquiv.ofInjective _ (hιinj 1)).apply_symm_apply _)⟩
  have hgk : ∀ p : P, g p ∈ LinearMap.ker (d A ρA 1) := fun p =>
    LinearMap.mem_ker.mpr (hιinj (1 + 1) ((hιd 1 (g p)).trans (by
      rw [hg, d_one_d_zero hρB, map_zero])))
  obtain ⟨ψ, hψ0⟩ : ∃ ψ : P →ₗ[R] H A ρA 1, ∀ p, ψ p = 0 ↔ ∃ g', d A ρA 0 g' = g p :=
    ⟨(Submodule.mkQ _).comp (LinearMap.codRestrict _ g hgk), fun p => by
      change Submodule.Quotient.mk _ = 0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact LinearMap.mem_range⟩
  have hle : LinearMap.ker θ ≤ LinearMap.ker ψ := fun p hp => by
    obtain ⟨a, ha⟩ := (hq0 0 _).mp ((hθ0 p).mp hp)
    refine (hψ0 p).mpr ⟨a, hιinj 1 ?_⟩
    rw [hg, hιd 0, ha]

  let f := (LinearMap.ker θ).liftQ ψ hle
  have hZP : LinearMap.ker (d B ρB 0) ≤ P := fun z hz =>
    (hP z).mpr (by rw [LinearMap.mem_ker.mp hz, map_zero])
  let j := (LinearMap.ker θ).mkQ.comp (Submodule.inclusion hZP)
  have hker : LinearMap.ker f = LinearMap.range j := by
    apply le_antisymm
    · intro m hm
      obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ m
      have hm' : ψ p = 0 := hm
      obtain ⟨g', hg'⟩ := (hψ0 p).mp hm'
      have hz : p.1 - mapC (R := R) (G := A) (G' := B) ι 0 g' ∈ LinearMap.ker (d B ρB 0) := by
        rw [LinearMap.mem_ker, map_sub, ← hιd 0, hg', hg, sub_self]
      have hqι : mapC (R := R) (G := B) (G' := C) q 0 (mapC (R := R) (G := A) (G' := B) ι 0 g') = 0 :=
        (hq0 0 _).mpr ⟨g', rfl⟩
      refine ⟨⟨_, hz⟩, (Submodule.Quotient.eq _).mpr ((hθ0 _).mpr ?_)⟩
      change mapC (R := R) (G := B) (G' := C) q 0
        (p.1 - mapC (R := R) (G := A) (G' := B) ι 0 g' - p.1) = 0
      rw [sub_sub_cancel_left, map_neg, hqι, neg_zero]
    · rintro _ ⟨z, rfl⟩
      show ψ (Submodule.inclusion hZP z) = 0
      refine (hψ0 _).mpr ⟨0, hιinj 1 ?_⟩
      rw [map_zero, map_zero, hg]
      exact (LinearMap.mem_ker.mp z.2).symm

  have hZfin : Module.Finite R (LinearMap.ker (d B ρB 0)) := by
    have : Module.Finite R (LinearMap.ker (d B ρB 0) ⧸
        (bdry B ρB 0).comap (LinearMap.ker (d B ρB 0)).subtype) := hB
    exact Module.Finite.equiv (Submodule.quotEquivOfEqBot
      ((bdry B ρB 0).comap (LinearMap.ker (d B ρB 0)).subtype) (eq_bot_iff.mpr fun z hz =>
      (Submodule.mem_bot R).mpr (Subtype.ext ((Submodule.mem_bot R).mp
        (show (z : Cochain B 0) ∈ (⊥ : Submodule R (Cochain B 0)) from hz)))))
  have hM : Module.Finite R (P ⧸ LinearMap.ker θ) := by
    refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker f (IsNoetherian.noetherian _) ?_⟩
    rw [top_inf_eq, hker, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map j
  exact Module.Finite.equiv (θ.quotKerEquivOfSurjective hθs)

end Cech

theorem QuotientH0Finite.proof : QuotientH0Finite.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ F G hGF hF hG
  have key := Cech.finite_H_zero_of_exact (A := fun I => ↥(G.sub I)) (B := fun I => ↥(F.sub I))
    (C := fun I => ↥(F.sub I) ⧸ SubSystem.quotSub F G I) G.res F.res (SubSystem.quotRes F G)
    (fun _ _ _ _ _ _ => rfl)
    (fun I => { toFun := fun y => ⟨y, hGF I y.2⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl })
    (fun I => (SubSystem.quotSub F G I).mkQ) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun I a b hab => Subtype.ext (congrArg (fun y : F.sub I => (y : E)) hab))
    (fun I => Submodule.mkQ_surjective _)
    (fun I b => ⟨fun h => ⟨⟨b, (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F G I)).mp h⟩, rfl⟩,
      fun ⟨a, ha⟩ => (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F G I)).mpr (ha ▸ a.2)⟩)
    hF hG
  exact key

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PQuotTrans
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace QuotTrans

section CechFacts

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type v}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}

theorem subsingleton_H_one_iff :
    Subsingleton (Cech.H G ρ 1) ↔
      ∀ z : Cech.Cochain G 1, Cech.d G ρ 1 z = 0 → ∃ w : Cech.Cochain G 0, Cech.d G ρ 0 w = z := by
  unfold Cech.H
  rw [Submodule.Quotient.subsingleton_iff, Submodule.comap_subtype_eq_top]
  constructor
  · intro h z hz
    exact h (LinearMap.mem_ker.mpr hz)
  · intro h z hz
    exact h z (LinearMap.mem_ker.mp hz)

theorem sgn_mul_sgn_erase {J : Finset (Fin n)} {j k : Fin n} (hj : j ∈ J) (hk : k ∈ J) (hjk : j ≠ k) :
    Cech.sgn J j * Cech.sgn (J.erase j) k = -(Cech.sgn J k * Cech.sgn (J.erase k) j) := by
  wlog h : j < k generalizing j k
  · have h' : k < j := lt_of_le_of_ne (not_lt.mp h) hjk.symm
    rw [this hk hj hjk.symm h', neg_neg]
  have hmem : j ∈ J.filter (· < k) := Finset.mem_filter.mpr ⟨hj, h⟩
  have e1 : (J.erase j).filter (· < k) = (J.filter (· < k)).erase j := by rw [Finset.filter_erase]
  have e2 : (J.erase k).filter (· < j) = J.filter (· < j) := by
    rw [Finset.filter_erase]
    apply Finset.erase_eq_of_notMem
    simp only [Finset.mem_filter, not_and, not_lt]
    intro _; exact h.le
  have hb : 1 ≤ (J.filter (· < k)).card := Finset.card_pos.mpr ⟨j, hmem⟩
  unfold Cech.sgn
  rw [e1, e2, Finset.card_erase_of_mem hmem]
  obtain ⟨b', hb'⟩ : ∃ b', (J.filter (· < k)).card = b' + 1 := ⟨_, (Nat.sub_add_cancel hb).symm⟩
  rw [hb', Nat.add_sub_cancel, pow_succ]
  ring

theorem d_one_d_zero
    (hρ : ∀ (I J K : Cell U) (h : I.1 ⊆ J.1) (h' : J.1 ⊆ K.1) (m : G I),
      ρ J K h' (ρ I J h m) = ρ I K (h.trans h') m)
    (w : Cech.Cochain G 0) : Cech.d G ρ 1 (Cech.d G ρ 0 w) = 0 := by
  funext J
  have key : ∀ (K K' : Cech.Idx U 0) (h : K.1.1 ⊆ J.1.1) (h' : K'.1.1 ⊆ J.1.1), K = K' →
      ρ K.1 J.1 h (w K) = ρ K'.1 J.1 h' (w K') := by
    rintro K _ h h' rfl; rfl
  rw [Cech.d_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Cech.d_apply, map_sum, map_zsmul, hρ, Finset.smul_sum, smul_smul]
  rw [Pi.zero_apply, Finset.sum_sigma']
  refine Finset.sum_involution
    (fun p _ => ⟨⟨p.2.1, Finset.mem_of_mem_erase p.2.2⟩,
      ⟨p.1.1, Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp p.2.2).1.symm, p.1.2⟩⟩⟩) ?_ ?_
    (fun _ _ => Finset.mem_univ _) (fun p _ => rfl)
  · rintro ⟨⟨j, hj⟩, ⟨k, hk⟩⟩ -
    have hk' := Finset.mem_erase.mp hk
    have hidx : Cech.face (Cech.face J ⟨j, hj⟩) ⟨k, hk⟩ =
        Cech.face (Cech.face J ⟨k, hk'.2⟩) ⟨j, Finset.mem_erase.mpr ⟨hk'.1.symm, hj⟩⟩ :=
      Subtype.ext (Subtype.ext (Finset.erase_right_comm))
    dsimp only
    rw [key _ _ _ (((Cech.face_subset _ _).trans (Cech.face_subset _ _))) hidx, ← add_smul]
    have hs : Cech.sgn J.1.1 j * Cech.sgn (Cech.face J ⟨j, hj⟩).1.1 k =
        -(Cech.sgn J.1.1 k * Cech.sgn (Cech.face J ⟨k, hk'.2⟩).1.1 j) :=
      sgn_mul_sgn_erase hj hk'.2 hk'.1.symm
    rw [hs, neg_add_cancel, zero_smul]
  · rintro ⟨⟨j, hj⟩, ⟨k, hk⟩⟩ - - heq
    exact (Finset.mem_erase.mp hk).1 (congrArg (fun p => p.1.1) heq)

theorem subsingleton_H_one_of_exact {A B C : Cell U → Type v}
    [∀ I, AddCommGroup (A I)] [∀ I, Module R (A I)] [∀ I, AddCommGroup (B I)] [∀ I, Module R (B I)]
    [∀ I, AddCommGroup (C I)] [∀ I, Module R (C I)]
    {ρA : ∀ I J : Cell U, I.1 ⊆ J.1 → A I →ₗ[R] A J} {ρB : ∀ I J : Cell U, I.1 ⊆ J.1 → B I →ₗ[R] B J}
    {ρC : ∀ I J : Cell U, I.1 ⊆ J.1 → C I →ₗ[R] C J}
    (ι : ∀ I, A I →ₗ[R] B I) (π : ∀ I, B I →ₗ[R] C I)
    (hι : ∀ I J h m, ι J (ρA I J h m) = ρB I J h (ι I m))
    (hπ : ∀ I J h m, π J (ρB I J h m) = ρC I J h (π I m))
    (hinj : ∀ I, Function.Injective (ι I)) (hsurj : ∀ I, Function.Surjective (π I))
    (hex : ∀ I b, π I b = 0 → ∃ a, ι I a = b)
    (hρB : ∀ (I J K : Cell U) (h : I.1 ⊆ J.1) (h' : J.1 ⊆ K.1) (m : B I),
      ρB J K h' (ρB I J h m) = ρB I K (h.trans h') m)
    (hA : Subsingleton (Cech.H A ρA 1)) (hC : Subsingleton (Cech.H C ρC 1)) :
    Subsingleton (Cech.H B ρB 1) := by
  rw [subsingleton_H_one_iff] at hA hC ⊢
  intro z hz
  have hπd := Cech.mapC_d (R := R) (G := B) (G' := C) π hπ
  have hιd := Cech.mapC_d (R := R) (G := A) (G' := B) ι hι

  obtain ⟨wc, hwc⟩ := hC (Cech.mapC (R := R) (G := B) (G' := C) π 1 z) (by rw [← hπd, hz, map_zero])
  choose w hw using fun I : Cech.Idx U 0 => hsurj I.1 (wc I)
  have hmw : Cech.mapC (R := R) (G := B) (G' := C) π 0 w = wc := funext hw
  have hr : Cech.mapC (R := R) (G := B) (G' := C) π 1 (z - Cech.d B ρB 0 w) = 0 := by
    rw [map_sub, hπd 0, hmw, hwc, sub_self]

  choose g hg using fun J : Cech.Idx U 1 => hex J.1 _ (congrFun hr J)
  have hg' : Cech.mapC (R := R) (G := A) (G' := B) ι 1 g = z - Cech.d B ρB 0 w := funext hg
  have hdg : Cech.d A ρA 1 g = 0 := by
    have h2 : Cech.mapC (R := R) (G := A) (G' := B) ι (1 + 1) (Cech.d A ρA 1 g) = 0 := by
      rw [hιd 1 g, hg', map_sub, hz, d_one_d_zero hρB, sub_zero]
    funext J
    exact hinj J.1 ((congrFun h2 J).trans (map_zero (ι J.1)).symm)
  obtain ⟨v, hv⟩ := hA g hdg
  refine ⟨w + Cech.mapC (R := R) (G := A) (G' := B) ι 0 v, ?_⟩
  rw [map_add (f := _), ← hιd, hv, hg', add_sub_cancel]

end CechFacts

end QuotTrans

theorem QuotTrans.proof : QuotTrans.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F₁ F₂ F₃ h32 h21 h23 h12
  unfold SubSystem.quotH at h23 h12 ⊢

  let π : ∀ I, (F₁.sub I ⧸ SubSystem.quotSub F₁ F₃ I) →ₗ[S] (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) :=
    fun I => (SubSystem.quotSub F₁ F₃ I).mapQ (SubSystem.quotSub F₁ F₂ I) LinearMap.id
      (fun y hy => h32 I hy)

  let incl : ∀ I, F₂.sub I →ₗ[S] F₁.sub I := fun I =>
    { toFun := fun y => ⟨y, h21 I y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let ι : ∀ I, (F₂.sub I ⧸ SubSystem.quotSub F₂ F₃ I) →ₗ[S] (F₁.sub I ⧸ SubSystem.quotSub F₁ F₃ I) :=
    fun I => (SubSystem.quotSub F₂ F₃ I).mapQ (SubSystem.quotSub F₁ F₃ I) (incl I) (fun _ hy => hy)
  refine QuotTrans.subsingleton_H_one_of_exact ι π ?_ ?_ ?_ ?_ ?_ ?_ h23 h12
  · intro I J h m
    induction m using Submodule.Quotient.induction_on
    rfl
  · intro I J h m
    induction m using Submodule.Quotient.induction_on
    rfl
  ·
    intro I
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro q hq
    induction q using Submodule.Quotient.induction_on with
    | H y =>
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        ((Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₃ I)).mp (LinearMap.mem_ker.mp hq))
  · intro I q
    induction q using Submodule.Quotient.induction_on with
    | H y => exact ⟨Submodule.Quotient.mk y, rfl⟩
  ·
    intro I b hb
    induction b using Submodule.Quotient.induction_on with
    | H y =>
      have hy : (y : E) ∈ F₂.sub I := (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₂ I)).mp hb
      exact ⟨Submodule.Quotient.mk ⟨y, hy⟩, rfl⟩
  · intro I J K h h' m
    induction m using Submodule.Quotient.induction_on
    rfl

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDrop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

universe u w

namespace SectionCount.Drop

theorem pow_add_le (c n : ℝ) (hc : 0 ≤ c) (hn : 1 ≤ n) :
    ∀ e : ℕ, (n + c) ^ e ≤ n ^ e + ((1 + c) ^ e - 1) * (n ^ e / n)
  | 0 => by simp
  | e + 1 => by
    have ih := pow_add_le c n hc hn e
    have hn0 : 0 < n := by linarith
    have hA : 0 ≤ (1 + c) ^ e - 1 := by
      have : 1 ≤ (1 + c) ^ e := one_le_pow₀ (by linarith)
      linarith
    have hq : n ^ e / n ≤ n ^ e := div_le_self (by positivity) hn
    have hq' : n ^ (e + 1) / n = n ^ e := by
      rw [pow_succ]; field_simp
    have hqn : n ^ e / n * n = n ^ e := by field_simp
    have h1 : (n + c) ^ e * (n + c) ≤ (n ^ e + ((1 + c) ^ e - 1) * (n ^ e / n)) * (n + c) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    have h2 : ((1 + c) ^ e - 1) * c * (n ^ e / n) ≤ ((1 + c) ^ e - 1) * c * n ^ e :=
      mul_le_mul_of_nonneg_left hq (mul_nonneg hA hc)
    rw [hq', pow_succ, pow_succ, pow_succ]
    nlinarith [h1, h2, hqn]

theorem pow_add_le_mul (c n : ℝ) (hc : 0 ≤ c) (hn : 1 ≤ n) (e : ℕ) :
    (n + c) ^ e ≤ (1 + c) ^ e * n ^ e := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by linarith) (by nlinarith) e

theorem term_le (I C c n h : ℝ) (e d : ℕ) (hed : e ≤ d) (hc : 0 ≤ c) (hn : 1 ≤ n)
    (hh : |h - I * (n + c) ^ e / (e.factorial : ℝ)| ≤ C * (n + c) ^ e / (n + c)) :
    h ≤ (if e = d then I else 0) * n ^ d / (d.factorial : ℝ) +
      (|I| + |C|) * (1 + c) ^ e * (n ^ d / n) := by
  have hn0 : 0 < n := by linarith
  have hnc : n ≤ n + c := by linarith
  have hP : (n + c) ^ e ≤ (1 + c) ^ e * n ^ e := pow_add_le_mul c n hc hn e
  have hPe : 0 ≤ (n + c) ^ e := by positivity
  have hne : n ^ e ≤ n ^ d := pow_le_pow_right₀ hn hed
  have h1 := (abs_le.mp hh).2

  have hC : C * (n + c) ^ e / (n + c) ≤ |C| * (1 + c) ^ e * (n ^ d / n) := by
    calc C * (n + c) ^ e / (n + c) ≤ |C| * (n + c) ^ e / (n + c) := by
          gcongr; exact le_abs_self C
      _ ≤ |C| * (n + c) ^ e / n := by
          apply div_le_div_of_nonneg_left (by positivity) hn0 hnc
      _ ≤ |C| * ((1 + c) ^ e * n ^ e) / n := by gcongr
      _ ≤ |C| * ((1 + c) ^ e * n ^ d) / n := by gcongr
      _ = |C| * (1 + c) ^ e * (n ^ d / n) := by ring
  have hfac : (1 : ℝ) ≤ (e.factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero e)

  have hM : I * (n + c) ^ e / (e.factorial : ℝ) ≤
      (if e = d then I else 0) * n ^ d / (d.factorial : ℝ) + |I| * (1 + c) ^ e * (n ^ d / n) := by
    split_ifs with hde
    · subst hde
      have hA := pow_add_le c n hc hn e
      have hlow : n ^ e ≤ (n + c) ^ e := pow_le_pow_left₀ hn0.le hnc e
      have hD : 0 ≤ (n + c) ^ e - n ^ e := by linarith
      have hq : 0 ≤ n ^ e / n := by positivity
      have hdiff : I * ((n + c) ^ e - n ^ e) ≤ |I| * (1 + c) ^ e * (n ^ e / n) := by
        calc I * ((n + c) ^ e - n ^ e) ≤ |I| * ((n + c) ^ e - n ^ e) :=
              mul_le_mul_of_nonneg_right (le_abs_self I) hD
          _ ≤ |I| * (((1 + c) ^ e - 1) * (n ^ e / n)) :=
              mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg I)
          _ ≤ |I| * (1 + c) ^ e * (n ^ e / n) := by
              rw [mul_assoc]
              exact mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg I)
      have hpos : (0 : ℝ) < (e.factorial : ℝ) := by linarith
      have hR : 0 ≤ |I| * (1 + c) ^ e * (n ^ e / n) := by positivity
      rw [div_le_iff₀ hpos]
      have : I * (n + c) ^ e = I * n ^ e + I * ((n + c) ^ e - n ^ e) := by ring
      rw [this, add_mul, div_mul_cancel₀ _ hpos.ne']
      nlinarith
    · have hlt : e < d := lt_of_le_of_ne hed hde
      have hd1 : n ^ e ≤ n ^ d / n := by
        rw [le_div_iff₀ hn0, ← pow_succ]
        exact pow_le_pow_right₀ hn hlt
      have hpos : (0 : ℝ) < (e.factorial : ℝ) := by linarith
      calc I * (n + c) ^ e / (e.factorial : ℝ) ≤ |I| * (n + c) ^ e / (e.factorial : ℝ) := by
            gcongr; exact le_abs_self I
        _ ≤ |I| * (n + c) ^ e := div_le_self (by positivity) hfac
        _ ≤ |I| * ((1 + c) ^ e * n ^ e) := by gcongr
        _ ≤ |I| * ((1 + c) ^ e * (n ^ d / n)) := by gcongr
        _ = 0 * n ^ d / (d.factorial : ℝ) + |I| * (1 + c) ^ e * (n ^ d / n) := by ring
  have : (|I| + |C|) * (1 + c) ^ e * (n ^ d / n) =
      |I| * (1 + c) ^ e * (n ^ d / n) + |C| * (1 + c) ^ e * (n ^ d / n) := by ring
  rw [this]
  linarith

theorem interNum_fin_congr {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} {a a' : ℕ} (h : a = a') (pp : Ideal (Poly S N)) (F : SubSystem S x Ω) :
    interNum pp (fun _ : Fin a => F) = interNum pp (fun _ : Fin a' => F) := by
  subst h; rfl

end SectionCount.Drop


open Classical in
theorem SectionCount.Drop.proof (hF : SectionCount.Drop.Filt.Statement.{u, w})
    (hT : SectionCount.Drop.Term.Statement.{u, w}) (hH : SectionCount.Drop.HilbW.Statement.{u, w})
    (hR : GenericPointSectionInput.Statement.{u, w}) : SectionCount.Drop.Statement.{u, w} := by
  intro k _ Ω _ _ N x d Nb b hZ hN hb
  obtain ⟨β, hβ, hβZ, m, pp, e, c, hpp, hcount, hloss⟩ := hF k Ω N x d Nb b hZ hb
  choose c' hc' using fun j => hT k Ω N x Nb b (pp j) (e j) (c j) hN (hpp j).1
  choose C hC using fun j => hH k Ω N x Nb (pp j) (e j) hN (hpp j).1
  obtain ⟨-, hsym, -, hcut, -⟩ := hR k Ω N x
  set g : Ideal (Poly k N) → ℤ := fun qq => interNum qq (fun _ : Fin d => Nb.toSubSystem) with hg

  have hkey : ∑ j, (if e j = d then interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) else 0) =
      interNum (primeOf (S := k) x) (Fin.cons (α := fun _ => SubSystem k x Ω) (twistSys k x (b : ℤ))
        (fun _ : Fin d => Nb.toSubSystem)) := by
    have h1 : ∀ j, (if e j = d then interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) else 0) =
        if e j = d then g (pp j) else 0 := fun j => by
      split_ifs with h
      · exact SectionCount.Drop.interNum_fin_congr h _ _
      · rfl
    have hc4 := hcut d (primeOf (S := k) x) (fun _ => Nb) (twistBundle k x (b : ℤ)) β hZ hβ hβZ
    have htb : (twistBundle k x (b : ℤ)).toSubSystem = twistSys k x (b : ℤ) := rfl
    simp only [htb] at hc4
    have hrot := hsym (d + 1) (primeOf (S := k) x)
      (Fin.cons (α := fun _ => LineBundle k x) (twistBundle k x (b : ℤ)) (fun _ => Nb))
      (finRotate (d + 1)) hZ
    have hL : (fun i => (Fin.cons (α := fun _ => LineBundle k x) (twistBundle k x (b : ℤ))
        (fun _ => Nb) i).toSubSystem) = Fin.cons (α := fun _ => SubSystem k x Ω) (twistSys k x (b : ℤ))
          (fun _ : Fin d => Nb.toSubSystem) := by
      funext i; refine Fin.cases ?_ (fun i => ?_) i
      · simp only [Fin.cons_zero]; rfl
      · simp only [Fin.cons_succ]
    have hLr : (fun i => (Fin.cons (α := fun _ => LineBundle k x) (twistBundle k x (b : ℤ))
        (fun _ => Nb) (finRotate (d + 1) i)).toSubSystem) =
          Fin.snoc (α := fun _ => SubSystem k x Ω) (fun i : Fin d => ((fun _ => Nb) i).toSubSystem)
            (twistSys k x (b : ℤ)) := by
      funext i; refine Fin.lastCases ?_ (fun i => ?_) i
      · simp; rfl
      · simp [finRotate_apply]
    rw [← hL, ← hrot, hLr, hc4, Finset.sum_congr rfl (fun j _ => h1 j)]
    have hTq : ∀ qq : Ideal (Poly k N),
        (if h : qq ∈ (primeOf (S := k) x ⊔ zeroIdeal (twistSys k x (b : ℤ)) β).minimalPrimes ∧
            IsSubvar x qq d then
          haveI : qq.IsPrime := h.1.1.1
          ((cutMult (primeOf (S := k) x ⊔ zeroIdeal (twistSys k x (b : ℤ)) β) qq).toNat : ℤ) *
            interNum qq (fun _ : Fin d => Nb.toSubSystem)
        else 0) = ∑ j, if e j = d ∧ pp j = qq then g qq else 0 := by
      intro qq
      have hq := hcount qq
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      by_cases hP : qq ∈ (primeOf (S := k) x ⊔ zeroIdeal (twistSys k x (b : ℤ)) β).minimalPrimes ∧
          IsSubvar x qq d
      · rw [dite_eq_left hP]; rw [dite_eq_left hP] at hq; rw [hq]
      · rw [dite_eq_right hP]; rw [dite_eq_right hP] at hq; rw [hq]; simp
    rw [finsum_congr hTq, finsum_eq_sum_of_support_subset (s := Finset.univ.image pp)]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases hd : e j = d
      · simp only [hd, true_and, if_true]
        rw [Finset.sum_ite_eq]
        simp
      · simp [hd]
    · intro qq hqq
      rw [Function.mem_support] at hqq
      obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hqq
      have : pp j = qq := by
        by_contra hne; simp [hne] at hj
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
      exact ⟨j, this⟩
  have hkeyR : ∑ j, (if e j = d then (interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) : ℝ) else 0) =
      (interNum (primeOf (S := k) x) (Fin.cons (α := fun _ => SubSystem k x Ω) (twistSys k x (b : ℤ))
        (fun _ : Fin d => Nb.toSubSystem)) : ℝ) := by
    rw [← hkey]; push_cast; rfl
  have hev : ∀ᶠ n : ℕ in atTop, ∀ j,
      |(Module.finrank k (SubSystem.quotH (twistMul Nb.toSubSystem (n + c' j) 0)
          ((twistMul Nb.toSubSystem (n + c' j) 0).twist (idealSys x (pp j))) 0) : ℝ) -
        (interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) : ℝ) * ((n + c' j : ℕ) : ℝ) ^ (e j) /
          ((e j).factorial : ℝ)| ≤ C j * ((n + c' j : ℕ) : ℝ) ^ (e j) / ((n + c' j : ℕ) : ℝ) := by
    rw [eventually_all]; intro j
    exact (tendsto_add_atTop_nat (c' j)).eventually (hC j)
  refine ⟨∑ j, (|(interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) : ℝ)| + |C j|) *
    (1 + (c' j : ℝ)) ^ (e j), ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1 i _
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have h1 := (Int.cast_le (R := ℝ)).mpr (hloss n i)
  push_cast at h1
  have h3 : ∀ j, (Module.finrank k (SubSystem.quotH (twistMul Nb.toSubSystem (n + c' j) 0)
      ((twistMul Nb.toSubSystem (n + c' j) 0).twist (idealSys x (pp j))) 0) : ℝ) ≤
      (if e j = d then (interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) : ℝ) else 0) *
        (n : ℝ) ^ d / (d.factorial : ℝ) +
      (|(interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) : ℝ)| + |C j|) * (1 + (c' j : ℝ)) ^ (e j) *
        ((n : ℝ) ^ d / n) := fun j => by
    have hj := hn j
    push_cast at hj
    exact SectionCount.Drop.term_le _ _ _ _ _ (e j) d (hpp j).2.1 (Nat.cast_nonneg _) hn1' hj
  calc _ ≤ _ := h1
    _ ≤ _ := Finset.sum_le_sum (fun j _ => by exact_mod_cast ((hc' j) n i).2)
    _ ≤ _ := Finset.sum_le_sum (fun j _ => h3 j)
    _ = (∑ j, (if e j = d then (interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) : ℝ) else 0)) *
          (n : ℝ) ^ d / (d.factorial : ℝ) +
        (∑ j, (|(interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) : ℝ)| + |C j|) *
          (1 + (c' j : ℝ)) ^ (e j)) * ((n : ℝ) ^ d / n) := by
      simp only [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_div]
    _ = _ := by rw [hkeyR]; ring

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PClaimSeq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Forms

variable {R : Type u} [CommRing R] {N : ℕ}

theorem homogeneousComponent_mul_form (r g : Poly R N) {d : ℕ} (hg : g.IsHomogeneous d) (e : ℕ) :
    homogeneousComponent e (r * g) ∈ Submodule.span R
      {z | ∃ (h : Poly R N) (d' : ℕ), h.IsHomogeneous d' ∧ d' + d = e ∧ z = h * g} := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show r * g = ∑ i ∈ Finset.range (r.totalDegree + 1), homogeneousComponent i r * g by
    rw [← Finset.sum_mul, sum_homogeneousComponent], map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hm : homogeneousComponent i r * g ∈ homogeneousSubmodule (Fin (N + 1)) R (i + d) :=
    (mem_homogeneousSubmodule _ _).mpr ((homogeneousComponent_isHomogeneous i r).mul hg)
  rw [homogeneousComponent_of_mem hm]
  split_ifs with h
  · exact Submodule.subset_span ⟨_, i, homogeneousComponent_isHomogeneous i r, h.symm, rfl⟩
  · exact Submodule.zero_mem _

theorem mem_span_forms_of_mem_ideal {G : Set (Poly R N)} (deg : Poly R N → ℕ)
    (hG : ∀ g ∈ G, g.IsHomogeneous (deg g)) {f : Poly R N} {e : ℕ} (hf : f ∈ Ideal.span G)
    (he : f.IsHomogeneous e) :
    f ∈ Submodule.span R {z | ∃ g ∈ G, ∃ (h : Poly R N) (d' : ℕ), h.IsHomogeneous d' ∧
      d' + deg g = e ∧ z = h * g} := by
  obtain ⟨c, t, htG, -, rfl⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hf
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← homogeneousComponent_eq_self he, map_sum]
  refine Submodule.sum_mem _ fun g hg => ?_
  have hc := homogeneousComponent_mul_form (c g) g (hG g (htG hg)) e
  rw [smul_eq_mul]
  refine Submodule.span_le.mpr ?_ hc
  rintro _ ⟨h, d', hh, hd, rfl⟩
  exact Submodule.subset_span ⟨g, htG hg, h, d', hh, hd, rfl⟩

theorem isHomogeneous_totalDegree {g : Poly R N} {d : ℕ} (hg : g.IsHomogeneous d) :
    g.IsHomogeneous g.totalDegree := by
  by_cases h0 : g = 0
  · rw [h0]; exact isHomogeneous_zero _ _ _
  · rwa [hg.totalDegree h0]

end Forms

section Chart

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem form_mul_mem_twistMod {h : Poly k N} {d : ℕ} (hh : h.IsHomogeneous d) {c : ℤ} (I : Chart x)
    {o : Ω} (ho : o ∈ twistMod k x c I) : aeval x h * o ∈ twistMod k x (c + d) I := by
  refine Submodule.span_induction (p := fun o _ => aeval x h * o ∈ twistMod k x (c + d) I) ?_ ?_ ?_ ?_ ho
  · rintro _ ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩
    exact Submodule.subset_span ⟨h * f, s, e, d + e', hs, hh.mul hf, hse, by push_cast; omega,
      by rw [map_mul, mul_div_assoc]⟩
  · rw [mul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [mul_add]; exact Submodule.add_mem _ ha hb
  · intro a z _ hz
    have := Submodule.smul_mem _ a hz
    rw [chartRing_smul_def] at this ⊢
    rwa [mul_left_comm]

theorem div_mem_chartRing {e : ℕ} (I : Chart x) {o : Ω} (ho : o ∈ twistMod k x e I) {s : Poly k N}
    (hs : s ∈ monos I.1) (hse : s.IsHomogeneous e) : o / aeval x s ∈ chartRing k x I := by
  obtain ⟨i, hi⟩ := I.2.1
  rw [twistMod_eq_span _ I hi, Submodule.mem_span_singleton] at ho
  obtain ⟨a, rfl⟩ := ho
  have hq : x i ^ (e : ℤ) / aeval x s ∈ chartRing k x I :=
    ⟨X i ^ e, s, e, hs, isHomogeneous_X_pow i e, hse, by rw [map_pow, aeval_X, zpow_natCast]⟩
  rw [chartRing_smul_def, mul_div_assoc]
  exact mul_mem a.2 hq

variable (T : StepData k x)

theorem StepData.form_mem_J {f : Poly k N} {e : ℕ} (hf : f ∈ T.J) (he : f.IsHomogeneous e) (I : Chart x)
    {δ : Ω} (hδ : δ ∈ T.D.sub I) : ∃ o ∈ twistMod k x e I, aeval x f * δ = T.si * o := by
  have hG : ∀ g ∈ {f : Poly k N | ∃ c : ℕ, f.IsHomogeneous c ∧ ∀ (I : Chart x), ∀ δ ∈ T.D.sub I,
      ∃ o ∈ twistMod k x (c : ℤ) I, aeval x f * δ = T.si * o}, g.IsHomogeneous g.totalDegree :=
    fun g ⟨c, hc, _⟩ => isHomogeneous_totalDegree hc
  have hmem := mem_span_forms_of_mem_ideal _ hG hf he
  refine Submodule.span_induction (p := fun f _ => ∃ o ∈ twistMod k x e I, aeval x f * δ = T.si * o)
    ?_ ?_ ?_ ?_ hmem
  · rintro _ ⟨g, ⟨c, hc, hg⟩, h, d', hh, hd, rfl⟩
    by_cases h0 : g = 0
    · exact ⟨0, Submodule.zero_mem _, by rw [h0, mul_zero, map_zero, zero_mul, mul_zero]⟩
    obtain ⟨o, ho, hgo⟩ := hg I δ hδ
    rw [hc.totalDegree h0] at hd
    refine ⟨aeval x h * o, ?_, by rw [map_mul, mul_assoc, hgo, mul_left_comm]⟩
    have := form_mul_mem_twistMod hh I ho
    rwa [show (c : ℤ) + d' = e by omega] at this
  · exact ⟨0, Submodule.zero_mem _, by rw [map_zero, zero_mul, mul_zero]⟩
  · rintro _ _ _ _ ⟨o, ho, h1⟩ ⟨o', ho', h2⟩
    exact ⟨o + o', Submodule.add_mem _ ho ho', by rw [map_add (f := _), add_mul, h1, h2, mul_add]⟩
  · rintro a _ _ ⟨o, ho, h1⟩
    refine ⟨a • o, (twistMod k x e I).smul_of_tower_mem a ho, ?_⟩
    rw [map_smul, smul_mul_assoc, h1, mul_smul_comm]

def StepData.Jg : FinGradedSub (S := k) (x := x) Ω where
  piece c := Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ), f ∈ T.J ∧ f.IsHomogeneous e ∧ (e : ℤ) = c ∧
    z = aeval x f}
  smul_mem d c f m hf hm := by
    refine Submodule.span_induction (p := fun m _ => aeval x f • m ∈ Submodule.span k {z | ∃ (f : Poly k N)
      (e : ℕ), f ∈ T.J ∧ f.IsHomogeneous e ∧ (e : ℤ) = c + d ∧ z = aeval x f}) ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨g, e, hg, hge, rfl, rfl⟩
      exact Submodule.subset_span ⟨f * g, d + e, T.J.mul_mem_left f hg, hf.mul hge,
        by push_cast; ring, by rw [map_mul, smul_eq_mul]⟩
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro a z _ hz; rw [smul_comm]; exact Submodule.smul_mem _ a hz
  fg := by
    classical
    set G : Set (Poly k N) := {f : Poly k N | ∃ c : ℕ, f.IsHomogeneous c ∧ ∀ (I : Chart x), ∀ δ ∈ T.D.sub I,
      ∃ o ∈ twistMod k x (c : ℤ) I, aeval x f * δ = T.si * o} with hGdef
    have hJ : T.J = Ideal.span G := rfl
    have hfg : (Submodule.span (Poly k N) G).FG := IsNoetherian.noetherian _
    obtain ⟨G₀, hG₀, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset G).mp hfg
    have hG : ∀ g ∈ (G₀ : Set (Poly k N)), g.IsHomogeneous g.totalDegree :=
      fun g hg => by obtain ⟨c, hc, _⟩ := hG₀ hg; exact isHomogeneous_totalDegree hc
    let gj : Fin G₀.card → Poly k N := fun j => (G₀.equivFin.symm j : Poly k N)
    refine ⟨G₀.card, fun j => ((gj j).totalDegree : ℤ), fun j => aeval x (gj j), fun j => ?_, fun c => ?_⟩
    · refine Submodule.subset_span ⟨gj j, _, ?_, hG _ (G₀.equivFin.symm j).2, rfl, rfl⟩
      rw [hJ]; exact Ideal.subset_span (hG₀ (G₀.equivFin.symm j).2)
    · rw [Submodule.span_le]
      rintro _ ⟨f, e, hf, he, rfl, rfl⟩
      rw [hJ, Ideal.span, hspan] at hf
      have hm := mem_span_forms_of_mem_ideal _ hG hf he
      refine Submodule.span_induction (p := fun f _ => aeval x f ∈ _) ?_ ?_ ?_ ?_ hm
      · rintro _ ⟨g, hg, h, d', hh, hd, rfl⟩
        refine Submodule.subset_span ⟨G₀.equivFin ⟨g, hg⟩, h, d', hh, ?_, ?_⟩
        · simp only [gj, Equiv.symm_apply_apply]; omega
        · simp only [gj, Equiv.symm_apply_apply, map_mul, smul_eq_mul]
      · rw [map_zero]; exact Submodule.zero_mem _
      · intro a b _ _ ha hb; rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
      · intro a z _ hz; rw [map_smul]; exact Submodule.smul_mem _ a hz

theorem StepData.Jg_tilde (I : Chart x) : (T.Jg.tildeSys 0).sub I = idealMod T.J I := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    refine Submodule.span_induction (p := fun m _ => (aeval x s)⁻¹ • m ∈ idealMod T.J I)
      ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨f, e', hf, hfe, rfl, rfl⟩
      have he : e' = e := by omega
      subst he
      exact Submodule.subset_span ⟨f, s, e', hf, hs, hfe, hse, by rw [smul_eq_mul, div_eq_inv_mul]⟩
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro c z _ hz; rw [smul_comm]; exact (idealMod T.J I).smul_of_tower_mem c hz
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
    exact Submodule.subset_span ⟨aeval x f, s, e, e, hs, hse,
      Submodule.subset_span ⟨f, e, hf, hfe, rfl, rfl⟩, sub_self _, by rw [smul_eq_mul, div_eq_inv_mul]⟩

theorem StepData.isUnit_D (I : Chart x) : IsUnit (T.D.sub I) := by
  obtain ⟨i, hi⟩ := I.2.1
  have h0 : (twistSys k x 0).sub I = 1 := by
    change twistMod k x 0 I = 1
    rw [twistMod_eq_span 0 I hi, zpow_zero, Submodule.one_eq_span]
  have hO : IsUnit ((twistSys k x (T.m - T.c₁)).sub I) :=
    IsUnit.of_mul_eq_one ((twistSys k x (-(T.m - T.c₁))).sub I) (by rw [twistSys_sub_mul, add_neg_cancel, h0])
  obtain ⟨Q', hQ'⟩ := T.M.invertible I
  rw [StepData.D, twistMul_sub]
  exact hO.mul ((IsUnit.of_mul_eq_one _ hQ').pow _)

theorem StepData.idealMod_mul_D (hZ : ZeroIdealChart.Statement.{u, w}) (I : Chart x) :
    idealMod T.J I * T.D.sub I = Submodule.span (chartRing k x I) {T.si} := by
  apply le_antisymm
  · refine Submodule.mul_le.mpr fun a ha δ hδ => ?_
    obtain ⟨g, s, e, hg, hs, hge, hse, rfl⟩ := idealMod_mem_form T.J I ha
    obtain ⟨o, ho, hgo⟩ := T.form_mem_J hg hge I hδ
    refine Submodule.mem_span_singleton.mpr ⟨⟨o / aeval x s, div_mem_chartRing I ho hs hse⟩, ?_⟩
    rw [chartRing_smul_def]
    change o / aeval x s * T.si = aeval x g / aeval x s * δ
    rw [div_mul_eq_mul_div (aeval x g), hgo]
    ring
  · obtain ⟨Q', hQ'⟩ := (T.isUnit_D I).exists_right_inv
    have hle : Submodule.span (chartRing k x I) {T.si} * Q' ≤ idealMod T.J I := by
      refine Submodule.mul_le.mpr fun a ha b hb => ?_
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
      rw [smul_mul_assoc]
      refine Submodule.smul_mem _ c (hZ k Ω N x T I b fun δ hδ => ?_)
      have h1 : b * δ ∈ T.D.sub I * Q' := by
        rw [mul_comm b]; exact Submodule.mul_mem_mul hδ hb
      rw [hQ', Submodule.mem_one] at h1
      obtain ⟨y, hy⟩ := h1
      rw [← hy]; exact y.2
    calc Submodule.span (chartRing k x I) {T.si}
        = Submodule.span (chartRing k x I) {T.si} * Q' * T.D.sub I := by
          rw [mul_assoc, mul_comm Q', hQ', mul_one]
      _ ≤ idealMod T.J I * T.D.sub I := Submodule.mul_le.mpr fun a ha b hb => Submodule.mul_mem_mul (hle ha) hb

end Chart

theorem ClaimSeq.proof (hZ : ZeroIdealChart.Statement.{u, w}) : ClaimSeq.Statement.{u, w} := by
  intro k _ Ω _ _ N x T
  refine ⟨T.Jg, fun c => rfl, fun b c I z => ?_⟩
  have hm : (twistSys k x T.m).sub I = (twistSys k x T.c₁).sub I * (twistSys k x (T.m - T.c₁)).sub I := by
    rw [twistSys_sub_mul, show T.c₁ + (T.m - T.c₁) = T.m by ring]
  have hc : (twistSys k x (c + T.c₁)).sub I = (twistSys k x c).sub I * (twistSys k x T.c₁).sub I := by
    rw [twistSys_sub_mul]
  have hJD := T.idealMod_mul_D hZ I
  have hL : T.L.sub I = (twistSys k x T.c₁).sub I * T.D.sub I := by
    rw [StepData.L, StepData.D, twistMul_sub, twistMul_sub, hm, mul_assoc]
  have key : ((T.Jg.tildeSys 0).twist ((T.L.pow (b + 1)).twist (twistSys k x c))).sub I =
      Submodule.span (chartRing k x I) {T.si} * ((T.L.pow b).twist (twistSys k x (c + T.c₁))).sub I := by
    simp only [SubSystem.twist_sub_eq_mul_of_line, SubSystem.pow_sub, T.Jg_tilde I, hc, ← hJD, hL]
    ring
  rw [key, Submodule.mem_span_singleton_mul]
  exact ⟨fun ⟨y, hy, h⟩ => ⟨y, hy, h.symm⟩, fun ⟨y, hy, h⟩ => ⟨y, hy, h.symm⟩⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPointGenerated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace PointGenerated

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem inv_mem_chartRing (hx : IsSubvar x (primeOf (S := k) x) 0) (I : Chart x) {a : Ω}
    (ha : a ∈ chartRing k x I) : a⁻¹ ∈ chartRing k x I := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  set K := (HilbertPoint.affRing k x i).toIntermediateField' (HilbertPoint.isField_affRing hx hxi)

  have h1 : ∀ b ∈ K, b ∈ chartRing k x I := by
    intro b hb
    change b ∈ HilbertPoint.affRing k x i at hb
    rw [HilbertPoint.affRing, ← Algebra.adjoin_range_eq_range_aeval] at hb
    refine Algebra.adjoin_le (S := chartRing k x I) ?_ hb
    rintro _ ⟨l, rfl⟩
    exact ⟨X l, X i, 1, X_mem_monos hi, isHomogeneous_X k l, isHomogeneous_X k i, by
      simp [HilbertPoint.aff]⟩

  have h2 : a ∈ K := by
    obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
    have hs0 := eval_ne_zero_of_mem_monos I hs
    have hxe : x i ^ e ≠ 0 := pow_ne_zero _ hxi
    have heq : aeval x f / aeval x s =
        aeval (HilbertPoint.aff x i) f / aeval (HilbertPoint.aff x i) s := by
      rw [HilbertPoint.aff_def, aeval_div_of_isHomogeneous hf, aeval_div_of_isHomogeneous hse]
      field_simp
    rw [heq]
    exact div_mem (show _ ∈ HilbertPoint.affRing k x i from ⟨f, rfl⟩)
      (show _ ∈ HilbertPoint.affRing k x i from ⟨s, rfl⟩)
  exact h1 _ (inv_mem h2)

theorem mem_sub_iff_of_subset (hx : IsSubvar x (primeOf (S := k) x) 0) (Q : LineBundle k x) {I J : Chart x}
    (h : I.1 ⊆ J.1) (y : Ω) : y ∈ Q.sub J ↔ y ∈ Q.sub I := by
  refine ⟨fun hy => ?_, Q.mono I J h y⟩
  obtain ⟨a, ha, hay⟩ := (Q.mem_iff I J h y).mp hy
  have ha0 : (a : Ω) ≠ 0 := by
    intro h0
    apply ha.ne_zero
    exact Subtype.ext h0
  have hy' : y = (⟨(a : Ω)⁻¹, inv_mem_chartRing hx I a.2⟩ : chartRing k x I) • ((a : Ω) • y) := by
    rw [chartRing_smul_def, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
  rw [hy']
  exact Submodule.smul_mem _ _ hay

theorem mem_sub_iff (hx : IsSubvar x (primeOf (S := k) x) 0) (Q : LineBundle k x) (I J : Chart x)
    (y : Ω) : y ∈ Q.sub I ↔ y ∈ Q.sub J := by
  let K : Chart x := ⟨I.1 ∪ J.1, I.2.1.mono Finset.subset_union_left, Finset.union_subset I.2.2 J.2.2⟩
  rw [← mem_sub_iff_of_subset hx Q (show I.1 ⊆ K.1 from Finset.subset_union_left),
    mem_sub_iff_of_subset hx Q (show J.1 ⊆ K.1 from Finset.subset_union_right)]

end PointGenerated

theorem PointGenerated.proof : PointGenerated.Statement.{u, w} := by
  intro k _ Ω _ _ N x Q hx I
  have hsecs : ∀ y, y ∈ Q.toSubSystem.secs ↔ y ∈ Q.sub I := by
    intro y
    rw [SubSystem.secs, Submodule.mem_iInf]
    exact ⟨fun h => h I, fun h J => (PointGenerated.mem_sub_iff hx Q I J y).mp h⟩
  apply le_antisymm
  · refine Submodule.span_le.mpr fun y hy => ?_
    exact (hsecs y).mp hy
  · intro y hy
    exact Submodule.subset_span ((hsecs y).mpr hy)

end

end GroundTheory.Heights₂.Heights.Kleiman
end
