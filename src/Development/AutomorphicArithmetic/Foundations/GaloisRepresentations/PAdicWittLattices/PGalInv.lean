module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpecHolds

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalInv
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem pull_congr {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {X Y : Scheme.{0}}
    {p : X ⟶ B} {q : Y ⟶ B} {f f' : Y ⟶ X} (e : f = f') (h : f ≫ p = q) (h' : f' ≫ p = q) (x : T.H p) :
    T.pull f h x = T.pull f' h' x := by
  subst e; rfl

theorem UpperTheory.Gal.G3.pGalInv :
    GalInv.{u} := by
  intro B R _ _ T hT Z W p r c hc G _ _ a ha hgal y
  obtain ⟨hac, -⟩ := hgal.2.2.2.2.2
  constructor
  · rintro ⟨x, rfl⟩ g
    have hcomp : (a g ≫ c) ≫ p = r := by rw [hac g, hc]
    rw [← T.pull_comp (a g) c (ha g) hc hcomp x]
    exact pull_congr T (hac g) hcomp hc x
  · intro hy
    haveI := hgal.1
    haveI := hgal.2.1
    haveI := Fintype.ofFinite G
    obtain ⟨tr, htr⟩ := hT.tr p r c hc
    have key := htr W r c hc G a ha hgal.2.2.2.2.2 y
    have hsum : ∑ g, T.pull (a g) (ha g) y = (Fintype.card G : R) • y := by
      rw [Finset.sum_congr rfl fun g _ => hy g, Finset.sum_const, Finset.card_univ,
        ← Nat.cast_smul_eq_nsmul R]
    refine ⟨(Fintype.card G : R)⁻¹ • tr y, ?_⟩
    rw [map_smul, key, hsum, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero), one_smul]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTwSplit
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem tr_left {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {i j : X.ι} {h k : G} (hk : k ∈ X.K j)
    (a : X.admitted i j h) (p q) : X.tr i j (k * h) p q = X.tr i j h a.1 a.2 := by
  rw [← X.tr_mul i j j h k a.1 a.2 (X.K_le j k hk) (X.tower_admissible_self hk).2 p q,
    X.tr_self j k _ _ hk, Category.comp_id]

private theorem tower_tr_eq_of_eq_mul_of_mem_K {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {i j : X.ι} {h k g : G}
    (hk : k ∈ X.K j) (a : X.admitted i j h) (hg : g = k * h) (p q) : X.tr i j g p q = X.tr i j h a.1 a.2 := by
  subst hg
  exact tr_left X hk a p q

private theorem tower_tr_comp_tr_eq_tr_mul {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {i j m : X.ι} {h h' : G}
    (p : h ∈ X.Δ) (q : ∀ u ∈ X.K i, h * u * h⁻¹ ∈ X.K j) (p' : h' ∈ X.Δ)
    (q' : ∀ u ∈ X.K j, h' * u * h'⁻¹ ∈ X.K m) :
    X.tr i j h p q ≫ X.tr j m h' p' q' =
      X.tr i m (h' * h) (Tower.admitted.mul (X := X) ⟨p, q⟩ ⟨p', q'⟩).1
        (Tower.admitted.mul (X := X) ⟨p, q⟩ ⟨p', q'⟩).2 :=
  X.tr_mul _ _ _ _ _ _ _ _ _ _ _

theorem UpperTheory.Gal.G3.pTwSplit :
    SplitsPts → TwSplit := by
  intro hS B G _ X m i j a b hmi hnorm J _ r c hr huniq
  have hij : ∀ u ∈ X.K i, u ∈ X.K j := fun u hu => by simpa using a.2 u hu
  have hmj : ∀ u ∈ X.K m, u ∈ X.K j := fun u hu => by simpa using b.2 u hu
  have Am : ∀ g ∈ X.K j, X.admitted m m g := fun g hg => ⟨X.K_le j g hg, fun u hu => hnorm g hg u hu⟩
  have hcomp : ∀ x, X.tr m i (r x) (c x).1 (c x).2 ≫ X.tr i j 1 a.1 a.2 = X.tr m j 1 b.1 b.2 := by
    intro x
    rw [X.tr_mul m i j (r x) 1 (c x).1 (c x).2 a.1 a.2 ((c x).mul a).1 ((c x).mul a).2]
    exact tower_tr_eq_of_eq_mul_of_mem_K X (hr x) b (by simp) _ _
  have U : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : sp Ω ⟶ X.Z m) (x1 x2 : J),
      x ≫ X.tr m i (r x1) (c x1).1 (c x1).2 = x ≫ X.tr m i (r x2) (c x2).1 (c x2).2 → x1 = x2 := by
    intro Ω _ _ x x1 x2 h12
    have p1 := X.isAdmissibleIntegralBasisChange_one hmi
    have e1 : (x ≫ X.tr m m (r x1) (Am _ (hr x1)).1 (Am _ (hr x1)).2) ≫ X.tr m i 1 p1.1 p1.2
        = (x ≫ X.tr m m (r x2) (Am _ (hr x2)).1 (Am _ (hr x2)).2) ≫ X.tr m i 1 p1.1 p1.2 := by
      rw [Category.assoc, Category.assoc, tower_tr_comp_tr_eq_tr_mul, tower_tr_comp_tr_eq_tr_mul,
        tower_tr_eq_of_eq_mul_of_mem_K X (one_mem (X.K i)) (c x1) (rfl : (1:G) * r x1 = 1 * r x1),
        tower_tr_eq_of_eq_mul_of_mem_K X (one_mem (X.K i)) (c x2) (rfl : (1:G) * r x2 = 1 * r x2)]
      exact h12
    obtain ⟨k, hki, a', b', hk⟩ := X.trans m i p1.1 p1.2
      (fun k hk u hu => hnorm k (hij k hk) u hu) Ω _ _ e1
    have hkj := hij k hki
    have e2 : x ≫ X.tr m m (r x2) (Am _ (hr x2)).1 (Am _ (hr x2)).2
        = x ≫ X.tr m m (k * r x1) (Am _ (mul_mem hkj (hr x1))).1 (Am _ (mul_mem hkj (hr x1))).2 := by
      rw [hk, Category.assoc, tower_tr_comp_tr_eq_tr_mul]
    have hinv : (r x2)⁻¹ ∈ X.K j := inv_mem (hr x2)
    have hg : (r x2)⁻¹ * (k * r x1) ∈ X.K j := mul_mem hinv (mul_mem hkj (hr x1))
    have hfix : x ≫ X.tr m m _ (Am _ hg).1 (Am _ hg).2 = x := by
      rw [← X.tr_mul m m m (k * r x1) (r x2)⁻¹ (Am _ (mul_mem hkj (hr x1))).1 (Am _ (mul_mem hkj (hr x1))).2
        (Am _ hinv).1 (Am _ hinv).2, ← Category.assoc, ← e2, Category.assoc,
        X.tr_mul m m m (r x2) (r x2)⁻¹ (Am _ (hr x2)).1 (Am _ (hr x2)).2 (Am _ hinv).1 (Am _ hinv).2
          (Am _ (mul_mem hinv (hr x2))).1 (Am _ (mul_mem hinv (hr x2))).2,
        X.tr_self m _ _ _ (by simp), Category.comp_id]
    have hgm := X.free m j (fun u hu => hmj u hu) _ hg (Am _ hg).1 (Am _ hg).2 Ω x hfix
    have hk0 : k * r x1 ∈ X.K j := mul_mem hkj (hr x1)
    apply (huniq _ hk0).unique
    · simpa using hki
    · have := (c x2).2 _ hgm
      convert this using 1
      group
  have hpts : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : sp Ω ⟶ X.Z m) (y : sp Ω ⟶ X.Z i),
      y ≫ X.tr i j 1 a.1 a.2 = x ≫ X.tr m j 1 b.1 b.2 → ∃! x0, x ≫ X.tr m i (r x0) (c x0).1 (c x0).2 = y := by
    intro Ω _ _ x y hxy
    have p1 := X.isAdmissibleIntegralBasisChange_one hmi
    haveI := X.fin m i p1.1 p1.2
    obtain ⟨v, hv⟩ := (X.onto m i p1.1 p1.2).surj (UpperTheory.Gal.TranscendenceTraces.pt (X := X.Z i) (Ω := Ω) y)
    obtain ⟨z, hz, -⟩ := UpperTheory.Gal.TranscendenceTraces.ptLift_holds (X.tr m i 1 p1.1 p1.2) Ω y v hv
    have hzj : x ≫ X.tr m j 1 b.1 b.2 = z ≫ X.tr m j 1 b.1 b.2 := by
      rw [← hxy, ← hz, Category.assoc, tower_tr_comp_tr_eq_tr_mul,
        tower_tr_eq_of_eq_mul_of_mem_K X (one_mem (X.K j)) b (rfl : (1:G) * 1 = 1 * 1)]
    obtain ⟨k, hkj, a', b', hk⟩ := X.trans m j b.1 b.2 hnorm Ω x z hzj
    obtain ⟨x0, hx0, -⟩ := huniq k hkj
    have ex : x ≫ X.tr m i (r x0) (c x0).1 (c x0).2 = y := by
      rw [← hz, hk, Category.assoc, tower_tr_comp_tr_eq_tr_mul,
        tower_tr_eq_of_eq_mul_of_mem_K X hx0 (c x0) (show (1:G) * k = k * (r x0)⁻¹ * r x0 by group)]
    exact ⟨x0, ex, fun x2 h2 => U Ω x x2 x0 (h2.trans ex.symm)⟩
  haveI := X.fin i j a.1 a.2
  haveI := X.etale i j a.1 a.2
  exact hS _ _ J _ hcomp hpts
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopEx
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem hop_summand {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R]
    (T : Th.{u} B R) {m j : X.ι} {f : G → R} (hf : X.IsFn j f) (had : ∀ g, f g ≠ 0 → X.admitted m j g⁻¹) (g : G)
    (x : T.H (X.q j)) :
    f (g : G ⧸ X.K j).out • X.pl T m j (g : G ⧸ X.K j).out⁻¹ x = f g • X.pl T m j g⁻¹ x := by
  obtain ⟨⟨k, hk⟩, hkeq⟩ := QuotientGroup.mk_out_eq_mul (X.K j) g
  rw [hkeq, (hf.1 k hk g).2]
  by_cases h0 : f g = 0
  · simp [h0]
  · rw [mul_inv_rev, X.pl_left T (had g h0) (inv_mem hk)]

theorem UpperTheory.Gal.G3.pHopEx :
    PlInv.{u} → HopDeep.{u} → HopEx.{u} := by
  intro hPl hD B G _ X R _ _ T hT j f hf
  obtain ⟨⟨m0, hm0j, had0⟩, hiso⟩ := hD X T hT j f hf
  have huniq : ∀ A A' : Module.End R (T.H (X.q j)), X.IsHop T j f A → X.IsHop T j f A' → A = A' := by
    intro A A' hA hA'
    ext x
    apply (hPl X T hT m0 j hm0j).1
    rw [hA m0 hm0j had0 x, hA' m0 hm0j had0 x]
  obtain ⟨m, hmj, hnorm, hS⟩ := X.deep j {(m0, 1)}
  have hmm0 : X.K m ≤ X.K m0 := fun u hu => by simpa using hS (m0, 1) (by simp) u hu
  have had : ∀ g, f g ≠ 0 → X.admitted m j g⁻¹ := fun g hg => by
    simpa using (X.isAdmissibleIntegralBasisChange_one hmm0).mul (had0 g hg)
  set S := hf.2.2.toFinset with hSdef
  have hsub : ∀ (w : G ⧸ X.K j → T.H (X.q m)),
      Function.support (fun z => f z.out • w z) ⊆ (S : Set (G ⧸ X.K j)) := by
    intro w z hz
    simp only [S, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h0
    exact hz (by simp [h0])
  let Y : T.H (X.q j) →ₗ[R] T.H (X.q m) := ∑ z ∈ S, f z.out • X.pl T m j z.out⁻¹
  have hYS : ∀ x, Y x = ∑ z ∈ S, f z.out • X.pl T m j z.out⁻¹ x := by
    intro x
    simp [Y, LinearMap.sum_apply]
  have hY : ∀ x, Y x = ∑ᶠ z : G ⧸ X.K j, f z.out • X.pl T m j z.out⁻¹ x := by
    intro x
    rw [finsum_eq_sum_of_support_subset _ (hsub _), hYS]
  have hinv : ∀ x, ∀ k ∈ X.K j, X.pl T m m k (Y x) = Y x := by
    intro x k hk
    have hadk : X.admitted m m k := ⟨X.K_le j k hk, fun u hu => hnorm k hk u hu⟩
    have key : ∀ z : G ⧸ X.K j, X.pl T m m k (f z.out • X.pl T m j z.out⁻¹ x) =
        f (k⁻¹ • z).out • X.pl T m j (k⁻¹ • z).out⁻¹ x := by
      intro z
      have hz : k⁻¹ • z = ((k⁻¹ * z.out : G) : G ⧸ X.K j) := by
        conv_lhs => rw [← QuotientGroup.out_eq' z]
        rfl
      rw [hz, hop_summand X T hf had, (hf.1 k⁻¹ (inv_mem hk) z.out).1, map_smul]
      by_cases h0 : f z.out = 0
      · simp [h0]
      · rw [X.pl_pl T hadk (had _ h0), mul_inv_rev, inv_inv]
    have hsub2 : Function.support (fun z : G ⧸ X.K j => X.pl T m m k (f z.out • X.pl T m j z.out⁻¹ x))
        ⊆ (S : Set (G ⧸ X.K j)) := by
      intro z hz
      simp only [S, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
      intro h0
      exact hz (by simp [h0])
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hYS, map_sum, ← finsum_eq_sum_of_support_subset _ hsub2, ← hYS, hY]
    simp_rw [key]
    exact finsum_comp_equiv (MulAction.toPerm k⁻¹ : Equiv.Perm (G ⧸ X.K j))
      (f := fun z : G ⧸ X.K j => f z.out • X.pl T m j z.out⁻¹ x)
  have hinj := (hPl X T hT m j hmj).1
  have hrange : ∀ x, Y x ∈ LinearMap.range (X.pl T m j 1) := by
    intro x
    obtain ⟨w, hw⟩ := (hPl X T hT m j hmj).2 hnorm (Y x) (hinv x)
    exact ⟨w, hw⟩
  let A : Module.End R (T.H (X.q j)) :=
    (LinearEquiv.ofInjective (X.pl T m j 1) hinj).symm.toLinearMap ∘ₗ Y.codRestrict _ hrange
  have hA : ∀ x, X.pl T m j 1 (A x) = Y x := by
    intro x
    have h := congrArg Subtype.val
      ((LinearEquiv.ofInjective (X.pl T m j 1) hinj).apply_symm_apply ⟨Y x, hrange x⟩)
    rw [LinearEquiv.ofInjective_apply] at h
    exact h
  have hex : ∃ A, X.IsHop T j f A := ⟨A, hiso A m hmj had (fun x => by rw [hA, hY])⟩
  have hh : X.IsHop T j f (X.hecke T j f) := by
    unfold Tower.hecke
    rw [dite_eq_left hex]
    exact hex.choose_spec
  exact ⟨hh, fun A' hA' => huniq _ _ hA' hh⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PLiesGen
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem fEt_comp_iso {Y X X' : Scheme.{0}} (f : Y ⟶ X) (i : X ⟶ X') [IsIso i] (d : ℕ) (hf : FEt f d) :
    FEt (f ≫ i) d := by
  obtain ⟨h1, h2, h3⟩ := hf
  haveI := h1
  haveI := h2
  refine ⟨inferInstance, inferInstance, fun K _ _ x => ?_⟩
  rw [← h3 K (x ≫ inv i)]
  apply Nat.card_congr
  refine Equiv.subtypeEquivRight fun y => ?_
  constructor
  · intro h
    rw [← h]
    simp
  · intro h
    rw [← Category.assoc, h]
    simp

theorem UpperTheory.Gal.G3.pLiesGen :
    LiesGen := by
  intro k L O _ _ _ _ H θ C g D s t hst m hL
  obtain ⟨-, κ0, h0, h1, hF⟩ := hL
  have hq : κ0 ≫ s ≫ C.p = (H.s g ≫ H.q) ≫ gen O k := by
    rw [← Category.assoc, ← h0, Category.assoc, C.ov, Category.assoc]
  let κ : H.Y g ⟶ pullback (s ≫ C.p) (gen O k) := pullback.lift κ0 (H.s g ≫ H.q) hq
  have hA : H.s g ≫ piK C = κ ≫ bcMap (gen O k) s rfl := by
    apply pullback.hom_ext
    · simp only [piK, bcMap, κ, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      exact h0
    · simp only [piK, bcMap, κ, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
  refine ⟨κ, hA, ?_, ?_⟩
  · apply pullback.hom_ext
    · simp only [piK, bcMap, κ, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      exact h1
    · simp only [piK, bcMap, κ, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      exact (H.comm g).symm
  · have w1 : pullback.snd C.π s ≫ s ≫ C.p = (pullback.fst C.π s ≫ H.q) ≫ gen O k := by
      rw [← Category.assoc, ← pullback.condition, Category.assoc, C.ov, Category.assoc]
    let i0 : pullback C.π s ⟶ pullback (s ≫ C.p) (gen O k) :=
      pullback.lift (pullback.snd C.π s) (pullback.fst C.π s ≫ H.q) w1
    have w2 : pullback.fst C.π s ≫ piK C = i0 ≫ bcMap (gen O k) s rfl := by
      apply pullback.hom_ext
      · simp only [piK, bcMap, i0, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
        exact pullback.condition
      · simp only [piK, bcMap, i0, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    let i : pullback C.π s ⟶ pullback (piK C) (bcMap (gen O k) s rfl) :=
      pullback.lift (pullback.fst C.π s) i0 w2
    have c0 := pullback.condition (f := piK C) (g := bcMap (gen O k) s rfl)
    have c1 := congrArg (· ≫ pullback.fst C.p (gen O k)) c0
    have c2 := congrArg (· ≫ pullback.snd C.p (gen O k)) c0
    simp only [piK, bcMap, Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc] at c1 c2
    have w3 : pullback.fst (piK C) (bcMap (gen O k) s rfl) ≫ C.π
        = (pullback.snd (piK C) (bcMap (gen O k) s rfl) ≫ pullback.fst (s ≫ C.p) (gen O k)) ≫ s := by
      rw [Category.assoc]
      exact c1
    let j : pullback (piK C) (bcMap (gen O k) s rfl) ⟶ pullback C.π s :=
      pullback.lift _ _ w3
    haveI : IsIso i := by
      refine ⟨⟨j, ?_, ?_⟩⟩
      · apply pullback.hom_ext
        · simp only [i, j, Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_fst_assoc]
        · simp only [i, j, i0, Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd,
            pullback.lift_fst_assoc, pullback.lift_snd_assoc]
      · apply pullback.hom_ext
        · simp only [i, j, Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_fst_assoc]
        · apply pullback.hom_ext
          · simp only [i, j, i0, Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd,
              pullback.lift_fst_assoc, pullback.lift_snd_assoc]
          · simp only [i, j, i0, Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd,
              pullback.lift_fst_assoc, pullback.lift_snd_assoc]
            exact c2
    have key : pullback.lift (H.s g) κ hA = pullback.lift (H.s g) κ0 h0 ≫ i := by
      apply pullback.hom_ext
      · simp only [i, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      · apply pullback.hom_ext
        · simp only [i, i0, κ, Category.assoc, pullback.lift_fst, pullback.lift_snd,
            pullback.lift_fst_assoc, pullback.lift_snd_assoc]
        · simp only [i, i0, κ, Category.assoc, pullback.lift_fst, pullback.lift_snd,
            pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    rw [key]
    exact fEt_comp_iso _ i m hF
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHodgeInj
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPullbackFromSpecAppPreimage
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HodgeCoh

set_option autoImplicit false

namespace GlobalTheory.HodgeCoh
open GlobalTheory.CechDR

theorem isPullback_fromSpec_app_preimage {X Y : Scheme.{0}} (π : X ⟶ Y) {W : Y.Opens}
    (hW : IsAffineOpen W) (hV : IsAffineOpen (π ⁻¹ᵁ W)) :
    IsPullback hV.fromSpec (Spec.map (π.app W)) π hW.fromSpec := by
  refine (IsOpenImmersion.isPullback (Spec.map (π.app W)) hV.fromSpec hW.fromSpec π ?_ ?_).flip
  · rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec π hW hV le_rfl]
  · rw [IsAffineOpen.opensRange_fromSpec, IsAffineOpen.opensRange_fromSpec]

end GlobalTheory.HodgeCoh
end

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
open Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR KaehlerDifferential
universe u v

set_option autoImplicit false

private theorem natCast_isUnit (k : Type) [Field k] [CharZero k] {A : Type} [CommRing A] [Algebra k A]
    {n : ℕ} (hn : n ≠ 0) : IsUnit (n : A) := by
  have h : IsUnit (n : k) := isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hn)
  simpa using h.map (algebraMap k A)

private theorem unit_of_trace_one (k : Type) [Field k] [CharZero k] {A A' : Type} [CommRing A]
    [CommRing A'] [Algebra k A] [Algebra A A'] [Module.Finite A A'] [Module.Projective A A']
    (onto : Function.Surjective (PrimeSpectrum.comap (algebraMap A A'))) :
    IsUnit (algTrace A A' 1) := by
  by_contra hnot
  obtain ⟨M, hM, hmem⟩ := exists_max_ideal_of_mem_nonunits hnot
  obtain ⟨Q, hQ⟩ := onto ⟨M, hM.isPrime⟩
  have hcomap : Q.asIdeal.comap (algebraMap A A') = M := congrArg PrimeSpectrum.asIdeal hQ
  let Am := Localization.AtPrime M
  let L := LocalizedModule M.primeCompl A'
  have base := IsLocalizedModule.isBaseChange M.primeCompl Am
    (LocalizedModule.mkLinearMap M.primeCompl A')
  haveI : Module.Free Am L := Module.free_of_flat_of_isLocalRing
  haveI : Nontrivial L := by
    refine ⟨⟨LocalizedModule.mkLinearMap M.primeCompl _ 1, 0, fun h ↦ ?_⟩⟩
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff M.primeCompl
      (LocalizedModule.mkLinearMap M.primeCompl A')).1 h
    have ht0 : algebraMap A A' t = 0 := by
      rw [Algebra.algebraMap_eq_smul_one]; exact ht
    have hin : (t : A) ∈ Q.asIdeal.comap (algebraMap A A') := by
      rw [Ideal.mem_comap, ht0]; exact Q.asIdeal.zero_mem
    exact t.2 (hcomap.le hin)
  have hrank : algebraMap A Am (algTrace A A' 1) = (Module.finrank Am L : Am) := by
    rw [algTrace_apply, ← projTrace_of_isBaseChange base (LinearMap.mul _ _ 1) LinearMap.id
      (fun x ↦ by simp), projTrace_eq_trace, LinearMap.trace_id]
  have hne : Module.finrank Am L ≠ 0 := fun h ↦
    not_subsingleton L ((Module.finrank_eq_zero_iff_of_free Am L).1 h)
  have hunit : IsUnit (algebraMap A Am (algTrace A A' 1)) := by
    rw [hrank, ← map_natCast (algebraMap A Am)]
    exact (natCast_isUnit k hne).map _
  exact (IsLocalization.AtPrime.isUnit_to_map_iff Am M _).1 hunit hmem

section
variable {k : Type} [Field k] [CharZero k] {X X' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k}
  {f : X' ⟶ X} [IsFinite f] [Etale f]

private theorem unit_secTrace [Surjective f] {U : X.Opens} (hU : IsAffineOpen U) :
    IsUnit (secTrace (f := f) s s' hU 1) := by
  letI := secAlg s s' f U
  haveI := sec_finite (s := s) (s' := s') (f := f) hU
  haveI := sec_etale (s := s) (s' := s') (f := f) hU
  haveI := projective_of_etale (Sec s U) (Sec s' (f ⁻¹ᵁ U))
  have hsq : Surjective (Spec.map (f.app U)) :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (isPullback_fromSpec_app_preimage f hU (hU.preimage f)) inferInstance
  exact unit_of_trace_one k (A := Sec s U) (A' := Sec s' (f ⁻¹ᵁ U)) hsq.surj

omit [CharZero k] in
private theorem pull_trace_app (hf : f ≫ s = s') (j : ℕ) {U : X.Opens} (hU : IsAffineOpen U)
    (w : Γ(Omega s j, U)) :
    (omegaPull hf j ≫ omegaTrace hf j).app U w = secTrace (f := f) s s' hU 1 • w := by
  obtain ⟨x, rfl⟩ := toOm_surjective (s := s) (j := j) hU w
  rw [Scheme.Modules.Hom.comp_app]
  change (omegaTrace hf j).app U ((omegaPull hf j).val.app (op U) ((toOmega s j).app (op U) x)) = _
  rw [omegaPull_toOmega hf j U x, ← one_smul (Sec s' (f ⁻¹ᵁ U)) (formPull hf U j x)]
  erw [omegaTrace_toOm_smul_formPull hf j hU]
  exact (toOm s j U).map_smul _ x

private theorem pull_trace_leftInv [Surjective f] (hf : f ≫ s = s') (j : ℕ) :
    ∃ ψ : Omega s j ⟶ Omega s j, (omegaPull hf j ≫ omegaTrace hf j) ≫ ψ = 𝟙 _ := by
  let t : ∀ U : X.affineOpens, (Sec s U.1)ˣ := fun U ↦
    (unit_secTrace (s := s) (s' := s') (f := f) U.2).unit
  have ht : ∀ U : X.affineOpens, (t U : Sec s U.1) = secTrace (f := f) s s' U.2 1 := fun _ ↦ rfl
  have hinv : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1),
      Sec.res s h ((t U)⁻¹ : (Sec s U.1)ˣ) = ((t V)⁻¹ : (Sec s V.1)ˣ) := fun U V h ↦ by
    have e : Sec.res s h (t U) = t V := by
      rw [ht, ht, secTrace_res U.2 V.2 h, map_one]
    refine Units.eq_inv_of_mul_eq_one_right ?_
    rw [← e, ← map_mul, Units.inv_mul, map_one]
  let mulInv : ∀ U : X.affineOpens, Γ(Omega s j, U.1) →ₗ[Γ(X, U.1)] Γ(Omega s j, U.1) := fun U ↦
    LinearMap.lsmul Γ(X, U.1) Γ(Omega s j, U.1) (show Sec s U.1 from ((t U)⁻¹ : (Sec s U.1)ˣ))
  have hmul : ∀ (U : X.affineOpens) (w : Γ(Omega s j, U.1)),
      mulInv U w = (((t U)⁻¹ : (Sec s U.1)ˣ) : Sec s U.1) • w := fun _ _ ↦ rfl
  have hres : ∀ (U V : X.Opens) (h : V ≤ U) (g : Sec s U) (n : Γ(Omega s j, U)),
      (Omega s j).presheaf.map (homOfLE h).op (g • n) =
        Sec.res s h g • (Omega s j).presheaf.map (homOfLE h).op n :=
    fun _ _ _ _ _ ↦ Scheme.Modules.map_smul _ _ _ _
  refine ⟨homOfAffine mulInv fun U V h w ↦ by rw [hmul, hmul, hres, hinv],
    hom_ext_affine fun U hU w ↦ ?_⟩
  refine (homOfAffine_app mulInv _ ⟨U, hU⟩ ((omegaPull hf j ≫ omegaTrace hf j).app U w)).trans ?_
  rw [hmul, pull_trace_app hf j hU, ← ht ⟨U, hU⟩, smul_smul, Units.inv_mul, one_smul]
  rfl
end

theorem UpperTheory.Gal.G3.pHodgeInj :
    HodgeInj := by
  intro k _ _ a b Z W p r c _ _ _ hc x y hxy
  letI := algΓ p
  obtain ⟨ψ, hψ⟩ := pull_trace_leftInv hc a
  have back : ∀ z : hodgeH p a b,
      cohOn.map k ψ ⊤ b (hodgeTrace hc a b (hodgePull hc a b z)) = z := fun z ↦ by
    refine (congrArg (cohOn.map k ψ ⊤ b) (hodgeTrace_hodgePull hc a b z)).trans ?_
    refine (cohOn.map_map k _ ψ z).trans ?_
    rw [hψ]
    exact LinearMap.congr_fun (cohOn.map_id k _ ⊤ b) z
  rw [← back x, ← back y, hxy]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopMul
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

namespace UpperTheory.Gal.G3

private theorem sum_translate {G R M : Type*} [Group G] [Field R] [AddCommGroup M] [Module R M]
    (K : Subgroup G) (f' : G → R) (Φ : G → M) (hf' : ∀ k ∈ K, ∀ g, f' (g * k) = f' g)
    (hΦ : ∀ k ∈ K, ∀ g, Φ (g * k) = Φ g) (g : G) :
    ∑ᶠ z : G ⧸ K, f' z.out • Φ (g * z.out) = ∑ᶠ w : G ⧸ K, f' (g⁻¹ * w.out) • Φ w.out := by
  refine Eq.trans (finsum_congr fun z => ?_)
    (finsum_comp_equiv (MulAction.toPerm g : Equiv.Perm (G ⧸ K))
      (f := fun w : G ⧸ K => f' (g⁻¹ * w.out) • Φ w.out))
  have e : (MulAction.toPerm g : Equiv.Perm (G ⧸ K)) z = ((g * z.out : G) : G ⧸ K) := by
    rw [MulAction.toPerm_apply]
    conv_lhs => rw [← QuotientGroup.out_eq' z]
    rfl
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (g * z.out)
  simp only [e, hk]
  rw [show g⁻¹ * (g * z.out * (k : G)) = z.out * k by group, hf' _ k.2, hΦ _ k.2]

private theorem sum_conv {G R : Type} {M : Type*} [Group G] [Field R] [AddCommGroup M] [Module R M]
    (K : Subgroup G) (f f' : G → R) (Φ : G → M) (hf' : ∀ k ∈ K, ∀ g, f' (g * k) = f' g)
    (hΦ : ∀ k ∈ K, ∀ g, Φ (g * k) = Φ g) (sf : {y : G ⧸ K | f y.out ≠ 0}.Finite)
    (sf' : {y : G ⧸ K | f' y.out ≠ 0}.Finite) :
    ∑ᶠ y : G ⧸ K, f y.out • ∑ᶠ z : G ⧸ K, f' z.out • Φ (y.out * z.out) =
      ∑ᶠ w : G ⧸ K, conv K f f' w.out • Φ w.out := by
  classical
  let Tw : Finset (G ⧸ K) := sf.toFinset.biUnion fun y => sf'.toFinset.image fun z => y.out • z
  have hT : ∀ y ∈ sf.toFinset, ∀ w : G ⧸ K, f' (y.out⁻¹ * w.out) ≠ 0 → w ∈ Tw := by
    intro y hy w hw
    refine Finset.mem_biUnion.2 ⟨y, hy, Finset.mem_image.2 ⟨((y.out⁻¹ * w.out : G) : G ⧸ K), ?_, ?_⟩⟩
    · obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (y.out⁻¹ * w.out)
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      rw [hk, hf' _ k.2]
      exact hw
    · show ((y.out * (y.out⁻¹ * w.out) : G) : G ⧸ K) = w
      rw [mul_inv_cancel_left, QuotientGroup.out_eq']
  have hin : ∀ y ∈ sf.toFinset, ∑ᶠ w : G ⧸ K, f' (y.out⁻¹ * w.out) • Φ w.out =
      ∑ w ∈ Tw, f' (y.out⁻¹ * w.out) • Φ w.out := by
    intro y hy
    refine finsum_eq_sum_of_support_subset _ fun w hw => ?_
    refine hT y hy w fun h => hw ?_
    simp [h]
  have hc : ∀ w : G ⧸ K, conv K f f' w.out = ∑ y ∈ sf.toFinset, f y.out * f' (y.out⁻¹ * w.out) := by
    intro w
    refine finsum_eq_sum_of_support_subset _ fun y hy => ?_
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h
    exact hy (by simp [h])
  have hl : ∑ᶠ y : G ⧸ K, f y.out • ∑ᶠ z : G ⧸ K, f' z.out • Φ (y.out * z.out) =
      ∑ y ∈ sf.toFinset, f y.out • ∑ᶠ w : G ⧸ K, f' (y.out⁻¹ * w.out) • Φ w.out := by
    refine (finsum_congr fun y => by rw [sum_translate K f' Φ hf' hΦ y.out]).trans ?_
    refine finsum_eq_sum_of_support_subset _ fun y hy => ?_
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h
    exact hy (by simp [h])
  have hs : Function.support (fun w : G ⧸ K => conv K f f' w.out • Φ w.out) ⊆ (Tw : Set (G ⧸ K)) := by
    intro w hw
    have h0 : conv K f f' w.out ≠ 0 := fun h => hw (by simp [h])
    rw [hc w] at h0
    obtain ⟨y, hy, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
    exact Finset.mem_coe.2 (hT y hy w (right_ne_zero_of_mul hne))
  rw [hl, finsum_eq_sum_of_support_subset _ hs]
  calc ∑ y ∈ sf.toFinset, f y.out • ∑ᶠ w : G ⧸ K, f' (y.out⁻¹ * w.out) • Φ w.out
      = ∑ y ∈ sf.toFinset, f y.out • ∑ w ∈ Tw, f' (y.out⁻¹ * w.out) • Φ w.out :=
        Finset.sum_congr rfl fun y hy => by rw [hin y hy]
    _ = ∑ w ∈ Tw, (∑ y ∈ sf.toFinset, f y.out * f' (y.out⁻¹ * w.out)) • Φ w.out := by
        simp only [Finset.smul_sum, Finset.sum_smul, mul_smul]
        exact Finset.sum_comm
    _ = ∑ w ∈ Tw, conv K f f' w.out • Φ w.out :=
        Finset.sum_congr rfl fun w _ => by rw [hc w]

private theorem pl_left_all {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R]
    (T : Th.{u} B R) {i j : X.ι} {k : G} (hk : k ∈ X.K j) (h : G) (x : T.H (X.q j)) :
    X.pl T i j (k * h) x = X.pl T i j h x := by
  by_cases a : X.admitted i j h
  · exact X.pl_left T a hk x
  · have b : ¬ X.admitted i j (k * h) := fun b => a (by
      simpa using b.mul (X.tower_admissible_self ((X.K j).inv_mem hk)))
    simp [Tower.pl, a, b]

end UpperTheory.Gal.G3

theorem UpperTheory.Gal.G3.pHopMul :
    FnRing → HopDeep.{u} → HopEx.{u} → HopMul.{u} := by
  intro hR hD hE B G _ X R _ _ T hT j f f' hf hf'
  have hF : X.IsFn j (conv (X.K j) f f') := ((hR X R j).2.2.1 f f' hf hf').2
  have hA := (hE X T hT j f hf).1
  have hA' := (hE X T hT j f' hf').1
  refine ((hE X T hT j _ hF).2 _ ?_).symm
  obtain ⟨m1, l1, a1⟩ := (hD X T hT j f hf).1
  obtain ⟨m2, l2, a2⟩ := (hD X T hT j f' hf').1
  obtain ⟨m3, l3, a3⟩ := (hD X T hT j _ hF).1
  classical
  let S : Finset (X.ι × G) :=
    {(m1, 1), (m2, 1), (m3, 1)} ∪ hf.2.2.toFinset.image fun y => (m2, y.out⁻¹)
  obtain ⟨m, lm, -, hm⟩ := X.deep j S
  have le1 : X.K m ≤ X.K m1 := fun u hu => by simpa using hm (m1, 1) (by simp [S]) u hu
  have le3 : X.K m ≤ X.K m3 := fun u hu => by simpa using hm (m3, 1) (by simp [S]) u hu
  have ad1 : ∀ g, f g ≠ 0 → X.admitted m j g⁻¹ := fun g hg => by
    simpa using (X.isAdmissibleIntegralBasisChange_one le1).mul (a1 g hg)
  have ad3 : ∀ g, conv (X.K j) f f' g ≠ 0 → X.admitted m j g⁻¹ := fun g hg => by
    simpa using (X.isAdmissibleIntegralBasisChange_one le3).mul (a3 g hg)
  refine (hD X T hT j _ hF).2 _ m lm ad3 fun x => ?_
  have step : ∀ y : G ⧸ X.K j, f y.out • X.pl T m j y.out⁻¹ (X.hecke T j f' x) =
      f y.out • ∑ᶠ z : G ⧸ X.K j, f' z.out • X.pl T m j (y.out * z.out)⁻¹ x := by
    intro y
    by_cases h : f y.out = 0
    · simp [h]
    have ad : X.admitted m m2 y.out⁻¹ := ⟨hf.2.1 _ h, fun u hu => hm (m2, y.out⁻¹)
      (Finset.mem_union_right _ (Finset.mem_image.2 ⟨y, by simpa using h, rfl⟩)) u hu⟩
    have e : X.pl T m j y.out⁻¹ (X.hecke T j f' x) =
        X.pl T m m2 y.out⁻¹ (X.pl T m2 j 1 (X.hecke T j f' x)) := by
      rw [X.pl_pl T ad (X.isAdmissibleIntegralBasisChange_one l2), one_mul]
    have fin : (Function.support fun z : G ⧸ X.K j => f' z.out • X.pl T m2 j z.out⁻¹ x).Finite :=
      hf'.2.2.subset fun z hz h0 => hz (by simp [h0])
    rw [e, hA' m2 l2 a2 x, map_finsum _ fin]
    congr 1
    refine finsum_congr fun z => ?_
    by_cases h' : f' z.out = 0
    · simp [h']
    rw [map_smul, X.pl_pl T ad (a2 _ h'), mul_inv_rev]
  rw [Module.End.mul_apply, hA m lm ad1, finsum_congr step]
  exact sum_conv (X.K j) f f' (fun g => X.pl T m j g⁻¹ x) (fun k hk g => (hf'.1 k hk g).2)
    (fun k hk g => by
      simp only [mul_inv_rev]
      exact pl_left_all X T ((X.K j).inv_mem hk) _ x) hf.2.2 hf'.2.2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PAlgSplit
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsEvaluation
theorem UpperTheory.Reformulated.B.ExistsEvaluation.exists_eval :
    ∀ {C Ω J : Type}
    [inst : CommRing C] [inst_1 : Field Ω] [Fintype J] (f : (J → C) →+* Ω),
    ∃ (j : J),
      ∀ (v : J → C), (f : (J → C) → Ω) v = (f : (J → C) → Ω) ((Algebra.algebraMap C (J → C) : C → J → C) (v j)) := by
  intro C Ω J _ _ _ f
  classical
  have hsum : ∑ j : J, f (Pi.single j 1) = 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum]
    have h : (∑ j : J, (Pi.single j (1 : C) : J → C)) = 1 := by
      simpa using Finset.univ_sum_single (1 : J → C)
    rw [h, map_one]
  obtain ⟨j, hj⟩ : ∃ j : J, f (Pi.single j 1) ≠ 0 := by
    by_contra hne
    push_neg at hne
    rw [Finset.sum_eq_zero (fun j _ => hne j)] at hsum
    exact zero_ne_one hsum
  have hidem : f (Pi.single j 1) * f (Pi.single j 1) = f (Pi.single j 1) := by
    rw [← map_mul]
    congr 1
    funext i
    by_cases hi : i = j
    · subst hi; simp
    · simp [Pi.single_eq_of_ne hi]
  have hone : f (Pi.single j 1) = 1 := by
    exact mul_left_cancel₀ hj (by rw [hidem, mul_one])
  refine ⟨j, fun v => ?_⟩
  have hmul : v * Pi.single j 1 =
      (Algebra.algebraMap C (J → C) : C → J → C) (v j) * Pi.single j 1 := by
    funext i
    by_cases hi : i = j
    · subst hi; simp [Algebra.algebraMap_eq_smul_one]
    · simp [Pi.single_eq_of_ne hi]
  have h2 := congrArg f hmul
  simpa [map_mul, hone] using h2
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TensorHomExt
theorem UpperTheory.Reformulated.B.Qk54.tensor_hom_ext :
    ∀ {A A' C Ω : Type}
    [inst : CommRing A] [inst_1 : CommRing A'] [inst_2 : CommRing C] [inst_3 : Algebra A A'] [inst_4 : Algebra A C]
    [inst_5 : CommRing Ω] {u v : TensorProduct A C A' →+* Ω},
    (∀ (c : C), (u : TensorProduct A C A' → Ω) (c ⊗ₜ[A] (1 : A')) = (v : TensorProduct A C A' → Ω) (c ⊗ₜ[A] (1 : A'))) →
      (∀ (b : A'), (u : TensorProduct A C A' → Ω) ((1 : C) ⊗ₜ[A] b) = (v : TensorProduct A C A' → Ω) ((1 : C) ⊗ₜ[A] b)) →
        u = v := by
  intro A A' C Ω _ _ _ _ _ _ u v h₁ h₂
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul c b =>
    have e : c ⊗ₜ[A] b = (c ⊗ₜ[A] (1 : A')) * ((1 : C) ⊗ₜ[A] b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, map_mul, map_mul, h₁, h₂]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
end

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

namespace UpperTheory.Gal.G3.AlgebraSplitting

private noncomputable def sec {A A' C J : Type} [CommRing A] [CommRing A'] [CommRing C] [Algebra A A'] [Algebra A C]
    (τ : J → (A' →ₐ[A] C)) : C ⊗[A] A' →ₐ[C] (J → C) :=
  Pi.algHom C (fun _ => C) fun j =>
    Algebra.TensorProduct.lift (AlgHom.id C C) (τ j) fun _ _ => Commute.all _ _

private lemma sec_tmul {A A' C J : Type} [CommRing A] [CommRing A'] [CommRing C] [Algebra A A'] [Algebra A C]
    (τ : J → (A' →ₐ[A] C)) (c : C) (b : A') (j : J) : sec τ (c ⊗ₜ b) j = c * τ j b := by
  simp [sec]

private lemma tensor_hom_ext {A A' C Ω : Type} [CommRing A] [CommRing A'] [CommRing C] [Algebra A A'] [Algebra A C]
    [CommRing Ω] {u v : C ⊗[A] A' →+* Ω} (h₁ : ∀ c : C, u (c ⊗ₜ 1) = v (c ⊗ₜ 1))
    (h₂ : ∀ b : A', u (1 ⊗ₜ b) = v (1 ⊗ₜ b)) : u = v :=
  _root_.UpperTheory.Reformulated.B.Qk54.tensor_hom_ext h₁ h₂

private lemma exists_eval {C Ω J : Type} [CommRing C] [Field Ω] [Fintype J] (f : (J → C) →+* Ω) :
    ∃ j, ∀ v : J → C, f v = f (algebraMap C (J → C) (v j)) :=
  _root_.UpperTheory.Reformulated.B.ExistsEvaluation.exists_eval f

private lemma bij_of_pts (hiso : AlgIsoPts) {C D E : Type} [CommRing C] [CommRing D] [CommRing E] [Algebra C D]
    [Algebra C E] [Algebra.Etale C D] [Algebra.Etale C E] (φ : D →ₐ[C] E)
    (pts : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : D →+* Ω), ∃! y : E →+* Ω, y.comp (φ : D →+* E) = x) :
    Function.Bijective φ := by
  letI : Algebra D E := (φ : D →+* E).toAlgebra
  haveI : IsScalarTower C D E := IsScalarTower.of_algebraMap_eq' (φ.comp_algebraMap).symm
  haveI : Algebra.Etale D E := Algebra.Etale.of_restrictScalars C D E
  exact hiso D E pts

end UpperTheory.Gal.G3.AlgebraSplitting

open UpperTheory.Gal.G3.AlgebraSplitting in
theorem UpperTheory.Gal.G3.pAlgSplit :
    AlgIsoPts → AlgSplit := by
  intro hiso A A' C _ _ _ _ _ _ J _ τ h
  refine ⟨AlgEquiv.ofBijective (sec τ) (bij_of_pts hiso (sec τ) ?_), fun b j => ?_⟩
  swap
  · simp [sec_tmul]
  intro Ω _ _ x
  let x₀ : C →+* Ω := x.comp (Algebra.TensorProduct.includeLeftRingHom)
  let y₀ : A' →+* Ω := x.comp (Algebra.TensorProduct.includeRight : A' →ₐ[A] C ⊗[A] A').toRingHom
  have hx₀ : ∀ c, x₀ c = x (c ⊗ₜ 1) := fun _ => rfl
  have hy₀ : ∀ b, y₀ b = x (1 ⊗ₜ b) := fun _ => rfl
  have compat : y₀.comp (algebraMap A A') = x₀.comp (algebraMap A C) := by
    ext a
    simp only [RingHom.comp_apply, hx₀, hy₀]
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  obtain ⟨j, hj, huniq⟩ := h Ω x₀ y₀ compat
  have hτ : ∀ b, x₀ (τ j b) = y₀ b := fun b => congrArg (fun f : A' →+* Ω => f b) hj
  refine ⟨x₀.comp (Pi.evalRingHom (fun _ => C) j), ?_, ?_⟩
  · apply tensor_hom_ext
    · intro c
      simp [sec_tmul, hx₀]
    · intro b
      have := hτ b
      simp only [RingHom.comp_apply, RingHom.coe_coe, Pi.evalRingHom_apply, sec_tmul, one_mul]
      rw [this, hy₀]
  · intro y' hy'
    have hy'd : ∀ d, y' (sec τ d) = x d := fun d => congrArg (fun f : C ⊗[A] A' →+* Ω => f d) hy'
    obtain ⟨j', hj'⟩ := exists_eval y'
    have hal : ∀ c : C, y' (algebraMap C (J → C) c) = x₀ c := by
      intro c
      rw [hx₀, ← hy'd]
      congr 1
      funext i
      simp [sec_tmul]
    have hy'e : ∀ v : J → C, y' v = x₀ (v j') := fun v => by rw [hj', hal]
    have hjj : j' = j := by
      apply huniq
      ext b
      have := hy'e (sec τ (1 ⊗ₜ b))
      rw [hy'd, sec_tmul, one_mul] at this
      simpa [hy₀] using this.symm
    subst hjj
    ext v
    simp [hy'e]
end
