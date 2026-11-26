module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.Cohen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.BaseExistsPrime
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.CompDim
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.Bridge

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.DimLeOfForall
open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem dim_le_of_forall {R : Type} [CommRing R] (I : Ideal R) (d : WithBot ℕ∞)
    (h : ∀ P : Ideal R, P.IsPrime → I ≤ P → ∃ J : Ideal R, J ≤ P ∧ ringKrullDim (R ⧸ J) ≤ d) :
    ringKrullDim (R ⧸ I) ≤ d := by
  rw [ringKrullDim_quotient]
  unfold Order.krullDim
  apply iSup_le
  intro l
  obtain ⟨J, hJP, hJd⟩ := h l.head.1.asIdeal l.head.1.isPrime l.head.2
  rw [ringKrullDim_quotient] at hJd
  let l' : LTSeries (PrimeSpectrum.zeroLocus (J : Set R)) :=
    { length := l.length
      toFun := fun i => ⟨(l i).1, fun r hr => (l.monotone (Fin.zero_le i)) (hJP hr)⟩
      step := fun i => l.step i }
  exact le_trans (le_iSup (fun p : LTSeries (PrimeSpectrum.zeroLocus (J : Set R)) => (p.length : WithBot ℕ∞)) l') hJd

theorem UpperTheory.V.AlgebraTools.Conn.chain :
    ∀ {R : Type} [CommRing R] [IsNoetherianRing R] (a : Ideal R) (k : WithBot ℕ∞), ConnOn a k →
      ∀ p ∈ a.minimalPrimes, ∀ q ∈ a.minimalPrimes,
        Relation.ReflTransGen (fun x y : Ideal R => x ∈ a.minimalPrimes ∧ y ∈ a.minimalPrimes ∧ ReciprocityTheory.CA.Linked R k x y) p q := by
  intro R _ _ a k hconn p hp q hq
  classical
  let rel : Ideal R → Ideal R → Prop := fun x y =>
    x ∈ a.minimalPrimes ∧ y ∈ a.minimalPrimes ∧ ReciprocityTheory.CA.Linked R k x y
  change Relation.ReflTransGen rel p q
  by_contra hpq
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing R a
  obtain ⟨K, hK⟩ : ∃ K : Finset (Ideal R),
      ∀ x, x ∈ K ↔ x ∈ a.minimalPrimes ∧ Relation.ReflTransGen rel p x :=
    ⟨hfin.toFinset.filter (fun x => Relation.ReflTransGen rel p x), fun x => by
      rw [Finset.mem_filter, Set.Finite.mem_toFinset]⟩
  obtain ⟨L, hL⟩ : ∃ L : Finset (Ideal R),
      ∀ x, x ∈ L ↔ x ∈ a.minimalPrimes ∧ ¬ Relation.ReflTransGen rel p x :=
    ⟨hfin.toFinset.filter (fun x => ¬ Relation.ReflTransGen rel p x), fun x => by
      rw [Finset.mem_filter, Set.Finite.mem_toFinset]⟩
  have hpK : p ∈ K := (hK p).mpr ⟨hp, Relation.ReflTransGen.refl⟩
  have hqL : q ∈ L := (hL q).mpr ⟨hq, hpq⟩
  obtain ⟨g, hg⟩ : ∃ g : Ideal R × Ideal R → WithBot ℕ∞,
      ∀ xy, g xy = ringKrullDim (R ⧸ (xy.1 ⊔ xy.2)) := ⟨_, fun _ => rfl⟩
  have hnl : ∀ x ∈ K, ∀ y ∈ L, g (x, y) < k := by
    intro x hx y hy
    obtain ⟨hxM, hpx⟩ := (hK x).mp hx
    obtain ⟨hyM, hpy⟩ := (hL y).mp hy
    rw [hg]
    by_contra hle
    exact hpy (hpx.tail ⟨hxM, hyM, not_lt.mp hle⟩)
  have hk : ⊥ < k := lt_of_le_of_lt bot_le (hnl p hpK q hqL)
  obtain ⟨J1, hJ1⟩ : ∃ J1 : Ideal R, J1 = K.inf id := ⟨_, rfl⟩
  obtain ⟨J2, hJ2⟩ : ∃ J2 : Ideal R, J2 = L.inf id := ⟨_, rfl⟩
  have haJ1 : a ≤ J1 := hJ1 ▸ Finset.le_inf (fun x hx => ((hK x).mp hx).1.1.2)
  have haI : a ≤ J1 ⊔ J2 := le_sup_of_le_left haJ1
  have hdim : ringKrullDim (R ⧸ (J1 ⊔ J2)) < k := by
    have hd : ringKrullDim (R ⧸ (J1 ⊔ J2)) ≤ (K ×ˢ L).sup g := by
      apply dim_le_of_forall
      intro P hP hIP
      obtain ⟨x, hx, hxP⟩ :=
        (Ideal.IsPrime.inf_le' (s := K) (f := id) hP).mp (hJ1 ▸ le_sup_left.trans hIP)
      obtain ⟨y, hy, hyP⟩ :=
        (Ideal.IsPrime.inf_le' (s := L) (f := id) hP).mp (hJ2 ▸ le_sup_right.trans hIP)
      refine ⟨x ⊔ y, sup_le hxP hyP, ?_⟩
      have hle : g (x, y) ≤ (K ×ˢ L).sup g := Finset.le_sup (Finset.mem_product.mpr ⟨hx, hy⟩)
      rw [hg] at hle
      exact hle
    refine lt_of_le_of_lt hd ((Finset.sup_lt_iff hk).mpr ?_)
    intro xy hxy
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hxy
    exact hnl _ h1 _ h2
  have mz : ∀ (J : Ideal R) (z : PrimeSpectrum R),
      z ∈ PrimeSpectrum.zeroLocus (J : Set R) ↔ J ≤ z.asIdeal := fun J z => by
    rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
  have hJ2p : ¬ J2 ≤ p := by
    intro h
    rw [hJ2] at h
    obtain ⟨y, hy, hyp⟩ := (Ideal.IsPrime.inf_le' (s := L) (f := id) hp.1.1).mp h
    have hyM := ((hL y).mp hy).1
    have hyeq : y = p := le_antisymm hyp (hp.2 hyM.1 hyp)
    exact ((hL y).mp hy).2 (hyeq ▸ Relation.ReflTransGen.refl)
  have hJ1q : ¬ J1 ≤ q := by
    intro h
    rw [hJ1] at h
    obtain ⟨x, hx, hxq⟩ := (Ideal.IsPrime.inf_le' (s := K) (f := id) hq.1.1).mp h
    have hxM := ((hK x).mp hx).1
    have hxeq : x = q := le_antisymm hxq (hq.2 hxM.1 hxq)
    exact hpq (hxeq ▸ ((hK x).mp hx).2)
  obtain ⟨z, hzS, hzu, hzv⟩ := (hconn (J1 ⊔ J2) haI hdim).isPreconnected
    (PrimeSpectrum.zeroLocus (J2 : Set R))ᶜ (PrimeSpectrum.zeroLocus (J1 : Set R))ᶜ
    (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl
    (by
      rintro z ⟨_, hzI⟩
      by_contra hz
      simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hz
      exact hzI ((mz _ z).mpr (sup_le ((mz J1 z).mp hz.2) ((mz J2 z).mp hz.1))))
    ⟨⟨p, hp.1.1⟩, ⟨(mz a _).mpr hp.1.2, fun h => hJ2p (le_sup_right.trans ((mz _ _).mp h))⟩,
      fun h => hJ2p ((mz J2 _).mp h)⟩
    ⟨⟨q, hq.1.1⟩, ⟨(mz a _).mpr hq.1.2, fun h => hJ1q (le_sup_left.trans ((mz _ _).mp h))⟩,
      fun h => hJ1q ((mz J1 _).mp h)⟩
  obtain ⟨m, hm, hmz⟩ := Ideal.exists_minimalPrimes_le ((mz a z).mp hzS.1)
  by_cases hpm : Relation.ReflTransGen rel p m
  · refine hzv ((mz J1 z).mpr ?_)
    rw [hJ1]
    exact (Finset.inf_le (f := id) ((hK m).mpr ⟨hm, hpm⟩)).trans hmz
  · refine hzu ((mz J2 z).mpr ?_)
    rw [hJ2]
    exact (Finset.inf_le (f := id) ((hL m).mpr ⟨hm, hpm⟩)).trans hmz
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.ClConn
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.DimOfUniv
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IterCancel
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.StepArith
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.WithBotAddOneLeAddTwo
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.ImportsVariant
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.CutDimCongr
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.MaxNotMemMinimalPrimes
open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem UpperTheory.V.AlgebraTools.Conn.drop_one {R : Type} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (I : Ideal R) (y : R) (hy : y ∈ maximalIdeal R)
    (hn : ∀ p ∈ I.minimalPrimes, y ∉ p) :
    ringKrullDim (R ⧸ (I ⊔ Ideal.span {y})) + 1 = ringKrullDim (R ⧸ I) := by
  have hy' : y ∈ (Module.annihilator R (R ⧸ I)).jacobson := by
    rw [Ideal.annihilator_quotient]
    exact (IsLocalRing.maximalIdeal_le_jacobson _) hy
  have hn' : ∀ p ∈ (Module.annihilator R (R ⧸ I)).minimalPrimes, y ∉ p := by
    rw [Ideal.annihilator_quotient]
    exact hn
  have key := Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_jacobson hn' hy'
  rw [Module.supportDim_quotient_eq_ringKrullDim] at key
  rw [← key, ← Module.supportDim_quotient_eq_ringKrullDim]
  have hs : Module.support R (R ⧸ (I ⊔ Ideal.span {y})) = Module.support R (QuotSMulTop y (R ⧸ I)) := by
    rw [Module.support_quotSMulTop, Module.support_eq_zeroLocus, Module.support_eq_zeroLocus,
      Ideal.annihilator_quotient, Ideal.annihilator_quotient, PrimeSpectrum.zeroLocus_sup,
      PrimeSpectrum.zeroLocus_span]
  simp only [Module.supportDim]
  rw [hs]

private theorem UpperTheory.V.AlgebraTools.Conn.max_notMem_minimalPrimes {R : Type} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (h : 0 < ringKrullDim (R ⧸ I)) : maximalIdeal R ∉ I.minimalPrimes := by
  intro hm
  rw [ringKrullDim_quotient, Order.krullDim_pos_iff] at h
  obtain ⟨a, b, hab⟩ := h
  have ha : I ≤ a.1.asIdeal := a.2
  have hma : maximalIdeal R ≤ a.1.asIdeal :=
    hm.2 ⟨a.1.isPrime, ha⟩ (IsLocalRing.le_maximalIdeal a.1.isPrime.ne_top)
  have hbm : b.1.asIdeal ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal b.1.isPrime.ne_top
  have hlt : a.1.asIdeal < b.1.asIdeal := hab
  exact absurd (hbm.trans hma) (not_le_of_gt hlt)

theorem UpperTheory.V.AlgebraTools.Conn.drop :
    ∀ {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra A R]
      [Algebra.IsIntegral A R] (S : Finset (Ideal R)), (∀ I ∈ S, 0 < ringKrullDim (R ⧸ I)) →
      ∃ x ∈ maximalIdeal A, ∀ I ∈ S, ringKrullDim (R ⧸ (I ⊔ Ideal.span {algebraMap A R x})) + 1 = ringKrullDim (R ⧸ I) := by
  intro A R _ _ _ _ _ _ _ S hS
  classical
  let T : Set (Ideal A) := ⋃ I ∈ S, (Ideal.comap (algebraMap A R)) '' I.minimalPrimes
  have hT : T.Finite := Set.Finite.biUnion S.finite_toSet
    (fun I _ => (Ideal.finite_minimalPrimes_of_isNoetherianRing R I).image _)
  have memT : ∀ q, q ∈ T ↔ ∃ I ∈ S, ∃ p ∈ I.minimalPrimes, Ideal.comap (algebraMap A R) p = q := by
    intro q
    simp only [T, Set.mem_iUnion, Set.mem_image, exists_prop]
  have hmA : Ideal.comap (algebraMap A R) (maximalIdeal R) = maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (maximalIdeal R))
  have hTprime : ∀ q ∈ T, q.IsPrime := by
    intro q hq
    obtain ⟨I, _, p, hp, rfl⟩ := (memT q).mp hq
    haveI := hp.1.1
    infer_instance
  have hnot : ¬ ∃ q ∈ hT.toFinset, maximalIdeal A ≤ id q := by
    rintro ⟨q, hq, hle⟩
    obtain ⟨I, hI, p, hp, rfl⟩ := (memT _).mp (hT.mem_toFinset.mp hq)
    haveI := hp.1.1
    have heq : maximalIdeal A = Ideal.comap (algebraMap A R) p :=
      (IsLocalRing.maximalIdeal.isMaximal A).eq_of_le Ideal.IsPrime.ne_top' hle
    haveI : (Ideal.comap (algebraMap A R) p).IsMaximal := heq ▸ IsLocalRing.maximalIdeal.isMaximal A
    have hpm : p = maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_of_isIntegral_of_isMaximal_under p this)
    exact UpperTheory.V.AlgebraTools.Conn.max_notMem_minimalPrimes I (hS I hI) (hpm ▸ hp)
  have hsub := (Ideal.subset_union_prime (s := hT.toFinset) (f := id) ⊥ ⊥
    (fun q hq _ _ => hTprime q (hT.mem_toFinset.mp hq)) (I := maximalIdeal A)).not.mpr hnot
  obtain ⟨x, hxm, hx⟩ := Set.not_subset.mp hsub
  refine ⟨x, hxm, fun I hI => UpperTheory.V.AlgebraTools.Conn.drop_one I _ ?_ ?_⟩
  · have hx' : x ∈ Ideal.comap (algebraMap A R) (maximalIdeal R) := hmA ▸ hxm
    exact hx'
  · intro p hp hxp
    apply hx
    simp only [Set.mem_iUnion, id]
    exact ⟨Ideal.comap (algebraMap A R) p, hT.mem_toFinset.mpr ((memT _).mpr ⟨I, hI, p, hp, rfl⟩), hxp⟩
end

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem cut_rad_iff {R : Type} [CommRing R] (I J : Ideal R) :
    I.radical = J.radical ↔ ∀ p : Ideal R, p.IsPrime → (I ≤ p ↔ J ≤ p) := by
  constructor
  · intro h p hp
    rw [← hp.radical_le_iff (I := I), h, hp.radical_le_iff]
  · intro h
    rw [Ideal.radical_eq_sInf I, Ideal.radical_eq_sInf J]
    congr 1
    ext p
    simp only [Set.mem_setOf_eq]
    exact ⟨fun ⟨h1, h2⟩ => ⟨(h p h2).mp h1, h2⟩, fun ⟨h1, h2⟩ => ⟨(h p h2).mpr h1, h2⟩⟩

private theorem cut_dim_congr {R : Type} [CommRing R] {I J : Ideal R} (h : I.radical = J.radical) :
    ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ J) := by
  have e : PrimeSpectrum.zeroLocus (I : Set R) = PrimeSpectrum.zeroLocus (J : Set R) := by
    rw [← PrimeSpectrum.zeroLocus_radical, h, PrimeSpectrum.zeroLocus_radical]
  rw [ringKrullDim_quotient, ringKrullDim_quotient, e]

private theorem cut_dim_nat {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {I : Ideal R} (h : I ≠ ⊤) : ∃ n : ℕ, ringKrullDim (R ⧸ I) = n := by
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr h
  haveI : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have h1 := ringKrullDim_ne_top (R := R ⧸ I)
  have h2 := ringKrullDim_ne_bot (R := R ⧸ I)
  generalize ringKrullDim (R ⧸ I) = d at h1 h2 ⊢
  induction d using WithBot.recBotCoe with
  | bot => exact absurd rfl h2
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact absurd rfl h1
    | coe n => exact ⟨n, rfl⟩

private theorem cut_dim_map {A R : Type} [CommRing A] [CommRing R] [Algebra A R]
    [Algebra.IsIntegral A R] [FaithfulSMul A R] (J : Ideal A) :
    ringKrullDim (R ⧸ J.map (algebraMap A R)) = ringKrullDim (A ⧸ J) := by
  rw [ReciprocityTheory.CA.ringKrullDim_quotient_eq_quotient_comap_of_isIntegral (A := A)]
  apply cut_dim_congr
  rw [cut_rad_iff]
  intro p hp
  constructor
  · intro h
    exact le_trans Ideal.le_comap_map h
  · intro hJ
    haveI := hp
    obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p (⊥ : Ideal R)
      (by simp [← RingHom.ker_eq_comap_bot,
        (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective A R)])
    change Ideal.comap (algebraMap A R) Q = p at hQp
    have hle : J.map (algebraMap A R) ≤ Q := Ideal.map_le_iff_le_comap.mpr (by simpa [hQp] using hJ)
    have hcomap : Ideal.comap (algebraMap A R) (J.map (algebraMap A R)) ≤
        Ideal.comap (algebraMap A R) Q := Ideal.comap_mono hle
    simpa [hQp] using hcomap

private theorem cut_rad_max {R : Type} [CommRing R] [IsLocalRing R] {I : Ideal R} (hI : I ≠ ⊤)
    (h : ringKrullDim (R ⧸ I) = 0) : I.radical = maximalIdeal R := by
  have hm : (maximalIdeal R).radical = maximalIdeal R := (maximalIdeal.isMaximal R).isPrime.radical
  rw [← hm, cut_rad_iff]
  intro p hp
  constructor
  · intro hIp
    haveI : Ring.KrullDimLE 0 (R ⧸ I) := Ring.krullDimLE_iff.mpr (by simp [h])
    haveI := hp
    haveI hpm : (p.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
    haveI hmax : (p.map (Ideal.Quotient.mk I)).IsMaximal := hpm.isMaximal'
    have hpc : p = (p.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.mpr hIp]
    have hpmax : p.IsMaximal := by
      rw [hpc]
      exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    rw [IsLocalRing.eq_maximalIdeal hpmax]
  · intro hmp
    exact (IsLocalRing.le_maximalIdeal hI).trans hmp

private theorem cut_ne_top {R : Type} [CommRing R] {I : Ideal R} {k : WithBot ℕ∞}
    (h : ringKrullDim (R ⧸ I) + 1 = k) (hk : k ≠ ⊥) : I ≠ ⊤ := by
  rintro rfl
  haveI : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.mpr rfl
  rw [ringKrullDim_eq_bot_of_subsingleton, WithBot.bot_add] at h
  exact hk h.symm

theorem UpperTheory.V.AlgebraTools.Conn.cut :
    ∀ {A R : Type} [CommRing A] [IsLocalRing A] [IsDomain A] [CommRing R] [IsLocalRing R] [IsDomain R] [Algebra A R] [Module.Finite A R] [FaithfulSMul A R] [IsAdicComplete (maximalIdeal A) A], ReciprocityTheory.CA.IsCM A → ∀ (xs : List A) (b c : Ideal R),
      (∀ x ∈ xs, x ∈ maximalIdeal A) → ringKrullDim (A ⧸ Ideal.ofList xs) + xs.length = ringKrullDim A →
      (b ⊓ c).radical = ((Ideal.ofList xs).map (algebraMap A R)).radical → b ≠ ⊤ → c ≠ ⊤ →
      ringKrullDim (R ⧸ (b ⊔ c)) < ringKrullDim (R ⧸ b) → ringKrullDim (R ⧸ (b ⊔ c)) < ringKrullDim (R ⧸ c) →
      ringKrullDim R ≤ ringKrullDim (R ⧸ (b ⊔ c)) + 1 + xs.length := by
  classical
  intro A R _ _ _ _ _ _ _ _ _ _ hCM
  haveI : IsNoetherianRing A := hCM.1
  haveI : IsNoetherianRing R := isNoetherian_of_tower A inferInstance
  have hRA : ringKrullDim R = ringKrullDim A :=
    ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective (FaithfulSMul.algebraMap_injective A R)
  obtain ⟨N, hN, -⟩ := hCM.2
  have hxs_ne : ∀ xs : List A, (∀ x ∈ xs, x ∈ maximalIdeal A) → Ideal.ofList xs ≠ ⊤ := by
    intro xs hxs
    exact ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top (Ideal.span_le.mpr fun y hy => hxs y hy)
  have hsup_ne : ∀ b c : Ideal R, b ≠ ⊤ → c ≠ ⊤ → b ⊔ c ≠ ⊤ := fun b c hb hc =>
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top
      (sup_le (IsLocalRing.le_maximalIdeal hb) (IsLocalRing.le_maximalIdeal hc))
  have key : ∀ d : ℕ, ∀ (xs : List A) (b c : Ideal R), (∀ x ∈ xs, x ∈ maximalIdeal A) →
      ringKrullDim (A ⧸ Ideal.ofList xs) + xs.length = ringKrullDim A →
      (b ⊓ c).radical = ((Ideal.ofList xs).map (algebraMap A R)).radical → b ≠ ⊤ → c ≠ ⊤ →
      ringKrullDim (R ⧸ (b ⊔ c)) < ringKrullDim (R ⧸ b) →
      ringKrullDim (R ⧸ (b ⊔ c)) < ringKrullDim (R ⧸ c) →
      ringKrullDim (R ⧸ (b ⊔ c)) = d → ringKrullDim R ≤ d + 1 + xs.length := by
    intro d
    induction d with
    | zero =>
      intro xs b c hxs hdim hrad hb hc hlt1 hlt2 hd
      have hbc := hsup_ne b c hb hc
      have hd0 : ringKrullDim (R ⧸ (b ⊔ c)) = 0 := by rw [hd, Nat.cast_zero]
      have hmax := cut_rad_max hbc hd0
      by_contra hcon
      obtain ⟨a, ha⟩ := cut_dim_nat (hxs_ne xs hxs)
      have hdim' : a + xs.length = N := by
        have h' := hdim
        rw [ha, hN] at h'
        exact_mod_cast h'
      have hcon' : ¬ N ≤ 0 + 1 + xs.length := by
        intro h'
        apply hcon
        rw [hRA, hN]
        exact_mod_cast h'
      have h2 : 2 ≤ ringKrullDim (A ⧸ Ideal.ofList xs) := by
        rw [ha]
        exact_mod_cast (by omega : 2 ≤ a)
      exact base hCM xs b c hxs hdim h2 hrad hmax (by rwa [hd0] at hlt1) (by rwa [hd0] at hlt2)
    | succ d ih =>
      intro xs b c hxs hdim hrad hb hc hlt1 hlt2 hd
      have hpos_bc : 0 < ringKrullDim (R ⧸ (b ⊔ c)) := by
        rw [hd]
        exact_mod_cast Nat.succ_pos d
      have hpos_b : 0 < ringKrullDim (R ⧸ b) := hpos_bc.trans hlt1
      have hpos_c : 0 < ringKrullDim (R ⧸ c) := hpos_bc.trans hlt2
      have hpos_J : 0 < ringKrullDim (R ⧸ (Ideal.ofList xs).map (algebraMap A R)) := by
        have e1 : ringKrullDim (R ⧸ (Ideal.ofList xs).map (algebraMap A R)) = ringKrullDim (R ⧸ (b ⊓ c)) :=
          cut_dim_congr hrad.symm
        have e2 : ringKrullDim (R ⧸ (b ⊔ c)) ≤ ringKrullDim (R ⧸ (b ⊓ c)) :=
          ringKrullDim_le_of_surjective (Ideal.Quotient.factor (inf_le_sup : b ⊓ c ≤ b ⊔ c))
            (Ideal.Quotient.factor_surjective inf_le_sup)
        rw [e1]
        exact hpos_bc.trans_le e2
      obtain ⟨x, hxm, hx⟩ := drop (A := A) ({b ⊔ c, b, c, (Ideal.ofList xs).map (algebraMap A R)} : Finset (Ideal R))
        (by
          intro I hI
          simp only [Finset.mem_insert, Finset.mem_singleton] at hI
          rcases hI with rfl | rfl | rfl | rfl
          exacts [hpos_bc, hpos_b, hpos_c, hpos_J])
      have hxbc := hx (b ⊔ c) (by simp)
      have hxb := hx b (by simp)
      have hxc := hx c (by simp)
      have hxJ := hx ((Ideal.ofList xs).map (algebraMap A R)) (by simp)
      obtain ⟨kb, hkb⟩ := cut_dim_nat hb
      obtain ⟨kc, hkc⟩ := cut_dim_nat hc
      have hb' : b ⊔ Ideal.span {algebraMap A R x} ≠ ⊤ := cut_ne_top hxb (by rw [hkb]; simp)
      have hc' : c ⊔ Ideal.span {algebraMap A R x} ≠ ⊤ := cut_ne_top hxc (by rw [hkc]; simp)
      obtain ⟨kb', hkb'⟩ := cut_dim_nat hb'
      obtain ⟨kc', hkc'⟩ := cut_dim_nat hc'
      have hbcs : (b ⊔ Ideal.span {algebraMap A R x}) ⊔ (c ⊔ Ideal.span {algebraMap A R x}) =
          (b ⊔ c) ⊔ Ideal.span {algebraMap A R x} := (sup_sup_distrib_right b c _).symm
      obtain ⟨e, he⟩ := cut_dim_nat (hsup_ne _ _ hb' hc')
      rw [← hbcs, he, hd] at hxbc
      rw [hkb', hkb] at hxb
      rw [hkc', hkc] at hxc
      rw [hd, hkb] at hlt1
      rw [hd, hkc] at hlt2
      have ne : e + 1 = d + 1 := by exact_mod_cast hxbc
      have nb : kb' + 1 = kb := by exact_mod_cast hxb
      have nc : kc' + 1 = kc := by exact_mod_cast hxc
      have lb : d + 1 < kb := by exact_mod_cast hlt1
      have lc : d + 1 < kc := by exact_mod_cast hlt2
      have hxs' : ∀ y ∈ x :: xs, y ∈ maximalIdeal A := by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hxm
        · exact hxs y hy
      have hJ' : (Ideal.ofList (x :: xs)).map (algebraMap A R) =
          (Ideal.ofList xs).map (algebraMap A R) ⊔ Ideal.span {algebraMap A R x} := by
        rw [Ideal.ofList_cons, Ideal.map_sup, Ideal.map_span, Set.image_singleton, sup_comm]
      obtain ⟨a, ha⟩ := cut_dim_nat (hxs_ne xs hxs)
      obtain ⟨a', ha'⟩ := cut_dim_nat (hxs_ne (x :: xs) hxs')
      rw [← hJ', cut_dim_map, cut_dim_map, ha, ha'] at hxJ
      have na : a' + 1 = a := by exact_mod_cast hxJ
      have hdimN : a + xs.length = N := by
        have h' := hdim
        rw [ha, hN] at h'
        exact_mod_cast h'
      have hdim' : ringKrullDim (A ⧸ Ideal.ofList (x :: xs)) + (x :: xs).length = ringKrullDim A := by
        rw [ha', hN, List.length_cons]
        exact_mod_cast (by omega : a' + (xs.length + 1) = N)
      have hrad' : ((b ⊔ Ideal.span {algebraMap A R x}) ⊓ (c ⊔ Ideal.span {algebraMap A R x})).radical =
          ((Ideal.ofList (x :: xs)).map (algebraMap A R)).radical := by
        rw [hJ', cut_rad_iff]
        intro p hp
        have hr := (cut_rad_iff _ _).mp hrad p hp
        rw [hp.inf_le] at hr
        rw [hp.inf_le, sup_le_iff, sup_le_iff, sup_le_iff]
        tauto
      have h1' : ringKrullDim (R ⧸ ((b ⊔ Ideal.span {algebraMap A R x}) ⊔ (c ⊔ Ideal.span {algebraMap A R x}))) <
          ringKrullDim (R ⧸ (b ⊔ Ideal.span {algebraMap A R x})) := by
        rw [he, hkb']
        exact_mod_cast (by omega : e < kb')
      have h2' : ringKrullDim (R ⧸ ((b ⊔ Ideal.span {algebraMap A R x}) ⊔ (c ⊔ Ideal.span {algebraMap A R x}))) <
          ringKrullDim (R ⧸ (c ⊔ Ideal.span {algebraMap A R x})) := by
        rw [he, hkc']
        exact_mod_cast (by omega : e < kc')
      have hfin := ih (x :: xs) _ _ hxs' hdim' hrad' hb' hc' h1' h2' (by rw [he]; exact_mod_cast (by omega : e = d))
      have heq : ((d : WithBot ℕ∞) + 1 + ((x :: xs).length : WithBot ℕ∞)) =
          ((d + 1 : ℕ) : WithBot ℕ∞) + 1 + (xs.length : WithBot ℕ∞) := by
        rw [List.length_cons]
        push_cast
        ring
      rw [← heq]
      exact hfin
  intro xs b c hxs hdim hrad hb hc hlt1 hlt2
  obtain ⟨d, hd⟩ := cut_dim_nat (hsup_ne b c hb hc)
  rw [hd]
  exact key d xs b c hxs hdim hrad hb hc hlt1 hlt2 hd
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.Adjoin
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.CmFree
open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.cmFree :
    ∀ {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra A B] [Module.Finite A B]
      [Module.Free A B], ReciprocityTheory.CA.IsCM A → ReciprocityTheory.CA.IsCM B := by
  intro A B _ _ _ _ _ _ _ h
  obtain ⟨hN, n, hdim, rs, hlen, hmem, hreg⟩ := h
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have hm : (maximalIdeal B).comap (algebraMap A B) = maximalIdeal A :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal B))
  refine ⟨IsNoetherianRing.of_finite A B, n, ?_, rs.map (algebraMap A B), by simpa using hlen, ?_,
    hreg.of_faithfullyFlat⟩
  · rw [← hdim]
    exact ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj
  · intro r hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    have := hmem a ha
    rw [← hm] at this
    exact this
end

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.adjoin :
    ∀ {A R : Type} [CommRing A] [IsLocalRing A] [IsDomain A] [CommRing R] [IsLocalRing R] [IsDomain R] [Algebra A R] [Module.Finite A R] [FaithfulSMul A R], IsBase A → ∀ f : R,
      ∃ _ : IsLocalRing (Algebra.adjoin A {f}), ReciprocityTheory.CA.IsCM (Algebra.adjoin A {f}) := by
  intro A R _ _ _ _ _ _ _ _ _ hA f
  have hf : IsIntegral A f := Algebra.IsIntegral.isIntegral f
  haveI : IsIntegrallyClosed A := hA.normal
  haveI : Algebra.IsIntegral (Algebra.adjoin A {f}) R := Algebra.IsIntegral.tower_top A
  haveI : IsLocalRing (Algebra.adjoin A {f}) :=
    RingHom.domain_isLocalRing (algebraMap (Algebra.adjoin A {f}) R)
  refine ⟨inferInstance, ?_⟩
  haveI : Module.Free A (Algebra.adjoin A {f}) := .of_basis (Algebra.adjoin.powerBasis' hf).basis
  haveI : Module.Finite A (Algebra.adjoin A {f}) := .of_basis (Algebra.adjoin.powerBasis' hf).basis
  exact cmFree hA.cm
end

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.one :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] [IsDomain R], HasBase R → ∀ (f : R) (b c : Ideal R), f ∈ maximalIdeal R →
      (b ⊓ c).radical = (Ideal.span {f}).radical → b ≠ ⊤ → c ≠ ⊤ →
      ringKrullDim (R ⧸ (b ⊔ c)) < ringKrullDim (R ⧸ b) → ringKrullDim (R ⧸ (b ⊔ c)) < ringKrullDim (R ⧸ c) →
      ringKrullDim R ≤ ringKrullDim (R ⧸ (b ⊔ c)) + 2 := by
  intro R _ _ _ hB f b c hf hrad hb hc hdb hdc
  obtain ⟨A, _, _, i, hA, hinj, hfin⟩ := hB
  letI : Algebra A R := i.toAlgebra
  haveI : Module.Finite A R := hfin
  haveI : FaithfulSMul A R := (faithfulSMul_iff_algebraMap_injective A R).mpr hinj
  haveI : IsDomain A := hA.dom
  haveI : IsNoetherianRing A := hA.cm.1
  haveI : IsAdicComplete (maximalIdeal A) A := hA.complete
  by_cases hf0 : f = 0
  · exfalso
    subst hf0
    have hbc : b ⊓ c ≤ ⊥ := by
      intro x hx
      have : x ∈ (b ⊓ c).radical := Ideal.le_radical hx
      rw [hrad, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.radical_eq_iff.mpr (Ideal.isPrime_bot).isRadical] at this
      exact this
    have hprod : b * c = ⊥ := le_bot_iff.mp (le_trans Ideal.mul_le_inf hbc)
    rcases Ideal.mul_eq_bot.mp hprod with h | h
    · subst h
      rw [bot_sup_eq] at hdc
      exact lt_irrefl _ hdc
    · subst h
      rw [sup_bot_eq] at hdb
      exact lt_irrefl _ hdb
  obtain ⟨hloc, hcm⟩ := adjoin hA f
  haveI : IsNoetherianRing (Algebra.adjoin A {f}) := hcm.1
  haveI : Module.Finite A (Algebra.adjoin A {f}) :=
    Module.Finite.of_injective (IsScalarTower.toAlgHom A (Algebra.adjoin A {f}) R).toLinearMap Subtype.val_injective
  haveI : IsAdicComplete (maximalIdeal (Algebra.adjoin A {f})) (Algebra.adjoin A {f}) :=
    cplFinite (A := A) (maximalIdeal _) (maximalIdeal.isMaximal _).ne_top
  haveI : Module.Finite (Algebra.adjoin A {f}) R := Module.Finite.of_restrictScalars_finite A _ R
  let x : Algebra.adjoin A {f} := ⟨f, Algebra.self_mem_adjoin_singleton A f⟩
  have hx0 : x ≠ 0 := fun h => hf0 (congrArg Subtype.val h)
  have hxm : x ∈ maximalIdeal (Algebra.adjoin A {f}) := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have : IsUnit f := hu.map (Algebra.adjoin A {f}).val
    exact ((mem_maximalIdeal f).mp hf) this
  have hdim : ringKrullDim (Algebra.adjoin A {f} ⧸ Ideal.ofList [x]) + ↑([x].length) =
      ringKrullDim (Algebra.adjoin A {f}) := by
    have hsp : Ideal.ofList [x] = Ideal.span {x} := by simp [Ideal.ofList]
    rw [hsp]
    apply ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_jacobson
    · exact IsSMulRegular.of_ne_zero hx0
    · rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
      exact hxm
  have hmap : Ideal.map (algebraMap (Algebra.adjoin A {f}) R) (Ideal.ofList [x]) = Ideal.span {f} := by
    simp [Ideal.ofList, Ideal.map_span]
    rfl
  have key := cut (A := Algebra.adjoin A {f}) (R := R) hcm [x] b c (by simpa using hxm) hdim (hmap ▸ hrad) hb hc hdb hdc
  simp only [List.length_singleton, Nat.cast_one] at key
  rw [add_assoc] at key
  exact key
end

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem hyper_dim_mono {R : Type} [CommRing R] {I J : Ideal R}
    (h : PrimeSpectrum.zeroLocus (J : Set R) ⊆ PrimeSpectrum.zeroLocus (I : Set R)) :
    ringKrullDim (R ⧸ J) ≤ ringKrullDim (R ⧸ I) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient]
  exact Order.krullDim_le_of_strictMono (Set.inclusion h) (fun _ _ hxy => hxy)

private theorem withBot_le_of_add_two (k : ℕ) (d : WithBot ℕ∞) (h : (k : WithBot ℕ∞) + 2 ≤ d + 2) :
    (k : WithBot ℕ∞) ≤ d := by
  induction d using WithBot.recBotCoe with
  | bot => exact absurd h (by rw [WithBot.bot_add, le_bot_iff]; exact_mod_cast WithBot.coe_ne_bot (a := ((k + 2 : ℕ) : ℕ∞)))
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact le_top
    | coe d =>
      have h' : ((k + 2 : ℕ) : WithBot ℕ∞) ≤ ((d + 2 : ℕ) : WithBot ℕ∞) := by
        push_cast; exact h
      have h'' : k + 2 ≤ d + 2 := by exact_mod_cast h'
      have h3 : k ≤ d := by omega
      exact_mod_cast h3

private theorem withBot_add_one_le_add_two (d : WithBot ℕ∞) : d + ((1 : ℕ) : WithBot ℕ∞) ≤ d + 2 := by
  gcongr
  exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2)

theorem UpperTheory.V.AlgebraTools.Conn.hyper :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R], CohenType R → ∀ (p : Ideal R) (f : R) (k : ℕ), p.IsPrime →
      f ∈ maximalIdeal R → (k : WithBot ℕ∞) + 2 ≤ ringKrullDim (R ⧸ p) → ConnOn (p ⊔ Ideal.span {f}) k := by
  intro R _ _ _ hC p f k hp hf hk I haI hI
  set a : Ideal R := p ⊔ Ideal.span {f} with ha
  have ham : a ≤ maximalIdeal R :=
    sup_le (le_maximalIdeal hp.ne_top) ((Ideal.span_singleton_le_iff_mem _).2 hf)
  have hcomp : ∀ q ∈ a.minimalPrimes, (k : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q) := by
    intro q hq
    have h1 := compDim hC p q {f} hp (by simpa using hq)
    rw [Finset.card_singleton] at h1
    exact withBot_le_of_add_two k _ (hk.trans (h1.trans (withBot_add_one_le_add_two _)))
  have hle : ∀ {J K : Ideal R}, J ≤ K → ringKrullDim (R ⧸ K) ≤ ringKrullDim (R ⧸ J) :=
    fun h => hyper_dim_mono (PrimeSpectrum.zeroLocus_anti_mono_ideal h)
  have hmem : ∀ (q : Ideal R) (hq : q ∈ a.minimalPrimes),
      (⟨q, hq.1.1⟩ : PrimeSpectrum R) ∈
        PrimeSpectrum.zeroLocus (a : Set R) \ PrimeSpectrum.zeroLocus (I : Set R) := by
    intro q hq
    refine ⟨hq.1.2, fun h => ?_⟩
    have h' : I ≤ q := h
    exact absurd ((hcomp q hq).trans (hle h')) (not_le.2 hI)
  refine ⟨?_, ?_⟩
  · obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le ham
    exact ⟨_, hmem q hq⟩
  rw [isPreconnected_closed_iff]
  intro t t' ht ht' hcov hx hy
  by_contra hne
  obtain ⟨b0, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal t).1 ht
  obtain ⟨c0, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal t').1 ht'
  have hdisj : ∀ x : PrimeSpectrum R, a ≤ x.asIdeal → b0 ≤ x.asIdeal → c0 ≤ x.asIdeal →
      I ≤ x.asIdeal := by
    intro x h1 h2 h3
    by_contra h4
    exact hne ⟨x, ⟨h1, h4⟩, h2, h3⟩
  have hmin : ∀ q ∈ a.minimalPrimes, b0 ≤ q ∨ c0 ≤ q := fun q hq => hcov (hmem q hq)
  have hb : ∃ q ∈ a.minimalPrimes, a ⊔ b0 ≤ q := by
    obtain ⟨x, ⟨h1, h2⟩, h3⟩ := hx
    obtain ⟨q, hq, hqx⟩ := Ideal.exists_minimalPrimes_le (I := a) (J := x.asIdeal) h1
    rcases hmin q hq with h | h
    · exact ⟨q, hq, sup_le hq.1.2 h⟩
    · exact absurd (hdisj x h1 h3 (h.trans hqx)) h2
  have hc : ∃ q ∈ a.minimalPrimes, a ⊔ c0 ≤ q := by
    obtain ⟨x, ⟨h1, h2⟩, h3⟩ := hy
    obtain ⟨q, hq, hqx⟩ := Ideal.exists_minimalPrimes_le (I := a) (J := x.asIdeal) h1
    rcases hmin q hq with h | h
    · exact absurd (hdisj x h1 (h.trans hqx) h3) h2
    · exact ⟨q, hq, sup_le hq.1.2 h⟩
  set b : Ideal R := a ⊔ b0 with hbdef
  set c : Ideal R := a ⊔ c0 with hcdef
  have hpb : p ≤ b := le_sup_of_le_left le_sup_left
  have hpc : p ≤ c := le_sup_of_le_left le_sup_left
  have hbc : ringKrullDim (R ⧸ (b ⊔ c)) < k := by
    refine lt_of_le_of_lt (hyper_dim_mono fun x hx => ?_) hI
    have hx' : b ⊔ c ≤ x.asIdeal := hx
    exact hdisj x ((le_sup_of_le_left le_sup_left).trans hx')
      ((le_sup_of_le_left le_sup_right).trans hx') ((le_sup_of_le_right le_sup_right).trans hx')
  obtain ⟨q1, hq1, hbq⟩ := hb
  obtain ⟨q2, hq2, hcq⟩ := hc
  have hrad : (b ⊓ c).radical = a.radical := by
    refine le_antisymm ?_ (Ideal.radical_mono (le_inf le_sup_left le_sup_left))
    rw [Ideal.radical_le_radical_iff, ← Ideal.sInf_minimalPrimes]
    refine le_sInf fun q hq => ?_
    rcases hmin q hq with h | h
    · exact inf_le_left.trans (sup_le hq.1.2 h)
    · exact inf_le_right.trans (sup_le hq.1.2 h)
  have hdq : ∀ J : Ideal R, p ≤ J →
      ringKrullDim ((R ⧸ p) ⧸ J.map (Ideal.Quotient.mk p)) = ringKrullDim (R ⧸ J) :=
    fun J h => ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE h)
  have hcm : ∀ J : Ideal R, p ≤ J → (J.map (Ideal.Quotient.mk p)).comap (Ideal.Quotient.mk p) = J := by
    intro J h
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.2 h]
  have hnt : ∀ J : Ideal R, p ≤ J → J ≠ ⊤ → J.map (Ideal.Quotient.mk p) ≠ ⊤ := by
    intro J h hJ h2
    apply hJ
    rw [← hcm J h, h2, Ideal.comap_top]
  haveI : IsLocalRing (R ⧸ p) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hamap : a.map (Ideal.Quotient.mk p) = Ideal.span {Ideal.Quotient.mk p f} := by
    rw [ha, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span, Set.image_singleton]
  have key := one (hC p hp) (Ideal.Quotient.mk p f) (b.map (Ideal.Quotient.mk p))
    (c.map (Ideal.Quotient.mk p)) ?_ ?_
    (hnt b hpb fun h => hq1.1.1.ne_top (top_le_iff.1 (h ▸ hbq)))
    (hnt c hpc fun h => hq2.1.1.ne_top (top_le_iff.1 (h ▸ hcq))) ?_ ?_
  · rw [← Ideal.map_sup, hdq _ (le_sup_of_le_left hpb)] at key
    exact absurd (withBot_le_of_add_two k _ (hk.trans key)) (not_le.2 hbc)
  · rw [← Ideal.span_singleton_le_iff_mem, ← hamap]
    exact le_maximalIdeal (hnt a le_sup_left fun h =>
      (maximalIdeal.isMaximal R).ne_top (top_le_iff.1 (h ▸ ham)))
  · apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    rw [← hamap, Ideal.comap_radical, Ideal.comap_radical, Ideal.comap_inf, hcm b hpb, hcm c hpc,
      hcm a le_sup_left, hrad]
  · rw [← Ideal.map_sup, hdq _ (le_sup_of_le_left hpb), hdq _ hpb]
    exact hbc.trans_le ((hcomp q1 hq1).trans (hle hbq))
  · rw [← Ideal.map_sup, hdq _ (le_sup_of_le_left hpb), hdq _ hpc]
    exact hbc.trans_le ((hcomp q2 hq2).trans (hle hcq))
end

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem UpperTheory.V.AlgebraTools.Conn.step_krull {R : Type} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (J : Ideal R) (y : R) (hy : y ∈ maximalIdeal R) :
    ringKrullDim (R ⧸ J) ≤ ringKrullDim (R ⧸ (J ⊔ Ideal.span {y})) + 1 := by
  have h := Module.supportDim_le_supportDim_quotSMulTop_succ
    (R := R) (M := R ⧸ J) (x := y) hy
  rw [Module.supportDim_quotient_eq_ringKrullDim] at h
  refine h.trans (le_of_eq ?_)
  rw [ringKrullDim_quotient, Module.supportDim, Module.support_quotSMulTop,
    Module.support_eq_zeroLocus, Ideal.annihilator_quotient, PrimeSpectrum.zeroLocus_sup,
    PrimeSpectrum.zeroLocus_span]

private theorem UpperTheory.V.AlgebraTools.Conn.step_mono {R : Type} [CommRing R] (J I : Ideal R)
    (h : PrimeSpectrum.zeroLocus (J : Set R) ⊆ PrimeSpectrum.zeroLocus (I : Set R)) :
    ringKrullDim (R ⧸ J) ≤ ringKrullDim (R ⧸ I) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient]
  exact Order.krullDim_le_of_strictMono (Set.inclusion h) (fun _ _ hab => hab)

private theorem UpperTheory.V.AlgebraTools.Conn.step_arith (d e : WithBot ℕ∞) (k : ℕ) (h1 : d ≤ e) (h2 : e < k)
    (h3 : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ d + 1) : False := by
  have h4 : d < k := lt_of_le_of_lt h1 h2
  induction d using WithBot.recBotCoe with
  | bot => simp at h3
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact absurd h4 (not_lt.2 (WithBot.coe_le_coe.2 le_top))
    | coe d =>
      have h5 : d < k := by exact_mod_cast h4
      have h6 : k + 1 ≤ d + 1 := by exact_mod_cast h3
      omega

theorem UpperTheory.V.AlgebraTools.Conn.step :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R], CohenType R → ∀ (a : Ideal R) (f : R) (k : ℕ),
      f ∈ maximalIdeal R → ConnOn a ((k + 1 : ℕ) : WithBot ℕ∞) →
      (∀ p ∈ a.minimalPrimes, (k : WithBot ℕ∞) + 2 ≤ ringKrullDim (R ⧸ p)) → ConnOn (a ⊔ Ideal.span {f}) k := by
  intro R _ _ _ hC a f k hf hconn hdim I hI hIk
  set X : Ideal R → Set (PrimeSpectrum R) := fun b =>
    PrimeSpectrum.zeroLocus ((b ⊔ Ideal.span {f} : Ideal R) : Set R) \ PrimeSpectrum.zeroLocus (I : Set R)
    with hX
  have hmem : ∀ (b : Ideal R) (z : PrimeSpectrum R),
      z ∈ X b ↔ (b ≤ z.asIdeal ∧ Ideal.span {f} ≤ z.asIdeal) ∧ ¬ I ≤ z.asIdeal := by
    intro b z
    simp only [hX, Set.mem_diff, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, sup_le_iff]
  have hXc : ∀ p ∈ a.minimalPrimes, IsConnected (X p) := by
    intro p hp
    have h := hyper hC p f k hp.1.1 hf (hdim p hp) ((p ⊔ Ideal.span {f}) ⊔ I) le_sup_left
      (lt_of_le_of_lt (step_mono _ _ (PrimeSpectrum.zeroLocus_anti_mono_ideal le_sup_right)) hIk)
    convert h using 1
    ext z
    rw [hmem]
    simp only [Set.mem_diff, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, sup_le_iff]
    tauto
  have hsub : ∀ p ∈ a.minimalPrimes, X p ⊆ X a := by
    intro p hp z hz
    rw [hmem] at hz ⊢
    exact ⟨⟨hp.1.2.trans hz.1.1, hz.1.2⟩, hz.2⟩
  have hmeet : ∀ p q : Ideal R, ReciprocityTheory.CA.Linked R ((k + 1 : ℕ) : WithBot ℕ∞) p q →
      (X p ∩ X q).Nonempty := by
    intro p q hl
    by_contra hne
    have hl' : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ (p ⊔ q)) := hl
    refine step_arith _ _ k (step_mono ((p ⊔ q) ⊔ Ideal.span {f}) I ?_) hIk
      (hl'.trans (step_krull _ f hf))
    intro z hz
    simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, sup_le_iff] at hz ⊢
    by_contra hzI
    exact hne ⟨z, (hmem p z).2 ⟨⟨hz.1.1, hz.2⟩, hzI⟩, (hmem q z).2 ⟨⟨hz.1.2, hz.2⟩, hzI⟩⟩
  have ha : a ≠ ⊤ := by
    rintro rfl
    have h := hconn ⊤ le_rfl (by
      rw [ringKrullDim_eq_bot_of_subsingleton]
      exact WithBot.bot_lt_coe _)
    simpa using h.nonempty
  obtain ⟨p₀, hp₀, -⟩ := Ideal.exists_minimalPrimes_le (I := a) (J := maximalIdeal R)
    (le_maximalIdeal ha)
  have key : ∀ q, Relation.ReflTransGen (fun x y : Ideal R => x ∈ a.minimalPrimes ∧
      y ∈ a.minimalPrimes ∧ ReciprocityTheory.CA.Linked R ((k + 1 : ℕ) : WithBot ℕ∞) x y) p₀ q →
      ∃ t, t ⊆ X a ∧ X p₀ ⊆ t ∧ X q ⊆ t ∧ IsConnected t := by
    intro q hq
    induction hq with
    | refl => exact ⟨X p₀, hsub _ hp₀, le_rfl, le_rfl, hXc _ hp₀⟩
    | @tail b c _ hbc ih =>
      obtain ⟨t, h1, h2, h3, h4⟩ := ih
      refine ⟨t ∪ X c, Set.union_subset h1 (hsub _ hbc.2.1), h2.trans Set.subset_union_left,
        Set.subset_union_right, h4.union ?_ (hXc _ hbc.2.1)⟩
      exact (hmeet b c hbc.2.2).mono (Set.inter_subset_inter_left _ h3)
  obtain ⟨x, hx⟩ := (hXc _ hp₀).nonempty
  change IsConnected (X a)
  refine ⟨⟨x, hsub _ hp₀ hx⟩, isPreconnected_of_forall x fun y hy => ?_⟩
  have hy' := (hmem a y).1 hy
  obtain ⟨q, hq, hqy⟩ := Ideal.exists_minimalPrimes_le (I := a) (J := y.asIdeal) hy'.1.1
  obtain ⟨t, h1, h2, h3, h4⟩ := key q (chain a _ hconn p₀ hp₀ q hq)
  exact ⟨t, h1, h2 hx, h3 ((hmem q y).2 ⟨⟨hqy, hy'.1.2⟩, hy'.2⟩), h4.isPreconnected⟩
end

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem iter_cancel (n : ℕ) (x : WithBot ℕ∞)
    (h : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ x + ((1 : ℕ) : WithBot ℕ∞)) : (n : WithBot ℕ∞) ≤ x := by
  induction x using WithBot.recBotCoe with
  | bot => simp at h
  | coe y =>
    induction y using ENat.recTopCoe with
    | top => exact le_top
    | coe m =>
      have h' : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ ((m + 1 : ℕ) : WithBot ℕ∞) := by
        simpa using h
      have h'' : n + 1 ≤ m + 1 := by exact_mod_cast h'
      have h3 : n ≤ m := by omega
      exact_mod_cast h3

private theorem iter_min {R : Type} [CommRing R] (a b q : Ideal R)
    (hq : q ∈ (a ⊔ b).minimalPrimes) : ∃ p ∈ a.minimalPrimes, q ∈ (p ⊔ b).minimalPrimes := by
  have hqp : q.IsPrime := hq.1.1
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (show a ≤ q from le_sup_left.trans hq.1.2)
  refine ⟨p, hp, ⟨hqp, sup_le hpq (le_sup_right.trans hq.1.2)⟩, ?_⟩
  rintro r ⟨hr, hr'⟩ hrq
  exact hq.2 ⟨hr, sup_le (hp.1.2.trans (le_sup_left.trans hr')) (le_sup_right.trans hr')⟩ hrq

private theorem iter_lemma (m n : ℕ) (x : WithBot ℕ∞)
    (h : ((n + m : ℕ) : WithBot ℕ∞) ≤ x + (m : WithBot ℕ∞)) : (n : WithBot ℕ∞) ≤ x := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
    apply ih
    apply iter_cancel
    have e : ((m + 1 : ℕ) : WithBot ℕ∞) = (m : WithBot ℕ∞) + ((1 : ℕ) : WithBot ℕ∞) := by push_cast; rfl
    rw [e, ← add_assoc] at h
    simpa [Nat.add_assoc, add_assoc] using h

theorem UpperTheory.V.AlgebraTools.Conn.iter :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R], CohenType R → ∀ (a : Ideal R) (s : Finset R) (k : ℕ),
      (∀ f ∈ s, f ∈ maximalIdeal R) → ConnOn a ((k + s.card : ℕ) : WithBot ℕ∞) →
      (∀ p ∈ a.minimalPrimes, ((k + s.card + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p)) →
      ConnOn (a ⊔ Ideal.span (s : Set R)) k := by
  classical
  intro R _ _ _ hC a s
  induction s using Finset.induction_on with
  | empty =>
    intro k _ hc _
    simpa using hc
  | insert f s hf ih =>
    intro k hs hc hmin
    rw [Finset.card_insert_of_notMem hf] at hc hmin
    have e : a ⊔ Ideal.span ((↑(insert f s) : Set R)) = (a ⊔ Ideal.span (s : Set R)) ⊔ Ideal.span {f} := by
      rw [Finset.coe_insert, Ideal.span_insert, sup_comm (Ideal.span {f}), sup_assoc]
    rw [e]
    have h1 : ConnOn (a ⊔ Ideal.span (s : Set R)) ((k + 1 : ℕ) : WithBot ℕ∞) := by
      refine ih (k + 1) (fun g hg => hs g (Finset.mem_insert_of_mem hg)) ?_ ?_
      · have e1 : k + 1 + s.card = k + (s.card + 1) := by omega
        rw [e1]; exact hc
      · intro p hp
        have e1 : k + 1 + s.card + 1 = k + (s.card + 1) + 1 := by omega
        rw [e1]; exact hmin p hp
    refine step hC _ f k (hs f (Finset.mem_insert_self f s)) h1 ?_
    intro q hq
    obtain ⟨p, hp, hq'⟩ := iter_min a _ q hq
    have hd := compDim hC p q s hp.1.1 hq'
    have hk := hmin p hp
    have e2 : k + (s.card + 1) + 1 = (k + 2) + s.card := by omega
    rw [e2] at hk
    have := iter_lemma s.card (k + 2) _ (hk.trans hd)
    push_cast at this
    exact this
end

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem dim_of_univ {R : Type} [CommRing R] (I : Ideal R)
    (h : PrimeSpectrum.zeroLocus (I : Set R) = Set.univ) :
    ringKrullDim (R ⧸ I) = ringKrullDim R := by
  rw [ringKrullDim_quotient, h]
  exact Order.krullDim_eq_of_orderIso OrderIso.Set.univ

private theorem connOn_irr {R : Type} [CommRing R] [IrreducibleSpace (PrimeSpectrum R)]
    (j : WithBot ℕ∞) (hj : j ≤ ringKrullDim R) : ConnOn (⊥ : Ideal R) j := by
  intro I _ hI
  rw [PrimeSpectrum.zeroLocus_bot, ← Set.compl_eq_univ_diff]
  have hne : (PrimeSpectrum.zeroLocus (I : Set R))ᶜ.Nonempty := by
    rw [Set.nonempty_compl]
    intro h
    rw [dim_of_univ I h] at hI
    exact absurd hj (not_le.mpr hI)
  have ho : IsOpen (PrimeSpectrum.zeroLocus (I : Set R))ᶜ :=
    (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl
  have hp : IsPreirreducible (PrimeSpectrum.zeroLocus (I : Set R))ᶜ :=
    (PreirreducibleSpace.isPreirreducible_univ).open_subset ho (Set.subset_univ _)
  exact ⟨hne, hp.isPreconnected⟩

private theorem dim_min {R : Type} [CommRing R] [IrreducibleSpace (PrimeSpectrum R)]
    (p : Ideal R) (hp : p ∈ (⊥ : Ideal R).minimalPrimes) :
    ringKrullDim (R ⧸ p) = ringKrullDim R := by
  have hn : (nilradical R).IsPrime :=
    PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp inferInstance
  have hpp : p.IsPrime := hp.1.1
  have hle : p ≤ nilradical R := hp.2 ⟨hn, bot_le⟩ (nilradical_le_prime p)
  apply dim_of_univ
  refine Set.eq_univ_of_forall fun q => ?_
  rw [PrimeSpectrum.mem_zeroLocus]
  exact hle.trans (nilradical_le_prime q.asIdeal)

private theorem connOn_rad {R : Type} [CommRing R] (a b : Ideal R) (k : WithBot ℕ∞)
    (hab : a.radical = b.radical) (h : ConnOn a k) : ConnOn b k := by
  intro I hbI hI
  have hz : PrimeSpectrum.zeroLocus (a : Set R) = PrimeSpectrum.zeroLocus (b : Set R) := by
    rw [← PrimeSpectrum.zeroLocus_radical a, hab, PrimeSpectrum.zeroLocus_radical]
  have haI : a ≤ I.radical :=
    Ideal.le_radical.trans (hab.le.trans (Ideal.radical_mono hbI))
  have hd : ringKrullDim (R ⧸ I.radical) = ringKrullDim (R ⧸ I) := by
    rw [ringKrullDim_quotient, ringKrullDim_quotient, PrimeSpectrum.zeroLocus_radical]
  have := h I.radical haI (hd ▸ hI)
  rwa [hz, PrimeSpectrum.zeroLocus_radical] at this

theorem UpperTheory.V.AlgebraTools.Conn.main :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IrreducibleSpace (PrimeSpectrum R)], CohenType R →
      ∀ (a : Ideal R) (h k : ℕ), a ≠ ⊤ → ReciprocityTheory.CA.AraLE a h → ((k + h + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R →
        ReciprocityTheory.CA.ConnInDim (R ⧸ a) k := by
  intro R _ _ _ _ hC a h k ha ⟨s, hs, hrad⟩ hdim
  have h1 : ((k + s.card + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R :=
    le_trans (by exact_mod_cast (by omega : k + s.card + 1 ≤ k + h + 1)) hdim
  have h0 : ((k + s.card : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R :=
    le_trans (by exact_mod_cast (by omega : k + s.card ≤ k + s.card + 1)) h1
  have hm : ∀ f ∈ s, f ∈ maximalIdeal R := by
    intro f hf
    have h2 : f ∈ a.radical := hrad ▸ Ideal.le_radical (Ideal.subset_span hf)
    exact le_maximalIdeal (fun ht => ha (Ideal.radical_eq_top.mp ht)) h2
  have key := UpperTheory.V.AlgebraTools.Conn.iter hC ⊥ s k hm (connOn_irr _ h0)
    (fun p hp => (dim_min p hp).symm ▸ h1)
  rw [bot_sup_eq] at key
  exact (UpperTheory.V.AlgebraTools.Conn.bridge a k).mp (connOn_rad _ _ _ hrad key)
end

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.clConn :
    ∀ {O R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
      [CommRing R] [IsLocalRing R] [Algebra O R] [IrreducibleSpace (PrimeSpectrum R)], UpperTheory.V.CA.IsCL O R → ∀ (a : Ideal R) (h k : ℕ), a ≠ ⊤ →
      ReciprocityTheory.CA.AraLE a h → ((k + h + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R → ReciprocityTheory.CA.ConnInDim (R ⧸ a) k := by
  intro O R _ _ _ _ _ _ _ _ hR a h k ha hh hd
  haveI := hR.noeth
  exact UpperTheory.V.AlgebraTools.Conn.main (UpperTheory.V.AlgebraTools.Conn.cohen hR) a h k ha hh hd
end

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.clChain :
    ∀ {O R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
      [CommRing R] [IsLocalRing R] [Algebra O R] [IrreducibleSpace (PrimeSpectrum R)], UpperTheory.V.CA.IsCL O R → ∀ (a : Ideal R) (h k : ℕ), a ≠ ⊤ →
      ReciprocityTheory.CA.AraLE a h → ((k + h + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R →
      ∀ p ∈ a.minimalPrimes, ∀ q ∈ a.minimalPrimes,
        Relation.ReflTransGen (fun x y : Ideal R => x ∈ a.minimalPrimes ∧ y ∈ a.minimalPrimes ∧ ReciprocityTheory.CA.Linked R k x y) p q := by
  intro O R _ _ _ _ _ _ _ _ hCL a h k ha hara hdim p hp q hq
  haveI : IsNoetherianRing R := hCL.noeth
  exact chain a (k : WithBot ℕ∞) ((bridge a _).2 (clConn hCL a h k ha hara hdim)) p hp q hq
