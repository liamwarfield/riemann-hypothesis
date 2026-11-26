module

public import ReciprocityTheory.ClassFieldTheory.LocalClassField.InflationH2InjectiveOfSameRamification
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.CyclicBr

@[expose] public section

section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.Brauer
section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.InvRes
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

noncomputable def trivPull {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (φ : G' →* G)
    (hφ : Continuous φ) (A : Type) [AddCommGroup A] : Pair (trivRep G A) (trivRep G' A) where
  φ := φ
  u := LinearMap.id
  φ_cont := hφ
  u_cont := continuous_of_discreteTopology
  equiv _ _ := rfl

theorem conn_trivPull {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] (φ : G' →* G) (hφ : Continuous φ) (δ δ')
    (hδ : Cx.IsConn (trivMap G (Int.castAddHom ℚ)).hom
      (trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom δ)
    (hδ' : Cx.IsConn (trivMap G' (Int.castAddHom ℚ)).hom
      (trivMap G' (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom δ') (n : ℕ) (x) :
    δ' n ((trivPull φ hφ QZ).hom.H n x) = (trivPull φ hφ ℤ).hom.H (n + 1) (δ n x) :=
  connNat_holds ℤ _ _ _ _ _ _ _ _ _ _ (trivPull φ hφ ℤ).hom (trivPull φ hφ ℚ).hom (trivPull φ hφ QZ).hom δ δ'
    (admissibility_holds ℤ G _ _ _ _ _ (admissible_int_rat_sequence G)) (admissibility_holds ℤ G' _ _ _ _ _ (admissible_int_rat_sequence G'))
    (fun _ _ => rfl) (fun _ _ => rfl) hδ hδ' n x

theorem cocycle_pow {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (x : (trivRep G QZ).coch.X 1) (hx : (trivRep G QZ).coch.d 1 x = 0)
    (g : G) (k : ℕ) : x.1 ![g ^ k] = k • x.1 ![g] := by
  obtain ⟨e, he⟩ := exists_h1_equiv_characters G
  rw [← he x hx, ← he x hx, ofMul_pow, map_nsmul]
  rfl

theorem resGK_mem_subG_Kur (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    (σ : GK p L) (hσ : σ ∈ subG p L (MaximalUnramifiedExtension p L)) : resGK h σ ∈ subG p K (MaximalUnramifiedExtension p K) :=
  fun x hx => hσ x (Kur_le_Kur L hK hL h hx)

noncomputable def invMap {R : Type} [CommRing R] {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] {M : TRep R G} {M' : TRep R G'} (Q : Pair M M') (N : Subgroup G)
    [N.Normal] (N' : Subgroup G') [N'.Normal] (hN : ∀ g ∈ N', Q.φ g ∈ N) :
    Pair (InflationRestrictionInvariants.invQ M N) (InflationRestrictionInvariants.invQ M' N') where
  φ := QuotientGroup.map N' N Q.φ hN
  u :=
    { toFun := fun x => ⟨Q.u x.1, fun g => by
        have h1 : M.rho (Q.φ g.1) x.1 = x.1 := x.2 ⟨Q.φ g.1, hN g.1 g.2⟩
        show M'.rho g.1 (Q.u x.1) = Q.u x.1
        rw [← Q.equiv, h1]⟩
      map_add' := fun x y => Subtype.ext (map_add Q.u x.1 y.1)
      map_smul' := fun r x => Subtype.ext (map_smul Q.u r x.1) }
  φ_cont := (QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff).2
    (continuous_quot_mk.comp Q.φ_cont)
  u_cont := Continuous.subtype_mk (Q.u_cont.comp continuous_subtype_val) _
  equiv g m := by
    induction g using QuotientGroup.induction_on with
    | H σ => exact Subtype.ext (Q.equiv σ m.1)

theorem invMap_φ {R : Type} [CommRing R] {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] {M : TRep R G} {M' : TRep R G'} (Q : Pair M M') (N : Subgroup G)
    [N.Normal] (N' : Subgroup G') [N'.Normal] (hN : ∀ g ∈ N', Q.φ g ∈ N) (σ : G') :
    (invMap Q N N' hN).φ (QuotientGroup.mk σ) = QuotientGroup.mk (Q.φ σ) := rfl

theorem invMap_u {R : Type} [CommRing R] {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] {M : TRep R G} {M' : TRep R G'} (Q : Pair M M') (N : Subgroup G)
    [N.Normal] (N' : Subgroup G') [N'.Normal] (hN : ∀ g ∈ N', Q.φ g ∈ N) (x : (InflationRestrictionInvariants.invQ M N).V) :
    ((invMap Q N N' hN).u x).1 = Q.u x.1 := rfl

theorem invMap_H {R : Type} [CommRing R] {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] {M : TRep R G} {M' : TRep R G'} (Q : Pair M M') (N : Subgroup G)
    [N.Normal] (N' : Subgroup G') [N'.Normal] (hN : ∀ g ∈ N', Q.φ g ∈ N) (n : ℕ) (x : (InflationRestrictionInvariants.invQ M N).H n) :
    Q.hom.H n ((InflationRestrictionInvariants.invP M N).hom.H n x) =
      (InflationRestrictionInvariants.invP M' N').hom.H n ((invMap Q N N' hN).hom.H n x) := by
  induction x using Cx.H_ind with
  | h x hx => exact Cx.cls_congr _ _ (Subtype.ext (funext fun _ => rfl))

noncomputable def urRes (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) :
    Pair (urT p K) (urT p L) :=
  invMap (resPair h) (subG p K (MaximalUnramifiedExtension p K)) (subG p L (MaximalUnramifiedExtension p L)) (resGK_mem_subG_Kur hK hL h)

theorem exists_urRes (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) :
    ∃ P : Pair (urT p K) (urT p L), (∀ σ : GK p L, P.φ (QuotientGroup.mk σ) = QuotientGroup.mk (resGK h σ)) ∧
      (∀ x, (P.u x).1 = x.1) ∧
      ∀ n x, (resPair h).hom.H n ((layerInf p K (MaximalUnramifiedExtension p K)).hom.H n x) =
        (layerInf p L (MaximalUnramifiedExtension p L)).hom.H n (P.hom.H n x) := by
  exact ⟨urRes hK hL h, invMap_φ (resPair h) _ _ _, invMap_u (resPair h) _ _ _, invMap_H (resPair h) _ _ _⟩

theorem vLayerMap_urRes (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    (x : (urT p K).V) (y : (urT p L).V) (hxy : y.1 = x.1) :
    vLayerMap p L (MaximalUnramifiedExtension p L) y = (eLK p K L : ℤ) • vLayerMap p K (MaximalUnramifiedExtension p K) x := by
  apply Int.cast_injective (α := ℝ)
  rw [vLayerMap_spec p (le_Kur (K := L)), smul_eq_mul, Int.cast_mul, vLayerMap_spec p (le_Kur (K := K)), eK_Kur p hK,
    eK_Kur p hL, eK_eq_mul p hL h, hxy]
  push_cast
  ring

theorem invUr_urRes (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    (P : Pair (urT p K) (urT p L)) (hφ : ∀ σ : GK p L, P.φ (QuotientGroup.mk σ) = QuotientGroup.mk (resGK h σ))
    (hu : ∀ x, (P.u x).1 = x.1) (x : (urT p K).H 2) :
    invUr p L (P.hom.H 2 x) = degLK p K L • invUr p K x := by
  obtain ⟨⟨δ, hδ, -⟩, -⟩ := lES_holds ℤ _ _ _ _ _
    (admissibility_holds ℤ (GalLK p K (MaximalUnramifiedExtension p K)) _ _ _ _ _ (admissible_int_rat_sequence (GalLK p K (MaximalUnramifiedExtension p K))))
  obtain ⟨⟨δ', hδ', -⟩, -⟩ := lES_holds ℤ _ _ _ _ _
    (admissibility_holds ℤ (GalLK p L (MaximalUnramifiedExtension p L)) _ _ _ _ _ (admissible_int_rat_sequence (GalLK p L (MaximalUnramifiedExtension p L))))
  obtain ⟨c, hc⟩ := (conn_int_rat_bijective _ δ hδ 1 one_pos).2 ((vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2 x)
  obtain ⟨χ, hχ, rfl⟩ := Cx.exists_cls c
  have h1 := invUr_eq hK δ hδ x χ hχ hc.symm
  have hv : (vLayer p L (MaximalUnramifiedExtension p L)).hom.H 2 (P.hom.H 2 x) =
      (eLK p K L : ℤ) • (trivPull P.φ P.φ_cont ℤ).hom.H 2 ((vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2 x) := by
    induction x using Cx.H_ind with
    | h z hz =>
      refine Cx.cls_congr _ _ (Subtype.ext (funext fun g => ?_))
      exact vLayerMap_urRes hK hL h _ _ (hu _)
  have hn := conn_trivPull P.φ P.φ_cont δ δ' hδ hδ' 1 (Cx.cls _ 1 χ hχ)
  rw [← hc] at hv
  have hd : (trivRep (GalLK p L (MaximalUnramifiedExtension p L)) QZ).coch.d 1
      ((eLK p K L : ℤ) • (trivPull P.φ P.φ_cont QZ).hom.f 1 χ) = 0 := by
    rw [map_smul, ← Cx.Hom.comm, hχ, map_zero, smul_zero]
  have h2 := invUr_eq hL δ' hδ' (P.hom.H 2 x) ((eLK p K L : ℤ) • (trivPull P.φ P.φ_cont QZ).hom.f 1 χ) hd
    (hv.trans ((congrArg ((eLK p K L : ℤ) • ·) hn.symm).trans (map_smul (δ' 1) _ _).symm))
  have h3 : ((eLK p K L : ℤ) • (trivPull P.φ P.φ_cont QZ).hom.f 1 χ).1 ![frobLK p L (MaximalUnramifiedExtension p L)] =
      eLK p K L • χ.1 ![P.φ (frobLK p L (MaximalUnramifiedExtension p L))] := by
    refine Eq.trans ?_ (natCast_zsmul _ _)
    refine congrArg ((eLK p K L : ℤ) • ·) (congrArg χ.1 (funext fun i => ?_))
    fin_cases i
    rfl
  have h4 : P.φ (frobLK p L (MaximalUnramifiedExtension p L)) = frobLK p K (MaximalUnramifiedExtension p K) ^ fLK p K L :=
    (hφ _).trans (resGK_frobK L hK hL h (qK_eq_pow_fLK p hL h))
  rw [h2, h3, h4, cocycle_pow χ hχ, h1, ← eLK_mul_fLK_eq_degLK p hL h]
  exact (mul_smul (eLK p K L) (fLK p K L) (χ.1 ![frobLK p K (MaximalUnramifiedExtension p K)] : QZ)).symm

theorem exists_res_ur (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    (x : (urT p K).H 2) : ∃ y : (urT p L).H 2,
      (resPair h).hom.H 2 ((layerInf p K (MaximalUnramifiedExtension p K)).hom.H 2 x) = (layerInf p L (MaximalUnramifiedExtension p L)).hom.H 2 y ∧
      invUr p L y = degLK p K L • invUr p K x := by
  obtain ⟨P, hφ, hu, hP⟩ := exists_urRes hK hL h
  exact ⟨P.hom.H 2 x, hP 2 x, invUr_urRes hK hL h P hφ hu x⟩

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.BrBound
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem card_le_mul_of_ker {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [Finite B] [Finite C] (f : A →+ B)
    (g : C → A) (hg : ∀ a, f a = 0 → ∃ c, g c = a) : Finite A ∧ Nat.card A ≤ Nat.card C * Nat.card B := by
  classical
  have hsec : ∀ x : A, ∃ c : C, g c = x - Function.invFun f (f x) := fun x => by
    apply hg
    rw [map_sub, sub_eq_zero]
    exact (Function.invFun_eq (f := f) ⟨x, rfl⟩).symm
  choose σ hσ using hsec
  have hinj : Injective fun x : A => (σ x, f x) := fun x y hxy => by
    have h1 : σ x = σ y := congrArg Prod.fst hxy
    have h2 : f x = f y := congrArg Prod.snd hxy
    have e1 := hσ x
    have e2 := hσ y
    rw [h1, h2] at e1
    exact sub_left_injective (e1.symm.trans e2)
  refine ⟨Finite.of_injective _ hinj, ?_⟩
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective _ hinj

theorem card_BrKer_le_mul {K' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ K') (h' : K' ≤ L)
    (h1 : Finite (BrKer h)) (h2 : Finite (BrKer h')) :
    Finite (BrKer (h.trans h')) ∧ Nat.card (BrKer (h.trans h')) ≤ Nat.card (BrKer h) * Nat.card (BrKer h') := by
  let f : BrKer (h.trans h') →+ BrKer h' :=
    { toFun := fun x => ⟨(resPair h).hom.H 2 x.1, by
        show (resPair h').hom.H 2 _ = 0
        rw [← resPair_trans]; exact x.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ _ _) }
  refine card_le_mul_of_ker f (fun c : BrKer h => ⟨c.1, ?_⟩) (fun a ha => ⟨⟨a.1, congrArg Subtype.val ha⟩, rfl⟩)
  show (resPair (h.trans h')).hom.H 2 c.1 = 0
  rw [resPair_trans h h', show (resPair h).hom.H 2 c.1 = 0 from c.2, map_zero]

theorem card_BrKer_cyclic (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] (g₀ : GalLK p K L) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) :
    Nat.card (BrKer h) = degLK p K L := by
  rw [BrKer_eq_BrLK hL h, card_BrLK, card_h2_cyclic_layer hK hL h g₀ hg]

theorem card_BrKer_prime (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] (hp : (degLK p K L).Prime) : Nat.card (BrKer h) = degLK p K L := by
  have : Fact (degLK p K L).Prime := ⟨hp⟩
  have hc : IsCyclic (GalLK p K L) := isCyclic_of_prime_card (p := degLK p K L) card_GalLK
  obtain ⟨g₀, hg⟩ := hc.exists_generator
  exact card_BrKer_cyclic hK hL h g₀ hg

theorem exists_field_of_quotient (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] (N : Subgroup (GalLK p K L)) :
    ∃ K' : IntermediateField ℚ_[p] (PadicAlgCl p), K ≤ K' ∧ K' ≤ L ∧ FiniteDimensional ℚ_[p] K' ∧
      subG p K K' = N.comap (QuotientGroup.mk' (subG p K L)) ∧ degLK p K K' = N.index := by
  have hle : subG p K L ≤ N.comap (QuotientGroup.mk' (subG p K L)) := fun σ hσ => by
    rw [Subgroup.mem_comap]
    have : QuotientGroup.mk' (subG p K L) σ = 1 := (QuotientGroup.eq_one_iff σ).2 hσ
    rw [this]; exact N.one_mem
  obtain ⟨K', h1, h2, h3⟩ := exists_subG_eq_of_isOpen hK (N.comap (QuotientGroup.mk' (subG p K L)))
    (Subgroup.isOpen_mono hle (isOpen_subG hL))
  refine ⟨K', h1, ?_, h2, h3, ?_⟩
  · have := (subG_le_iff (L' := L) h1).1 (h3 ▸ hle)
    rwa [sup_eq_right.2 h] at this
  · show (subG p K K').index = _
    rw [h3, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem card_BrKer_le_of_prime_pow (l : ℕ) (hl : l.Prime) (k : ℕ) :
    ∀ (K L : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → FiniteDimensional ℚ_[p] L →
      ∀ h : K ≤ L, (subG p K L).Normal → degLK p K L = l ^ k →
        Finite (BrKer h) ∧ Nat.card (BrKer h) ≤ l ^ k := by
  have : Fact l.Prime := ⟨hl⟩
  induction k with
  | zero =>
    intro K L hK hL h hn hd
    have hs : Subsingleton (BrKer h) := ⟨fun x y => by
      have h0 : ∀ z : BrKer h, z = 0 := fun z => Subtype.ext (by
        have := degLK_smul_eq_zero hL h z.1 z.2
        rwa [hd, pow_zero, one_smul] at this)
      rw [h0 x, h0 y]⟩
    exact ⟨inferInstance, by rw [Nat.card_unique]; simp⟩
  | succ k ih =>
    intro K L hK hL h hn hd
    have hfin := finite_GalLK (K := K) hL
    have hcard : Nat.card (GalLK p K L) = l ^ (k + 1) := hd
    have hnt : Nontrivial (GalLK p K L) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hcard]
      exact Nat.one_lt_pow (Nat.succ_ne_zero k) hl.one_lt
    obtain ⟨N, hN, hNi⟩ := exists_normal_index_eq_prime l (IsPGroup.of_card hcard)
    obtain ⟨K', h1, h2, h3, h4, h5⟩ := exists_field_of_quotient hK hL h N
    have hn1 : (subG p K K').Normal := by rw [h4]; infer_instance
    have hn2 : (subG p K' L).Normal := subG_normal_of_le h1 h hn
    have hd1 : degLK p K K' = l := h5.trans hNi
    have hd2 : degLK p K' L = l ^ k := by
      have := degLK_mul h1 h2
      rw [hd, hd1, pow_succ'] at this
      exact (Nat.eq_of_mul_eq_mul_left hl.pos this).symm
    have hc1 : Nat.card (BrKer h1) = l := by
      rw [card_BrKer_prime hK h3 h1 (hd1 ▸ hl), hd1]
    have hf1 : Finite (BrKer h1) := Nat.finite_of_card_ne_zero (hc1 ▸ hl.ne_zero)
    obtain ⟨hf2, hc2⟩ := ih K' L h3 hL h2 hn2 hd2
    obtain ⟨hf, hc⟩ := card_BrKer_le_mul h1 h2 hf1 hf2
    refine ⟨hf, hc.trans ?_⟩
    rw [hc1, pow_succ']
    exact Nat.mul_le_mul_left _ hc2

theorem card_le_of_primary {A : Type*} [AddCommGroup A] (n : ℕ) (hn : 0 < n) (hA : ∀ a : A, n • a = 0)
    (h : ∀ l : ℕ, l.Prime → Finite {a : A // ∃ k : ℕ, l ^ k • a = 0} ∧
      Nat.card {a : A // ∃ k : ℕ, l ^ k • a = 0} ≤ l ^ n.factorization l) :
    Finite A ∧ Nat.card A ≤ n := by
  classical
  let T : n.primeFactors → Type _ := fun l => {a : A // ∃ k : ℕ, l.1 ^ k • a = 0}
  have hfin : ∀ l, Finite (T l) := fun l => (h l.1 (Nat.prime_of_mem_primeFactors l.2)).1
  let F : A → ∀ l, T l := fun a l => ⟨(n / l.1 ^ n.factorization l.1) • a, n.factorization l.1, by
    rw [smul_smul, Nat.mul_div_cancel' (Nat.ordProj_dvd n l.1)]; exact hA a⟩
  have hF0 : ∀ a : A, (∀ l : n.primeFactors, (n / l.1 ^ n.factorization l.1) • a = 0) → a = 0 := fun a ha => by
    rw [← AddMonoid.addOrderOf_eq_one_iff]
    by_contra hne
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
    have hqn : q ∣ n := hqd.trans (addOrderOf_dvd_of_nsmul_eq_zero (hA a))
    have hmem : q ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hq, hqn, hn.ne'⟩
    exact Nat.not_dvd_ordCompl hq hn.ne' (hqd.trans (addOrderOf_dvd_of_nsmul_eq_zero (ha ⟨q, hmem⟩)))
  have hinj : Injective F := fun a b hab => by
    rw [← sub_eq_zero]
    refine hF0 _ fun l => ?_
    rw [smul_sub, sub_eq_zero]
    exact congrArg Subtype.val (congrFun hab l)
  refine ⟨Finite.of_injective F hinj, (Nat.card_le_card_of_injective F hinj).trans ?_⟩
  rw [Nat.card_pi]
  calc ∏ l : n.primeFactors, Nat.card (T l) ≤ ∏ l : n.primeFactors, l.1 ^ n.factorization l.1 :=
        Finset.prod_le_prod' fun l _ => (h l.1 (Nat.prime_of_mem_primeFactors l.2)).2
    _ = n := by
        rw [Finset.prod_coe_sort n.primeFactors (fun l => l ^ n.factorization l)]
        exact Nat.prod_factorization_pow_eq_self hn.ne'

theorem exists_sylow_field (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] (l : ℕ) (hl : l.Prime) :
    ∃ K' : IntermediateField ℚ_[p] (PadicAlgCl p), K ≤ K' ∧ K' ≤ L ∧
      degLK p K' L = l ^ (degLK p K L).factorization l ∧ ¬ l ∣ degLK p K K' := by
  have : Fact l.Prime := ⟨hl⟩
  have hfin := finite_GalLK (K := K) hL
  obtain ⟨S⟩ : Nonempty (Sylow l (GalLK p K L)) := inferInstance
  obtain ⟨K', h1, h2, h3, h4, h5⟩ := exists_field_of_quotient hK hL h (S : Subgroup (GalLK p K L))
  refine ⟨K', h1, h2, ?_, h5 ▸ S.not_dvd_index⟩
  have e1 := degLK_mul h1 h2
  have e2 : (S : Subgroup (GalLK p K L)).index * Nat.card (S : Subgroup (GalLK p K L)) = degLK p K L :=
    (S : Subgroup (GalLK p K L)).index_mul_card
  rw [h5, ← e2] at e1
  have e3 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)) e1
  rw [← e3, S.card_eq_multiplicity]
  rfl

theorem finiteDimensional_of_le' {K' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K' ≤ L)
    (hL : FiniteDimensional ℚ_[p] L) : FiniteDimensional ℚ_[p] K' :=
  FiniteDimensional.of_injective (IntermediateField.inclusion h).toLinearMap (IntermediateField.inclusion h).injective

theorem eq_of_resPair_eq_of_coprime {K' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hK' : FiniteDimensional ℚ_[p] K')
    (h : K ≤ K') (l : ℕ) (hl : l.Prime) (hd : ¬ l ∣ degLK p K K') (x y : Br p K) (kx ky : ℕ) (hx : l ^ kx • x = 0)
    (hy : l ^ ky • y = 0) (hxy : (resPair h).hom.H 2 x = (resPair h).hom.H 2 y) : x = y := by
  rw [← sub_eq_zero]
  refine eq_zero_of_mem_BrKer_of_coprime hK' h _ ?_ (l ^ (kx + ky)) ?_
    (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hl).2 hd))
  · exact (map_sub ((resPair h).hom.H 2) x y).trans (sub_eq_zero.2 hxy)
  · rw [smul_sub, pow_add, mul_comm, mul_smul, hx, smul_zero, mul_comm, mul_smul, hy, smul_zero, sub_zero]

theorem card_BrKer_le (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] : Finite (BrKer h) ∧ Nat.card (BrKer h) ≤ degLK p K L := by
  refine card_le_of_primary (degLK p K L) (degLK_pos hL)
    (fun a => Subtype.ext (degLK_smul_eq_zero hL h a.1 a.2)) fun l hl => ?_
  obtain ⟨K', h1, h2, h3, h4⟩ := exists_sylow_field hK hL h l hl
  have hK' := finiteDimensional_of_le' h2 hL
  obtain ⟨hf, hc⟩ := card_BrKer_le_of_prime_pow l hl _ K' L hK' hL h2 (subG_normal_of_le h1 h inferInstance) h3
  let F : {a : BrKer h // ∃ k : ℕ, l ^ k • a = 0} → BrKer h2 := fun a => ⟨(resPair h1).hom.H 2 a.1.1, by
    show (resPair h2).hom.H 2 _ = 0
    rw [← resPair_trans h1 h2]; exact a.1.2⟩
  have hinj : Injective F := fun a b hab => by
    obtain ⟨ka, hka⟩ := a.2
    obtain ⟨kb, hkb⟩ := b.2
    exact Subtype.ext (Subtype.ext (eq_of_resPair_eq_of_coprime hK' h1 l hl h4 a.1.1 b.1.1 ka kb
      (congrArg Subtype.val hka) (congrArg Subtype.val hkb) (congrArg Subtype.val hab)))
  exact ⟨Finite.of_injective F hinj, (Nat.card_le_card_of_injective F hinj).trans hc⟩

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem layerInf_Kur_mem_BrLK_Kn_iff (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (z : (urT p K).H 2) :
    (layerInf p K (MaximalUnramifiedExtension p K)).hom.H 2 z ∈ BrLK p K (Kn p K n) ↔ n • z = 0 := by
  rw [← mem_range_layerInfl_Kn_iff hK hn]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, layer_inflation_h2_injective ((layerInf_layerInfl (Kn_le_Kur hn) 2 y).trans hy)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, (layerInf_layerInfl (Kn_le_Kur hn) 2 y).symm⟩

theorem BrLK_Kn_le_BrKer (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) :
    BrLK p K (Kn p K (degLK p K L)) ≤ BrKer h := by
  have hn : 0 < degLK p K L := degLK_pos hL
  intro x hx
  obtain ⟨z, rfl⟩ := BrLK_mono (Kn_le_Kur hn) hx
  have hz : degLK p K L • z = 0 := (layerInf_Kur_mem_BrLK_Kn_iff hK hn z).1 hx
  obtain ⟨y, hy, hinv⟩ := exists_res_ur hK hL h z
  rw [← map_nsmul, hz, map_zero] at hinv
  have hy0 : y = 0 := (invUr_bijective hL).1 (hinv.trans (map_zero _).symm)
  exact hy.trans (by rw [hy0, map_zero])

theorem BrKer_eq_BrLK_Kn (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] : BrKer h = BrLK p K (Kn p K (degLK p K L)) := by
  have hn : 0 < degLK p K L := degLK_pos hL
  obtain ⟨hfin, hcard⟩ := card_BrKer_le hK hL h
  have hle := BrLK_Kn_le_BrKer hK hL h
  have hc : Nat.card (BrLK p K (Kn p K (degLK p K L))) = degLK p K L := by
    rw [card_BrLK, card_h2_unramified_layer hK hn]
  have hset : (BrLK p K (Kn p K (degLK p K L)) : Set (Br p K)) = (BrKer h : Set (Br p K)) := by
    refine Set.eq_of_subset_of_ncard_le hle ?_ hfin
    show Nat.card (BrKer h) ≤ Nat.card (BrLK p K (Kn p K (degLK p K L)))
    rw [hc]; exact hcard
  exact (SetLike.coe_injective hset).symm

theorem inflation_unramified_closure_h2_bijective (hK : FiniteDimensional ℚ_[p] K) :
    Bijective ((layerInf p K (MaximalUnramifiedExtension p K)).hom.H 2) := by
  refine ⟨layer_inflation_h2_injective, fun x => ?_⟩
  obtain ⟨L, h, hL, hN, hx⟩ := exists_mem_BrKer hK x
  rw [BrKer_eq_BrLK_Kn hK hL h] at hx
  exact BrLK_mono (Kn_le_Kur (degLK_pos hL)) hx


open Classical in
variable (p K) in
noncomputable def invBr : Br p K →+ QZ :=
  if h : ∃ f : Br p K →+ QZ, ∀ x, f ((layerInf p K (MaximalUnramifiedExtension p K)).hom.H 2 x) = invUr p K x then h.choose else 0

theorem invBr_layerInf (hK : FiniteDimensional ℚ_[p] K) (x : (urT p K).H 2) :
    invBr p K ((layerInf p K (MaximalUnramifiedExtension p K)).hom.H 2 x) = invUr p K x := by
  have h : ∃ f : Br p K →+ QZ, ∀ x, f ((layerInf p K (MaximalUnramifiedExtension p K)).hom.H 2 x) = invUr p K x := by
    let e := LinearEquiv.ofBijective ((layerInf p K (MaximalUnramifiedExtension p K)).hom.H 2) (inflation_unramified_closure_h2_bijective hK)
    refine ⟨(invUr p K).comp e.symm.toAddEquiv.toAddMonoidHom, fun x => ?_⟩
    show invUr p K (e.symm (e x)) = _
    rw [LinearEquiv.symm_apply_apply]
  unfold invBr
  rw [dite_eq_left h]
  exact h.choose_spec x

theorem invBr_bijective (hK : FiniteDimensional ℚ_[p] K) : Bijective (invBr p K) := by
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := (inflation_unramified_closure_h2_bijective hK).2 x
    obtain ⟨b, rfl⟩ := (inflation_unramified_closure_h2_bijective hK).2 y
    rw [invBr_layerInf hK, invBr_layerInf hK] at hxy
    rw [(invUr_bijective hK).1 hxy]
  · intro q
    obtain ⟨a, rfl⟩ := (invUr_bijective hK).2 q
    exact ⟨_, invBr_layerInf hK a⟩

theorem invBr_res (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (x : Br p K) :
    invBr p L ((resPair h).hom.H 2 x) = degLK p K L • invBr p K x := by
  obtain ⟨z, rfl⟩ := (inflation_unramified_closure_h2_bijective hK).2 x
  obtain ⟨y, hy, hinv⟩ := exists_res_ur hK hL h z
  rw [hy, invBr_layerInf hL, invBr_layerInf hK, hinv]


end ReciprocityTheory.DiscreteGroups.LocalClassField
end

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

def IsPairClass (a : (kbarT p K).V) (χ : charGrp (GK p K)) (c : Br p K) : Prop :=
  ∃ (t : GK p K → ℚ) (m : (Fin 2 → GK p K) → ℤ) (z : (kbarT p K).coch.X 2) (hz : (kbarT p K).coch.d 2 z = 0),
    IsLocallyConstant t ∧ (∀ g, (QuotientAddGroup.mk (t g) : QZ) = χ.1 (Additive.ofMul g)) ∧
    (∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) ∧ (∀ g, z.1 g = m g • a) ∧
    c = (kbarT p K).coch.cls 2 z hz


open Classical in
def pairBr (a : Kˣ) (χ : charGrp (GK p K)) : Br p K :=
  if h : ∃ c, IsPairClass p K (ofK p K (Additive.ofMul a)) χ c then h.choose else 0

def pairK (a : Kˣ) (χ : charGrp (GK p K)) : QZ := invBr p K (pairBr p K a χ)


variable {p K L} in
def resChar (h : K ≤ L) : charGrp (GK p K) →+ charGrp (GK p L) where
  toFun χ := ⟨χ.1.comp (MonoidHom.toAdditive (resGK h)),
    (show IsLocallyConstant fun g : GK p K => χ.1 (Additive.ofMul g) from χ.2).comp_continuous
      (resGK_continuous h)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

def TrivOn (χ : charGrp (GK p K)) : Prop := ∀ g ∈ subG p K L, χ.1 (Additive.ofMul g) = 0

def IsRecip (a : Kˣ) (g : GK p K) : Prop :=
  ∀ χ : charGrp (GK p K), TrivOn p K L χ → χ.1 (Additive.ofMul g) = pairK p K a χ

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
