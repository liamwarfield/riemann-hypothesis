module

public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RestrictedMultiplicativeH1Subsingleton
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.EqZeroOfResEqZeroOfCoprime
public import ReciprocityTheory.GroupCohomology.LengthKerEqCoker
public import ReciprocityTheory.GroupCohomology.CupCor
public import ReciprocityTheory.GroupCohomology.RankLen

@[expose] public section

section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportDefs
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ValuativeRel

structure Model (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] (p : ℕ) [Fact p.Prime] where
  K' : IntermediateField ℚ_[p] (PadicAlgCl p)
  fin : FiniteDimensional ℚ_[p] K'
  e : K ≃+* K'
  E : AlgebraicClosure K ≃+* PadicAlgCl p
  comm : ∀ x, E (algebraMap K (AlgebraicClosure K) x) = (e x : PadicAlgCl p)
  homeo : IsHomeomorph e
  int : ∀ x, x ∈ 𝒪[K] ↔ ‖(e x : PadicAlgCl p)‖ ≤ 1

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] {p : ℕ} [Fact p.Prime]

def Model.IsGalIso (m : Model K p) (φ : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) ≃* GK p m.K') : Prop :=
  ∀ σ x, φ σ (m.E x) = m.E (σ x)

def Model.Corr (m : Model K p) (L : IntermediateField K (AlgebraicClosure K))
    (L' : IntermediateField ℚ_[p] (PadicAlgCl p)) : Prop := ∀ x, m.E x ∈ L' ↔ x ∈ L

noncomputable def Model.eU (m : Model K p) : Kˣ ≃* (m.K')ˣ := Units.mapEquiv m.e.toMulEquiv

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.EqZeroOfMemBrKerOfCoprime
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem layer_inflation_h2_injective [(subG p K L).Normal] : Injective ((layerInf p K L).hom.H 2) :=
  multiplicative_inflation_h2_injective p K (subG p K L) (isClosed_subG p K L) _ _ (InflationRestrictionInvariants.invariants_isInvRep _ _)

theorem layerInf_layerInfl {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : L ≤ L') [(subG p K L).Normal]
    [(subG p K L').Normal] (n : ℕ) (x : (layer p K L).H n) :
    (layerInf p K L').hom.H n ((layerInfl h).hom.H n x) = (layerInf p K L).hom.H n x := by
  induction x using Cx.H_ind with
  | h x hx => rfl

theorem BrLK_mono {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : L ≤ L') [(subG p K L).Normal]
    [(subG p K L').Normal] : BrLK p K L ≤ BrLK p K L' := by
  rintro _ ⟨x, rfl⟩
  exact ⟨(layerInfl h).hom.H 2 x, layerInf_layerInfl h 2 x⟩

theorem card_BrLK [(subG p K L).Normal] : Nat.card (BrLK p K L) = Nat.card ((layer p K L).H 2) :=
  (Nat.card_congr (LinearEquiv.ofInjective ((layerInf p K L).hom.H 2) layer_inflation_h2_injective).toEquiv).symm

theorem mem_BrKer_iff (h : K ≤ L) (x : Br p K) :
    x ∈ BrKer h ↔ (resP (kbarT p K) (subG p K L)).hom.H 2 x = 0 := by
  obtain ⟨e, he, hf⟩ := exists_resPair_factor h
  show (resPair h).hom.H 2 x = 0 ↔ _
  rw [hf 2 x]
  exact map_eq_zero_iff _ (he 2).1

theorem BrKer_eq_BrLK (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) [(subG p K L).Normal] :
    BrKer h = BrLK p K L := by
  ext x
  rw [mem_BrKer_iff]
  exact infRes2_exact (kbarT p K) (subG p K L) (isOpen_subG hL) _ _ (InflationRestrictionInvariants.invariants_isInvRep _ _)
    (restricted_multiplicative_h1_subsingleton p K _) x

theorem degLK_smul_eq_zero (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (x : Br p K) (hx : x ∈ BrKer h) :
    degLK p K L • x = 0 := by
  have := finiteIndex_subG (K := K) hL
  obtain ⟨cor, -, hcor⟩ := cor_holds ℤ (GK p K) (kbarT p K) (subG p K L) (isOpen_subG hL)
  have h2 := hcor 2 x
  rw [(mem_BrKer_iff h x).1 hx, map_zero] at h2
  exact h2.symm

theorem eq_zero_of_mem_BrKer_of_coprime (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (x : Br p K)
    (hx : x ∈ BrKer h) (k : ℕ) (hk : k • x = 0) (hc : Nat.Coprime k (degLK p K L)) : x = 0 := by
  have h1 := Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hk)
    (addOrderOf_dvd_of_nsmul_eq_zero (degLK_smul_eq_zero hL h x hx))
  rw [Nat.Coprime.gcd_eq_one hc, Nat.dvd_one] at h1
  exact AddMonoid.addOrderOf_eq_one_iff.1 h1

theorem exists_mem_BrKer (hK : FiniteDimensional ℚ_[p] K) (x : Br p K) :
    ∃ (L : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : K ≤ L), FiniteDimensional ℚ_[p] L ∧
      (subG p K L).Normal ∧ x ∈ BrKer h := by
  obtain ⟨N, hN, hNo, hx⟩ := FiniteLevelCohomology.exists_level (kbarT p K) 2 x
  obtain ⟨L, h, hL, rfl⟩ := exists_subG_eq_of_isOpen hK N hNo
  refine ⟨L, h, hL, hN, ?_⟩
  rw [BrKer_eq_BrLK hL h]
  exact hx _ _ (InflationRestrictionInvariants.invariants_isInvRep _ _)

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.UnramA
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.InflationOneCocycles

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

noncomputable section

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (N : Subgroup G) [N.Normal] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  (rho : Representation R G M)

def qRho (hN : ∀ σ ∈ N, ∀ m, rho σ m = m) : Representation R (G ⧸ N) M :=
  QuotientGroup.lift N rho (fun σ hσ => LinearMap.ext (hN σ hσ))

abbrev qT (hrho : ContAction rho) (hN : ∀ σ ∈ N, ∀ m, rho σ m = m) : TRep R (G ⧸ N) where
  V := M
  rho := qRho N rho hN
  cont := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    rw [← QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff]
    exact hrho.comp (continuous_id.prodMk continuous_const)

variable {N rho}

theorem exists_desc1 (hN : ∀ σ ∈ N, ∀ m, rho σ m = m) (c : G → M) (hc : c ∈ Z1 rho) (h0 : ∀ σ ∈ N, c σ = 0) :
    ∃ c' : G ⧸ N → M, c' ∈ ReciprocityTheory.Gal.Z1 (qRho N rho hN) ∧ ∀ g, c' (QuotientGroup.mk g) = c g := by
  have hw : ∀ a b : G, QuotientGroup.leftRel N a b → c a = c b := by
    intro a b hab
    have h1 : a⁻¹ * b ∈ N := QuotientGroup.leftRel_apply.1 hab
    have h2 := hc.2 a (a⁻¹ * b)
    rw [mul_inv_cancel_left, h0 _ h1, map_zero, add_zero] at h2
    exact h2.symm
  refine ⟨fun q => Quotient.liftOn' q c hw, ⟨?_, ?_⟩, fun g => rfl⟩
  · exact hc.1.quotient_liftOn' hw
  · intro a b
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective b
    exact hc.2 g h

theorem inflation_mem_one_cocycles (hN : ∀ σ ∈ N, ∀ m, rho σ m = m) (c' : G ⧸ N → M) (hc : c' ∈ ReciprocityTheory.Gal.Z1 (qRho N rho hN)) :
    (fun g : G => c' (QuotientGroup.mk g)) ∈ Z1 rho :=
  ⟨hc.1.comp QuotientGroup.continuous_mk, fun g h => hc.2 (QuotientGroup.mk g) (QuotientGroup.mk h)⟩

theorem apply_eq_zero_of_mem_H1ur (hN : ∀ σ ∈ N, ∀ m, rho σ m = m) (c : Z1 rho)
    (hc : (Submodule.Quotient.mk c : H1 rho) ∈ H1ur rho N) (σ : G) (hσ : σ ∈ N) : c.1 σ = 0 := by
  have h1 : (Submodule.Quotient.mk (restrictCocycles1 rho N.subtype continuous_subtype_val c) : H1 (rho.comp N.subtype)) = 0 := hc
  rw [Submodule.Quotient.mk_eq_zero] at h1
  obtain ⟨m, hm⟩ := (mem_contCoboundaries1 _ _).1 h1
  have h3 : c.1 σ = rho σ m - m := hm ⟨σ, hσ⟩
  rw [h3, hN σ hσ, sub_self]

theorem torsion_of_finite [Finite M] (m : M) : ∃ k : ℕ, 0 < k ∧ k • m = 0 :=
  ⟨Nat.card M, Nat.card_pos, card_nsmul_eq_zero'⟩

variable [CompactSpace (G ⧸ N)] [T2Space (G ⧸ N)] [TotallyDisconnectedSpace (G ⧸ N)] [Finite M]

theorem ker_frobenius_sub_id_eq_invariants (hrho : ContAction rho) (hN : ∀ σ ∈ N, ∀ m, rho σ m = m) {s : G}
    (hs : IsZHat (G ⧸ N) (QuotientGroup.mk s)) : LinearMap.ker (rho s - LinearMap.id) = H0 rho := by
  ext m
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, mem_riemannRochSpace_iff_regularAt_everywhere]
  refine ⟨fun h g => ?_, fun h => h s⟩
  set W := ProcyclicCohomology.stab (qT N rho hrho hN) m with hW
  have hWo : IsOpen (W : Set (G ⧸ N)) := ProcyclicCohomology.stab_isOpen (qT N rho hrho hN) m
  have hWc : IsClosed (W : Set (G ⧸ N)) := W.isClosed_of_isOpen hWo
  have hsW : (QuotientGroup.mk s : G ⧸ N) ∈ W := h
  have hz : (Subgroup.zpowers (QuotientGroup.mk s : G ⧸ N) : Set (G ⧸ N)) ⊆ W :=
    (Subgroup.zpowers_le.2 hsW)
  have htop : (W : Set (G ⧸ N)) = Set.univ := by
    rw [← hWc.closure_eq, ← Set.univ_subset_iff, ← hs.1.closure_eq]
    exact closure_mono hz
  have : (QuotientGroup.mk g : G ⧸ N) ∈ (W : Set (G ⧸ N)) := by rw [htop]; trivial
  exact this

theorem card_quot_range (u : M →ₗ[R] M) : Nat.card (M ⧸ LinearMap.range u) = Nat.card (LinearMap.ker u) := by
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range u)
  have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker u)
  rw [Nat.card_congr u.quotKerEquivRange.toEquiv] at h2
  have h3 : 0 < Nat.card (LinearMap.range u) := Nat.card_pos
  rw [h2, mul_comm] at h1
  exact (Nat.eq_of_mul_eq_mul_left h3 h1).symm

theorem card_H1ur (hrho : ContAction rho) (hN : ∀ σ ∈ N, ∀ m, rho σ m = m) {s : G}
    (hs : IsZHat (G ⧸ N) (QuotientGroup.mk s)) : Nat.card (H1ur rho N) = Nat.card (H0 rho) := by
  set P : Submodule R M := LinearMap.range (rho s - LinearMap.id) with hP
  let f : Z1 rho →ₗ[R] M ⧸ P := P.mkQ ∘ₗ ((LinearMap.proj s) ∘ₗ (Z1 rho).subtype)
  have hker : (Bd1 rho).comap (Z1 rho).subtype ≤ LinearMap.ker f := by
    intro c hc'
    obtain ⟨m, hm⟩ := (mem_contCoboundaries1 _ _).1 hc'
    rw [LinearMap.mem_ker]
    change (Submodule.Quotient.mk (c.1 s) : M ⧸ P) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨m, by simpa using (hm s).symm⟩
  let φ : H1 rho →ₗ[R] M ⧸ P := ((Bd1 rho).comap (Z1 rho).subtype).liftQ f hker
  have hφ : ∀ c : Z1 rho, φ (Submodule.Quotient.mk c) = Submodule.Quotient.mk (c.1 s) := fun c => rfl
  have hinj0 : ∀ z ∈ H1ur rho N, φ z = 0 → z = 0 := by
    intro z hz hz0
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨c', hc', hcc⟩ := exists_desc1 hN c.1 c.2 (apply_eq_zero_of_mem_H1ur hN c hz)
    rw [hφ, Submodule.Quotient.mk_eq_zero] at hz0
    obtain ⟨m, hm⟩ := hz0
    have h1 : c' (QuotientGroup.mk s) = rho s m - m := by rw [hcc, ← hm]; rfl
    have h2 := ProcyclicCohomology.cocycle_eq_of_apply (qT N rho hrho hN) hs.1 c' hc' m h1
    rw [Submodule.Quotient.mk_eq_zero]
    refine (mem_contCoboundaries1 _ _).2 ⟨m, fun g => ?_⟩
    change c.1 g = _
    rw [← hcc]
    exact h2 (QuotientGroup.mk g)
  have hbij : Bijective (fun x : H1ur rho N => φ x.1) := by
    constructor
    · intro x y hxy
      have h1 : φ (x.1 - y.1) = 0 := by rw [map_sub]; exact sub_eq_zero.2 hxy
      exact Subtype.ext (sub_eq_zero.1 (hinj0 _ ((H1ur rho N).sub_mem x.2 y.2) h1))
    · intro y
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨c', hc', hcs⟩ := ProcyclicCohomology.exists_cocycle (qT N rho hrho hN) (ProcyclicCohomology.comm_of_dense hs.1) hs.1 hs.2 m
        (torsion_of_finite (M := M) m)
      have hZ := inflation_mem_one_cocycles hN c' hc'
      refine ⟨⟨Submodule.Quotient.mk ⟨_, hZ⟩, ?_⟩, ?_⟩
      · change (Submodule.Quotient.mk (restrictCocycles1 rho N.subtype continuous_subtype_val ⟨_, hZ⟩) :
          H1 (rho.comp N.subtype)) = 0
        rw [Submodule.Quotient.mk_eq_zero]
        refine (mem_contCoboundaries1 _ _).2 ⟨0, fun σ => ?_⟩
        change c' (QuotientGroup.mk σ.1) = _
        rw [(QuotientGroup.eq_one_iff σ.1).2 σ.2, map_zero, sub_zero]
        have h1 : c' (1 * 1) = c' 1 + qRho N rho hN 1 (c' 1) := hc'.2 1 1
        rw [mul_one, map_one, Module.End.one_apply] at h1
        exact left_eq_add.1 h1
      · change φ (Submodule.Quotient.mk _) = _
        rw [hφ]
        exact congrArg _ hcs
  rw [Nat.card_eq_of_bijective _ hbij, hP, card_quot_range, ker_frobenius_sub_id_eq_invariants hrho hN hs]

end

end ReciprocityTheory.DiscreteGroups.LocalClassField.InflationOneCocycles
end

section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.HSubsingletonOfUniquelyDivisible
section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.MemZmultiplesOfAddOrderOf
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 Function

namespace RationalModIntegerChains

open scoped Nat

variable {A : Type} [AddCommGroup A]

section Chain

variable {C : Type} [AddCommGroup C]

end Chain

theorem qz_torsion (x : QZ) : ∃ k : ℕ, 0 < k ∧ k • x = 0 := by
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
  refine ⟨q.den, q.den_pos, ?_⟩
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
  exact ⟨q.num, by
    show (q.num : ℚ) = _
    rw [nsmul_eq_mul, mul_comm, Rat.mul_den_eq_num]⟩

end RationalModIntegerChains

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Gal Function

noncomputable section

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem h_subsingleton_of_uniquely_divisible [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {R : Type} [CommRing R]
    (M : TRep R G) [DiscreteTopology M.V] (hM : ∀ k : ℕ, 0 < k → Bijective fun m : M.V => k • m)
    (n : ℕ) (hn : 0 < n) : Subsingleton (M.H n) := by
  suffices h : ∀ x : M.H n, x = 0 from ⟨fun x y => (h x).trans (h y).symm⟩
  intro x
  obtain ⟨-, h⟩ := finiteLevel_holds R G M n x
  obtain ⟨k, hk, hkx⟩ := h hn
  let e : M.V ≃ₗ[R] M.V := LinearEquiv.ofBijective ((k : R) • LinearMap.id) (by
    have := hM k hk
    convert this using 2 with m
    simp [Nat.cast_smul_eq_nsmul])
  have he : ∀ m, e m = (k : R) • m := fun m => rfl
  let Q : Pair M M := Pair.ofMap e.symm.toLinearMap continuous_of_discreteTopology (by
    intro g m
    apply e.injective
    show e (e.symm _) = e (M.rho g (e.symm m))
    rw [e.apply_symm_apply, he, ← map_smul, ← he, e.apply_symm_apply])
  have hQ : ∀ y : M.H n, (k : R) • Q.hom.H n y = y := by
    intro y
    induction y using Cx.H_ind with
    | h c hc =>
      rw [Cx.Hom.H_cls, Cx.cls_smul]
      refine Cx.cls_congr _ _ (Subtype.ext (funext fun g => ?_))
      exact e.apply_symm_apply _
  rw [← hQ x, ← map_smul, Nat.cast_smul_eq_nsmul, hkx, map_zero]

theorem h_subsingleton_of_divisible [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (M : TRep ℤ G) [DiscreteTopology M.V] (hM : ∀ k : ℕ, 0 < k → Bijective fun m : M.V => k • m)
    (n : ℕ) (hn : 0 < n) : Subsingleton (M.H n) :=
  h_subsingleton_of_uniquely_divisible G M hM n hn

theorem h_rat_subsingleton [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (n : ℕ) (hn : 0 < n) :
    Subsingleton ((trivRep G ℚ).H n) := by
  refine h_subsingleton_of_divisible G (trivRep G ℚ) (fun k hk => ?_) n hn
  show Bijective fun m : ℚ => k • m
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  refine ⟨fun a b h => ?_, fun y => ⟨y / k, ?_⟩⟩
  · simpa [nsmul_eq_mul, hk'] using h
  · simp only [nsmul_eq_mul]; field_simp

theorem admissible_int_rat_sequence : admitted (trivMap G (Int.castAddHom ℚ)) (trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · have hi : Injective (trivMap G (Int.castAddHom ℚ)).u := Int.cast_injective (α := ℚ)
    exact (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap continuous_of_discreteTopology hi
      fun _ _ => isOpen_discrete _).isEmbedding
  · intro (y : ℚ)
    show (QuotientAddGroup.mk y : QZ) = 0 ↔ y ∈ Set.range (Int.castAddHom ℚ)
    rw [QuotientAddGroup.eq_zero_iff]; rfl
  · exact ⟨Function.surjInv (QuotientAddGroup.mk'_surjective (Int.castAddHom ℚ).range),
      continuous_of_discreteTopology, Function.surjInv_eq _⟩

theorem conn_int_rat_bijective [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (δ : ∀ n, (trivRep G QZ).H n →ₗ[ℤ] (trivRep G ℤ).H (n + 1))
    (hδ : Cx.IsConn (trivMap G (Int.castAddHom ℚ)).hom
      (trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom δ) (n : ℕ) (hn : 0 < n) :
    Bijective (δ n) := by
  have hs := admissibility_holds ℤ G _ _ _ _ _ (admissible_int_rat_sequence G)
  obtain ⟨⟨δ', h1, h2⟩, hu⟩ := lES_holds ℤ _ _ _ _ _ hs
  obtain rfl := hu δ δ' hδ h1
  have s1 := h_rat_subsingleton G n hn
  have s2 := h_rat_subsingleton G (n + 1) n.succ_pos
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (h2.exC n x).1 hx
    rw [Subsingleton.elim y 0, map_zero]
  · intro y
    exact (h2.exA n y).1 (Subsingleton.elim _ _)

def oneCocycleEquivCharacters : Gal.Z1 (trivRep G QZ).rho ≃+ charGrp G where
  toFun c := ⟨AddMonoidHom.mk' (fun a : Additive G => (c.1 a.toMul : QZ)) fun a b => c.2.2 a.toMul b.toMul,
    (@IsLocallyConstant.iff_continuous G (trivRep G QZ).V _ _ _ c.1).2 c.2.1⟩
  invFun χ := ⟨fun g => χ.1 (Additive.ofMul g),
    (@IsLocallyConstant.iff_continuous G (trivRep G QZ).V _ _ _ _).1 χ.2,
    fun g h => map_add χ.1 (Additive.ofMul g) (Additive.ofMul h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem one_coboundaries_trivial_eq_bot (A : Type) [AddCommGroup A] : Gal.B1 (trivRep G A).rho = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨m, rfl⟩
  refine (Submodule.mem_bot _).2 (funext fun g => ?_)
  exact sub_self m

theorem exists_h1_equiv_characters : ∃ e : (trivRep G QZ).H 1 ≃+ charGrp G,
    ∀ x hx g, (e ((trivRep G QZ).coch.cls 1 x hx)).1 (Additive.ofMul g) = x.1 ![g] := by
  obtain ⟨-, -, ⟨e, he⟩, -⟩ := low_holds ℤ G (trivRep G QZ)
  have hB : (Gal.B1 (trivRep G QZ).rho).comap (Gal.Z1 (trivRep G QZ).rho).subtype = ⊥ := by
    rw [one_coboundaries_trivial_eq_bot, Submodule.comap_bot, Submodule.ker_subtype]
  refine ⟨e.toAddEquiv.trans ((Submodule.quotEquivOfEqBot _ hB).toAddEquiv.trans (oneCocycleEquivCharacters G)), ?_⟩
  intro x hx g
  obtain ⟨hz, h⟩ := he x hx
  show (oneCocycleEquivCharacters G (Submodule.quotEquivOfEqBot _ hB (e _))).1 (Additive.ofMul g) = _
  rw [h, Submodule.quotEquivOfEqBot_apply_mk]
  rfl

theorem exists_h2_int_equiv_characters [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    ∃ e : (trivRep G ℤ).H 2 ≃+ charGrp G, ∀ δ, Cx.IsConn (trivMap G (Int.castAddHom ℚ)).hom
      (trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom δ →
      ∀ x hx g, (e (δ 1 ((trivRep G QZ).coch.cls 1 x hx))).1 (Additive.ofMul g) = x.1 ![g] := by
  have hs := admissibility_holds ℤ G _ _ _ _ _ (admissible_int_rat_sequence G)
  obtain ⟨⟨δ', h1, -⟩, hu⟩ := lES_holds ℤ _ _ _ _ _ hs
  obtain ⟨e, he⟩ := exists_h1_equiv_characters G
  let d : (trivRep G QZ).H 1 ≃+ (trivRep G ℤ).H 2 :=
    AddEquiv.ofBijective (δ' 1).toAddMonoidHom (conn_int_rat_bijective G δ' h1 1 one_pos)
  refine ⟨d.symm.trans e, fun δ hδ x hx g => ?_⟩
  obtain rfl := hu δ δ' hδ h1
  show (e (d.symm (d _))).1 _ = _
  rw [d.symm_apply_apply, he]

theorem charGrp_eval_injective (s : G) (hs : Dense (Subgroup.zpowers s : Set G)) :
    Injective fun χ : charGrp G => χ.1 (Additive.ofMul s) := by
  have key : ∀ ψ : charGrp G, ψ.1 (Additive.ofMul s) = 0 → ψ = 0 := by
    intro ψ h
    have hcl : IsClosed {g : G | ψ.1 (Additive.ofMul g) = 0} := (IsLocallyConstant.isClopen_fiber ψ.2 0).1
    have hsub : (Subgroup.zpowers s : Set G) ⊆ {g : G | ψ.1 (Additive.ofMul g) = 0} := by
      rintro _ ⟨k, rfl⟩
      show ψ.1 (Additive.ofMul (s ^ k)) = 0
      rw [ofMul_zpow, map_zsmul, h, smul_zero]
    have hall := closure_minimal hsub hcl
    rw [hs.closure_eq] at hall
    exact Subtype.ext (AddMonoidHom.ext fun a => hall (Set.mem_univ a.toMul))
  intro χ χ' h
  refine sub_eq_zero.1 (key (χ - χ') ?_)
  show χ.1 (Additive.ofMul s) - χ'.1 (Additive.ofMul s) = 0
  exact sub_eq_zero.2 h

theorem charGrp_eval_bijective [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (s : G)
    (hs : IsZHat G s) : Bijective fun χ : charGrp G => χ.1 (Additive.ofMul s) := by
  refine ⟨charGrp_eval_injective G s hs.1, fun (q : (trivRep G QZ).V) => ?_⟩
  obtain ⟨⟨e, he⟩, -⟩ := zHat_holds ℤ G s hs (trivRep G QZ) RationalModIntegerChains.qz_torsion
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (e.symm (Submodule.Quotient.mk q))
  have h := he c
  rw [hc, e.apply_symm_apply] at h
  obtain ⟨m, hm⟩ := (Submodule.Quotient.eq _).1 h
  have hm' : 0 = q - c.1 s := by rw [← hm]; exact (sub_self m).symm
  exact ⟨oneCocycleEquivCharacters G c, (sub_eq_zero.1 hm'.symm).symm⟩

theorem exists_h2_int_equiv_rat_mod_int [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (s : G)
    (hs : IsZHat G s) : ∃ e : (trivRep G ℤ).H 2 ≃+ QZ, ∀ δ, Cx.IsConn (trivMap G (Int.castAddHom ℚ)).hom
      (trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom δ →
      ∀ x hx, e (δ 1 ((trivRep G QZ).coch.cls 1 x hx)) = x.1 ![s] := by
  obtain ⟨e, he⟩ := exists_h2_int_equiv_characters G
  let ev : charGrp G →+ QZ :=
    { toFun := fun χ => χ.1 (Additive.ofMul s), map_zero' := rfl, map_add' := fun _ _ => rfl }
  exact ⟨e.trans (AddEquiv.ofBijective ev (charGrp_eval_bijective G s hs)),
    fun δ hδ x hx => he δ hδ x hx s⟩

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
end
