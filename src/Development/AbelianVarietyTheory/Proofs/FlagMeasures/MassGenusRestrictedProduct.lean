module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerIsometry
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingAffine

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitMassEqOfFiniteDoubleCosets
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitMassEqInvStabilizerVolume
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitMassEquivariantConstantFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitMassEquivariantConstantFibre
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.MassFibre

theorem card_mul_relIndex {G : Type} [Group G] (H K : Subgroup G) (hle : H ≤ K) :
    Nat.card H * H.relIndex K = Nat.card K := by
  have h1 := Subgroup.card_mul_index (H.subgroupOf K)
  have h2 : Nat.card (H.subgroupOf K) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [h2] at h1
  exact h1

theorem encard_coe_subgroup {G : Type} [Group G] (H : Subgroup G) :
    ((H : Set G).encard : ℝ≥0∞) = if Nat.card H = 0 then ⊤ else (Nat.card H : ℝ≥0∞) := by
  split_ifs with h
  · have : (H : Set G).Infinite := by
      rcases Nat.card_eq_zero.mp h with h' | h'
      · exact absurd h' (not_isEmpty_of_nonempty _)
      · exact Set.infinite_coe_iff.mp h'
    rw [Set.encard_eq_top_iff.mpr this]; rfl
  · have hf : (H : Set G).Finite := by
      have := Nat.finite_of_card_ne_zero h
      exact Set.toFinite _
    rw [← hf.cast_ncard_eq, ← Nat.card_coe_set_eq]
    rfl

theorem inv_encard_eq_relIndex_mul {G : Type} [Group G] (H K : Subgroup G) (hle : H ≤ K)
    (hr : H.relIndex K ≠ 0) :
    (((H : Set G).encard : ℝ≥0∞))⁻¹ = (H.relIndex K : ℝ≥0∞) * (((K : Set G).encard : ℝ≥0∞))⁻¹ := by
  have hc := card_mul_relIndex H K hle
  rw [encard_coe_subgroup, encard_coe_subgroup]
  by_cases hK : Nat.card K = 0
  · have hH : Nat.card H = 0 := by
      rw [hK] at hc
      rcases Nat.mul_eq_zero.mp hc with h | h
      · exact h
      · exact absurd h hr
    simp [hH, hK]
  · have hH : Nat.card H ≠ 0 := by
      intro h; rw [h, zero_mul] at hc; exact hK hc.symm
    rw [if_neg hH, if_neg hK, ← hc]
    push_cast
    rw [ENNReal.mul_inv (Or.inl (by exact_mod_cast hH)) (Or.inl (by simp)), mul_comm,
      mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hr) (by simp), mul_one]

end GlobalTheory.MassFibre

namespace GlobalTheory.MassFibre

open MulAction

noncomputable def wt {G : Type} [Group G] (Γ : Subgroup G) {Y : Type} [MulAction G Y] (y : Y) : ℝ≥0∞ :=
  ((((Γ ⊓ MulAction.stabilizer G y : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹

theorem wt_smul {G : Type} [Group G] (Γ : Subgroup G) {Y : Type} [MulAction G Y] (γ : G)
    (hγ : γ ∈ Γ) (y : Y) : wt Γ (γ • y) = wt Γ y := by
  unfold wt
  congr 2
  have hset : ((Γ ⊓ MulAction.stabilizer G (γ • y) : Subgroup G) : Set G)
      = (fun h => γ * h * γ⁻¹) '' ((Γ ⊓ MulAction.stabilizer G y : Subgroup G) : Set G) := by
    ext x
    simp only [Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, MulAction.mem_stabilizer_iff,
      Set.mem_image]
    constructor
    · rintro ⟨hx1, hx2⟩
      refine ⟨γ⁻¹ * x * γ, ⟨?_, ?_⟩, by group⟩
      · exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) hx1) hγ
      · rw [mul_smul, mul_smul, hx2, inv_smul_smul]
    · rintro ⟨h, ⟨hh1, hh2⟩, rfl⟩
      refine ⟨Γ.mul_mem (Γ.mul_mem hγ hh1) (Γ.inv_mem hγ), ?_⟩
      rw [mul_smul, mul_smul, inv_smul_smul, hh2]
  rw [hset, Function.Injective.encard_image]
  intro a b hab
  simpa using hab

theorem wt_of_mem_orbit {G : Type} [Group G] (Γ : Subgroup G) {Y : Type} [MulAction G Y]
    {y y' : Y} (h : y' ∈ MulAction.orbit Γ y) : wt Γ y' = wt Γ y := by
  obtain ⟨γ, rfl⟩ := h
  show wt Γ (γ • y) = wt Γ y
  rw [Subgroup.smul_def]
  exact wt_smul Γ γ γ.2 y

theorem wt_out_mk {G : Type} [Group G] (Γ : Subgroup G) {Y : Type} [MulAction G Y] (y : Y) :
    wt Γ (Quotient.out (Quotient.mk (MulAction.orbitRel Γ Y) y : MulAction.orbitRel.Quotient Γ Y)) = wt Γ y :=
  wt_of_mem_orbit Γ (Quotient.mk_out (s := MulAction.orbitRel Γ Y) y)

end GlobalTheory.MassFibre

namespace GlobalTheory.MassFibre

theorem fibre_sum {G : Type} [Group G] (Γ : Subgroup G) {Y Z : Type} [MulAction G Y] [MulAction G Z]
    (f : Y → Z) (S : Set Z) (n : ℕ) (hf : ∀ (g : G) (y : Y), f (g • y) = g • f y)
    (hfin : ∀ z ∈ S, Finite {y // f y = z} ∧ Nat.card {y // f y = z} = n)
    (hemp : ∀ z, z ∉ S → IsEmpty {y // f y = z})
    (fbar : MulAction.orbitRel.Quotient Γ Y → MulAction.orbitRel.Quotient Γ Z)
    (hfbar : ∀ y, fbar (Quotient.mk _ y) = Quotient.mk _ (f y))
    (O : MulAction.orbitRel.Quotient Γ Z) :
    ∑' P : {P // fbar P = O}, wt Γ (Quotient.out P.1) = (n : ℝ≥0∞) * (if Quotient.out O ∈ S then wt Γ (Quotient.out O) else 0) := by

  classical
  by_cases hz : Quotient.out O ∈ S
  swap
  · rw [if_neg hz, mul_zero]
    haveI : IsEmpty {P // fbar P = O} := by
      refine ⟨fun ⟨P, hP⟩ => ?_⟩
      have h1 : Quotient.mk (MulAction.orbitRel Γ Z) (f (Quotient.out P))
          = Quotient.mk (MulAction.orbitRel Γ Z) (Quotient.out O) := by
        rw [← hfbar, Quotient.out_eq, Quotient.out_eq, hP]
      obtain ⟨γ, hγ⟩ := Quotient.exact h1
      exact (hemp _ hz).false ⟨(γ⁻¹ : G) • Quotient.out P, by
        rw [hf, ← hγ]; simp [Subgroup.smul_def]⟩
    simp
  rw [if_pos hz]
  obtain ⟨z, hzO⟩ : ∃ z, Quotient.out O = z := ⟨_, rfl⟩
  rw [hzO] at hz ⊢
  have hOz : Quotient.mk (MulAction.orbitRel Γ Z) z = O := by rw [← hzO, Quotient.out_eq]
  let Δ : Subgroup G := Γ ⊓ MulAction.stabilizer G z
  have hΔ : ∀ {g : G}, g ∈ Δ ↔ g ∈ Γ ∧ g • z = z := fun {g} => by
    simp [Δ, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  let p : SubMulAction Δ Y :=
    { carrier := f ⁻¹' {z}
      smul_mem' := fun δ y hy => by
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy ⊢
        rw [Subgroup.smul_def, hf, hy]; exact (hΔ.mp δ.2).2 }
  have hmem : ∀ y : Y, y ∈ p ↔ f y = z := fun y => Iff.rfl
  let e : p ≃ {y // f y = z} := Equiv.subtypeEquivRight hmem
  haveI : Finite {y // f y = z} := (hfin z hz).1
  haveI : Finite p := Finite.of_equiv _ e.symm
  have hcard : Nat.card p = n := (Nat.card_congr e).trans (hfin z hz).2

  let φ : MulAction.orbitRel.Quotient Δ p → {P // fbar P = O} := fun Q =>
    ⟨Quotient.mk _ (Quotient.out Q : p).1, by
      rw [hfbar, (hmem _).mp (Quotient.out Q).2, hOz]⟩
  have hinj : Function.Injective φ := by
    intro Q1 Q2 h
    have h' := congrArg Subtype.val h
    obtain ⟨γ, hγ⟩ := Quotient.exact h'
    have hγΔ : (γ : G) ∈ Δ := by
      refine hΔ.mpr ⟨γ.2, ?_⟩
      have hy1 := (hmem _).mp (Quotient.out Q1).2
      have hy2 := (hmem _).mp (Quotient.out Q2).2
      calc (γ : G) • z = (γ : G) • f (Quotient.out Q2 : p).1 := by rw [hy2]
        _ = f ((γ : G) • (Quotient.out Q2 : p).1) := (hf _ _).symm
        _ = f (Quotient.out Q1 : p).1 := by rw [← hγ]; rfl
        _ = z := hy1
    rw [← Quotient.out_equiv_out]
    refine ⟨⟨γ, hγΔ⟩, ?_⟩
    apply Subtype.ext
    exact hγ
  have hsurj : Function.Surjective φ := by
    rintro ⟨P, hP⟩
    have h1 : Quotient.mk (MulAction.orbitRel Γ Z) (f (Quotient.out P))
        = Quotient.mk (MulAction.orbitRel Γ Z) z := by
      rw [← hfbar, Quotient.out_eq, hP, hOz]
    obtain ⟨γ, hγ⟩ := Quotient.exact h1
    let y' : p := ⟨(γ⁻¹ : G) • Quotient.out P, by
      rw [hmem, hf, ← hγ]; simp [Subgroup.smul_def]⟩
    refine ⟨Quotient.mk _ y', Subtype.ext ?_⟩
    obtain ⟨δ, hδ⟩ := (Quotient.mk_out (s := MulAction.orbitRel Δ p) y')
    show Quotient.mk _ _ = P
    conv_rhs => rw [← Quotient.out_eq P]
    apply Quotient.sound
    refine ⟨⟨(δ : G) * (γ : G)⁻¹, Γ.mul_mem (hΔ.mp δ.2).1 (Γ.inv_mem γ.2)⟩, ?_⟩
    rw [← hδ]
    show ((δ : G) * (γ : G)⁻¹) • Quotient.out P = (δ : G) • ((γ⁻¹ : G) • Quotient.out P)
    rw [mul_smul]

  have hw : ∀ y : p, wt Γ (y : Y) = ((MulAction.orbit Δ y).ncard : ℝ≥0∞) * wt Γ z := by
    intro y
    have hy := (hmem _).mp y.2
    have hle : (Γ ⊓ MulAction.stabilizer G (y : Y) : Subgroup G) ≤ Δ := by
      intro g hg
      rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff] at hg
      refine hΔ.mpr ⟨hg.1, ?_⟩
      rw [← hy, ← hf, hg.2]
    have hsub : (Γ ⊓ MulAction.stabilizer G (y : Y) : Subgroup G).subgroupOf Δ
        = MulAction.stabilizer Δ y := by
      ext δ
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
        MulAction.mem_stabilizer_iff]
      constructor
      · rintro ⟨-, h⟩; exact Subtype.ext h
      · intro h; exact ⟨(hΔ.mp δ.2).1, congrArg Subtype.val h⟩
    have hri : (Γ ⊓ MulAction.stabilizer G (y : Y) : Subgroup G).relIndex Δ
        = (MulAction.orbit Δ y).ncard := by
      rw [Subgroup.relIndex, hsub, MulAction.index_stabilizer]
    have hne : (MulAction.orbit Δ y).ncard ≠ 0 :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨y, MulAction.mem_orbit_self y⟩ |>.ne'
    unfold wt
    rw [inv_encard_eq_relIndex_mul _ _ hle (hri ▸ hne), hri]
  rw [← (Equiv.ofBijective φ ⟨hinj, hsurj⟩).tsum_eq]
  haveI : Fintype (MulAction.orbitRel.Quotient Δ p) := Fintype.ofFinite _
  rw [tsum_fintype]
  have hterm : ∀ Q : MulAction.orbitRel.Quotient Δ p,
      wt Γ (Quotient.out (Equiv.ofBijective φ ⟨hinj, hsurj⟩ Q).1)
        = ((MulAction.orbit Δ (Quotient.out Q)).ncard : ℝ≥0∞) * wt Γ z := by
    intro Q
    rw [← hw]
    exact wt_out_mk Γ _
  simp_rw [hterm, ← Finset.sum_mul]
  congr 1
  have hsum : ∑ Q : MulAction.orbitRel.Quotient Δ p, (MulAction.orbit Δ (Quotient.out Q)).ncard = n := by
    rw [← hcard, Nat.card_congr (MulAction.selfEquivSigmaOrbits Δ p), Nat.card_sigma]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    rw [Nat.card_coe_set_eq]
  rw [← hsum]
  push_cast
  rfl

theorem mass_fibre : ∀ {G : Type} [Group G] (Γ : Subgroup G) (Y Z : Type) [MulAction G Y] [MulAction G Z] (f : Y → Z) (S : Set Z) (n : ℕ), (∀ (g : G) (y : Y), f (g • y) = g • f y) → (∀ (g : G) (z : Z), z ∈ S → g • z ∈ S) → (∀ z ∈ S, Finite {y // f y = z} ∧ Nat.card {y // f y = z} = n) → (∀ z, z ∉ S → IsEmpty {y // f y = z}) → (∑' o : MulAction.orbitRel.Quotient Γ Y, ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹) = (n : ℝ≥0∞) * ∑' o : MulAction.orbitRel.Quotient Γ Z, if o.out ∈ S then ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0 := by
  intro G _ Γ Y Z _ _ f S n hf hS hfin hemp
  let fbar : MulAction.orbitRel.Quotient Γ Y → MulAction.orbitRel.Quotient Γ Z :=
    Quotient.map' f (fun a b h => by
      obtain ⟨γ, hγ⟩ := h
      refine ⟨γ, ?_⟩
      show (γ : G) • f b = f a
      rw [← hf, ← hγ]; rfl)
  have hfbar : ∀ y, fbar (Quotient.mk _ y) = Quotient.mk _ (f y) := fun y => rfl
  have key := fibre_sum Γ f S n hf hfin hemp fbar hfbar
  change ∑' o : MulAction.orbitRel.Quotient Γ Y, wt Γ (Quotient.out o) = _
  rw [← (Equiv.sigmaFiberEquiv fbar).tsum_eq, ENNReal.tsum_sigma', ← ENNReal.tsum_mul_left]
  refine tsum_congr (fun O => ?_)
  exact key O

end GlobalTheory.MassFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitMassEquivariantConstantFibreStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_mass_equivariant_constant_fibre : ∀ {G : Type} [Group G] (Γ : Subgroup G) (Y Z : Type) [MulAction G Y] [MulAction G Z] (f : Y → Z) (S : Set Z) (n : ℕ), (∀ (g : G) (y : Y), f (g • y) = g • f y) → (∀ (g : G) (z : Z), z ∈ S → g • z ∈ S) → (∀ z ∈ S, Finite {y // f y = z} ∧ Nat.card {y // f y = z} = n) → (∀ z, z ∉ S → IsEmpty {y // f y = z}) → (∑' o : MulAction.orbitRel.Quotient Γ Y, ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹) = (n : ℝ≥0∞) * ∑' o : MulAction.orbitRel.Quotient Γ Z, if o.out ∈ S then ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0 := by
  first | exact @GlobalTheory.MassFibre.mass_fibre | exact GlobalTheory.MassFibre.mass_fibre | (intros; apply GlobalTheory.MassFibre.mass_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitMassEqInvStabilizerVolume
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem coset_fibre_card {G : Type} [Group G] (D H : Subgroup G) (h : D ≤ H) (hDH : D.relIndex H ≠ 0)
    (z : G ⧸ H) : Finite {y : G ⧸ D // Subgroup.quotientMapOfLE h y = z} ∧
      Nat.card {y : G ⧸ D // Subgroup.quotientMapOfLE h y = z} = D.relIndex H := by
  let e := Subgroup.quotientEquivProdOfLE (α := G) h
  have he : ∀ y, (e y).1 = Subgroup.quotientMapOfLE h y := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H a => rfl
  let e2 : {y : G ⧸ D // Subgroup.quotientMapOfLE h y = z} ≃ (H ⧸ D.subgroupOf H) :=
    { toFun := fun y => (e y.1).2
      invFun := fun c => ⟨e.symm (z, c), by rw [← he, Equiv.apply_symm_apply]⟩
      left_inv := fun y => by
        apply Subtype.ext
        apply e.injective
        rw [Equiv.apply_symm_apply]
        exact Prod.ext ((he y.1).trans y.2).symm rfl
      right_inv := fun c => by simp }
  haveI : (D.subgroupOf H).FiniteIndex := ⟨hDH⟩
  refine ⟨Finite.of_equiv _ e2.symm, ?_⟩
  rw [Nat.card_congr e2]
  rfl

theorem mass_orbit_eq : ∀ {G : Type} [Group G] (Γ K0 : Subgroup G), ∃ V₀ : ℝ≥0∞, ∀ (X : Type) [MulAction G X] (x : X), K0.relIndex (MulAction.stabilizer G x) ≠ 0 → (MulAction.stabilizer G x).relIndex K0 ≠ 0 → (∑' o : MulAction.orbitRel.Quotient Γ X, if o.out ∈ MulAction.orbit G x then ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0) = V₀ * ENNReal.ofReal (invVol K0 (MulAction.stabilizer G x)) := by
  intro G _ Γ K0
  let M : Subgroup G → ℝ≥0∞ := fun U => ∑' o : MulAction.orbitRel.Quotient Γ (G ⧸ U),
    ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹
  have hq : ∀ (D H : Subgroup G) (h : D ≤ H), D.relIndex H ≠ 0 → M D = (D.relIndex H : ℝ≥0∞) * M H := by
    intro D H h hDH
    have e := GlobalTheory.T.orbit_mass_equivariant_constant_fibre Γ (G ⧸ D) (G ⧸ H) (Subgroup.quotientMapOfLE h) Set.univ (D.relIndex H) ?_
      (fun _ _ _ => trivial) (fun z _ => coset_fibre_card D H h hDH z) (fun z hz => absurd trivial hz)
    · simp only [Set.mem_univ, ite_true] at e
      exact e
    · intro g y
      induction y using QuotientGroup.induction_on with
      | H a => rfl
  refine ⟨M K0, fun X _ x h1 h2 => ?_⟩
  have hX : (∑' o : MulAction.orbitRel.Quotient Γ X, if o.out ∈ MulAction.orbit G x then
      ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0) =
      M (MulAction.stabilizer G x) := by
    have e := GlobalTheory.T.orbit_mass_equivariant_constant_fibre Γ (G ⧸ MulAction.stabilizer G x) X (MulAction.ofQuotientStabilizer G x)
      (MulAction.orbit G x) 1 (fun g y => MulAction.ofQuotientStabilizer_smul G x g y)
      (fun g z hz => by obtain ⟨a, rfl⟩ := hz; exact ⟨g * a, mul_smul g a x⟩) ?_ ?_
    · rw [Nat.cast_one, one_mul] at e
      exact e.symm
    · intro z hz
      have hs : Subsingleton {y // MulAction.ofQuotientStabilizer G x y = z} :=
        ⟨fun a b => Subtype.ext (MulAction.injective_ofQuotientStabilizer G x (a.2.trans b.2.symm))⟩
      obtain ⟨a, rfl⟩ := hz
      have hn : Nonempty {y // MulAction.ofQuotientStabilizer G x y = a • x} :=
        ⟨⟨(a : G ⧸ MulAction.stabilizer G x), MulAction.ofQuotientStabilizer_mk G x a⟩⟩
      exact ⟨inferInstance, Nat.card_unique⟩
    · intro z hz
      refine ⟨fun y => hz ?_⟩
      rw [← y.2]
      induction y.1 using QuotientGroup.induction_on with
      | H a => exact ⟨a, (MulAction.ofQuotientStabilizer_mk G x a).symm⟩
  rw [hX]
  set U := MulAction.stabilizer G x
  have ha := hq (U ⊓ K0) U inf_le_left (by rw [Subgroup.inf_relIndex_left]; exact h1)
  have hb := hq (U ⊓ K0) K0 inf_le_right (by rw [Subgroup.inf_relIndex_right]; exact h2)
  rw [Subgroup.inf_relIndex_left] at ha
  rw [Subgroup.inf_relIndex_right] at hb
  rw [ha] at hb
  have hr : ENNReal.ofReal (invVol K0 U) = (U.relIndex K0 : ℝ≥0∞) / (K0.relIndex U : ℝ≥0∞) := by
    rw [invVol, ENNReal.ofReal_div_of_pos (by exact_mod_cast Nat.pos_of_ne_zero h1),
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  have hA : (K0.relIndex U : ℝ≥0∞) ≠ 0 := by exact_mod_cast h1
  have hA' : (K0.relIndex U : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [hr, ← mul_div_assoc, ENNReal.eq_div_iff hA hA', mul_comm (M K0), ← hb]

end GlobalTheory.HL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitMassEqInvStabilizerVolumeStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_mass_eq_inv_stabilizer_volume : ∀ {G : Type} [Group G] (Γ K0 : Subgroup G), ∃ V0 : ℝ≥0∞, ∀ (X : Type) [MulAction G X] (x : X), K0.relIndex (MulAction.stabilizer G x) ≠ 0 → (MulAction.stabilizer G x).relIndex K0 ≠ 0 → (∑' o : MulAction.orbitRel.Quotient Γ X, if o.out ∈ MulAction.orbit G x then ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0) = V0 * ENNReal.ofReal (invVol K0 (MulAction.stabilizer G x)) := by
  first | exact @GlobalTheory.HL.mass_orbit_eq | exact GlobalTheory.HL.mass_orbit_eq | (intros; apply GlobalTheory.HL.mass_orbit_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitMassEqOfFiniteDoubleCosets
open GlobalTheory.HL
open scoped ENNReal Classical

namespace GlobalTheory.HL

theorem inv_encard_stab_ne {G : Type} [Group G] (Γ K0 : Subgroup G)
    (hF : ∀ a : G, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0}.Finite) (y : G ⧸ K0) :
    ((((Γ ⊓ MulAction.stabilizer G y : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ ≠ 0 ∧
    ((((Γ ⊓ MulAction.stabilizer G y : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ ≠ ⊤ := by
  induction y using QuotientGroup.induction_on with
  | H g =>
    have hsub : ((Γ ⊓ MulAction.stabilizer G (g : G ⧸ K0) : Subgroup G) : Set G) ⊆
        {γ | γ ∈ Γ ∧ g⁻¹ * γ * g ∈ K0} := by
      intro γ hγ
      simp only [Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hγ
      refine ⟨hγ.1, ?_⟩
      have h2 := hγ.2
      rw [MulAction.Quotient.smul_coe, QuotientGroup.eq] at h2
      have := K0.inv_mem h2
      simpa [mul_assoc] using this
    have hfin := (hF g).subset hsub
    have hne : (((Γ ⊓ MulAction.stabilizer G (g : G ⧸ K0) : Subgroup G) : Set G)).Nonempty :=
      ⟨1, Subgroup.one_mem _⟩
    constructor
    · rw [ne_eq, ENNReal.inv_eq_zero]
      intro h
      have : (((Γ ⊓ MulAction.stabilizer G (g : G ⧸ K0) : Subgroup G) : Set G)).encard = ⊤ := by
        exact_mod_cast h
      exact (Set.encard_ne_top_iff.2 hfin) this
    · rw [ne_eq, ENNReal.inv_eq_top]
      intro h
      have : (((Γ ⊓ MulAction.stabilizer G (g : G ⧸ K0) : Subgroup G) : Set G)).encard = 0 := by
        exact_mod_cast h
      exact hne.ne_empty (Set.encard_eq_zero.1 this)

theorem mass_quotient_pos_finite {G : Type} [Group G] (Γ K0 : Subgroup G)
    (hS : ∃ S : Finset G, ∀ g : G, ∃ a ∈ S, ∃ γ ∈ Γ, ∃ κ ∈ K0, g = γ * a * κ)
    (hF : ∀ a : G, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0}.Finite) :
    (∑' o : MulAction.orbitRel.Quotient Γ (G ⧸ K0),
      ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹) ≠ 0 ∧
    (∑' o : MulAction.orbitRel.Quotient Γ (G ⧸ K0),
      ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹) ≠ ⊤ := by
  obtain ⟨S, hS⟩ := hS
  have hfin : Finite (MulAction.orbitRel.Quotient Γ (G ⧸ K0)) := by
    let f : S → MulAction.orbitRel.Quotient Γ (G ⧸ K0) := fun a =>
      Quotient.mk _ ((a.1 : G) : G ⧸ K0)
    refine Finite.of_surjective f ?_
    intro o
    induction o using Quotient.inductionOn with
    | h y =>
      induction y using QuotientGroup.induction_on with
      | H g =>
        obtain ⟨a, ha, γ, hγ, κ, hκ, rfl⟩ := hS g
        refine ⟨⟨a, ha⟩, ?_⟩
        apply Quotient.sound
        refine ⟨⟨γ⁻¹, Γ.inv_mem hγ⟩, ?_⟩
        show (γ⁻¹ : G) • ((γ * a * κ : G) : G ⧸ K0) = _
        rw [MulAction.Quotient.smul_coe, QuotientGroup.eq]
        simpa [mul_assoc] using K0.inv_mem hκ
  have := Fintype.ofFinite (MulAction.orbitRel.Quotient Γ (G ⧸ K0))
  constructor
  · rw [ne_eq, ENNReal.tsum_eq_zero, not_forall]
    exact ⟨Quotient.mk _ ((1 : G) : G ⧸ K0), (inv_encard_stab_ne Γ K0 hF _).1⟩
  · rw [tsum_fintype]
    exact ENNReal.sum_ne_top.2 (fun o _ => (inv_encard_stab_ne Γ K0 hF _).2)

theorem mass_orbit_eq_of_finite_double_cosets : ∀ {G : Type} [Group G] (Γ K0 : Subgroup G), (∃ S : Finset G, ∀ g : G, ∃ a ∈ S, ∃ γ ∈ Γ, ∃ κ ∈ K0, g = γ * a * κ) → (∀ a : G, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0}.Finite) → ∃ V0 : ℝ, 0 < V0 ∧ ∀ (X : Type) [MulAction G X] (x : X), K0.relIndex (MulAction.stabilizer G x) ≠ 0 → (MulAction.stabilizer G x).relIndex K0 ≠ 0 → (∑' o : MulAction.orbitRel.Quotient Γ X, if o.out ∈ MulAction.orbit G x then ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0) = ENNReal.ofReal (V0 * invVol K0 (MulAction.stabilizer G x)) := by
  intro G _ Γ K0 hS hF
  obtain ⟨V, hV⟩ := GlobalTheory.T.orbit_mass_eq_inv_stabilizer_volume Γ K0
  have hstab : MulAction.stabilizer G ((1 : G) : G ⧸ K0) = K0 := MulAction.stabilizer_quotient K0
  have h0 := hV (G ⧸ K0) ((1 : G) : G ⧸ K0) (by rw [hstab, Subgroup.relIndex_self]; exact one_ne_zero)
    (by rw [hstab, Subgroup.relIndex_self]; exact one_ne_zero)
  have horb : ∀ y : G ⧸ K0, y ∈ MulAction.orbit G ((1 : G) : G ⧸ K0) := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H g => exact ⟨g, show g • ((1 : G) : G ⧸ K0) = g by rw [MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]⟩
  simp only [horb, ite_true, hstab] at h0
  rw [show invVol K0 K0 = 1 by simp [invVol, Subgroup.relIndex_self], ENNReal.ofReal_one,
    mul_one] at h0
  obtain ⟨hV0, hVt⟩ := mass_quotient_pos_finite Γ K0 hS hF
  have hV0' : V ≠ 0 := by rw [← h0]; exact hV0
  have hVt' : V ≠ ⊤ := by rw [← h0]; exact hVt
  refine ⟨V.toReal, ENNReal.toReal_pos hV0' hVt', fun X _ x h1 h2 => ?_⟩
  rw [hV X x h1 h2, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hVt']

end GlobalTheory.HL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitMassEqOfFiniteDoubleCosetsStatement
open GlobalTheory.HL
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_mass_eq_of_finite_double_cosets : ∀ {G : Type} [Group G] (Γ K0 : Subgroup G), (∃ S : Finset G, ∀ g : G, ∃ a ∈ S, ∃ γ ∈ Γ, ∃ κ ∈ K0, g = γ * a * κ) → (∀ a : G, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0}.Finite) → ∃ V0 : ℝ, 0 < V0 ∧ ∀ (X : Type) [MulAction G X] (x : X), K0.relIndex (MulAction.stabilizer G x) ≠ 0 → (MulAction.stabilizer G x).relIndex K0 ≠ 0 → (∑' o : MulAction.orbitRel.Quotient Γ X, if o.out ∈ MulAction.orbit G x then ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0) = ENNReal.ofReal (V0 * invVol K0 (MulAction.stabilizer G x)) := by
  first | exact @GlobalTheory.HL.mass_orbit_eq_of_finite_double_cosets | exact GlobalTheory.HL.mass_orbit_eq_of_finite_double_cosets | (intros; apply GlobalTheory.HL.mass_orbit_eq_of_finite_double_cosets <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassGenusRestrictedProduct
open GlobalTheory.HL
open scoped ENNReal Classical

namespace GlobalTheory.HL

def resPi {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (A : ∀ i, Subgroup (G i)) :
    Subgroup (∀ i, G i) where
  carrier := {g | {i | g i ∉ A i}.Finite}
  one_mem' := by
    have : {i | (1 : ∀ i, G i) i ∉ A i} = ∅ := by
      ext i; simp [one_mem]
    simp only [Set.mem_setOf_eq, this, Set.finite_empty]
  mul_mem' := by
    intro a b ha hb
    refine (Set.Finite.union ha hb).subset (fun i hi => ?_)
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
    exact hi (mul_mem h.1 h.2)
  inv_mem' := by
    intro a ha
    refine Set.Finite.subset ha (fun i hi => ?_)
    simpa using hi

theorem pi_le_resPi {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (A U : ∀ i, Subgroup (G i))
    (h : {i | A i ≠ U i}.Finite) : Subgroup.pi Set.univ U ≤ resPi A := by
  intro g hg
  refine Set.Finite.subset h (fun i hi hAU => hi ?_)
  rw [hAU]
  exact hg i (Set.mem_univ i)

theorem exists_finset_cosets {G : Type} [Group G] (K L : Subgroup G) (h : L.relIndex K ≠ 0) :
    ∃ T : Finset G, ∀ k ∈ K, ∃ t ∈ T, t⁻¹ * k ∈ L := by
  haveI : (L.subgroupOf K).FiniteIndex := ⟨h⟩
  haveI : Fintype (K ⧸ L.subgroupOf K) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : K ⧸ L.subgroupOf K => ((Quotient.out q : K) : G)), ?_⟩
  intro k hk
  refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk ⟨k, hk⟩)), ?_⟩
  have h1 : ((Quotient.out (QuotientGroup.mk ⟨k, hk⟩ : K ⧸ L.subgroupOf K) : K) :
      K ⧸ L.subgroupOf K) = QuotientGroup.mk ⟨k, hk⟩ := QuotientGroup.out_eq' _
  have h2 := QuotientGroup.eq.1 h1
  simpa [Subgroup.mem_subgroupOf] using h2

theorem double_cosets_transfer {G : Type} [Group G] (Γ KA K0 : Subgroup G)
    (h : K0.relIndex KA ≠ 0)
    (hS : ∃ S : Finset G, ∀ g : G, ∃ a ∈ S, ∃ γ ∈ Γ, ∃ κ ∈ KA, g = γ * a * κ) :
    ∃ S : Finset G, ∀ g : G, ∃ a ∈ S, ∃ γ ∈ Γ, ∃ κ ∈ K0, g = γ * a * κ := by
  obtain ⟨S, hS⟩ := hS
  obtain ⟨T, hT⟩ := exists_finset_cosets KA K0 h
  refine ⟨Finset.image₂ (· * ·) S T, fun g => ?_⟩
  obtain ⟨a, ha, γ, hγ, κ, hκ, rfl⟩ := hS g
  obtain ⟨t, ht, htκ⟩ := hT κ hκ
  exact ⟨a * t, Finset.mem_image₂_of_mem ha ht, γ, hγ, t⁻¹ * κ, htκ, by group⟩

theorem finite_conj_transfer {G : Type} [Group G] (Γ KA K0 : Subgroup G)
    (h : KA.relIndex K0 ≠ 0) (hF : ∀ a : G, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ KA}.Finite) (a : G) :
    {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0}.Finite := by
  obtain ⟨T, hT⟩ := exists_finset_cosets K0 KA h
  have hpiece : ∀ t ∈ T, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0 ∧ t⁻¹ * (a⁻¹ * γ * a) ∈ KA}.Finite := by
    intro t _
    by_cases hne : ∃ γ₀, γ₀ ∈ Γ ∧ a⁻¹ * γ₀ * a ∈ K0 ∧ t⁻¹ * (a⁻¹ * γ₀ * a) ∈ KA
    · obtain ⟨γ₀, hγ₀, -, h₀⟩ := hne
      refine ((hF a).image (fun δ => γ₀ * δ)).subset ?_
      rintro γ ⟨hγ, -, h₁⟩
      refine ⟨γ₀⁻¹ * γ, ⟨Γ.mul_mem (Γ.inv_mem hγ₀) hγ, ?_⟩, by group⟩
      have := KA.mul_mem (KA.inv_mem h₀) h₁
      convert this using 1
      group
    · refine Set.Finite.subset Set.finite_empty ?_
      rintro γ ⟨h1, h2, h3⟩
      exact hne ⟨γ, h1, h2, h3⟩
  refine (T.finite_toSet.biUnion hpiece).subset ?_
  rintro γ ⟨hγ, hk⟩
  obtain ⟨t, ht, htk⟩ := hT _ hk
  exact Set.mem_biUnion ht ⟨hγ, hk, htk⟩

theorem invVol_subgroupOf {G : Type} [Group G] (R K L : Subgroup G) (hK : K ≤ R) (hL : L ≤ R) :
    invVol (K.subgroupOf R) (L.subgroupOf R) = invVol K L := by
  simp only [invVol, Subgroup.relIndex_subgroupOf hK, Subgroup.relIndex_subgroupOf hL]

theorem tsum_quot_out {Y : Type} (r : Y → Y → Prop) (s : Setoid Y) (hr : ∀ a b, r a b ↔ s.r a b)
    (F : Y → ℝ≥0∞) : ∑' o : Quot r, F o.out = ∑' o : Quotient s, F o.out := by
  obtain rfl : r = s.r := by
    funext a b
    exact propext (hr a b)
  rfl

theorem stabilizer_pi {ι : Type} {G : ι → Type} [∀ i, Group (G i)] {X : ι → Type}
    [∀ i, MulAction (G i) (X i)] (x : ∀ i, X i) :
    MulAction.stabilizer (∀ i, G i) x =
      Subgroup.pi Set.univ (fun i => MulAction.stabilizer (G i) (x i)) := by
  ext g
  simp [MulAction.mem_stabilizer_iff, Subgroup.mem_pi, funext_iff]

theorem stabilizer_res {P : Type} [Group P] (R : Subgroup P) {Y : Type} [MulAction P Y] (y : Y) :
    MulAction.stabilizer R y = (MulAction.stabilizer P y).subgroupOf R := by
  ext g
  simp [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.smul_def]

end GlobalTheory.HL

namespace GlobalTheory.HL

theorem mass_restricted_product : ∀ {ι : Type} (G : ι → Type) [∀ i, Group (G i)] (X : ι → Type) [∀ i, MulAction (G i) (X i)] (A : ∀ i, Subgroup (G i)) (H : Type) [Group H] (φ : H →* ∀ i, G i), Function.Injective φ → (∀ h, {i | φ h i ∉ A i}.Finite) → (∃ S : Finset (∀ i, G i), (∀ s ∈ S, {i | s i ∉ A i}.Finite) ∧ ∀ g : ∀ i, G i, {i | g i ∉ A i}.Finite → ∃ s ∈ S, ∃ h : H, ∃ k : ∀ i, G i, (∀ i, k i ∈ A i) ∧ g = φ h * s * k) → (∀ a : ∀ i, G i, {i | a i ∉ A i}.Finite → {h : H | ∀ i, (a i)⁻¹ * φ h i * a i ∈ A i}.Finite) → ∀ x0 : ∀ i, X i, (∀ i, (MulAction.stabilizer (G i) (x0 i)).relIndex (A i) ≠ 0 ∧ (A i).relIndex (MulAction.stabilizer (G i) (x0 i)) ≠ 0) → {i | A i ≠ MulAction.stabilizer (G i) (x0 i)}.Finite → ∃ V1 : ℝ, 0 < V1 ∧ ∀ x : ∀ i, X i, (∀ i, (MulAction.stabilizer (G i) (x0 i)).relIndex (MulAction.stabilizer (G i) (x i)) ≠ 0 ∧ (MulAction.stabilizer (G i) (x i)).relIndex (MulAction.stabilizer (G i) (x0 i)) ≠ 0) → {i | x i ≠ x0 i}.Finite → (∑' o : Quot (fun y y' : (∀ i, X i) => ∃ h : H, φ h • y = y'), if (∀ i, ∃ g : G i, g • x i = o.out i) ∧ {i | o.out i ≠ x i}.Finite then (({h : H | φ h • o.out = o.out}.encard : ℝ≥0∞))⁻¹ else 0) = ENNReal.ofReal (V1 * ∏ᶠ i, invVol (MulAction.stabilizer (G i) (x0 i)) (MulAction.stabilizer (G i) (x i))) := by
  intro ι G _ X _ A H _ φ hinj hres hdc hfin x0 hcomm hae
  set R := resPi A with hRdef
  let φ' : H →* R := φ.codRestrict R hres
  have hφ' : ∀ h, ((φ' h : R) : ∀ i, G i) = φ h := fun h => rfl
  set Γ : Subgroup R := φ'.range with hΓ
  set KA : Subgroup R := (Subgroup.pi Set.univ A).subgroupOf R with hKA
  set K0 : Subgroup R := MulAction.stabilizer R x0 with hK0
  have hAR : Subgroup.pi Set.univ A ≤ R := pi_le_resPi A A (by simp)
  have hstab0 : Subgroup.pi Set.univ (fun i => MulAction.stabilizer (G i) (x0 i)) ≤ R :=
    pi_le_resPi A _ hae
  have hK0' : K0 = (Subgroup.pi Set.univ (fun i => MulAction.stabilizer (G i) (x0 i))).subgroupOf R := by
    rw [hK0, stabilizer_res, stabilizer_pi]
  have hpi := invVol_pi_univ (fun i => MulAction.stabilizer (G i) (x0 i)) A
    (by simpa [eq_comm] using hae) hcomm
  have hc1 : K0.relIndex KA ≠ 0 := by
    rw [hK0', hKA, Subgroup.relIndex_subgroupOf hAR]; exact hpi.1
  have hc2 : KA.relIndex K0 ≠ 0 := by
    rw [hK0', hKA, Subgroup.relIndex_subgroupOf hstab0]; exact hpi.2.1
  have hDC : ∃ S : Finset R, ∀ g : R, ∃ a ∈ S, ∃ γ ∈ Γ, ∃ κ ∈ K0, g = γ * a * κ := by
    refine double_cosets_transfer Γ KA K0 hc1 ?_
    obtain ⟨S, hSR, hS⟩ := hdc
    refine ⟨S.subtype (· ∈ R), fun g => ?_⟩
    obtain ⟨s, hs, h, k, hk, hg⟩ := hS g g.2
    have hkR : k ∈ R := hAR (fun i _ => hk i)
    refine ⟨⟨s, hSR s hs⟩, by simpa using hs, φ' h, ⟨h, rfl⟩, ⟨k, hkR⟩, ?_, ?_⟩
    · simpa [hKA, Subgroup.mem_subgroupOf, Subgroup.mem_pi] using hk
    · ext1; simpa [hφ'] using hg
  have hFin : ∀ a : R, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0}.Finite := by
    refine finite_conj_transfer Γ KA K0 hc2 (fun a => ?_)
    refine ((hfin a a.2).image φ').subset ?_
    rintro γ ⟨⟨h, rfl⟩, hγ⟩
    refine ⟨h, fun i => ?_, rfl⟩
    have := hγ
    simp only [hKA, Subgroup.mem_subgroupOf, Subgroup.mem_pi, Set.mem_univ, forall_const] at this
    simpa [hφ'] using this i
  obtain ⟨V0, hV0, hmass⟩ := GlobalTheory.T.orbit_mass_eq_of_finite_double_cosets Γ K0 hDC hFin
  refine ⟨V0, hV0, fun x hx hxae => ?_⟩

  have hAx : {i | A i ≠ MulAction.stabilizer (G i) (x i)}.Finite := by
    refine (hae.union hxae).subset (fun i hi => ?_)
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
    exact hi (by rw [h.1, h.2])
  have hstabx : Subgroup.pi Set.univ (fun i => MulAction.stabilizer (G i) (x i)) ≤ R :=
    pi_le_resPi A _ hAx
  have hSx : MulAction.stabilizer R x =
      (Subgroup.pi Set.univ (fun i => MulAction.stabilizer (G i) (x i))).subgroupOf R := by
    rw [stabilizer_res, stabilizer_pi]
  have hpx := invVol_pi_univ (fun i => MulAction.stabilizer (G i) (x0 i))
    (fun i => MulAction.stabilizer (G i) (x i))
    (hxae.subset (fun i hi h => hi (by rw [h]))) hx
  have d1 : K0.relIndex (MulAction.stabilizer R x) ≠ 0 := by
    rw [hK0', hSx, Subgroup.relIndex_subgroupOf hstabx]; exact hpx.1
  have d2 : (MulAction.stabilizer R x).relIndex K0 ≠ 0 := by
    rw [hK0', hSx, Subgroup.relIndex_subgroupOf hstab0]; exact hpx.2.1
  have hm := hmass (∀ i, X i) x d1 d2
  have hvol : invVol K0 (MulAction.stabilizer R x) =
      ∏ᶠ i, invVol (MulAction.stabilizer (G i) (x0 i)) (MulAction.stabilizer (G i) (x i)) := by
    rw [hK0', hSx, invVol_subgroupOf R _ _ hstab0 hstabx]; exact hpx.2.2
  rw [← hvol, ← hm]
  have hφinj : Function.Injective φ' := fun a b hab => hinj (congrArg Subtype.val hab)
  have horb : ∀ y : ∀ i, X i, ((∀ i, ∃ g : G i, g • x i = y i) ∧ {i | y i ≠ x i}.Finite) ↔
      y ∈ MulAction.orbit R x := by
    intro y
    constructor
    · rintro ⟨hall, hf⟩
      let g : ∀ i, G i := fun i => if y i = x i then 1 else Classical.choose (hall i)
      have hgR : g ∈ R := by
        refine hf.subset (fun i hi hyx => hi ?_)
        simp only [g, hyx, if_true]
        exact one_mem _
      refine ⟨⟨g, hgR⟩, funext fun i => ?_⟩
      dsimp only
      rw [Subgroup.smul_def, Pi.smul_apply']
      by_cases hyx : y i = x i
      · simp [g, hyx]
      · simp only [g, hyx, if_false]
        exact Classical.choose_spec (hall i)
    · rintro ⟨g, rfl⟩
      refine ⟨fun i => ⟨(g : ∀ i, G i) i, by dsimp only; rw [Subgroup.smul_def, Pi.smul_apply']⟩, ?_⟩
      refine ((g.2 : {i | (g : ∀ i, G i) i ∉ A i}.Finite).union hAx).subset (fun i hi => ?_)
      by_contra h
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
      apply hi
      dsimp only
      rw [Subgroup.smul_def, Pi.smul_apply']
      have := h.1
      rw [h.2] at this
      exact this
  have henc : ∀ y : ∀ i, X i, {h : H | φ h • y = y}.encard =
      ((Γ ⊓ MulAction.stabilizer R y : Subgroup R) : Set R).encard := by
    intro y
    rw [← hφinj.encard_image]
    congr 1
    ext γ
    simp only [Set.mem_image, Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_inf,
      MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, rfl⟩, by rw [Subgroup.smul_def]; exact hh⟩
    · rintro ⟨⟨h, rfl⟩, hh⟩
      exact ⟨h, by rw [Subgroup.smul_def] at hh; exact hh, rfl⟩
  refine (tsum_congr fun o => ?_).trans (tsum_quot_out _ (MulAction.orbitRel Γ (∀ i, X i)) ?_ (fun y =>
    if y ∈ MulAction.orbit R x then
      ((((Γ ⊓ MulAction.stabilizer R y : Subgroup R) : Set R).encard : ℝ≥0∞))⁻¹ else 0))
  · beta_reduce
    simp only [henc, horb]
  · intro a b
    rw [MulAction.orbitRel_apply]
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨⟨φ' h, h, rfl⟩⁻¹, ?_⟩
      dsimp only
      simp [Subgroup.smul_def, hφ']
    · rintro ⟨⟨γ, h, rfl⟩, hγ⟩
      refine ⟨h⁻¹, ?_⟩
      rw [← hγ]
      dsimp only
      simp [Subgroup.smul_def, hφ']

end GlobalTheory.HL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassGenusRestrictedProductStatement
open GlobalTheory.HL
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mass_genus_restricted_product : ∀ {ι : Type} (G : ι → Type) [∀ i, Group (G i)] (X : ι → Type) [∀ i, MulAction (G i) (X i)] (A : ∀ i, Subgroup (G i)) (H : Type) [Group H] (φ : H →* ∀ i, G i), Function.Injective φ → (∀ h, {i | φ h i ∉ A i}.Finite) → (∃ S : Finset (∀ i, G i), (∀ s ∈ S, {i | s i ∉ A i}.Finite) ∧ ∀ g : ∀ i, G i, {i | g i ∉ A i}.Finite → ∃ s ∈ S, ∃ h : H, ∃ k : ∀ i, G i, (∀ i, k i ∈ A i) ∧ g = φ h * s * k) → (∀ a : ∀ i, G i, {i | a i ∉ A i}.Finite → {h : H | ∀ i, (a i)⁻¹ * φ h i * a i ∈ A i}.Finite) → ∀ x0 : ∀ i, X i, (∀ i, (MulAction.stabilizer (G i) (x0 i)).relIndex (A i) ≠ 0 ∧ (A i).relIndex (MulAction.stabilizer (G i) (x0 i)) ≠ 0) → {i | A i ≠ MulAction.stabilizer (G i) (x0 i)}.Finite → ∃ V1 : ℝ, 0 < V1 ∧ ∀ x : ∀ i, X i, (∀ i, (MulAction.stabilizer (G i) (x0 i)).relIndex (MulAction.stabilizer (G i) (x i)) ≠ 0 ∧ (MulAction.stabilizer (G i) (x i)).relIndex (MulAction.stabilizer (G i) (x0 i)) ≠ 0) → {i | x i ≠ x0 i}.Finite → (∑' o : Quot (fun y y' : (∀ i, X i) => ∃ h : H, φ h • y = y'), if (∀ i, ∃ g : G i, g • x i = o.out i) ∧ {i | o.out i ≠ x i}.Finite then (({h : H | φ h • o.out = o.out}.encard : ℝ≥0∞))⁻¹ else 0) = ENNReal.ofReal (V1 * ∏ᶠ i, invVol (MulAction.stabilizer (G i) (x0 i)) (MulAction.stabilizer (G i) (x i))) := by
  first | exact @GlobalTheory.HL.mass_restricted_product | exact GlobalTheory.HL.mass_restricted_product | (intros; apply GlobalTheory.HL.mass_restricted_product <;> assumption)
end
