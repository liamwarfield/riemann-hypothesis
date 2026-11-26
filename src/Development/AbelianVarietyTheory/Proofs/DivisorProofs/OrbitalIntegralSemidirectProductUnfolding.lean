module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftedCapelliDeterminantSubleadingCoeffTrace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetRelIndexInfConjConst
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetRelIndexInfConjConst
namespace GlobalTheory.DoubleCosetWeight

open Subgroup

theorem inf_map_conj_mul_eq {G : Type} [Group G] (T K : Subgroup G) {t k : G}
    (ht : t ∈ T) (hk : k ∈ K) (q : G) :
    T ⊓ K.map (MulAut.conj (t * q * k)).toMonoidHom =
      (T ⊓ K.map (MulAut.conj q).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
  ext x
  simp only [mem_inf, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hxT, y, hy, rfl⟩
    refine ⟨q * (k * y * k⁻¹) * q⁻¹, ⟨?_, k * y * k⁻¹, K.mul_mem (K.mul_mem hk hy) (K.inv_mem hk), rfl⟩, ?_⟩
    · have : q * (k * y * k⁻¹) * q⁻¹ = t⁻¹ * (t * q * k * y * (t * q * k)⁻¹) * t := by group
      rw [this]; exact T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) ht
    · group
  · rintro ⟨z, ⟨hzT, y, hy, rfl⟩, rfl⟩
    refine ⟨T.mul_mem (T.mul_mem ht hzT) (T.inv_mem ht), k⁻¹ * y * k, K.mul_mem (K.mul_mem (K.inv_mem hk) hy) hk, ?_⟩
    group

def gen {G : Type} [Group G] (T K : Subgroup G) : Subgroup G :=
  ⨆ q : G, T ⊓ K.map (MulAut.conj q).toMonoidHom

theorem gen_map_le {G : Type} [Group G] (T K : Subgroup G) {t : G} (ht : t ∈ T) :
    (gen T K).map (MulAut.conj t).toMonoidHom ≤ gen T K := by
  rw [map_le_iff_le_comap]
  refine iSup_le fun q => ?_
  intro x hx
  rw [mem_comap]
  have h1 : (MulAut.conj t).toMonoidHom x ∈ T ⊓ K.map (MulAut.conj (t * q * 1)).toMonoidHom := by
    rw [inf_map_conj_mul_eq T K ht K.one_mem q]
    exact mem_map_of_mem _ hx
  exact (le_iSup (fun q : G => T ⊓ K.map (MulAut.conj q).toMonoidHom) (t * q * 1)) h1

theorem gen_map_eq {G : Type} [Group G] (T K : Subgroup G) {t : G} (ht : t ∈ T) :
    (gen T K).map (MulAut.conj t).toMonoidHom = gen T K := by
  refine le_antisymm (gen_map_le T K ht) fun x hx => ?_
  have : (MulAut.conj t⁻¹).toMonoidHom x ∈ gen T K :=
    gen_map_le T K (T.inv_mem ht) (mem_map_of_mem _ hx)
  refine ⟨_, this, ?_⟩
  simp [MulAut.conj_apply, mul_assoc]

theorem relIndex_eq {G : Type} [Group G] (T C K : Subgroup G)
    (hC : ∀ q : G, T ⊓ K.map (MulAut.conj q).toMonoidHom ≤ C) :
    ∀ t ∈ T, ∀ k ∈ K, ∀ q : G,
      (T ⊓ K.map (MulAut.conj (t * q * k)).toMonoidHom).relIndex C =
        (T ⊓ K.map (MulAut.conj q).toMonoidHom).relIndex C := by
  intro t ht k hk q
  have hN : gen T K ≤ C := iSup_le hC
  have hA : ∀ p : G, T ⊓ K.map (MulAut.conj p).toMonoidHom ≤ gen T K := fun p =>
    le_iSup (fun q : G => T ⊓ K.map (MulAut.conj q).toMonoidHom) p
  have e1 := relIndex_mul_relIndex _ _ _ (hA (t * q * k)) hN
  have e2 := relIndex_mul_relIndex _ _ _ (hA q) hN
  rw [← e1, ← e2, inf_map_conj_mul_eq T K ht hk q]
  congr 1
  conv_lhs => rw [← gen_map_eq T K ht]
  exact relIndex_map_map_of_injective _ _ (MulAut.conj t).injective

end GlobalTheory.DoubleCosetWeight

theorem GlobalTheory.doubleCoset_relIndex_const : ∀ (G : Type) [Group G] (T C K : Subgroup G), (∀ q : G, T ⊓ K.map (MulAut.conj q).toMonoidHom ≤ C) → ∀ t ∈ T, ∀ k ∈ K, ∀ q : G, (T ⊓ K.map (MulAut.conj (t * q * k)).toMonoidHom).relIndex C = (T ⊓ K.map (MulAut.conj q).toMonoidHom).relIndex C :=
  fun G _ T C K hC => GlobalTheory.DoubleCosetWeight.relIndex_eq T C K hC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetRelIndexInfConjConstStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleCoset_relIndex_inf_conj_const : ∀ (G : Type) [Group G] (T C K : Subgroup G), (∀ q : G, T ⊓ K.map (MulAut.conj q).toMonoidHom ≤ C) → ∀ t ∈ T, ∀ k ∈ K, ∀ q : G, (T ⊓ K.map (MulAut.conj (t * q * k)).toMonoidHom).relIndex C = (T ⊓ K.map (MulAut.conj q).toMonoidHom).relIndex C := by
  first | exact @GlobalTheory.doubleCoset_relIndex_const | exact GlobalTheory.doubleCoset_relIndex_const | (intros; apply GlobalTheory.doubleCoset_relIndex_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitCountParabolicUnfoldLevi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitCountParabolicUnfoldLevi
namespace GlobalTheory

theorem orbit_count_parabolic_unfold : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ (TM CM : Subgroup M) (TP CP : Subgroup P), CM ≤ TM → (∀ p, p ∈ TP ↔ ∃ t ∈ TM, s t = p) → (∀ p, p ∈ CP ↔ ∃ t ∈ CM, s t = p) → (∀ q : M, TM ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ CM) → ∀ (q : M) (X : N), Nat.card {x : N ⧸ L // DoubleCoset.mk TP KP (s q * u (Quotient.out x)) = DoubleCoset.mk TP KP (s q * u X)} = (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓ KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).relIndex (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM) := by
  intro P M N _ _ _ s π u hπs hu hker KP KM L hsK hπK huK TM CM TP CP _ hTP _ _ q X
  set S : Subgroup M := TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM with hS
  set C : Subgroup M := KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s) with hC
  letI : MulAction M (P ⧸ KP) := MulAction.compHom (P ⧸ KP) s
  have hsmul : ∀ (r : M) (p : P), r • (QuotientGroup.mk p : P ⧸ KP) = QuotientGroup.mk (s r * p) := by
    intro r p; rfl
  have memS : ∀ r : M, r ∈ S ↔ (∃ t ∈ TM, q⁻¹ * t * q = r) ∧ r ∈ KM := by
    intro r
    simp only [hS, Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hπu : ∀ Y, π (u Y) = 1 := fun Y => (hker _).2 ⟨Y, rfl⟩
  set x0 : P ⧸ KP := QuotientGroup.mk (u X) with hx0
  have key : ∀ Y : N, DoubleCoset.mk TP KP (s q * u Y) = DoubleCoset.mk TP KP (s q * u X) ↔
      (QuotientGroup.mk (u Y) : P ⧸ KP) ∈ MulAction.orbit S x0 := by
    intro Y
    rw [eq_comm, DoubleCoset.eq]
    constructor
    · rintro ⟨h, hh, k, hk, e⟩
      obtain ⟨t, ht, rfl⟩ := (hTP h).1 hh
      have e2 : u Y = s (q⁻¹ * t * q) * u X * k := by
        apply mul_left_cancel (a := s q)
        rw [e, map_mul, map_mul, map_inv]
        group
      have e3 := congrArg π e2
      simp only [map_mul, hπs, hπu, mul_one] at e3
      have e4 : q⁻¹ * t * q = (π k)⁻¹ := eq_inv_of_mul_eq_one_left e3.symm
      have hr : q⁻¹ * t * q ∈ S := (memS _).2 ⟨⟨t, ht, rfl⟩, e4 ▸ KM.inv_mem (hπK k hk)⟩
      refine ⟨⟨_, hr⟩, ?_⟩
      show (q⁻¹ * t * q) • x0 = _
      rw [hx0, hsmul, QuotientGroup.eq, e2]
      convert hk using 1
      group
    · rintro ⟨⟨r, hr⟩, e⟩
      change r • x0 = _ at e
      rw [hx0, hsmul, QuotientGroup.eq] at e
      obtain ⟨⟨t, ht, rfl⟩, -⟩ := (memS r).1 hr
      refine ⟨s t, (hTP _).2 ⟨t, ht, rfl⟩, _, e, ?_⟩
      simp only [map_mul, map_inv]
      group
  have hinj : ∀ x y : N ⧸ L, (QuotientGroup.mk (u (Quotient.out x)) : P ⧸ KP) = QuotientGroup.mk (u (Quotient.out y)) → x = y := by
    intro x y h
    rw [QuotientGroup.eq, ← map_inv, ← map_mul, huK] at h
    rw [← Quotient.out_eq' x, ← Quotient.out_eq' y]
    exact (QuotientGroup.eq (s := L)).2 h
  have hcard : Nat.card {x : N ⧸ L // DoubleCoset.mk TP KP (s q * u (Quotient.out x)) = DoubleCoset.mk TP KP (s q * u X)} = Nat.card (MulAction.orbit S x0) := by
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨QuotientGroup.mk (u (Quotient.out x.1)), (key _).1 x.2⟩) ⟨?_, ?_⟩)
    · intro x y h
      exact Subtype.ext (hinj _ _ (congrArg Subtype.val h))
    · rintro ⟨y, ⟨⟨r, hr⟩, rfl⟩⟩
      have hk : π (s r * u X * (s r)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_inv, hπs, hπu]; group
      obtain ⟨Z, hZ⟩ := (hker _).1 hk
      have hrK : (r : M) ∈ KM := ((memS r).1 hr).2
      have hyo : (QuotientGroup.mk (u (Quotient.out (QuotientGroup.mk Z : N ⧸ L))) : P ⧸ KP) = r • x0 := by
        obtain ⟨l, hl⟩ := QuotientGroup.mk_out_eq_mul L Z
        change _ = r • x0
        rw [hx0, hsmul, hl, QuotientGroup.eq, map_mul, hZ]
        have h1 : s (r : M) ∈ KP := hsK _ hrK
        have h2 : u (l : N) ∈ KP := (huK _).2 l.2
        convert KP.mul_mem (KP.inv_mem h2) h1 using 1
        group
      refine ⟨⟨QuotientGroup.mk Z, (key _).2 ?_⟩, ?_⟩
      · rw [hyo]; exact ⟨⟨r, hr⟩, rfl⟩
      · exact Subtype.ext hyo
  have hstab : MulAction.stabilizer S x0 = (S ⊓ C).subgroupOf S := by
    ext ⟨r, hr⟩
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf, hC, Subgroup.mem_comap]
    change (r • x0 = x0) ↔ _
    rw [hx0, hsmul, QuotientGroup.eq]
    simp only [hr, true_and, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply, inv_inv]
    rw [← KP.inv_mem_iff]
    constructor <;> intro h <;> convert h using 1 <;> group
  rw [hcard, Subgroup.relIndex, ← hstab, MulAction.index_stabilizer, Nat.card_coe_set_eq]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitCountParabolicUnfoldLeviStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_count_parabolic_unfold_levi : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ (TM CM : Subgroup M) (TP CP : Subgroup P), CM ≤ TM → (∀ p, p ∈ TP ↔ ∃ t ∈ TM, s t = p) → (∀ p, p ∈ CP ↔ ∃ t ∈ CM, s t = p) → (∀ q : M, TM ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ CM) → ∀ (q : M) (X : N), Nat.card {x : N ⧸ L // DoubleCoset.mk TP KP (s q * u (Quotient.out x)) = DoubleCoset.mk TP KP (s q * u X)} = (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓ KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).relIndex (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM) := by
  first | exact @GlobalTheory.orbit_count_parabolic_unfold | exact GlobalTheory.orbit_count_parabolic_unfold | (intros; apply GlobalTheory.orbit_count_parabolic_unfold <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerRelIndexNeZeroParabolic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerRelIndexNeZeroParabolic
namespace GlobalTheory

theorem stab_relIndex_ne_zero : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ TM : Subgroup M, (∀ X : N, ∃ U : Subgroup M, U ≤ KM ∧ U.relIndex KM ≠ 0 ∧ ∀ k ∈ U, (u X)⁻¹ * s k * u X ∈ KP) → ∀ (q : M) (X : N), (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓ KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).relIndex (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM) ≠ 0 := by
  intro P M N _ _ _ s π u _ _ _ KP KM L _ _ _ TM hU q X
  obtain ⟨U, hUK, hUi, hUk⟩ := hU X
  set S := TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM
  set C := KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)
  have hUC : U ≤ C := by
    intro k hk
    simp only [C, Subgroup.mem_comap, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact hUk k hk
  have hSK : S ≤ KM := inf_le_right
  have hUS : U.relIndex S ≠ 0 := fun h =>
    hUi (Subgroup.relIndex_eq_zero_of_le_right hSK h)
  have hCS : C.relIndex S ≠ 0 := fun h =>
    hUS (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.relIndex_dvd_of_le_left S hUC))
  rw [Subgroup.inf_relIndex_left]
  exact hCS

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerRelIndexNeZeroParabolicStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_relIndex_ne_zero_parabolic : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ TM : Subgroup M, (∀ X : N, ∃ U : Subgroup M, U ≤ KM ∧ U.relIndex KM ≠ 0 ∧ ∀ k ∈ U, (u X)⁻¹ * s k * u X ∈ KP) → ∀ (q : M) (X : N), (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓ KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).relIndex (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM) ≠ 0 := by
  first | exact @GlobalTheory.stab_relIndex_ne_zero | exact GlobalTheory.stab_relIndex_ne_zero | (intros; apply GlobalTheory.stab_relIndex_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldSumInvariantLeviConj
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldSumInvariantLeviConj
namespace GlobalTheory

theorem unfold_sum_conj_invariant : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ F : P → ℂ, (∀ k ∈ KP, ∀ x, F (k⁻¹ * x * k) = F x) → ∀ k ∈ KM, ∀ y : P, (∑ᶠ x : N ⧸ L, F ((u (Quotient.out x))⁻¹ * ((s k)⁻¹ * y * s k) * u (Quotient.out x))) = ∑ᶠ x : N ⧸ L, F ((u (Quotient.out x))⁻¹ * y * u (Quotient.out x)) := by
  intro P M N _ _ _ s π u hπs hu hker KP KM L hsK hπK hL F hF k hk y
  set c := s k with hc_def
  have hc : c ∈ KP := hsK k hk
  have hπu : ∀ X, π (u X) = 1 := fun X => (hker _).2 ⟨X, rfl⟩
  have hex : ∀ (d : P), ∀ X, ∃ Y, u Y = d * u X * d⁻¹ := by
    intro d X
    exact (hker _).1 (by simp [map_mul, map_inv, hπu])
  choose φ hφ using hex c
  choose ψ hψ using hex c⁻¹
  have h1 : ∀ X, φ (ψ X) = X := fun X => hu (by rw [hφ, hψ]; group)
  have h2 : ∀ X, ψ (φ X) = X := fun X => hu (by rw [hψ, hφ]; group)
  have hconj : ∀ z, c * z * c⁻¹ ∈ KP ↔ z ∈ KP := by
    intro z
    constructor
    · intro h
      have := KP.mul_mem (KP.mul_mem (KP.inv_mem hc) h) hc
      simpa [mul_assoc] using this
    · intro h
      exact KP.mul_mem (KP.mul_mem hc h) (KP.inv_mem hc)
  let eN : N ≃ N := ⟨φ, ψ, h2, h1⟩
  let e : N ⧸ L ≃ N ⧸ L := Quotient.congr eN (by
    intro a b
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, ← hL, ← hL]
    simp only [eN, Equiv.coe_fn_mk, map_mul, map_inv, hφ]
    rw [← hconj]
    constructor <;> intro h <;> convert h using 1 <;> group)
  conv_rhs => rw [← finsum_comp_equiv e]
  apply finsum_congr
  intro x
  set X := Quotient.out x with hX
  have hex' : e x = (QuotientGroup.mk (φ X) : N ⧸ L) := by
    conv_lhs => rw [← Quotient.out_eq x]
    rfl
  set Z := Quotient.out (e x) with hZ
  have hZL : Z⁻¹ * φ X ∈ L := by
    apply QuotientGroup.eq.mp
    rw [← hex']
    exact Quotient.out_eq _
  have hw : u (Z⁻¹ * φ X) ∈ KP := (hL _).2 hZL
  calc F ((u X)⁻¹ * (c⁻¹ * y * c) * u X) = F (c⁻¹ * ((u (φ X))⁻¹ * y * u (φ X)) * c) := by
        congr 1; rw [hφ]; group
    _ = F ((u (φ X))⁻¹ * y * u (φ X)) := hF c hc _
    _ = F ((u Z * u (Z⁻¹ * φ X))⁻¹ * y * (u Z * u (Z⁻¹ * φ X))) := by
        rw [← map_mul, mul_inv_cancel_left]
    _ = F ((u (Z⁻¹ * φ X))⁻¹ * ((u Z)⁻¹ * y * u Z) * u (Z⁻¹ * φ X)) := by
        congr 1; group
    _ = F ((u Z)⁻¹ * y * u Z) := hF _ hw _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldSumInvariantLeviConjStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfold_sum_invariant_levi_conj : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ F : P → ℂ, (∀ k ∈ KP, ∀ x, F (k⁻¹ * x * k) = F x) → ∀ k ∈ KM, ∀ y : P, (∑ᶠ x : N ⧸ L, F ((u (Quotient.out x))⁻¹ * ((s k)⁻¹ * y * s k) * u (Quotient.out x))) = ∑ᶠ x : N ⧸ L, F ((u (Quotient.out x))⁻¹ * y * u (Quotient.out x)) := by
  first | exact @GlobalTheory.unfold_sum_conj_invariant | exact GlobalTheory.unfold_sum_conj_invariant | (intros; apply GlobalTheory.unfold_sum_conj_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetSemidirectRepSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetSemidirectRepSurjective
namespace GlobalTheory

theorem doubleCoset_semidirect_surj :
    ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P),
      (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) →
      ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N),
        (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) →
        ∀ (TM CM : Subgroup M) (TP CP : Subgroup P), CM ≤ TM →
          (∀ p, p ∈ TP ↔ ∃ t ∈ TM, s t = p) → (∀ p, p ∈ CP ↔ ∃ t ∈ CM, s t = p) →
          (∀ q : M, TM ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ CM) →
          ∀ d : DoubleCoset.Quotient (TP : Set P) (KP : Set P), ∃ X : N,
            DoubleCoset.mk TP KP (s (Quotient.out (DoubleCoset.mk TM KM (π (Quotient.out d)))) * u X)
              = d := by
  intro P M N _ _ _ s π u hs _ hker KP KM L hKs _ _ TM CM TP CP _ hTP _ _ d
  obtain ⟨t, ht, k, hk, hm⟩ := (@DoubleCoset.eq _ _ TM KM
    (Quotient.out (DoubleCoset.mk TM KM (π (Quotient.out d)))) (π (Quotient.out d))).1
    (DoubleCoset.out_eq' _)
  generalize Quotient.out (DoubleCoset.mk TM KM (π (Quotient.out d))) = q at hm ⊢
  obtain ⟨X, hX⟩ := (hker ((s q)⁻¹ * (s t)⁻¹ * Quotient.out d * (s k)⁻¹)).1 (by
    simp only [map_mul, map_inv, hs]
    rw [hm]; group)
  refine ⟨X, ?_⟩
  rw [hX]
  conv_rhs => rw [← DoubleCoset.out_eq' d]
  rw [DoubleCoset.eq]
  exact ⟨s t, (hTP _).2 ⟨t, ht, rfl⟩, s k, hKs k hk, by group⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetSemidirectRepSurjectiveStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleCoset_semidirect_rep_surjective : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ (TM CM : Subgroup M) (TP CP : Subgroup P), CM ≤ TM → (∀ p, p ∈ TP ↔ ∃ t ∈ TM, s t = p) → (∀ p, p ∈ CP ↔ ∃ t ∈ CM, s t = p) → (∀ q : M, TM ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ CM) → ∀ d : DoubleCoset.Quotient (TP : Set P) (KP : Set P), ∃ X : N, DoubleCoset.mk TP KP (s (Quotient.out (DoubleCoset.mk TM KM (π (Quotient.out d)))) * u X) = d := by
  first | exact @GlobalTheory.doubleCoset_semidirect_surj | exact GlobalTheory.doubleCoset_semidirect_surj | (intros; apply GlobalTheory.doubleCoset_semidirect_surj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexUnfoldSemidirectProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexUnfoldSemidirectProduct
namespace GlobalTheory

open Subgroup

namespace UnfoldSemidirect

theorem mem_map_conj_iff {G : Type} [Group G] (K : Subgroup G) (g p : G) :
    p ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * p * g ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

end UnfoldSemidirect


open UnfoldSemidirect in
theorem relIndex_unfold_semidirect : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ (TM CM : Subgroup M) (TP CP : Subgroup P), CM ≤ TM → (∀ p, p ∈ TP ↔ ∃ t ∈ TM, s t = p) → (∀ p, p ∈ CP ↔ ∃ t ∈ CM, s t = p) → (∀ q : M, TM ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ CM) → ∀ (q : M) (X : N), (TP ⊓ KP.map (MulAut.conj (s q * u X)).toMonoidHom).relIndex CP = (TM ⊓ KM.map (MulAut.conj q).toMonoidHom).relIndex CM * (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓ KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).relIndex (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM) := by
  intro P M N _ _ _ s π u hsec hu hker KP KM L hsK hπK huK TM CM TP CP hCT hTP hCP hcond q X
  have hπu : ∀ Y, π (u Y) = 1 := fun Y => (hker _).2 ⟨Y, rfl⟩
  have hsinj : Function.Injective s := fun a b h => by
    have := congrArg π h
    rwa [hsec, hsec] at this
  have key : ∀ r : M, (s q * u X)⁻¹ * s (q * r * q⁻¹) * (s q * u X) = (u X)⁻¹ * s r * u X := by
    intro r; simp only [map_mul, map_inv]; group
  have hπc : ∀ r : M, π ((u X)⁻¹ * s r * u X) = r := by
    intro r; simp [map_mul, map_inv, hπu, hsec]
  have hCP' : CP = CM.map s := by
    ext p; rw [hCP p, Subgroup.mem_map]
  have hH : TP ⊓ KP.map (MulAut.conj (s q * u X)).toMonoidHom
      = ((TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓
          KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).map
          (MulAut.conj q).toMonoidHom).map s := by
    ext p
    rw [Subgroup.mem_inf, mem_map_conj_iff, hTP p, Subgroup.mem_map]
    simp only [mem_map_conj_iff, Subgroup.mem_inf, Subgroup.mem_comap, MonoidHom.coe_comp,
      Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hk⟩
      have hk' : (u X)⁻¹ * s (q⁻¹ * t * q) * u X ∈ KP := by
        rw [← key]; simpa [mul_assoc] using hk
      refine ⟨t, ⟨⟨?_, ?_⟩, ?_⟩, rfl⟩
      · simpa [mul_assoc] using ht
      · have h1 := hπK _ hk'
        rwa [hπc] at h1
      · simpa using hk'
    · rintro ⟨t, ⟨⟨hr1, hr2⟩, hr3⟩, rfl⟩
      refine ⟨⟨t, by simpa [mul_assoc] using hr1, rfl⟩, ?_⟩
      have := key (q⁻¹ * t * q)
      have e : q * (q⁻¹ * t * q) * q⁻¹ = t := by group
      rw [e] at this
      rw [this]; exact hr3
  have hSq : TM ⊓ KM.map (MulAut.conj q).toMonoidHom
      = (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM).map (MulAut.conj q).toMonoidHom := by
    ext p
    simp only [Subgroup.mem_inf, mem_map_conj_iff, inv_inv]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by simpa [mul_assoc] using h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by simpa [mul_assoc] using h1, h2⟩
  have hle1 : (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓
          KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).map (MulAut.conj q).toMonoidHom
        ≤ (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM).map (MulAut.conj q).toMonoidHom :=
    Subgroup.map_mono inf_le_left
  have hle2 : (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM).map (MulAut.conj q).toMonoidHom ≤ CM := by
    rw [← hSq]; exact hcond q
  rw [hH, hCP', Subgroup.relIndex_map_map_of_injective _ _ hsinj,
    ← Subgroup.relIndex_mul_relIndex _ _ _ hle1 hle2,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj q).injective, ← hSq, mul_comm]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexUnfoldSemidirectProductStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_unfold_semidirect_product : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ (TM CM : Subgroup M) (TP CP : Subgroup P), CM ≤ TM → (∀ p, p ∈ TP ↔ ∃ t ∈ TM, s t = p) → (∀ p, p ∈ CP ↔ ∃ t ∈ CM, s t = p) → (∀ q : M, TM ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ CM) → ∀ (q : M) (X : N), (TP ⊓ KP.map (MulAut.conj (s q * u X)).toMonoidHom).relIndex CP = (TM ⊓ KM.map (MulAut.conj q).toMonoidHom).relIndex CM * (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓ KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).relIndex (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM) := by
  first | exact @GlobalTheory.relIndex_unfold_semidirect | exact GlobalTheory.relIndex_unfold_semidirect | (intros; apply GlobalTheory.relIndex_unfold_semidirect <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralSemidirectProductUnfolding
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.Unfold

theorem lhs_eq {P : Type} [Group P] [TopologicalSpace P] (KP : Subgroup P) (δ : P) (F : P → ℂ)
    (hF : ∀ k ∈ KP, ∀ x, F (k⁻¹ * x * k) = F x) :
    twOrb (MonoidHom.id P) KP δ F = ∑ᶠ d : DoubleCoset.Quotient (twCent (MonoidHom.id P) δ : Set P) (KP : Set P),
      (((twCent (MonoidHom.id P) δ ⊓ KP.map (MulAut.conj (Quotient.out d)).toMonoidHom).relIndex
        (cptPart (twCent (MonoidHom.id P) δ)) : ℕ) : ℂ) * F ((Quotient.out d)⁻¹ * δ * Quotient.out d) := by
  unfold twOrb
  refine finsum_congr fun d => ?_
  congr 1
  have h : (fun k : KP => F ((Quotient.out d * k)⁻¹ * δ * (MonoidHom.id P) (Quotient.out d * k))) =
      fun _ => F ((Quotient.out d)⁻¹ * δ * Quotient.out d) := by
    funext k
    rw [MonoidHom.id_apply, ← hF k k.2 ((Quotient.out d)⁻¹ * δ * Quotient.out d)]
    congr 1
    group
  rw [h, GlobalTheory.IwRed.avg_const]

theorem hint_eq {P N : Type} [Group P] [Group N] (u : N →* P) (KP : Subgroup P) (L : Subgroup N)
    (huK : ∀ X, u X ∈ KP ↔ X ∈ L) (F : P → ℂ) (hF : ∀ k ∈ KP, ∀ x, F (k⁻¹ * x * k) = F x) (y : P) :
    hint L (fun X => F ((u X)⁻¹ * y * u X)) = ∑ᶠ x : N ⧸ L, F ((u (Quotient.out x))⁻¹ * y * u (Quotient.out x)) := by
  have hL : L ≤ rStab (fun X => F ((u X)⁻¹ * y * u X)) := by
    intro l hl x
    show F ((u (x * l))⁻¹ * y * u (x * l)) = F ((u x)⁻¹ * y * u x)
    rw [← hF (u l) ((huK l).2 hl) ((u x)⁻¹ * y * u x)]
    congr 1
    simp only [map_mul]
    group
  have he : rStab (fun X => F ((u X)⁻¹ * y * u X)) ⊓ L = L := inf_eq_right.2 hL
  unfold hint
  rw [he, Subgroup.relIndex_self]
  simp

end GlobalTheory.Unfold

noncomputable section
namespace GlobalTheory.Unfold

theorem rhs_eq (P M N : Type) [Group P] [Group M] [Group N] [TopologicalSpace M] (s : M →* P) (π : P →* M)
    (u : N →* P) (hs : ∀ m, π (s m) = m) (hinj : Function.Injective u) (hker : ∀ p, π p = 1 ↔ ∃ X, u X = p)
    (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N) (hsK : ∀ k ∈ KM, s k ∈ KP) (hπK : ∀ k ∈ KP, π k ∈ KM)
    (huK : ∀ X, u X ∈ KP ↔ X ∈ L) (γ : M) (F : P → ℂ) (hF : ∀ k ∈ KP, ∀ x, F (k⁻¹ * x * k) = F x) :
    twOrb (MonoidHom.id M) KM γ (fun m' => hint L (fun X => F ((u X)⁻¹ * s m' * u X))) =
      ∑ᶠ q : DoubleCoset.Quotient (twCent (MonoidHom.id M) γ : Set M) (KM : Set M),
        (((twCent (MonoidHom.id M) γ ⊓ KM.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex
          (cptPart (twCent (MonoidHom.id M) γ)) : ℕ) : ℂ) *
        ∑ᶠ x : N ⧸ L, F ((s (Quotient.out q) * u (Quotient.out x))⁻¹ * s γ * (s (Quotient.out q) * u (Quotient.out x))) := by
  unfold twOrb
  refine finsum_congr fun q => ?_
  congr 1
  have h : (fun k : KM => hint L (fun X => F ((u X)⁻¹ * s ((Quotient.out q * k)⁻¹ * γ *
      (MonoidHom.id M) (Quotient.out q * k)) * u X))) = fun _ =>
      ∑ᶠ x : N ⧸ L, F ((s (Quotient.out q) * u (Quotient.out x))⁻¹ * s γ * (s (Quotient.out q) * u (Quotient.out x))) := by
    funext k
    rw [hint_eq u KP L huK F hF]
    have e : s ((Quotient.out q * k)⁻¹ * γ * (MonoidHom.id M) (Quotient.out q * k)) =
        (s k)⁻¹ * s ((Quotient.out q)⁻¹ * γ * Quotient.out q) * s k := by
      simp only [MonoidHom.id_apply, map_mul, map_inv]
      group
    rw [e, GlobalTheory.T.unfold_sum_invariant_levi_conj P M N s π u hs hinj hker KP KM L hsK hπK huK F hF k k.2]
    refine finsum_congr fun x => ?_
    congr 1
    simp only [map_mul, map_inv]
    group
  rw [h, GlobalTheory.IwRed.avg_const]

theorem core : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ (TM CM : Subgroup M) (TP CP : Subgroup P), CM ≤ TM → (∀ p, p ∈ TP ↔ ∃ t ∈ TM, s t = p) → (∀ p, p ∈ CP ↔ ∃ t ∈ CM, s t = p) → (∀ q : M, TM ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ CM) → ∀ G : P → ℂ, (∀ t ∈ TP, ∀ p, G (t * p) = G p) → (∀ k ∈ KP, ∀ p, G (p * k) = G p) →
    (∀ X : N, ∃ U : Subgroup M, U ≤ KM ∧ U.relIndex KM ≠ 0 ∧ ∀ k ∈ U, (u X)⁻¹ * s k * u X ∈ KP) →
    {d : DoubleCoset.Quotient (TP : Set P) (KP : Set P) | G (Quotient.out d) ≠ 0}.Finite →
    ∑ᶠ d : DoubleCoset.Quotient (TP : Set P) (KP : Set P),
      (((TP ⊓ KP.map (MulAut.conj (Quotient.out d)).toMonoidHom).relIndex CP : ℕ) : ℂ) * G (Quotient.out d) =
    ∑ᶠ q : DoubleCoset.Quotient (TM : Set M) (KM : Set M),
      (((TM ⊓ KM.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex CM : ℕ) : ℂ) *
        ∑ᶠ x : N ⧸ L, G (s (Quotient.out q) * u (Quotient.out x)) := by
  intro P M N _ _ _ s π u hs hinj hker KP KM L hsK hπK huK TM CM TP CP hCT hTP hCP hTC G hGT hGK hU hfin
  have hGout : ∀ p, G (Quotient.out (DoubleCoset.mk TP KP p)) = G p := by
    intro p
    obtain ⟨t, ht, k, hk, he⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 (DoubleCoset.out_eq' (DoubleCoset.mk TP KP p)).symm
    rw [he, hGK k hk, hGT t ht]
  have hTCP : ∀ p : P, TP ⊓ KP.map (MulAut.conj p).toMonoidHom ≤ CP := by
    intro p x hx
    obtain ⟨hxT, hxK⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨t, ht, rfl⟩ := (hTP x).1 hxT
    refine (hCP _).2 ⟨t, hTC (π p) (Subgroup.mem_inf.2 ⟨ht, ?_⟩), rfl⟩
    obtain ⟨k, hk, hke⟩ := Subgroup.mem_map.1 hxK
    refine Subgroup.mem_map.2 ⟨π k, hπK k hk, ?_⟩
    have := congrArg π hke
    simpa [MulAut.conj_apply, hs] using this
  let ρ : DoubleCoset.Quotient (TP : Set P) (KP : Set P) → DoubleCoset.Quotient (TM : Set M) (KM : Set M) :=
    fun d => DoubleCoset.mk TM KM (π (Quotient.out d))
  have hρmk : ∀ p, ρ (DoubleCoset.mk TP KP p) = DoubleCoset.mk TM KM (π p) := by
    intro p
    obtain ⟨t, ht, k, hk, he⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 (DoubleCoset.out_eq' (DoubleCoset.mk TP KP p)).symm
    show DoubleCoset.mk TM KM (π (Quotient.out (DoubleCoset.mk TP KP p))) = _
    rw [he, DoubleCoset.eq]
    obtain ⟨t', ht', rfl⟩ := (hTP t).1 ht
    refine ⟨t'⁻¹, TM.inv_mem ht', (π k)⁻¹, KM.inv_mem (hπK k hk), ?_⟩
    simp only [map_mul, hs]
    group
  have hsupp : (Function.support fun d : DoubleCoset.Quotient (TP : Set P) (KP : Set P) =>
      (((TP ⊓ KP.map (MulAut.conj (Quotient.out d)).toMonoidHom).relIndex CP : ℕ) : ℂ) * G (Quotient.out d)).Finite :=
    hfin.subset fun d hd => right_ne_zero_of_mul hd
  rw [GlobalTheory.T.finsum_fiberwise_of_finite_support_complex ρ _ hsupp]
  refine finsum_congr fun q => ?_
  set q0 := Quotient.out q with hq0def
  have hq0 : DoubleCoset.mk TM KM q0 = q := DoubleCoset.out_eq' q
  have hψ : ∀ x : N ⧸ L, ρ (DoubleCoset.mk TP KP (s q0 * u (Quotient.out x))) = q := fun x => by
    rw [hρmk, map_mul, hs, (hker _).2 ⟨_, rfl⟩, mul_one]
    exact hq0
  let ψ : N ⧸ L → {d // ρ d = q} := fun x => ⟨DoubleCoset.mk TP KP (s q0 * u (Quotient.out x)), hψ x⟩
  have hfib : ∀ d : {d // ρ d = q}, ∃ X : N, DoubleCoset.mk TP KP (s q0 * u X) = d.1 ∧
      Nat.card (ψ ⁻¹' {d}) = (TM.map (MulAut.conj q0⁻¹).toMonoidHom ⊓ KM ⊓ KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).relIndex (TM.map (MulAut.conj q0⁻¹).toMonoidHom ⊓ KM) := by
    intro d
    obtain ⟨X, hX⟩ := GlobalTheory.T.doubleCoset_semidirect_rep_surjective P M N s π u hs hinj hker KP KM L hsK hπK huK TM CM TP CP hCT hTP hCP hTC d.1
    have e : Quotient.out (DoubleCoset.mk TM KM (π (Quotient.out d.1))) = q0 := by
      rw [show DoubleCoset.mk TM KM (π (Quotient.out d.1)) = q from d.2]
    rw [e] at hX
    refine ⟨X, hX, ?_⟩
    rw [← GlobalTheory.T.orbit_count_parabolic_unfold_levi P M N s π u hs hinj hker KP KM L hsK hπK huK TM CM TP CP hCT hTP hCP hTC q0 X]
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun x => ?_
    rw [Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff, hX]
  have hwt : ∀ d : {d // ρ d = q},
      (((TP ⊓ KP.map (MulAut.conj (Quotient.out d.1)).toMonoidHom).relIndex CP : ℕ) : ℂ) =
      (((TM ⊓ KM.map (MulAut.conj q0).toMonoidHom).relIndex CM : ℕ) : ℂ) * (Nat.card (ψ ⁻¹' {d}) : ℂ) := by
    intro d
    obtain ⟨X, hX, hc⟩ := hfib d
    obtain ⟨t, ht, k, hk, he⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 (hX.trans (DoubleCoset.out_eq' d.1).symm)
    rw [he, GlobalTheory.T.doubleCoset_relIndex_inf_conj_const P TP CP KP hTCP t ht k hk,
      GlobalTheory.T.relIndex_unfold_semidirect_product P M N s π u hs hinj hker KP KM L hsK hπK huK TM CM TP CP hCT hTP hCP hTC q0 X, hc]
    push_cast
    rfl
  have hR : ∑ᶠ x : N ⧸ L, G (s q0 * u (Quotient.out x)) =
      ∑ᶠ d : {d // ρ d = q}, (Nat.card (ψ ⁻¹' {d}) : ℂ) * G (Quotient.out d.1) := by
    rw [← GlobalTheory.finsum_comp_eq_finsum_natCard_fiber_mul ψ (fun d => G (Quotient.out d.1)) (Or.inl ?_)]
    · exact finsum_congr fun x => (hGout _).symm
    · intro d _
      obtain ⟨X, -, hc⟩ := hfib d
      have h0 := GlobalTheory.T.stabilizer_relIndex_ne_zero_parabolic P M N s π u hs hinj hker KP KM L hsK hπK huK TM hU q0 X
      rw [← hc] at h0
      haveI := Nat.finite_of_card_ne_zero h0
      exact Set.toFinite _
  rw [hR, mul_finsum]
  refine finsum_congr fun d => ?_
  rw [hwt d, mul_assoc]

theorem twOrb_unfold : ∀ (P M N : Type) [Group P] [Group M] [Group N] [TopologicalSpace P] [TopologicalSpace M] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ γ : M, (∀ p, p ∈ twCent (MonoidHom.id P) (s γ) ↔ ∃ t ∈ twCent (MonoidHom.id M) γ, s t = p) → (∀ p, p ∈ cptPart (twCent (MonoidHom.id P) (s γ)) ↔ ∃ t ∈ cptPart (twCent (MonoidHom.id M) γ), s t = p) → (∀ q : M, twCent (MonoidHom.id M) γ ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ cptPart (twCent (MonoidHom.id M) γ)) → (∀ X : N, ∃ U : Subgroup M, U ≤ KM ∧ U.relIndex KM ≠ 0 ∧ ∀ k ∈ U, (u X)⁻¹ * s k * u X ∈ KP) → ∀ F : P → ℂ, (∀ k ∈ KP, ∀ x, F (k⁻¹ * x * k) = F x) → {d : DoubleCoset.Quotient (twCent (MonoidHom.id P) (s γ) : Set P) (KP : Set P) | F ((Quotient.out d)⁻¹ * s γ * Quotient.out d) ≠ 0}.Finite → twOrb (MonoidHom.id P) KP (s γ) F = twOrb (MonoidHom.id M) KM γ (fun m' => hint L (fun X => F ((u X)⁻¹ * s m' * u X))) := by
  intro P M N _ _ _ _ _ s π u hs hinj hker KP KM L hsK hπK huK γ hTP hCP hTC hU F hF hfin
  rw [lhs_eq KP (s γ) F hF, rhs_eq P M N s π u hs hinj hker KP KM L hsK hπK huK γ F hF]
  refine core P M N s π u hs hinj hker KP KM L hsK hπK huK (twCent (MonoidHom.id M) γ)
    (cptPart (twCent (MonoidHom.id M) γ)) (twCent (MonoidHom.id P) (s γ)) (cptPart (twCent (MonoidHom.id P) (s γ)))
    ((Subgroup.closure_le _).2 fun t ht => ht.1) hTP hCP hTC (fun p => F (p⁻¹ * s γ * p)) ?_ ?_ hU hfin
  · intro t ht p
    have ht' : t * s γ = s γ * t := ht
    show F ((t * p)⁻¹ * s γ * (t * p)) = F (p⁻¹ * s γ * p)
    rw [show (t * p)⁻¹ * s γ * (t * p) = p⁻¹ * (t⁻¹ * (s γ * t)) * p by group, ← ht', inv_mul_cancel_left]
  · intro k hk p
    show F ((p * k)⁻¹ * s γ * (p * k)) = F (p⁻¹ * s γ * p)
    rw [← hF k hk (p⁻¹ * s γ * p)]
    congr 1
    group

end GlobalTheory.Unfold
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralSemidirectProductUnfoldingStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitalIntegral_semidirectProduct_unfolding : ∀ (P M N : Type) [Group P] [Group M] [Group N] [TopologicalSpace P] [TopologicalSpace M] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ γ : M, (∀ p, p ∈ twCent (MonoidHom.id P) (s γ) ↔ ∃ t ∈ twCent (MonoidHom.id M) γ, s t = p) → (∀ p, p ∈ cptPart (twCent (MonoidHom.id P) (s γ)) ↔ ∃ t ∈ cptPart (twCent (MonoidHom.id M) γ), s t = p) → (∀ q : M, twCent (MonoidHom.id M) γ ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ cptPart (twCent (MonoidHom.id M) γ)) → (∀ X : N, ∃ U : Subgroup M, U ≤ KM ∧ U.relIndex KM ≠ 0 ∧ ∀ k ∈ U, (u X)⁻¹ * s k * u X ∈ KP) → ∀ F : P → ℂ, (∀ k ∈ KP, ∀ x, F (k⁻¹ * x * k) = F x) → {d : DoubleCoset.Quotient (twCent (MonoidHom.id P) (s γ) : Set P) (KP : Set P) | F ((Quotient.out d)⁻¹ * s γ * Quotient.out d) ≠ 0}.Finite → twOrb (MonoidHom.id P) KP (s γ) F = twOrb (MonoidHom.id M) KM γ (fun m' => hint L (fun X => F ((u X)⁻¹ * s m' * u X))) := by
  first | exact @GlobalTheory.Unfold.twOrb_unfold | exact GlobalTheory.Unfold.twOrb_unfold | (intros; apply GlobalTheory.Unfold.twOrb_unfold <;> assumption)
end
