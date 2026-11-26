module

public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPair

@[expose] public section

section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.RecCyclicB
section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.RecCyclicA
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.RecCyc

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

theorem qz_mem_zmultiples {n : ℕ} (hn : 0 < n) (x : QZ) (hx : n • x = 0) :
    x ∈ AddSubgroup.zmultiples (QuotientAddGroup.mk ((1 : ℚ) / n) : QZ) := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
  have h1 : (QuotientAddGroup.mk (n • q) : QZ) = 0 := hx
  obtain ⟨k, hk⟩ := (QuotientAddGroup.eq_zero_iff _).1 h1
  have hk' : (k : ℚ) = n • q := hk
  refine AddSubgroup.mem_zmultiples_iff.2 ⟨k, ?_⟩
  show (QuotientAddGroup.mk (k • ((1 : ℚ) / n)) : QZ) = _
  congr 1
  rw [zsmul_eq_mul, hk', nsmul_eq_mul]
  field_simp

section general

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G)

theorem exists_defect {t : G → ℚ} (χ : Additive G →+ QZ)
    (h : ∀ g, (QuotientAddGroup.mk (t g) : QZ) = χ (Additive.ofMul g)) :
    ∃ m : (Fin 2 → G) → ℤ, ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1) := by
  have : ∀ g : Fin 2 → G, ∃ k : ℤ, (k : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1) := fun g => by
    have h0 : (QuotientAddGroup.mk (t (g 0) + t (g 1) - t (g 0 * g 1)) : QZ) = 0 := by
      rw [QuotientAddGroup.mk_sub, QuotientAddGroup.mk_add, h, h, h, ofMul_mul, map_add (f := _), sub_self]
    obtain ⟨k, hk⟩ := (QuotientAddGroup.eq_zero_iff _).1 h0
    exact ⟨k, hk⟩
  choose m hm using this
  exact ⟨m, hm⟩

theorem isLocallyConstant_defect {t : G → ℚ} (ht : IsLocallyConstant t) {m : (Fin 2 → G) → ℤ}
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) : IsLocallyConstant m := by
  refine IsLocallyConstant.desc m (Int.cast : ℤ → ℚ) ?_ Int.cast_injective
  have : ((Int.cast : ℤ → ℚ) ∘ m) = fun g => t (g 0) + t (g 1) - t (g 0 * g 1) := funext hm
  rw [this]
  exact ((ht.comp_continuous (continuous_apply 0)).add (ht.comp_continuous (continuous_apply 1))).sub
    (ht.comp_continuous ((continuous_apply 0).mul (continuous_apply 1)))

theorem defect_cocycle {t : G → ℚ} {m : (Fin 2 → G) → ℤ}
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) (x y w : G) :
    m ![y, w] - m ![x * y, w] + m ![x, y * w] = m ![x, y] := by
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [hm, hm, hm, hm]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_assoc]
  ring

theorem exists_defect_cocycle {t : G → ℚ} (ht : IsLocallyConstant t) {m : (Fin 2 → G) → ℤ}
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) (a : M.V) (ha : ∀ g, M.rho g a = a) :
    ∃ z : M.coch.X 2, M.coch.d 2 z = 0 ∧ ∀ g, z.1 g = m g • a := by
  have hc : Continuous fun g => m g • a :=
    ((isLocallyConstant_defect ht hm).comp (fun k : ℤ => k • a)).continuous
  refine ⟨⟨fun g => m g • a, hc⟩, Subtype.ext (funext fun v => ?_), fun _ => rfl⟩
  show ReciprocityTheory.Gal.dn M.rho 2 (fun g => m g • a) v = 0
  rw [LowDeg.dn_two_apply, map_zsmul, ha, ← sub_smul, ← add_smul, ← sub_smul,
    defect_cocycle hm, sub_self, zero_smul]

variable [Fintype G]

theorem sum_defect_smul {m : (Fin 2 → G) → ℤ} (a : M.V) (b : M.coch.X 1)
    (hb : ∀ g, (M.coch.d 1 b).1 g = m g • a) (τ : G) :
    (∑ σ, m ![σ, τ]) • a = ∑ σ, M.rho σ (b.1 ![τ]) := by
  have h1 : ∀ σ : G, m ![σ, τ] • a = M.rho σ (b.1 ![τ]) - b.1 ![σ * τ] + b.1 ![σ] := fun σ => by
    rw [← hb]
    exact LowDeg.dn_one_apply M.rho b.1 ![σ, τ]
  have h2 : ∑ σ, b.1 ![σ * τ] = ∑ σ, b.1 ![σ] := Equiv.sum_comp (Equiv.mulRight τ) (fun σ => b.1 ![σ])
  rw [Finset.sum_smul, Finset.sum_congr rfl fun σ _ => h1 σ, Finset.sum_add_distrib, Finset.sum_sub_distrib, h2]
  abel

theorem sum_defect {t : G → ℚ} {m : (Fin 2 → G) → ℤ}
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) (τ : G) :
    ((∑ σ, m ![σ, τ] : ℤ) : ℚ) = Fintype.card G * t τ := by
  push_cast
  rw [Finset.sum_congr rfl fun σ _ => hm ![σ, τ]]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have h2 : ∑ σ, t (σ * τ) = ∑ σ, t σ := Equiv.sum_comp (Equiv.mulRight τ) t
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, h2]
  simp

theorem exists_cobound_of_norm [DiscreteTopology G] {t : G → ℚ} {m : (Fin 2 → G) → ℤ}
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) (y : M.V) :
    ∃ b : M.coch.X 1, ∀ g, (M.coch.d 1 b).1 g = m g • ∑ ρ, M.rho ρ y := by
  refine ⟨⟨fun w => ∑ ρ, m ![w 0, ρ] • M.rho (w 0 * ρ) y, continuous_of_discreteTopology⟩, fun v => ?_⟩
  show ReciprocityTheory.Gal.dn M.rho 1 (fun w => ∑ ρ, m ![w 0, ρ] • M.rho (w 0 * ρ) y) v = _
  rw [LowDeg.dn_one_apply]
  simp only [Matrix.cons_val_zero]
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Equiv.sum_comp (Equiv.mulLeft (v 1)) (fun ρ => m ![v 0, ρ] • M.rho (v 0 * ρ) y),
    ← Equiv.sum_comp (Equiv.mulLeft (v 0 * v 1)) (fun ρ => M.rho ρ y), map_sum, Finset.smul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  simp only [Equiv.coe_mulLeft]
  rw [map_zsmul, ← Module.End.mul_apply, ← map_mul, ← mul_assoc, ← sub_smul, ← add_smul, defect_cocycle hm, ← hv]

end general

end ReciprocityTheory.DiscreteGroups.LocalClassField.RecCyc
end

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.RecCyc

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

theorem isCoprime_of_gen {G : Type} [Group G] [Fintype G] (g₀ : G) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) (r : ℚ)
    (hr : ∀ e : ℕ, (∃ j : ℤ, (e : ℚ) * r = j) → g₀ ^ e = 1) (k : ℤ) (hk : (k : ℚ) = Fintype.card G * r) :
    IsCoprime k (Fintype.card G : ℤ) := by
  have hn : 0 < Fintype.card G := Fintype.card_pos
  have ho : orderOf g₀ = Fintype.card G := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  rw [Int.isCoprime_iff_gcd_eq_one]
  obtain ⟨j, hj⟩ : ((Int.gcd k (Fintype.card G : ℤ) : ℕ) : ℤ) ∣ k := Int.gcd_dvd_left ..
  obtain ⟨e, he⟩ : Int.gcd k (Fintype.card G : ℤ) ∣ Fintype.card G :=
    Int.natCast_dvd_natCast.1 (Int.gcd_dvd_right ..)
  generalize Int.gcd k (Fintype.card G : ℤ) = d at hj he
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos ⟨e, he⟩ hn
  have he0 : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; simp at he)
  have h1 : g₀ ^ e = 1 := by
    refine hr e ⟨j, ?_⟩
    have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd0.ne'
    rw [hj, he] at hk
    push_cast at hk
    apply mul_left_cancel₀ hd'
    rw [hk]; ring
  have h2 : Fintype.card G ∣ e := ho ▸ orderOf_dvd_of_pow_eq_one h1
  rw [he] at h2
  have h3 : d * e ≤ 1 * e := by simpa using Nat.le_of_dvd he0 h2
  have := Nat.le_of_mul_le_mul_right h3 he0
  omega

theorem exists_gen_of_injective {G : Type} [Group G] [Finite G] (f : Additive G →+ QZ) (hf : Injective f) :
    ∃ g₀ : G, ∀ g, g ∈ Subgroup.zpowers g₀ := by
  have hn : 0 < Nat.card (Additive G) := Nat.card_pos
  have hmem : ∀ g, f g ∈ AddSubgroup.zmultiples
      (QuotientAddGroup.mk ((1 : ℚ) / (Nat.card (Additive G) : ℕ)) : QZ) := fun g =>
    qz_mem_zmultiples hn _ (by rw [← map_nsmul, card_nsmul_eq_zero', map_zero])
  have hf' : Injective (f.codRestrict _ hmem) := fun a b h => hf (congrArg Subtype.val h)
  have h1 : IsAddCyclic (Additive G) := isAddCyclic_of_injective _ hf'
  have h2 : IsCyclic G := isAddCyclic_additive_iff.1 h1
  exact IsCyclic.exists_generator

theorem defect_mem_B_iff {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : TRep R G) [Fintype G] [DiscreteTopology G] {t : G → ℚ} {m : (Fin 2 → G) → ℤ}
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) (a : M.V) (ha : ∀ g, M.rho g a = a)
    (z : M.coch.X 2) (hza : ∀ g, z.1 g = m g • a) (g₀ : G) (hg : ∀ g, g ∈ Subgroup.zpowers g₀)
    (hr : ∀ e : ℕ, (∃ j : ℤ, (e : ℚ) * t g₀ = j) → g₀ ^ e = 1) :
    z ∈ M.coch.B 2 ↔ ∃ y, ∑ g, M.rho g y = a := by
  constructor
  · rintro ⟨b, hb⟩
    have h1 := sum_defect_smul M a b (fun g => by rw [hb]; exact hza g) g₀
    have h2 := sum_defect hm g₀
    generalize (∑ σ, m ![σ, g₀]) = k at h1 h2
    obtain ⟨u, v, huv⟩ := isCoprime_of_gen g₀ hg (t g₀) hr k h2
    have h3 : ∑ g, M.rho g a = (Fintype.card G : ℤ) • a := by
      rw [Finset.sum_congr rfl fun g _ => ha g]
      simp
    refine ⟨u • b.1 ![g₀] + v • a, ?_⟩
    simp only [map_add (f := _), map_zsmul]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, ← h1, h3, smul_smul, smul_smul, ← add_smul,
      huv, one_smul]
  · rintro ⟨y, rfl⟩
    obtain ⟨b, hb⟩ := exists_cobound_of_norm M hm y
    exact ⟨b, Subtype.ext (funext fun g => by rw [hb, hza])⟩

variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem kbarRep_ofK (σ : GK p K) (a : Additive Kˣ) : kbarRep p K σ (ofK p K a) = ofK p K a :=
  (mem_multOf_iff_fixed (le_refl K) _).1 (ofK_mem p K a) σ (fun y hy => σ.commutes ⟨y, hy⟩)

theorem exists_ofK_eq (x : KbarMult p) (hx : x ∈ multOf p K) : ∃ a : Kˣ, ofK p K (Additive.ofMul a) = x := by
  refine ⟨Units.mk0 ⟨((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p), hx⟩
    (fun h => (Additive.toMul x : (PadicAlgCl p)ˣ).ne_zero (congrArg Subtype.val h)), ?_⟩
  exact Units.ext rfl


variable (p K L) in
noncomputable def kToLayer [(subG p K L).Normal] : Additive Kˣ →+ (layer p K L).V where
  toFun a := ⟨ofK p K a, fun g => kbarRep_ofK g.1 a⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)

theorem kToLayer_val [(subG p K L).Normal] (a : Additive Kˣ) : (kToLayer p K L a).1 = ofK p K a := rfl

theorem kToLayer_rho [(subG p K L).Normal] (g : GalLK p K L) (a : Additive Kˣ) :
    (layer p K L).rho g (kToLayer p K L a) = kToLayer p K L a :=
  (layer_invariant_iff _).2 (ofK_mem p K a) g

theorem exists_lift_layer [(subG p K L).Normal] (χ : charGrp (GK p K)) (hχ : TrivOn p K L χ) :
    ∃ tb : GalLK p K L → ℚ, IsLocallyConstant tb ∧
      ∀ g : GK p K, (QuotientAddGroup.mk (tb (QuotientGroup.mk g)) : QZ) = χ.1 (Additive.ofMul g) := by
  have key : ∀ g : GK p K, χ.1 (Additive.ofMul (QuotientGroup.mk g : GalLK p K L).out) = χ.1 (Additive.ofMul g) := by
    intro g
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (subG p K L) g
    rw [hh, ofMul_mul, map_add (f := _), hχ h.1 h.2, add_zero]
  refine ⟨fun q => (χ.1 (Additive.ofMul q.out)).out, fun s => ?_, fun g => ?_⟩
  · rw [← QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.isOpen_preimage]
    have h1 : IsLocallyConstant fun g : GK p K => (χ.1 (Additive.ofMul g)).out :=
      IsLocallyConstant.comp (f := fun g : GK p K => χ.1 (Additive.ofMul g)) χ.2 (fun x : QZ => x.out)
    convert h1 s using 1
    ext g
    simp only [Set.mem_preimage, key]
  · rw [QuotientAddGroup.out_eq', key]

theorem exists_defect_layer [(subG p K L).Normal] (χ : charGrp (GK p K)) (tb : GalLK p K L → ℚ)
    (htb : ∀ g : GK p K, (QuotientAddGroup.mk (tb (QuotientGroup.mk g)) : QZ) = χ.1 (Additive.ofMul g)) :
    ∃ mb : (Fin 2 → GalLK p K L) → ℤ, ∀ q, (mb q : ℚ) = tb (q 0) + tb (q 1) - tb (q 0 * q 1) := by
  obtain ⟨m, hm⟩ := exists_defect (t := fun g : GK p K => tb (QuotientGroup.mk g)) χ.1 htb
  refine ⟨fun q => m fun i => (q i).out, fun q => ?_⟩
  rw [hm]
  simp only [QuotientGroup.mk_mul, QuotientGroup.out_eq']

theorem pairBr_eq_layerInf [(subG p K L).Normal] (a : Kˣ) (χ : charGrp (GK p K)) (tb : GalLK p K L → ℚ)
    (htb : IsLocallyConstant tb)
    (hχ : ∀ g : GK p K, (QuotientAddGroup.mk (tb (QuotientGroup.mk g)) : QZ) = χ.1 (Additive.ofMul g))
    (mb : (Fin 2 → GalLK p K L) → ℤ) (hmb : ∀ q, (mb q : ℚ) = tb (q 0) + tb (q 1) - tb (q 0 * q 1))
    (z : (layer p K L).coch.X 2) (hz : (layer p K L).coch.d 2 z = 0)
    (hza : ∀ q, z.1 q = mb q • kToLayer p K L (Additive.ofMul a)) :
    pairBr p K a χ = (layerInf p K L).hom.H 2 ((layer p K L).coch.cls 2 z hz) := by
  refine (isPairClass_pairBr a χ).unique ⟨fun g => tb (QuotientGroup.mk g), fun g => mb fun i => QuotientGroup.mk (g i),
    (layerInf p K L).hom.f 2 z, by rw [← (layerInf p K L).hom.comm, hz, map_zero],
    htb.comp_continuous continuous_quot_mk, hχ, fun g => hmb _, fun g => ?_, rfl⟩
  show (z.1 fun i => QuotientGroup.mk (g i)).1 = _
  rw [hza]
  rfl

theorem mem_normGrp_iff_layer (h : K ≤ L) [(subG p K L).Normal] [Fintype (GalLK p K L)] (a : Kˣ) :
    a ∈ normGrp p K L ↔ ∃ y : (layer p K L).V, ∑ g, (layer p K L).rho g y = kToLayer p K L (Additive.ofMul a) := by
  rw [mem_normGrp_iff]
  constructor
  · rintro ⟨y, hy, e⟩
    refine ⟨toLayer p ⟨y, hy⟩, Subtype.ext ?_⟩
    rw [← normHom_layer h, kToLayer_val]
    exact e
  · rintro ⟨y, hy⟩
    refine ⟨y.1, layer_val_mem h y, ?_⟩
    rw [normHom_layer h, hy, kToLayer_val]

end ReciprocityTheory.DiscreteGroups.LocalClassField.RecCyc
end

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

def RecCyc.kerChar (χ : charGrp (GK p K)) : Subgroup (GK p K) where
  carrier := {g | χ.1 (Additive.ofMul g) = 0}
  one_mem' := map_zero χ.1
  mul_mem' := fun {a b} ha hb => by
    show χ.1 (Additive.ofMul a + Additive.ofMul b) = 0
    rw [map_add (f := _), show χ.1 (Additive.ofMul a) = 0 from ha, show χ.1 (Additive.ofMul b) = 0 from hb, add_zero]
  inv_mem' := fun {a} ha => by
    show χ.1 (- Additive.ofMul a) = 0
    rw [map_neg, show χ.1 (Additive.ofMul a) = 0 from ha, neg_zero]

theorem exists_field_of_char (hK : FiniteDimensional ℚ_[p] K) (χ : charGrp (GK p K)) :
    ∃ L : IntermediateField ℚ_[p] (PadicAlgCl p), K ≤ L ∧ FiniteDimensional ℚ_[p] L ∧ ∀ g, χ.1 (Additive.ofMul g) = 0 ↔ g ∈ subG p K L := by
  obtain ⟨L, h, hL, e⟩ := exists_subG_eq_of_isOpen hK (RecCyc.kerChar χ) (χ.2 {0})
  exact ⟨L, h, hL, fun g => by rw [e]; exact Iff.rfl⟩

theorem normal_of_char (χ : charGrp (GK p K)) (hχ : ∀ g, χ.1 (Additive.ofMul g) = 0 ↔ g ∈ subG p K L) :
    (subG p K L).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [← hχ] at hn ⊢
  rw [ofMul_mul, ofMul_mul, ofMul_inv, map_add (f := _), map_add (f := _), map_neg, hn]
  abel

noncomputable def RecCyc.charBar [(subG p K L).Normal] (χ : charGrp (GK p K)) (hχ : TrivOn p K L χ) :
    Additive (GalLK p K L) →+ QZ :=
  MonoidHom.toAdditiveLeft (QuotientGroup.lift (subG p K L) (AddMonoidHom.toMultiplicativeRight χ.1)
    (fun g hg => congrArg Multiplicative.ofAdd (hχ g hg)))

theorem RecCyc.charBar_injective [(subG p K L).Normal] (χ : charGrp (GK p K))
    (hχ : ∀ g, χ.1 (Additive.ofMul g) = 0 ↔ g ∈ subG p K L) :
    Injective (RecCyc.charBar χ (fun g hg => (hχ g).2 hg)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (Additive.toMul a)
  have ha' : a = Additive.ofMul (QuotientGroup.mk g) := by rw [hg]; rfl
  rw [ha'] at ha
  have ha2 : χ.1 (Additive.ofMul g) = 0 := ha
  rw [hχ] at ha2
  rw [ha']
  exact congrArg Additive.ofMul ((QuotientGroup.eq_one_iff g).2 ha2)

theorem cyclic_of_char (hL : FiniteDimensional ℚ_[p] L) (χ : charGrp (GK p K)) (hχ : ∀ g, χ.1 (Additive.ofMul g) = 0 ↔ g ∈ subG p K L)
    [(subG p K L).Normal] : ∃ g₀ : GalLK p K L, ∀ g, g ∈ Subgroup.zpowers g₀ := by
  have := finite_GalLK (K := K) hL
  exact RecCyc.exists_gen_of_injective _ (RecCyc.charBar_injective χ hχ)

theorem RecCyc.cls_layer_eq_zero_iff (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (a : Kˣ) (χ : charGrp (GK p K))
    (hχ : ∀ g, χ.1 (Additive.ofMul g) = 0 ↔ g ∈ subG p K L) [(subG p K L).Normal] [Fintype (GalLK p K L)]
    [DiscreteTopology (GalLK p K L)] (tb : GalLK p K L → ℚ)
    (htχ : ∀ g : GK p K, (QuotientAddGroup.mk (tb (QuotientGroup.mk g)) : QZ) = χ.1 (Additive.ofMul g))
    (mb : (Fin 2 → GalLK p K L) → ℤ) (hmb : ∀ q, (mb q : ℚ) = tb (q 0) + tb (q 1) - tb (q 0 * q 1))
    (z : (layer p K L).coch.X 2) (hza : ∀ q, z.1 q = mb q • RecCyc.kToLayer p K L (Additive.ofMul a)) :
    z ∈ (layer p K L).coch.B 2 ↔ a ∈ normGrp p K L := by
  obtain ⟨g₀, hg⟩ := cyclic_of_char hL χ hχ
  rw [RecCyc.mem_normGrp_iff_layer h]
  refine RecCyc.defect_mem_B_iff (layer p K L) hmb _ (fun g => RecCyc.kToLayer_rho g _) z hza g₀ hg ?_
  rintro e ⟨j, hj⟩
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g₀
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, ← hχ, ofMul_pow, map_nsmul, ← htχ]
  show (QuotientAddGroup.mk (e • tb (QuotientGroup.mk σ)) : QZ) = 0
  rw [nsmul_eq_mul, hj, QuotientAddGroup.eq_zero_iff]
  exact ⟨j, rfl⟩

theorem pairBr_eq_zero_iff (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (a : Kˣ) (χ : charGrp (GK p K))
    (hχ : ∀ g, χ.1 (Additive.ofMul g) = 0 ↔ g ∈ subG p K L) :
    pairBr p K a χ = 0 ↔ a ∈ normGrp p K L := by
  have hN : (subG p K L).Normal := normal_of_char χ hχ
  have hT : TrivOn p K L χ := fun g hg => (hχ g).2 hg
  have hF := finite_GalLK (K := K) hL
  have hD : DiscreteTopology (GalLK p K L) := discreteTopology_GalLK hL
  obtain ⟨tb, htb, htχ⟩ := RecCyc.exists_lift_layer χ hT
  obtain ⟨mb, hmb⟩ := RecCyc.exists_defect_layer χ tb htχ
  obtain ⟨z, hz, hza⟩ := RecCyc.exists_defect_cocycle (layer p K L) htb hmb (RecCyc.kToLayer p K L (Additive.ofMul a))
    (fun g => RecCyc.kToLayer_rho g _)
  have key := @RecCyc.cls_layer_eq_zero_iff p _ K L hL h a χ hχ hN (Fintype.ofFinite _) hD tb htχ mb hmb z hza
  rw [RecCyc.pairBr_eq_layerInf a χ tb htb htχ mb hmb z hz hza, ← key, ← Cx.cls_eq_zero_iff hz]
  exact ⟨fun h0 => layer_inflation_h2_injective (h0.trans (map_zero _).symm), fun h0 => by rw [h0, map_zero]⟩

theorem pairK_eq_zero_iff (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (a : Kˣ) (χ : charGrp (GK p K))
    (hχ : ∀ g, χ.1 (Additive.ofMul g) = 0 ↔ g ∈ subG p K L) :
    pairK p K a χ = 0 ↔ a ∈ normGrp p K L := by
  rw [← pairBr_eq_zero_iff hK hL h a χ hχ]
  exact map_eq_zero_iff (invBr p K) (invBr_bijective hK).1

theorem index_normGrp_cyclic (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) [(subG p K L).Normal] (g₀ : GalLK p K L)
    (hg : ∀ g, g ∈ Subgroup.zpowers g₀) : (normGrp p K L).index = degLK p K L := by
  have hF := finite_GalLK (K := K) hL
  let _ : Fintype (GalLK p K L) := Fintype.ofFinite _
  rw [← card_H0hat_layer hK hL h g₀ hg]
  let f : Kˣ →* Multiplicative (Herbrand.TateZerothCohomology (layer p K L).rho g₀) := AddMonoidHom.toMultiplicativeRight
    ((QuotientAddGroup.mk' _).comp ((RecCyc.kToLayer p K L).codRestrict (Herbrand.dHom (layer p K L).rho g₀).ker
      (fun a => (Herbrand.mem_ker_dHom_iff _ g₀ hg _).2 (fun c => RecCyc.kToLayer_rho c a))))
  have hker : f.ker = normGrp p K L := by
    ext a
    rw [MonoidHom.mem_ker, RecCyc.mem_normGrp_iff_layer h]
    refine Iff.trans (Herbrand.mk_eq_zero_iff (D := Herbrand.dHom (layer p K L).rho g₀)
      (N := Herbrand.nHom (layer p K L).rho) _) ?_
    refine exists_congr fun y => ?_
    rw [Herbrand.nHom_apply]
    exact Iff.rfl
  have hsurj : Surjective f := by
    intro x
    obtain ⟨w, hw⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd x)
    obtain ⟨a, ha⟩ := RecCyc.exists_ofK_eq w.1.1
      ((layer_invariant_iff w.1).1 ((Herbrand.mem_ker_dHom_iff _ g₀ hg _).1 w.2))
    refine ⟨a, ?_⟩
    rw [← ofAdd_toAdd x, ← hw]
    exact congrArg (fun w => Multiplicative.ofAdd (QuotientAddGroup.mk w)) (Subtype.ext (Subtype.ext ha))
  rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj]
  exact Nat.card_congr Subgroup.topEquiv.toEquiv

theorem eq_zero_of_pairK_eq_zero (hK : FiniteDimensional ℚ_[p] K) (χ : charGrp (GK p K)) (h : ∀ a, pairK p K a χ = 0) : χ = 0 := by
  obtain ⟨L, hKL, hL, hχ⟩ := exists_field_of_char hK χ
  have hN := normal_of_char χ hχ
  obtain ⟨g₀, hg⟩ := cyclic_of_char hL χ hχ
  have h1 : normGrp p K L = ⊤ := eq_top_iff.2 fun a _ => (pairK_eq_zero_iff hK hL hKL a χ hχ).1 (h a)
  have h2 := index_normGrp_cyclic hK hL hKL g₀ hg
  rw [h1, Subgroup.index_top] at h2
  have h3 : subG p K L = ⊤ := Subgroup.index_eq_one.1 h2.symm
  refine Subtype.ext (AddMonoidHom.ext fun g => ?_)
  exact (hχ (Additive.toMul g)).2 (h3 ▸ Subgroup.mem_top _)

end ReciprocityTheory.DiscreteGroups.LocalClassField
