module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharFiniteOrderOfTrivialAtInfinity

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTameLocOfResidue
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr

variable {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))

theorem tame_valued_int (a : 𝓞 L) :
    Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) a) = v.valuation L (algebraMap (𝓞 L) L a) :=
  ReciprocityTheory.Aut.adic_valued_algebraMap v (algebraMap (𝓞 L) L a)

theorem tame_valued_lt_one_iff (a : 𝓞 L) :
    Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) a) < 1 ↔ a ∈ v.asIdeal := by
  rw [tame_valued_int,
    HeightOneSpectrum.valuation_lt_one_iff_mem]

theorem tame_mk_eq {u : v.adicCompletion L} {a b : 𝓞 L}
    (ha : Valued.v (u - algebraMap (𝓞 L) (v.adicCompletion L) a) < 1)
    (hb : Valued.v (u - algebraMap (𝓞 L) (v.adicCompletion L) b) < 1) :
    Ideal.Quotient.mk v.asIdeal a = Ideal.Quotient.mk v.asIdeal b := by
  rw [Ideal.Quotient.eq, ← tame_valued_lt_one_iff, map_sub]
  have e : algebraMap (𝓞 L) (v.adicCompletion L) a - algebraMap (𝓞 L) (v.adicCompletion L) b =
      (u - algebraMap (𝓞 L) (v.adicCompletion L) b) - (u - algebraMap (𝓞 L) (v.adicCompletion L) a) := by
    ring
  rw [e]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hb ha)

def unitPart : (v.adicCompletion L)ˣ →* (v.adicCompletion L)ˣ where
  toFun x := x * atFin v (unif v) ^ WithZero.log (Valued.v (x : v.adicCompletion L))
  map_one' := by simp
  map_mul' x y := by
    rw [Units.val_mul, map_mul, WithZero.log_mul (by simp) (by simp), zpow_add]
    exact mul_mul_mul_comm _ _ _ _

theorem isUnitAt_unitPart (x : (v.adicCompletion L)ˣ) : IsUnitAt v (unitPart v x) := by
  have h : Valued.v ((atFin v (unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) =
      WithZero.exp (-1 : ℤ) := unif_spec v
  have hx : Valued.v (x : v.adicCompletion L) ≠ 0 := by simp
  show Valued.v ((x * atFin v (unif v) ^ WithZero.log (Valued.v (x : v.adicCompletion L)) :
    (v.adicCompletion L)ˣ) : v.adicCompletion L) = 1
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, h, ← WithZero.exp_zsmul]
  nth_rewrite 1 [← WithZero.exp_log hx]
  rw [← WithZero.exp_add]
  simp

theorem unitPart_of_isUnitAt {x : (v.adicCompletion L)ˣ} (hx : IsUnitAt v x) : unitPart v x = x := by
  have h : Valued.v (x : v.adicCompletion L) = 1 := hx
  show x * atFin v (unif v) ^ WithZero.log (Valued.v (x : v.adicCompletion L)) = x
  rw [h]
  simp

theorem exists_unitPart_approx (x : (v.adicCompletion L)ˣ) : ∃ a : 𝓞 L,
    Valued.v ((unitPart v x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) a) < 1 :=
  ReciprocityTheory.Aut.adic_exists_approx v _ (le_of_eq (isUnitAt_unitPart v x))

def resPart : (v.adicCompletion L)ˣ →* 𝓞 L ⧸ v.asIdeal where
  toFun x := Ideal.Quotient.mk v.asIdeal (exists_unitPart_approx v x).choose
  map_one' := by
    refine tame_mk_eq v (b := 1) (exists_unitPart_approx v 1).choose_spec ?_
    simp
  map_mul' x y := by
    rw [← map_mul]
    refine tame_mk_eq v (exists_unitPart_approx v (x * y)).choose_spec ?_
    have hx := (exists_unitPart_approx v x).choose_spec
    have hy := (exists_unitPart_approx v y).choose_spec
    set a := (exists_unitPart_approx v x).choose
    set b := (exists_unitPart_approx v y).choose
    have hu : Valued.v (unitPart v x : v.adicCompletion L) = 1 := isUnitAt_unitPart v x
    have hb : Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) b) ≤ 1 := by
      rw [tame_valued_int]
      exact v.valuation_le_one b
    have e : (unitPart v (x * y) : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) (a * b) =
        (unitPart v x : v.adicCompletion L) *
          ((unitPart v y : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) b) +
        ((unitPart v x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) a) *
          algebraMap (𝓞 L) (v.adicCompletion L) b := by
      rw [map_mul, map_mul, Units.val_mul]
      ring
    rw [e]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rwa [map_mul, hu, one_mul]
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hb) hx

theorem resPart_eq {x : (v.adicCompletion L)ˣ} (hx : IsUnitAt v x) {a : 𝓞 L}
    (ha : Valued.v ((x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) a) < 1) :
    resPart v x = Ideal.Quotient.mk v.asIdeal a := by
  refine tame_mk_eq v (exists_unitPart_approx v x).choose_spec ?_
  rwa [unitPart_of_isUnitAt v hx]


open Classical in
theorem exists_tameLoc_of_residue : ∀ (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) (θ0 : (𝓞 L ⧸ v.asIdeal)ˣ →* ℂˣ), ∃ θ : (v.adicCompletion L)ˣ →* ℂˣ, TameLoc v θ ∧ (∀ (k : Lˣ) (y : 𝓞 L) (b : (𝓞 L ⧸ v.asIdeal)ˣ), (k : L) = (y : L) → (b : 𝓞 L ⧸ v.asIdeal) = Ideal.Quotient.mk v.asIdeal y → θ (atFin v k) = θ0 b) ∧ ∀ x, IsUnitAt v x → ∃ b, θ x = θ0 b := by
  intro L _ _ v θ0
  haveI : Finite (𝓞 L ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  refine ⟨θ0.comp (resPart v).toHomUnits, ⟨fun x => ?_, fun x hx h1 => ?_⟩, fun k y b hk hb => ?_,
    fun x _ => ⟨_, rfl⟩⟩
  · have hf : IsOfFinOrder ((θ0 ((resPart v).toHomUnits x) : ℂˣ) : ℂ) :=
      ((Units.coeHom ℂ).comp θ0).isOfFinOrder (isOfFinOrder_of_finite _)
    exact hf.norm_eq_one
  · have e : (resPart v).toHomUnits x = 1 := by
      apply Units.ext
      show resPart v x = Ideal.Quotient.mk v.asIdeal 1
      refine resPart_eq v hx ?_
      rw [map_one]
      refine lt_of_le_of_lt h1 ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num
    rw [MonoidHom.comp_apply, e, map_one]
  · have ek : ((atFin v k : (v.adicCompletion L)ˣ) : v.adicCompletion L) =
        algebraMap (𝓞 L) (v.adicCompletion L) y := by
      show algebraMap L (v.adicCompletion L) (k : L) = _
      rw [hk]
      rfl
    have hy : y ∉ v.asIdeal := by
      intro hy
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hy] at hb
      haveI := v.isPrime
      exact b.ne_zero hb
    have hu : IsUnitAt v (atFin v k) := by
      show Valued.v ((atFin v k : (v.adicCompletion L)ˣ) : v.adicCompletion L) = 1
      rw [ek]
      refine le_antisymm ?_ (not_lt.1 fun h => hy ((tame_valued_lt_one_iff v y).1 h))
      rw [tame_valued_int]
      exact v.valuation_le_one y
    have e : (resPart v).toHomUnits (atFin v k) = b := by
      apply Units.ext
      show resPart v (atFin v k) = _
      rw [hb]
      refine resPart_eq v hu ?_
      rw [ek, sub_self, map_zero]
      exact zero_lt_one
    rw [MonoidHom.comp_apply, e]

end GlobalTheory.Mem.Chr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeCharTrivOnRealSubfieldInfinityType
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr.AntiExist

variable {L : Type} [Field L] [NumberField L]

theorem loc_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 v = x := by
  classical
  have := Function.update_self (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v
    (x : v.adicCompletion L) (fun _ => 1)
  convert this
  rfl

theorem loc_ne {v w : HeightOneSpectrum (𝓞 L)} (hw : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 w = 1 := by
  classical
  have := Function.update_of_ne (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) hw
    (x : v.adicCompletion L) (fun _ => 1)
  convert this
  rfl

theorem loc_mem {v : HeightOneSpectrum (𝓞 L)} {x : (v.adicCompletion L)ˣ} (hx : IsUnitAt v x) :
    localIdele L v x ∈ unitIdl L := by
  intro w
  by_cases hw : w = v
  · subst hw
    rw [loc_self]
    exact hx
  · rw [loc_ne hw, map_one]

theorem inf_mem (w : InfinitePlace L) (y : (w.Completion)ˣ) : infIdele L w y ∈ unitIdl L := fun v => by
  show Valued.v (1 : v.adicCompletion L) = 1
  exact map_one _

theorem val_atFin (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) :
    Valued.v ((atFin v k : (v.adicCompletion L)ˣ) : v.adicCompletion L) = v.valuation L (k : L) :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _

theorem val_diag (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) :
    Valued.v (((diagUnits L k : Ideles L) : AdeleRing (𝓞 L) L).2 v) = v.valuation L (k : L) :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _

theorem isUnitAt_of_residue {w : HeightOneSpectrum (𝓞 L)} {k : Lˣ} {y : 𝓞 L} {b : (𝓞 L ⧸ w.asIdeal)ˣ}
    (hk : (k : L) = (y : L)) (hb : (b : 𝓞 L ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal y) :
    IsUnitAt w (atFin w k) := by
  have hy : y ∉ w.asIdeal := fun h => by
    rw [Ideal.Quotient.eq_zero_iff_mem.2 h] at hb
    have := w.isPrime
    exact b.ne_zero hb
  unfold IsUnitAt
  rw [val_atFin, hk]
  exact (HeightOneSpectrum.valuation_of_algebraMap w y).trans (HeightOneSpectrum.intValuation_eq_one_iff.2 hy)

theorem exists_lift {w : HeightOneSpectrum (𝓞 L)} (b : (𝓞 L ⧸ w.asIdeal)ˣ) :
    ∃ (k : Lˣ) (y : 𝓞 L), (k : L) = (y : L) ∧ (b : 𝓞 L ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal y := by
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (b : 𝓞 L ⧸ w.asIdeal)
  have h0 : (y : L) ≠ 0 := fun h => by
    have h' : y = 0 := by exact_mod_cast h
    rw [h', map_zero] at hy
    have := w.isPrime
    exact b.ne_zero hy.symm
  exact ⟨Units.mk0 _ h0, y, rfl, hy.symm⟩

theorem conjPl_symm {c : L ≃+* L} (hc : ∀ x, c (c x) = x) {v v' : HeightOneSpectrum (𝓞 L)} (h : ConjPl c v v') :
    ConjPl c v' v := fun x => by
  rw [← h (c x), hc]

theorem conj_loc {c : L ≃+* L} {C : Ideles L →* Ideles L} (hC : IsConjI c C) {v v' : HeightOneSpectrum (𝓞 L)}
    (h : ConjPl c v v') (x : (v.adicCompletion L)ˣ) :
    ∃ x' : (v'.adicCompletion L)ˣ, C (localIdele L v x) = localIdele L v' x' ∧
      Valued.v (x' : v'.adicCompletion L) = Valued.v (x : v.adicCompletion L) ∧
      Valued.v ((x' : v'.adicCompletion L) - 1) = Valued.v ((x : v.adicCompletion L) - 1) := by
  obtain ⟨x', hx'⟩ := hC.locRange v v' h x
  change C (localIdele L v x) = localIdele L v' x' at hx'
  have h1 := hC.val v v' h (localIdele L v x)
  rw [hx', loc_self, loc_self] at h1
  exact ⟨x', hx', h1⟩

section CM

variable {F : Type} [Field F] [NumberField F] [Algebra F L] {c : L ≃ₐ[F] L} {I : Type} {φ : I → L →+* ℂ}

theorem conj_conj (h : CMData F c φ) (x : L) : c (c x) = x := by
  obtain ⟨ψ⟩ : Nonempty (L →+* ℂ) := inferInstance
  apply ψ.injective
  rw [h.embedding_conj, h.embedding_conj, Complex.conj_conj]

theorem comap_eq (h : CMData F c φ) (w : InfinitePlace L) : w.comap (c.toRingEquiv.symm : L →+* L) = w := by
  ext x
  have e : c.toRingEquiv.symm x = c x := by
    apply c.toRingEquiv.injective
    rw [RingEquiv.apply_symm_apply]
    exact (conj_conj h x).symm
  show w (c.toRingEquiv.symm x) = w x
  rw [e, ← InfinitePlace.norm_embedding_eq, ← InfinitePlace.norm_embedding_eq, h.embedding_conj, Complex.norm_conj]

theorem conj_inf (h : CMData F c φ) {C : Ideles L →* Ideles L} (hC : IsConjI c.toRingEquiv C) (w : InfinitePlace L)
    (k : Lˣ) : C (infIdele L w (atInf w k)) =
      infIdele L w (atInf w (Units.map (MonoidHomClass.toMonoidHom c.toRingEquiv) k)) := by
  have h0 := hC.inf w k
  change C (infIdele L w (atInf w k)) =
    infIdele L (w.comap (c.toRingEquiv.symm : L →+* L)) (atInf _ (Units.map (MonoidHomClass.toMonoidHom c.toRingEquiv) k)) at h0
  rw [h0, comap_eq h]

theorem conj_upF (k : Fˣ) : Units.map (MonoidHomClass.toMonoidHom c.toRingEquiv) (upF F k : Lˣ) = upF F k :=
  Units.ext (c.commutes (k : F))

theorem conj_locF (h : CMData F c φ) {C : Ideles L →* Ideles L} (hC : IsConjI c.toRingEquiv C)
    (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : C (locF F v k) = locF F v k := by
  choose σ hσ hu using fun w => existsUnique_conjPl c.toRingEquiv w
  have hσσ : ∀ w, σ (σ w) = w := fun w => (hu _ _ (conjPl_symm (conj_conj h) (hσ w))).symm
  have hm : ∀ w ∈ aboveF (L := L) F v, σ w ∈ aboveF (L := L) F v := fun w hw => by
    simp only [aboveF, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hw ⊢
    rw [← hw]
    exact (under_eq_iff_conjPl c h.rank h.ne w (σ w)).2 (Or.inr (hσ w))
  unfold locF
  rw [map_prod]
  refine Finset.prod_nbij' σ σ hm hm (fun w _ => hσσ w) (fun w _ => hσσ w) fun w _ => ?_
  rw [hC.loc w (σ w) (hσ w)]
  exact congrArg _ (congrArg _ (conj_upF k))

def normOne (c : L ≃ₐ[F] L) : Subgroup Lˣ :=
  (MonoidHom.id Lˣ * Units.map (MonoidHomClass.toMonoidHom c.toRingEquiv)).ker

theorem mem_normOne {k : Lˣ} : k ∈ normOne c ↔ (k : L) * c (k : L) = 1 := by
  unfold normOne
  rw [MonoidHom.mem_ker, ← Units.val_inj]
  rfl

theorem exists_anti [Fintype I] (h : CMData F c φ) {C : Ideles L →* Ideles L} (hC : IsConjI c.toRingEquiv C)
    (ψ : Ideles L →* ℂˣ) (hψ : Continuous ψ) (hu : ∀ x, ‖((ψ x : ℂˣ) : ℂ)‖ = 1)
    (h1 : ∀ k : Lˣ, (∃ m : ℕ, 0 < m ∧ (k : L) ^ m = 1) → ψ (diagUnits L k) = 1) :
    ∃ χ : HChar L, χ.IsUnitary ∧ ∀ z, z / C z ∈ unitIdl L → χ.1 z = ψ (z / C z) := by
  obtain ⟨ν, hν, hνu, hνU, hν1⟩ := GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (Ideles L) (normOne c) (unitIdl L)
    GlobalTheory.Mem.UnitOpen.isOpen_unitIdl ((diagUnits L).comp (normOne c).subtype) 1 ψ hψ hu (fun _ => by simp) (by
      rintro ⟨k, hk⟩ hkU
      have := normOne_unit_isRoot F L c I φ h k (mem_normOne.1 hk) fun v => by
        rw [← val_diag]; exact hkU v
      show 1 = ψ (diagUnits L k)
      exact (h1 k this).symm)
  refine ⟨⟨ν.comp (MonoidHom.id _ / C), hν.comp (continuous_id.div' hC.cont), fun k => ?_⟩, fun z => hνu _,
    fun z hz => hνU _ hz⟩
  have hk : k / Units.map (MonoidHomClass.toMonoidHom c.toRingEquiv) k ∈ normOne c := by
    rw [mem_normOne, Units.val_div_eq_div_val, map_div₀]
    show (k : L) / c k * (c k / c (c k)) = 1
    have : c (k : L) ≠ 0 := by simp
    rw [conj_conj h]
    field_simp
  have := hν1 ⟨_, hk⟩
  show ν (diagUnits L k / C (diagUnits L k)) = 1
  have hd := hC.diag k
  change C (diagUnits L k) = diagUnits L _ at hd
  rw [hd, ← map_div]
  exact this

end CM

theorem phase_div (z : ℂ) (hz : z ≠ 0) (n : ℤ) :
    (z / (starRingEnd ℂ) z / ((‖z / (starRingEnd ℂ) z‖ : ℝ) : ℂ)) ^ (-n) = (z / ((‖z‖ : ℝ) : ℂ)) ^ (-2 * n) := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
  have hn' : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
  have hc : (starRingEnd ℂ) z ≠ 0 := by simpa using hz
  rw [norm_div, Complex.norm_conj, div_self hn, Complex.ofReal_one, div_one, show -2 * n = 2 * (-n) by ring, zpow_mul]
  congr 1
  rw [zpow_two, div_mul_div_comm, div_eq_div_iff hc (mul_ne_zero hn' hn'), mul_assoc, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  push_cast
  ring


open Classical in
theorem exists_hecke_trivOn : ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (c : L ≃ₐ[F] L) (I : Type) [Fintype I] (φ : I → L →+* ℂ), CMData F c φ → ∀ (e : I → ℤ) (S : Finset (HeightOneSpectrum (𝓞 L))) (θ0 : ∀ v : HeightOneSpectrum (𝓞 L), (𝓞 L ⧸ v.asIdeal)ˣ →* ℂˣ), (∀ w ∈ S, ∀ w', ConjPl c.toRingEquiv w w' → w' ∉ S) → (∀ ζ : (𝓞 L)ˣ, (∃ m : ℕ, 0 < m ∧ ((ζ : 𝓞 L) : L) ^ m = 1) → (∏ i, φ i ((ζ : 𝓞 L) : L) ^ (-e i)) * ∏ w ∈ S, ((θ0 w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom ζ) : ℂˣ) : ℂ) = 1) → ∃ χ : HChar L, χ.IsUnitary ∧ χ.TrivOn F ∧ χ.HasInf φ (fun i => -2 * e i) ∧ (∀ v, χ.TameAt v) ∧ (∀ v, v ∉ S → (∀ w ∈ S, ¬ ConjPl c.toRingEquiv w v) → χ.UnrAt v) ∧ (∀ w ∈ S, ∀ (k : Lˣ) (y : 𝓞 L) (b : (𝓞 L ⧸ w.asIdeal)ˣ), (k : L) = (y : L) → (b : 𝓞 L ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal y → χ.locK w k = θ0 w b) ∧ (∀ w ∈ S, ∀ n : ℕ, ((∀ x, IsUnitAt w x → χ.loc w x ^ n = 1) ↔ θ0 w ^ n = 1) ∧ ∀ w', ConjPl c.toRingEquiv w w' → ((∀ x, IsUnitAt w' x → χ.loc w' x ^ n = 1) ↔ θ0 w ^ n = 1)) := by
  intro F L _ _ _ _ _ c I _ φ h e S θ0 hS hpar
  have hcc : ∀ x, c.toRingEquiv (c.toRingEquiv x) = x := conj_conj h
  obtain ⟨C, hC⟩ := exists_isConjI L c.toRingEquiv
  choose θ hθt hθr hθs using fun v => GlobalTheory.Mem.Chr.exists_tameLoc_of_residue L v (θ0 v)
  obtain ⟨ψ, hψ, hψu, hψi, hψS, hψN, hψd⟩ := GlobalTheory.ModelChar.exists_modelChar L I φ h.bij (fun i => -e i) S θ (fun v _ => hθt v)
  have h1 : ∀ k : Lˣ, (∃ m : ℕ, 0 < m ∧ (k : L) ^ m = 1) → ψ (diagUnits L k) = 1 := by
    intro k hr
    obtain ⟨ζ, rfl⟩ := exists_unit_of_root k hr
    obtain ⟨m, hm, hpow⟩ := hr
    have hkv : ((Units.map (algebraMap (𝓞 L) L : 𝓞 L →* L) ζ : Lˣ) : L) = ((ζ : 𝓞 L) : L) := rfl
    apply Units.ext
    have hinf := (GlobalTheory.InfTypeLocal.infType_iff_local L I φ h.bij ψ hψ _).2 hψi
    change ∀ k, ((ψ (infDiag k) : ℂˣ) : ℂ) = _ at hinf
    rw [hψd, Units.val_mul, Units.coe_prod, hinf, Units.val_one,
      ← hpar ζ ⟨m, hm, hpow⟩]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      have hn : ‖φ i ((Units.map (algebraMap (𝓞 L) L : 𝓞 L →* L) ζ : Lˣ) : L)‖ = 1 :=
        Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hpow, map_one]) hm.ne'
      rw [hn, Complex.ofReal_one, div_one, hkv]
    · refine Finset.prod_congr rfl fun w _ => ?_
      rw [hθr w _ (ζ : 𝓞 L) (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom ζ) rfl rfl]
  obtain ⟨χ, hχu, hχ⟩ := exists_anti h hC ψ hψ hψu h1
  have hfix : ∀ z, C z = z → χ.1 z = 1 := fun z hz => by
    rw [hχ z (by rw [hz, div_self']; exact one_mem _), hz, div_self', map_one]
  have hloc : ∀ v v' x x', C (localIdele L v x) = localIdele L v' x' → IsUnitAt v x → IsUnitAt v' x' →
      χ.loc v x = ψ (localIdele L v x) / ψ (localIdele L v' x') := fun v v' x x' hx h1 h2 => by
    show χ.1 (localIdele L v x) = _
    rw [hχ _ (by rw [hx]; exact div_mem (loc_mem h1) (loc_mem h2)), hx, map_div]
  have htame : ∀ v x, IsUnitAt v x → Valued.v ((x : v.adicCompletion L) - 1) ≤ WithZero.exp (-1 : ℤ) →
      ψ (localIdele L v x) = 1 := fun v x h1 h2 => by
    by_cases hv : v ∈ S
    · rw [hψS v hv, (hθt v).2 x h1 h2]
    · exact hψN v hv x
  have hw : ∀ w ∈ S, ∀ x, IsUnitAt w x → χ.loc w x = θ w x := fun w hwS x hx => by
    obtain ⟨w', hw', -⟩ := existsUnique_conjPl c.toRingEquiv w
    obtain ⟨x', e1, e2, -⟩ := conj_loc hC hw' x
    rw [hloc w w' x x' e1 hx (e2.trans hx), hψS w hwS, hψN w' (hS w hwS w' hw'), div_one]
  let : IsOneApply (Fˣ →* ℂˣ) := ⟨fun _ => rfl⟩
  let : IsMulApply (Fˣ →* ℂˣ) := ⟨fun _ _ _ => rfl⟩
  refine ⟨χ, hχu, ⟨fun v k => ?_, fun w k => ?_⟩, ?_, fun v x hx hx1 => ?_, fun v hv hv' x hx => ?_,
    fun w hwS k y b hk hb => ?_, fun w hwS n => ⟨⟨fun H => ?_, fun H x hx => ?_⟩,
      fun w' hw' => ⟨fun H => ?_, fun H x hx => ?_⟩⟩⟩
  · rw [← hfix _ (conj_locF h hC v k)]
    unfold HChar.resFin locF
    rw [prod_apply, map_prod]
    rfl
  · unfold HChar.resInf
    rw [prod_apply]
    refine Finset.prod_eq_one fun w' _ => hfix (infIdele L w' (atInf w' (upF F k))) ?_
    rw [conj_inf h hC, conj_upF]
  · refine (GlobalTheory.InfTypeLocal.infType_iff_local L I φ h.bij χ.1 χ.2.1 _).2 fun i k => ?_
    change ((χ.1 (infIdele L (InfinitePlace.mk (φ i)) (atInf (InfinitePlace.mk (φ i)) k)) : ℂˣ) : ℂ) = _
    rw [hχ _ (by rw [conj_inf h hC]; exact div_mem (inf_mem _ _) (inf_mem _ _)), conj_inf h hC, ← map_div, ← map_div,
      hψi, Units.val_div_eq_div_val, map_div₀]
    have e1 : φ i ((Units.map (MonoidHomClass.toMonoidHom c.toRingEquiv) k : Lˣ) : L) = (starRingEnd ℂ) (φ i k) :=
      h.embedding_conj (φ i) k
    rw [e1]
    exact phase_div _ (by simp) _
  · obtain ⟨v', hv', -⟩ := existsUnique_conjPl c.toRingEquiv v
    obtain ⟨x', e1, e2, e3⟩ := conj_loc hC hv' x
    have hx2 : Valued.v ((x : v.adicCompletion L) - 1) ≤ WithZero.exp (-1 : ℤ) := by simpa using hx1
    rw [hloc v v' x x' e1 hx (e2.trans hx), htame v x hx hx2, htame v' x' (e2.trans hx) (e3.trans_le hx2), div_one]
  · obtain ⟨v', hc', -⟩ := existsUnique_conjPl c.toRingEquiv v
    obtain ⟨x', e1, e2, -⟩ := conj_loc hC hc' x
    rw [hloc v v' x x' e1 hx (e2.trans hx), hψN v hv, hψN v' (fun hS' => hv' v' hS' (conjPl_symm hcc hc')), div_one]
  · exact (hw w hwS _ (isUnitAt_of_residue hk hb)).trans (hθr w k y b hk hb)
  · ext1 b
    obtain ⟨k, y, hk, hb⟩ := exists_lift b
    have := H _ (isUnitAt_of_residue hk hb)
    rwa [hw w hwS _ (isUnitAt_of_residue hk hb), hθr w k y b hk hb] at this
  · obtain ⟨b, hb⟩ := hθs w x hx
    rw [hw w hwS x hx, hb]
    exact DFunLike.congr_fun H b
  · ext1 b
    obtain ⟨k, y, hk, hb⟩ := exists_lift b
    have hu := isUnitAt_of_residue hk hb
    have hu' : IsUnitAt w' (atFin w' (Units.map (MonoidHomClass.toMonoidHom c.toRingEquiv) k)) := by
      unfold IsUnitAt at hu ⊢
      rw [val_atFin] at hu ⊢
      exact (hw' k).trans hu
    have e1 := hC.loc w' w (conjPl_symm hcc hw') (Units.map (MonoidHomClass.toMonoidHom c.toRingEquiv) k)
    rw [show Units.map (MonoidHomClass.toMonoidHom c.toRingEquiv) (Units.map (MonoidHomClass.toMonoidHom c.toRingEquiv) k) = k
      from Units.ext (hcc k)] at e1
    change C (localIdele L w' (atFin w' (Units.map (MonoidHomClass.toMonoidHom c.toRingEquiv) k))) = localIdele L w (atFin w k) at e1
    have := H _ hu'
    rwa [hloc w' w _ _ e1 hu' hu, hψN w' (hS w hwS w' hw'), hψS w hwS, hθr w k y b hk hb, one_div, inv_pow,
      inv_eq_one] at this
  · obtain ⟨x', e1, e2, -⟩ := conj_loc hC (conjPl_symm hcc hw') x
    obtain ⟨b, hb⟩ := hθs w x' (e2.trans hx)
    rw [hloc w' w x x' e1 hx (e2.trans hx), hψN w' (hS w hwS w' hw'), hψS w hwS, hb, one_div, inv_pow, inv_eq_one]
    exact DFunLike.congr_fun H b

end GlobalTheory.Mem.Chr.AntiExist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeCharTrivOnRealSubfieldInfinityTypeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits GlobalTheory.Mem.Chr Classical
open Neutral.B1 hiding localIdele Ideles diagUnits
open ReciprocityTheory.Neutral.Bridge.HCFR hiding infIdele
open Formalism.L2.Host hiding HChar IsUnitAt ordF upF aboveF atFin atInf infDiag
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeChar_trivOn_realSubfield_infinityType : ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (c : L ≃ₐ[F] L) (I : Type) [Fintype I] (φ : I → L →+* ℂ), CMData F c φ → ∀ (e : I → ℤ) (S : Finset (HeightOneSpectrum (𝓞 L))) (θ0 : ∀ v : HeightOneSpectrum (𝓞 L), (𝓞 L ⧸ v.asIdeal)ˣ →* ℂˣ), (∀ w ∈ S, ∀ w', ConjPl c.toRingEquiv w w' → w' ∉ S) → (∀ ζ : (𝓞 L)ˣ, (∃ m : ℕ, 0 < m ∧ ((ζ : 𝓞 L) : L) ^ m = 1) → (∏ i, φ i ((ζ : 𝓞 L) : L) ^ (-e i)) * ∏ w ∈ S, ((θ0 w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom ζ) : ℂˣ) : ℂ) = 1) → ∃ χ : HChar L, χ.IsUnitary ∧ χ.TrivOn F ∧ χ.HasInf φ (fun i => -2 * e i) ∧ (∀ v, χ.TameAt v) ∧ (∀ v, v ∉ S → (∀ w ∈ S, ¬ ConjPl c.toRingEquiv w v) → χ.UnrAt v) ∧ (∀ w ∈ S, ∀ (k : Lˣ) (y : 𝓞 L) (b : (𝓞 L ⧸ w.asIdeal)ˣ), (k : L) = (y : L) → (b : 𝓞 L ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal y → χ.locK w k = θ0 w b) ∧ (∀ w ∈ S, ∀ n : ℕ, ((∀ x, IsUnitAt w x → χ.loc w x ^ n = 1) ↔ θ0 w ^ n = 1) ∧ ∀ w', ConjPl c.toRingEquiv w w' → ((∀ x, IsUnitAt w' x → χ.loc w' x ^ n = 1) ↔ θ0 w ^ n = 1)) := by
  first | exact @GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn | exact GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn | (intros; apply GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn <;> assumption)
end
