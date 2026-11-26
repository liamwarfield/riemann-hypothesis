module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.HformSmulRight

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.StHOfOpen
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.UnitsModSq
noncomputable section

namespace PIW.AdelClassFin

open NumberField NumberField.Units

theorem units_mod_sq (F : Type) [Field F] [NumberField F] :
    ∃ U : Set F, U.Finite ∧ ∀ c : (𝓞 F)ˣ, ∃ w ∈ U, ∃ v : (𝓞 F)ˣ,
      algebraMap (𝓞 F) F (c : 𝓞 F) = w * algebraMap (𝓞 F) F (v : 𝓞 F) ^ 2 := by
  classical
  let g : torsion F × (Fin (rank F) → Fin 2) → F := fun p =>
    algebraMap (𝓞 F) F (((p.1 : (𝓞 F)ˣ) * ∏ i, fundSystem F i ^ (((p.2 i : ℕ) : ℤ)) : (𝓞 F)ˣ) : 𝓞 F)
  refine ⟨Set.range g, Set.finite_range g, fun c => ?_⟩
  obtain ⟨⟨ζ, e⟩, he, -⟩ := exist_unique_eq_mul_prod F c
  dsimp only at he
  let f : Fin (rank F) → Fin 2 := fun i => ⟨(e i % 2).toNat, by omega⟩
  refine ⟨g (ζ, f), Set.mem_range_self _, ∏ i, fundSystem F i ^ (e i / 2), ?_⟩
  have key : c = ((ζ : (𝓞 F)ˣ) * ∏ i, fundSystem F i ^ (((f i : ℕ) : ℤ))) *
      (∏ i, fundSystem F i ^ (e i / 2)) ^ 2 := by
    rw [he, mul_assoc, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [sq, ← zpow_add, ← zpow_add]
    congr 1
    have h2 : (((f i : ℕ) : ℤ)) = e i % 2 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
    omega
  rw [key, Units.val_mul, map_mul, Units.val_pow_eq_pow_val, map_pow]

theorem partUnits : PartUnits := by
  intro F E _ _ _ _ _ _ hc C
  classical
  obtain ⟨U, hUf, hU⟩ := units_mod_sq F
  let S : Set (Ideal (𝓞 E)) := {I | Ideal.absNorm I ≤ ⌊C⌋₊}
  have hSf : S.Finite := Ideal.finite_setOfPred_absNorm_le _
  let P : Ideal (𝓞 E) → Prop := fun I => ∃ y : 𝓞 E, I = Ideal.span {y} ∧
    star (algebraMap (𝓞 E) E y) = algebraMap (𝓞 E) E y ∧ y ≠ 0
  let rep : Ideal (𝓞 E) → E := fun I => if h : P I then algebraMap (𝓞 E) E h.choose else 1
  refine ⟨Set.image2 (fun w I => algebraMap F E w * rep I) U S \ {0}, (hUf.image2 _ hSf).sdiff,
    fun h => h.2 rfl, ?_⟩
  rintro a ⟨x, rfl⟩ hstar ha hN
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := RingOfIntegers.coe_injective
  have hx0 : x ≠ 0 := by rintro rfl; exact ha (map_zero _)
  have hxS : Ideal.span {x} ∈ S := by
    show Ideal.absNorm _ ≤ _
    rw [Ideal.absNorm_span_singleton]
    apply Nat.le_floor
    have h1 := Algebra.coe_norm_int x
    rw [Nat.cast_natAbs, Int.cast_abs]
    rw [h1]
    exact hN
  have hP : P (Ideal.span {x}) := ⟨x, rfl, hstar, hx0⟩
  obtain ⟨hyI, hys, hy0⟩ := hP.choose_spec
  have hrep : rep (Ideal.span {x}) = algebraMap (𝓞 E) E hP.choose := dif_pos hP
  obtain ⟨w, hw⟩ : Associated hP.choose x := Ideal.span_singleton_eq_span_singleton.mp hyI.symm
  have hyE : algebraMap (𝓞 E) E hP.choose ≠ 0 := fun h => hy0 (hinj (h.trans (map_zero _).symm))
  have h1 : algebraMap (𝓞 E) E x =
      algebraMap (𝓞 E) E hP.choose * algebraMap (𝓞 E) E (w : 𝓞 E) := by
    rw [← map_mul]
    exact congrArg _ hw.symm
  have hWs : star (algebraMap (𝓞 E) E (w : 𝓞 E)) = algebraMap (𝓞 E) E (w : 𝓞 E) := by
    refine mul_left_cancel₀ hyE ?_
    calc algebraMap (𝓞 E) E hP.choose * star (algebraMap (𝓞 E) E (w : 𝓞 E))
        = star (algebraMap (𝓞 E) E hP.choose) * star (algebraMap (𝓞 E) E (w : 𝓞 E)) := by
          rw [hys]
      _ = star (algebraMap (𝓞 E) E hP.choose * algebraMap (𝓞 E) E (w : 𝓞 E)) :=
          (star_mul' _ _).symm
      _ = _ := by rw [← h1, hstar, h1]
  obtain ⟨c, hcW⟩ := (hc.fixed _).1 hWs
  have hWW' : algebraMap (𝓞 E) E (w : 𝓞 E) * algebraMap (𝓞 E) E ((w⁻¹ : (𝓞 E)ˣ) : 𝓞 E) = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [← hcW, map_zero, zero_mul] at hWW'
    exact zero_ne_one hWW'
  have hW' : algebraMap (𝓞 E) E ((w⁻¹ : (𝓞 E)ˣ) : 𝓞 E) = algebraMap F E c⁻¹ := by
    rw [map_inv₀, hcW]
    exact eq_inv_of_mul_eq_one_right hWW'
  have hci : IsIntegral ℤ c := by
    refine (isIntegral_algebraMap_iff (B := E) ).mp ?_
    rw [hcW]
    exact (w : 𝓞 E).2
  have hci' : IsIntegral ℤ c⁻¹ := by
    refine (isIntegral_algebraMap_iff (B := E) ).mp ?_
    rw [← hW']
    exact ((w⁻¹ : (𝓞 E)ˣ) : 𝓞 E).2
  let cu : (𝓞 F)ˣ :=
    { val := ⟨c, hci⟩
      inv := ⟨c⁻¹, hci'⟩
      val_inv := RingOfIntegers.ext (show c * c⁻¹ = 1 from mul_inv_cancel₀ hc0)
      inv_val := RingOfIntegers.ext (show c⁻¹ * c = 1 from inv_mul_cancel₀ hc0) }
  obtain ⟨w0, hw0U, v, hv⟩ := hU cu
  have hcv : c = w0 * algebraMap (𝓞 F) F (v : 𝓞 F) ^ 2 := hv
  let u : (𝓞 E)ˣ := Units.map (RingOfIntegers.mapRingHom (algebraMap F E)).toMonoidHom v
  have hu : algebraMap (𝓞 E) E (u : 𝓞 E) = algebraMap F E (algebraMap (𝓞 F) F (v : 𝓞 F)) := rfl
  have hus : star (algebraMap (𝓞 E) E (u : 𝓞 E)) = algebraMap (𝓞 E) E (u : 𝓞 E) :=
    (hc.fixed _).2 ⟨_, hu.symm⟩
  have main : algebraMap (𝓞 E) E x = star (algebraMap (𝓞 E) E (u : 𝓞 E)) *
      algebraMap (𝓞 E) E (u : 𝓞 E) * (algebraMap F E w0 * rep (Ideal.span {x})) := by
    rw [hus, hrep, h1, ← hcW, hcv, map_mul, map_pow, hu]
    ring
  refine ⟨u, algebraMap F E w0 * rep (Ideal.span {x}),
    ⟨Set.mem_image2_of_mem hw0U hxS, fun h0 => ha ?_⟩, main⟩
  rw [main]
  rw [Set.mem_singleton_iff.mp h0, mul_zero]

end PIW.AdelClassFin
end
end

namespace PIW.AdelClassFin

theorem stH_of_open (hO : SpOne) (hI : IdealBoundAll) (h1 : SvMajE) (h2 : SvCodiff) (h3 : SvBasis) (h4 : SvGramDet)
    (h5 : SvReal) : StH :=
  stH_of_parts (partShort_of partMink h1 h2 h3 h4 h5) partUnits (partIso_of hI) (partSplit_of_one hO)

end PIW.AdelClassFin
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.KsetMulVecMem
noncomputable section

namespace PIW.AdelClassFin

open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix

def StLatFin : Prop :=
  ∀ (I : AutInst) (g : ℕ), 1 ≤ g → ∃ R : Finset (Fin I.n → I.E ⊗[I.F] Af I.F), (∀ r ∈ R, r ∈ I.Lf) ∧
    ∀ y ∈ I.Lf, ∃ r ∈ R, ∃ z ∈ I.Lf, y - r = (g : I.E ⊗[I.F] Af I.F) • z

theorem kset_mulVec_mem (I : AutInst) {k : I.Gf} (hk : k ∈ I.Kset) {y : Fin I.n → I.E ⊗[I.F] Af I.F}
    (hy : y ∈ I.Lf) : I.fmat k *ᵥ y ∈ I.Lf := (hk y).mp hy

theorem kset_inv (I : AutInst) {k : I.Gf} (hk : k ∈ I.Kset) : k⁻¹ ∈ I.Kset := by
  show ((k⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
  rw [Subgroup.coe_inv]
  exact Subgroup.inv_mem _ hk

theorem kset_mul (I : AutInst) {k t : I.Gf} (hk : k ∈ I.Kset) (ht : t ∈ I.Kset) : k * t ∈ I.Kset := by
  show ((k * t : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
  rw [Subgroup.coe_mul]
  exact Subgroup.mul_mem _ hk ht

theorem stKFin_of (hL : StLatFin) : StKFin := by
  classical
  intro I g hg
  obtain ⟨R, hRLf, hR⟩ := hL I g hg
  choose! rep hrepR z hz hrepEq using hR
  let Ψ : I.Kset → (R → R) := fun k r =>
    ⟨rep (I.fmat k *ᵥ (r : Fin I.n → I.E ⊗[I.F] Af I.F)),
      hrepR _ (kset_mulVec_mem I k.2 (hRLf r r.2))⟩
  refine ⟨Finset.univ.image (fun φ : R → R =>
    if h : ∃ k, Ψ k = φ then ((h.choose : I.Kset) : I.Gf) else 1), ?_⟩
  intro k hk
  have hex : ∃ k', Ψ k' = Ψ ⟨k, hk⟩ := ⟨_, rfl⟩
  obtain ⟨t, htdef⟩ : ∃ t : I.Kset, t = hex.choose := ⟨_, rfl⟩
  have htΨ : Ψ t = Ψ ⟨k, hk⟩ := by rw [htdef]; exact hex.choose_spec
  refine ⟨(t : I.Gf), Finset.mem_image.mpr ⟨Ψ ⟨k, hk⟩, Finset.mem_univ _, by rw [dite_eq_left hex, htdef]⟩,
    (t : I.Gf)⁻¹ * k, ?_, (mul_inv_cancel_left (t : I.Gf) k).symm⟩
  refine ⟨kset_mul I (kset_inv I t.2) hk, ?_⟩
  intro y hy
  have hrR : rep y ∈ R := hrepR y hy
  have hkr := hrepEq (I.fmat k *ᵥ rep y) (kset_mulVec_mem I hk (hRLf _ hrR))
  have htr := hrepEq (I.fmat t *ᵥ rep y) (kset_mulVec_mem I t.2 (hRLf _ hrR))
  have hrep_eq : rep (I.fmat k *ᵥ rep y) = rep (I.fmat t *ᵥ rep y) := by
    have h1 := congrFun htΨ ⟨rep y, hrR⟩
    exact (congrArg Subtype.val h1).symm
  have hfu : I.fmat ((t : I.Gf)⁻¹ * k) = I.fmat (t : I.Gf)⁻¹ * I.fmat k := by
    simp only [Formalism.MainNotions.S.AutInst.fmat, Subgroup.coe_mul, Units.val_mul]
  have hinv : I.fmat (t : I.Gf)⁻¹ * I.fmat t = 1 := by
    simp only [Formalism.MainNotions.S.AutInst.fmat, Subgroup.coe_inv, Units.inv_mul]
  refine ⟨I.fmat (t : I.Gf)⁻¹ *ᵥ ((z (I.fmat k *ᵥ rep y) - z (I.fmat t *ᵥ rep y)) +
      (I.fmat k *ᵥ z y - I.fmat t *ᵥ z y)), ?_, ?_⟩
  · apply kset_mulVec_mem I (kset_inv I t.2)
    exact I.Lf.add_mem (I.Lf.sub_mem (hz _ (kset_mulVec_mem I hk (hRLf _ hrR)))
      (hz _ (kset_mulVec_mem I t.2 (hRLf _ hrR))))
      (I.Lf.sub_mem (kset_mulVec_mem I hk (hz y hy)) (kset_mulVec_mem I t.2 (hz y hy)))
  · have hyd : y = rep y + (g : I.E ⊗[I.F] Af I.F) • z y := by rw [← hrepEq y hy, add_sub_cancel]
    have hkrd : I.fmat k *ᵥ rep y = rep (I.fmat k *ᵥ rep y) +
        (g : I.E ⊗[I.F] Af I.F) • z (I.fmat k *ᵥ rep y) := by rw [← hkr, add_sub_cancel]
    have htrd : I.fmat t *ᵥ rep y = rep (I.fmat t *ᵥ rep y) +
        (g : I.E ⊗[I.F] Af I.F) • z (I.fmat t *ᵥ rep y) := by rw [← htr, add_sub_cancel]
    have hy' : y = I.fmat (t : I.Gf)⁻¹ *ᵥ (I.fmat t *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    have hdiff : I.fmat k *ᵥ y - I.fmat t *ᵥ y = (g : I.E ⊗[I.F] Af I.F) •
        ((z (I.fmat k *ᵥ rep y) - z (I.fmat t *ᵥ rep y)) + (I.fmat k *ᵥ z y - I.fmat t *ᵥ z y)) := by
      conv_lhs => rw [hyd, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        hkrd, htrd, hrep_eq]
      rw [smul_add, smul_sub, smul_sub]
      abel
    rw [hfu, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec]
    calc I.fmat (t : I.Gf)⁻¹ *ᵥ (I.fmat k *ᵥ y) - y
        = I.fmat (t : I.Gf)⁻¹ *ᵥ (I.fmat k *ᵥ y) - I.fmat (t : I.Gf)⁻¹ *ᵥ (I.fmat t *ᵥ y) := by
          rw [← hy']
      _ = I.fmat (t : I.Gf)⁻¹ *ᵥ (I.fmat k *ᵥ y - I.fmat t *ᵥ y) := (Matrix.mulVec_sub _ _ _).symm
      _ = _ := by rw [hdiff, Matrix.mulVec_smul]

theorem lat_mod_fin (I : AutInst) (g : ℕ) (hgpos : 0 < g) : ∃ R : Finset (Fin I.n → I.E), (∀ r ∈ R, r ∈ I.L) ∧
    ∀ l ∈ I.L, ∃ r ∈ R, ∃ l' ∈ I.L, l = r + (g : ℤ) • l' := by
  classical
  have hZfg : (I.L.restrictScalars ℤ).FG := I.L_fg.restrictScalars
  obtain ⟨m, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hZfg
  have hmem : ∀ v, v ∈ I.L ↔ ∃ c : Fin m → ℤ, ∑ i, c i • s i = v := by
    intro v
    rw [← Submodule.restrictScalars_mem ℤ, ← hs, Submodule.mem_span_range_iff_exists_fun]
  have hsL : ∀ i, s i ∈ I.L := fun i => (hmem (s i)).mpr ⟨Pi.single i 1, by simp [Pi.single_apply]⟩
  have hcomb : ∀ c : Fin m → ℤ, ∑ i, c i • s i ∈ I.L := fun c => (hmem _).mpr ⟨c, rfl⟩
  refine ⟨(Fintype.piFinset fun _ : Fin m => Finset.range g).image
    (fun c : Fin m → ℕ => ∑ i, ((c i : ℕ) : ℤ) • s i), ?_, ?_⟩
  · intro r hr
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hr
    exact hcomb _
  · intro l hl
    obtain ⟨c, rfl⟩ := (hmem l).mp hl
    have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast hgpos.ne'
    refine ⟨∑ i, (((c i % g).toNat : ℕ) : ℤ) • s i, Finset.mem_image.mpr ⟨fun i => (c i % g).toNat, ?_, rfl⟩,
      ∑ i, (c i / g) • s i, hcomb _, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_range]
      have h1 := Int.emod_nonneg (c i) hg0
      have h2 := Int.emod_lt_of_pos (c i) (by exact_mod_cast hgpos : (0 : ℤ) < g)
      omega
    · rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← add_smul, Int.toNat_of_nonneg (Int.emod_nonneg (c i) hg0), add_comm, Int.mul_ediv_add_emod]

theorem iv_add_smul (I : AutInst) (r l : Fin I.n → I.E) (g : ℕ) :
    iv I (r + (g : ℤ) • l) = iv I r + (g : I.E ⊗[I.F] Af I.F) • iv I l := by
  funext i
  simp [iv, zsmul_eq_mul]

theorem iv_mem (I : AutInst) {l : Fin I.n → I.E} (hl : l ∈ I.L) : iv I l ∈ I.Lf := Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩

theorem stLatFin_of (h : LDense) : StLatFin := by
  intro I g hg
  obtain ⟨R, hRL, hR⟩ := lat_mod_fin I g (by omega)
  classical
  refine ⟨R.image (iv I), ?_, ?_⟩
  · intro r hr
    obtain ⟨r0, hr0, rfl⟩ := Finset.mem_image.mp hr
    exact iv_mem I (hRL r0 hr0)
  · intro y hy
    obtain ⟨l, hl, y', hy', hyeq⟩ := h I g (by omega) y hy
    obtain ⟨r, hr, l', hl', hleq⟩ := hR l hl
    refine ⟨iv I r, Finset.mem_image_of_mem _ hr, iv I l' + y', I.Lf.add_mem (iv_mem I hl') hy', ?_⟩
    rw [hyeq, hleq, iv_add_smul, smul_add]
    abel

end PIW.AdelClassFin
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.IsImgTrans
noncomputable section

namespace PIW.AdelClassFin

open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix

theorem stCong : StCong := by
  intro I U hU
  obtain ⟨g, hg, hsub⟩ := I.topf_basis U (hU.mem_nhds U.one_mem)
  exact ⟨g, hg, fun x hx => hsub hx⟩

theorem stTop : StTop := by
  intro hC hK hG I U hU
  classical
  obtain ⟨g, hg, hgU⟩ := hC I U hU
  obtain ⟨T, hT⟩ := hK I g hg
  obtain ⟨S, hS⟩ := hG I
  refine ⟨(S ×ˢ T).image (fun p => p.1 * p.2), fun x => ?_⟩
  obtain ⟨γ, hγ, s, hs, k, hk, rfl⟩ := hS x
  obtain ⟨t, ht, u, hu, rfl⟩ := hT k hk
  refine ⟨γ, hγ, s * t, Finset.mem_image.mpr ⟨(s, t), Finset.mem_product.mpr ⟨hs, ht⟩, rfl⟩, u, hgU hu, ?_⟩
  simp only [mul_assoc]

theorem stGenusOf : StGenusOf := by
  intro hD hH I
  classical
  obtain ⟨Λ, hΛ1, hΛ2, hΛ3⟩ := hD I
  obtain ⟨T, hT⟩ := hH I.F I.E I.cm I.n I.J I.J_herm I.J_det
  have huniq : ∀ {g : GL (Fin I.n) I.E} {A B B' : Submodule (𝓞 I.E) (Fin I.n → I.E)},
      IsImg g A B → IsImg g A B' → B = B' := by
    intro g A B B' h h'
    ext v
    exact (h v).trans (h' v).symm
  let rep : Submodule (𝓞 I.E) (Fin I.n → I.E) → I.Gf := fun M₀ =>
    if h : ∃ y, Λ y = M₀ then Classical.choose h else 1
  have hrep : ∀ M₀, (∃ y, Λ y = M₀) → Λ (rep M₀) = M₀ := by
    intro M₀ h
    show Λ (dite _ _ _) = M₀
    rw [dite_eq_left h]
    exact Classical.choose_spec h
  refine ⟨T.image rep, fun x => ?_⟩
  obtain ⟨hfg, hspan, hsd⟩ := hΛ1 x
  obtain ⟨γ, hγ, M₀, hM₀, himg⟩ := hT (Λ x) hfg hspan hsd
  obtain ⟨c', -, -, hc'⟩ := hΛ3 γ⁻¹ (Subgroup.inv_mem _ hγ)
  have hrange : ∃ y, Λ y = M₀ := by
    refine ⟨c' * x, ?_⟩
    ext v
    rw [hc' x v]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨w0, hw0, rfl⟩ := (himg w).1 hw
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      exact hw0
    · intro hv
      refine ⟨(γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ v, (himg _).2 ⟨v, hv, rfl⟩, ?_⟩
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  obtain ⟨c, hcG, -, hc⟩ := hΛ3 γ hγ
  have heq : Λ (c * rep M₀) = Λ x := huniq (hc (rep M₀)) (by rw [hrep M₀ hrange]; exact himg)
  obtain ⟨k, hk, hxk⟩ := hΛ2 _ _ heq
  exact ⟨c, hcG, rep M₀, Finset.mem_image_of_mem _ hM₀, k, hk, hxk⟩

end PIW.AdelClassFin
end
end

noncomputable section

namespace PIW.AdelClassFin

theorem stKFin : StKFin := stKFin_of (stLatFin_of lattice_dense)

theorem adelClassFin_of_H (h : StH) : PI.AdelClassFin.AdelClassFin :=
  stTop stCong stKFin (stGenusOf stDict h)

theorem adelClassFin_of_open (h1 : SpOne) (h2 : IdealBoundAll) (h3 : SvMajE) (h4 : SvCodiff) (h5 : SvBasis)
    (h6 : SvGramDet) (h7 : SvReal) : PI.AdelClassFin.AdelClassFin :=
  adelClassFin_of_H (stH_of_open h1 h2 h3 h4 h5 h6 h7)

end PIW.AdelClassFin
