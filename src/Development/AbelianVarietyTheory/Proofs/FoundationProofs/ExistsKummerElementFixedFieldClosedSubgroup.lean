module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HTLawAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueModPrimePowDiamondIndepende
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousMatQApply

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerElementFixedFieldClosedSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerElementFixedFieldClosedSubgroup
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.KumFix

theorem pow_val_add {Ω : Type} [Field Ω] {n : ℕ} [NeZero n] {ζ : Ω} (h : ζ ^ n = 1) (a b : ZMod n) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) n, pow_add, pow_mul, h, one_pow, mul_one]

theorem isClosed_of_le {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (H N U : Subgroup Γ)
    (hH : IsClosed (H : Set Γ)) (hU : IsOpen (U : Set Γ)) (hNH : N ≤ H) (hUN : ∀ s ∈ H, s ∈ U → s ∈ N) :
    IsClosed (N : Set Γ) := by
  have h1 : IsOpen ((U.subgroupOf H : Subgroup H) : Set H) := hU.preimage continuous_subtype_val
  have h2 : IsOpen ((N.subgroupOf H : Subgroup H) : Set H) :=
    Subgroup.isOpen_mono (H₁ := U.subgroupOf H) (fun s hs => hUN s s.2 hs) h1
  have h3 : IsClosed ((N.subgroupOf H : Subgroup H) : Set H) := Subgroup.isClosed_of_isOpen _ h2
  have h4 := hH.isClosedMap_subtype_val _ h3
  convert h4 using 1
  ext s
  constructor
  · intro hs
    exact ⟨⟨s, hNH hs⟩, hs, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ht

theorem exists_eigen {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {n : ℕ} [NeZero n] (H : Subgroup (G ℚ Ω))
    (hH : IsClosed (H : Set (G ℚ Ω))) (ζ : Ω) (hζ : ζ ^ n = 1) (hfix : ∀ s ∈ H, s ζ = ζ) (χ : G ℚ Ω → ZMod n)
    (hχ : ∀ s ∈ H, ∀ t ∈ H, χ (s * t) = χ s + χ t) (U : Subgroup (G ℚ Ω)) (hU : IsOpen (U : Set (G ℚ Ω)))
    (hUχ : ∀ s ∈ H, s ∈ U → χ s = 0) : ∃ w : Ω, w ≠ 0 ∧ ∀ s ∈ H, s w = ζ ^ (χ s).val * w := by
  classical
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne n)] at hζ
    exact zero_ne_one hζ
  have h1 : χ 1 = 0 := by
    have := hχ 1 H.one_mem 1 H.one_mem
    rw [mul_one] at this
    exact left_eq_add.mp this
  have hinv : ∀ s ∈ H, χ s⁻¹ = -χ s := by
    intro s hs
    have := hχ s⁻¹ (H.inv_mem hs) s hs
    rw [inv_mul_cancel, h1] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  let N : Subgroup (G ℚ Ω) :=
    { carrier := {s | s ∈ H ∧ χ s = 0}
      mul_mem' := fun {a b} ha hb => ⟨H.mul_mem ha.1 hb.1, by rw [hχ a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩
      one_mem' := ⟨H.one_mem, h1⟩
      inv_mem' := fun {a} ha => ⟨H.inv_mem ha.1, by rw [hinv a ha.1, ha.2, neg_zero]⟩ }
  have hNc : IsClosed (N : Set (G ℚ Ω)) :=
    isClosed_of_le H N U hH hU (fun s hs => hs.1) (fun s hs hsU => ⟨hs, hUχ s hs hsU⟩)
  have hNfix : (IntermediateField.fixedField N).fixingSubgroup = N :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨N, hNc⟩
  let E := IntermediateField.fixedField N
  let ι := {k : ZMod n // ∃ g ∈ H, χ g = k}
  choose r hrH hrχ using fun k : ι => k.2
  let f : ι → (E →* Ω) := fun k =>
    { toFun := fun x => r k (x : Ω)
      map_one' := by simp
      map_mul' := fun x y => by simp }
  have hf : Function.Injective f := by
    intro j k hjk
    have hm : (r j)⁻¹ * r k ∈ N := by
      rw [← hNfix, IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have e : r j x = r k x := DFunLike.congr_fun hjk ⟨x, hx⟩
      rw [AlgEquiv.mul_apply, ← e]
      exact (r j).symm_apply_apply x
    have h2 := hm.2
    rw [hχ _ (H.inv_mem (hrH j)) _ (hrH k), hinv _ (hrH j), hrχ, hrχ] at h2
    exact Subtype.ext (neg_add_eq_zero.mp h2)
  have hli := (linearIndependent_monoidHom E Ω).comp f hf
  have hex : ∃ x : E, ∑ k : ι, ζ ^ (-(k : ZMod n)).val * r k (x : Ω) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := Fintype.linearIndependent_iff.mp hli (fun k => ζ ^ (-(k : ZMod n)).val) (by
      funext x
      rw [Finset.sum_apply]
      exact hcon x) ⟨0, 1, H.one_mem, h1⟩
    exact pow_ne_zero _ hζ0 this
  obtain ⟨x, hx⟩ := hex
  refine ⟨_, hx, fun s hs => ?_⟩
  let e : ι ≃ ι :=
    { toFun := fun k => ⟨χ s + k, s * r k, H.mul_mem hs (hrH k), by rw [hχ _ hs _ (hrH k), hrχ]⟩
      invFun := fun k => ⟨-χ s + k, s⁻¹ * r k, H.mul_mem (H.inv_mem hs) (hrH k), by
        rw [hχ _ (H.inv_mem hs) _ (hrH k), hrχ, hinv s hs]⟩
      left_inv := fun k => Subtype.ext (by simp)
      right_inv := fun k => Subtype.ext (by simp) }
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.mul_sum, ← Equiv.sum_comp e (fun k : ι => ζ ^ (χ s).val * (ζ ^ (-(k : ZMod n)).val * r k (x : Ω)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hm : (r (e k))⁻¹ * (s * r k) ∈ N := by
    refine ⟨H.mul_mem (H.inv_mem (hrH _)) (H.mul_mem hs (hrH k)), ?_⟩
    rw [hχ _ (H.inv_mem (hrH _)) _ (H.mul_mem hs (hrH k)), hinv _ (hrH _), hχ _ hs _ (hrH k), hrχ, hrχ]
    exact neg_add_cancel _
  have hx1 : ((r (e k))⁻¹ * (s * r k)) (x : Ω) = x := (IntermediateField.mem_fixedField_iff N x).mp x.2 _ hm
  have hx2 : s (r k (x : Ω)) = r (e k) (x : Ω) := by
    have := congrArg (r (e k)) hx1
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply] at this
    rw [← this]
    exact ((r (e k)).apply_symm_apply _).symm
  rw [map_mul, map_pow, hfix s hs, hx2, ← mul_assoc, ← pow_val_add hζ]
  congr 3
  change -(k : ZMod n) = χ s + -(χ s + k)
  ring

theorem exists_kumVal : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) (H : Subgroup (G ℚ Ω)), IsClosed (H : Set (G ℚ Ω)) → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ m) → (∀ s ∈ H, s ζ = ζ) → ∀ χ : G ℚ Ω → ZMod (l ^ m), (∀ s ∈ H, ∀ t ∈ H, χ (s * t) = χ s + χ t) → ∀ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) → (∀ s ∈ H, s ∈ U → χ s = 0) → ∃ u : Ω, u ≠ 0 ∧ (∀ s ∈ H, s u = u) ∧ ∀ s ∈ H, GlobalTheory.Col.KumVal (l := l) m ζ u s (χ s) := by
  intro l _ Ω _ _ _ m H hH ζ hζ hfix χ hχ U hU hUχ
  haveI : NeZero (l ^ m) := ⟨(pow_pos (Fact.out : l.Prime).pos m).ne'⟩
  obtain ⟨w, hw0, hw⟩ := exists_eigen H hH ζ hζ.pow_eq_one hfix χ hχ U hU hUχ
  refine ⟨w ^ (l ^ m), pow_ne_zero _ hw0, fun s hs => ?_, fun s hs => ⟨w, rfl, hw s hs⟩⟩
  rw [map_pow, hw s hs, mul_pow, ← pow_mul, mul_comm (χ s).val, pow_mul, hζ.pow_eq_one, one_pow, one_mul]

end GlobalTheory.KumFix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerElementFixedFieldClosedSubgroupStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kummer_element_fixed_field_closed_subgroup : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) (H : Subgroup (G ℚ Ω)), IsClosed (H : Set (G ℚ Ω)) → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ m) → (∀ s ∈ H, s ζ = ζ) → ∀ χ : G ℚ Ω → ZMod (l ^ m), (∀ s ∈ H, ∀ t ∈ H, χ (s * t) = χ s + χ t) → ∀ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) → (∀ s ∈ H, s ∈ U → χ s = 0) → ∃ u : Ω, u ≠ 0 ∧ (∀ s ∈ H, s u = u) ∧ ∀ s ∈ H, GlobalTheory.Col.KumVal (l := l) m ζ u s (χ s) := by
  first | exact @GlobalTheory.KumFix.exists_kumVal | exact GlobalTheory.KumFix.exists_kumVal | (intros; apply GlobalTheory.KumFix.exists_kumVal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondCommutesHeckeU
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondCommutesHeckeU
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

noncomputable section

namespace GlobalTheory.KZ.DiamU

theorem isDiam_sgD_of_coprime' {N l d : ℕ} (hl : l ≠ 0) (hd : Nat.Coprime d N) : IsDiam N l d (sgD N l d) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h1 : d = 1 := (Nat.coprime_zero_right d).1 hd
    subst h1
    exact Classical.epsilon_spec (p := IsDiam 0 l 1) ⟨1, Subgroup.one_mem _, by simp [en]⟩
  · exact Betti.isDiam_sgD hN.ne' hl hd

theorem upper_mul_eq {N l d : ℕ} {σ : SL(2, ℤ)} (hσ : IsDiam N l d σ) (hl : 0 < l) (j k : ℕ)
    (hk : (k : ZMod l) * ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod l) =
      (((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + j * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod l)) :
    ∃ s : SL(2, ℤ), IsDiam N l d s ∧
      !![1, (j : ℤ); 0, (l : ℤ)] * (σ : Matrix (Fin 2) (Fin 2) ℤ) =
        (s : Matrix (Fin 2) (Fin 2) ℤ) * !![1, (k : ℤ); 0, (l : ℤ)] := by
  obtain ⟨h0, hd⟩ := hσ
  rw [Subgroup.mem_inf] at h0
  have hcN := CongruenceSubgroup.Gamma0_mem.1 h0.1
  have hcl := CongruenceSubgroup.Gamma0_mem.1 h0.2
  have hdet := σ.det_coe
  rw [Matrix.det_fin_two] at hdet
  simp only [en] at hd
  have hdiv : (l : ℤ) ∣ (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + j * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      k * ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + j * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hk hcl ⊢
    rw [hcl]
    linear_combination -hk
  obtain ⟨q, hq⟩ := hdiv
  set a := (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  set b := (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  set c := (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  set e := (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  set S : Matrix (Fin 2) (Fin 2) ℤ := !![a + j * c, q; l * c, e - c * k] with hSdef
  have hM : !![1, (j : ℤ); 0, (l : ℤ)] * (σ : Matrix (Fin 2) (Fin 2) ℤ) = S * !![1, (k : ℤ); 0, (l : ℤ)] := by
    ext i i'
    fin_cases i <;> fin_cases i' <;>
      simp [hSdef, Matrix.mul_apply, Fin.sum_univ_two, a, b, c, e] <;> first | ring1 | linear_combination hq
  have hS : S.det = 1 := by
    have h := congrArg Matrix.det hM
    rw [Matrix.det_mul, Matrix.det_mul, σ.det_coe] at h
    simp only [Matrix.det_fin_two_of] at h
    have hl' : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne'
    have : ((l : ℤ)) * 1 = S.det * (l : ℤ) := by linarith
    exact (mul_right_cancel₀ hl' (by linarith : S.det * (l : ℤ) = 1 * (l : ℤ)))
  refine ⟨⟨S, hS⟩, ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩, hM⟩
  · refine CongruenceSubgroup.Gamma0_mem.2 ?_
    show ((l * c : ℤ) : ZMod N) = 0
    rw [Int.cast_mul, hcN, mul_zero]
  · refine CongruenceSubgroup.Gamma0_mem.2 ?_
    show ((l * c : ℤ) : ZMod l) = 0
    rw [Int.cast_mul, hcl, mul_zero]
  · simp only [en]
    simp [hSdef]
    rw [hcN]; simpa using hd

private def res (l : ℕ) (x : ℤ) : ℕ := (x % (l : ℤ)).toNat

private theorem res_lt {l : ℕ} (hl : 0 < l) (x : ℤ) : res l x < l := by
  have h1 := Int.emod_lt_of_pos x (show (0 : ℤ) < l by exact_mod_cast hl)
  have h2 := Int.emod_nonneg x (show (l : ℤ) ≠ 0 by exact_mod_cast hl.ne')
  unfold res; omega

private theorem res_cast {l : ℕ} (hl : 0 < l) (x : ℤ) : ((res l x : ℕ) : ZMod l) = (x : ZMod l) := by
  have h2 := Int.emod_nonneg x (show (l : ℤ) ≠ 0 by exact_mod_cast hl.ne')
  rw [← Int.cast_natCast, res, Int.toNat_of_nonneg h2, ZMod.intCast_mod]

private theorem res_eq {l : ℕ} (hl : 0 < l) {x : ℤ} {j : ℕ} (hj : j < l) (h : (x : ZMod l) = j) : res l x = j := by
  rw [← res_cast hl, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt (res_lt hl x)] at h
  exact h

theorem act_sgD_heckeU : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime]
    (w d : ℕ), d.Coprime N → ¬ l ∣ N → ∀ b : X.Fn l, b ∈ X.B N l w →
    X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeU l b) =
      X.heckeU l (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) := by
  intro Ω _ _ ε X N l _ w d hd _ b hb
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hσ := isDiam_sgD_of_coprime' hl.ne' hd
  have hcl := CongruenceSubgroup.Gamma0_mem.1 (Subgroup.mem_inf.1 hσ.1).2
  have hdet := (sgD N l d).det_coe
  rw [Matrix.det_fin_two] at hdet
  have hpos : ∀ g : SL(2, ℤ), 0 < (g : Matrix (Fin 2) (Fin 2) ℤ).det := fun g => by rw [g.det_coe]; exact one_pos
  have hm : ∀ j : ℕ, 0 < (!![1, (j : ℤ); 0, (l : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det := fun j => by
    rw [Matrix.det_fin_two_of]; simpa using hl
  have key := fun j k => upper_mul_eq hσ hl j k
  generalize hA : (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = A at hdet key
  generalize hB : (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = B at hdet key
  generalize hE : (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = E at hdet key
  have hae : (A : ZMod l) * E = 1 := by
    have h := congrArg (Int.cast : ℤ → ZMod l) hdet
    push_cast at h
    rw [hcl] at h
    linear_combination h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Tower.heckeU, LinearMap.coe_sum, Finset.sum_apply, map_sum]
  refine Finset.sum_nbij' (fun j : ℕ => res l ((B + j * E) * E)) (fun k : ℕ => res l ((k * A - B) * A))
    (fun j _ => Finset.mem_range.2 (res_lt hl _)) (fun k _ => Finset.mem_range.2 (res_lt hl _)) ?_ ?_ ?_
  · intro j hj
    refine res_eq hl (Finset.mem_range.1 hj) ?_
    push_cast
    rw [res_cast hl]
    push_cast
    linear_combination ((j : ZMod l) + (B + j * E) * A) * hae
  · intro k hk
    refine res_eq hl (Finset.mem_range.1 hk) ?_
    push_cast
    rw [res_cast hl]
    push_cast
    linear_combination ((k : ZMod l) + (k * A - B) * E) * hae
  · intro j _
    obtain ⟨s, hs, hM⟩ := key j (res l ((B + j * E) * E)) (by
      rw [res_cast hl]
      push_cast
      linear_combination ((B : ZMod l) + j * E) * hae)
    rw [Tower.act_act Ω ε X l _ _ (hm j) (hpos _), hM, ← Tower.act_act Ω ε X l _ _ (hpos _) (hm _),
      X.act_isDiam_eq hb hs]

end GlobalTheory.KZ.DiamU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondCommutesHeckeUStatement
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diamond_commutes_hecke_U : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (w d : ℕ), d.Coprime N → ¬ l ∣ N → ∀ b : X.Fn l, b ∈ X.B N l w →
  X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeU l b) = X.heckeU l (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) := by
  first | exact @GlobalTheory.KZ.DiamU.act_sgD_heckeU | exact GlobalTheory.KZ.DiamU.act_sgD_heckeU | (intros; apply GlobalTheory.KZ.DiamU.act_sgD_heckeU <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DvdOfMemIk
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefDualFreeRankOne
noncomputable section

open UpperTheory.V.HV

namespace GlobalTheory.Ord2.CoefDual

variable (l : ℕ) [Fact l.Prime] (c : Coef l)

def dualModule : Module c.O (c.O →ₗ[ℤ_[l]] ℤ_[l]) where
  smul a f := f ∘ₗ LinearMap.mulLeft ℤ_[l] a
  one_smul f := by apply LinearMap.ext; intro x; show f (1 * x) = f x; rw [one_mul]
  mul_smul a b f := by apply LinearMap.ext; intro x; show f (a * b * x) = f (b * (a * x)); rw [mul_comm a b, mul_assoc]
  smul_zero a := by apply LinearMap.ext; intro x; show (0 : c.O →ₗ[ℤ_[l]] ℤ_[l]) (a * x) = 0; rfl
  smul_add a f g := by apply LinearMap.ext; intro x; show (f + g) (a * x) = f (a * x) + g (a * x); rfl
  add_smul a b f := by apply LinearMap.ext; intro x; show f ((a + b) * x) = f (a * x) + f (b * x); rw [add_mul, map_add (f := _)]
  zero_smul f := by apply LinearMap.ext; intro x; show f (0 * x) = 0; rw [zero_mul, map_zero]

theorem dualModule_apply (a : c.O) (f : c.O →ₗ[ℤ_[l]] ℤ_[l]) (x : c.O) :
    (letI := dualModule l c; a • f) x = f (a * x) := rfl

theorem dual_tower :
    letI := dualModule l c; IsScalarTower ℤ_[l] c.O (c.O →ₗ[ℤ_[l]] ℤ_[l]) := by
  letI := dualModule l c
  refine ⟨fun r a f => ?_⟩
  ext x
  rw [dualModule_apply, LinearMap.smul_apply, dualModule_apply, smul_mul_assoc, map_smul]

theorem dual_torsionFree :
    letI := dualModule l c; Module.IsTorsionFree c.O (c.O →ₗ[ℤ_[l]] ℤ_[l]) := by
  letI := dualModule l c
  refine Module.IsTorsionFree.of_smul_eq_zero fun a f h => ?_
  by_cases ha : a = 0
  · exact Or.inl ha
  right
  have hne := Ideal.comap_ne_bot_of_integral_mem (R := ℤ_[l]) (I := Ideal.span {a}) ha
    (Ideal.mem_span_singleton_self a) (Algebra.IsIntegral.isIntegral a)
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hr
  obtain ⟨b, hb⟩ := hr
  ext x
  have h1 : r • f x = 0 := by
    rw [← map_smul, Algebra.smul_def, hb, mul_assoc, ← dualModule_apply, h]
    rfl
  simpa [hr0] using h1

end GlobalTheory.Ord2.CoefDual


open GlobalTheory.Ord2.CoefDual in
theorem GlobalTheory.Ord2.coef_dual_free_rank_one :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l), ∃ τ : c.O →ₗ[ℤ_[l]] ℤ_[l],
      ∀ f : c.O →ₗ[ℤ_[l]] ℤ_[l], ∃! a : c.O, ∀ x, f x = τ (a * x) := by
  intro l _ c
  letI := dualModule l c
  haveI := dual_tower l c
  haveI : Module.IsTorsionFree ℤ_[l] c.O := FaithfulSMul.to_isTorsionFree ℤ_[l] c.O
  haveI : Module.Free ℤ_[l] c.O := Module.free_of_finite_type_torsion_free'
  haveI : Module.Finite c.O (c.O →ₗ[ℤ_[l]] ℤ_[l]) := Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  haveI := dual_torsionFree l c
  haveI : Module.Free c.O (c.O →ₗ[ℤ_[l]] ℤ_[l]) := Module.free_of_finite_type_torsion_free'
  have h1 := Module.finrank_linearMap ℤ_[l] ℤ_[l] c.O ℤ_[l]
  have h2 := Module.finrank_mul_finrank ℤ_[l] c.O (c.O →ₗ[ℤ_[l]] ℤ_[l])
  have hpos : 0 < Module.finrank ℤ_[l] c.O := Module.finrank_pos
  have hr : Module.finrank c.O (c.O →ₗ[ℤ_[l]] ℤ_[l]) = 1 := by
    rw [h1, Module.finrank_self, mul_one] at h2
    exact Nat.eq_of_mul_eq_mul_left hpos (h2.trans (mul_one _).symm)
  let b := Module.finBasisOfFinrankEq c.O (c.O →ₗ[ℤ_[l]] ℤ_[l]) hr
  refine ⟨b 0, fun f => ⟨b.repr f 0, fun x => ?_, fun a ha => ?_⟩⟩
  · have hs := b.sum_repr f
    rw [Fin.sum_univ_one] at hs
    rw [← dualModule_apply, hs]
  · have hf : f = a • b 0 := LinearMap.ext fun x => (ha x).trans (dualModule_apply l c a (b 0) x).symm
    rw [hf, map_smul, b.repr_self]
    simp

end
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.SelPerp

variable {l : ℕ} [Fact l.Prime]

def tau (c : Coef l) : c.O →ₗ[ℤ_[l]] ℤ_[l] := Classical.choose (coef_dual_free_rank_one l c)

theorem tau_spec (c : Coef l) : ∀ f : c.O →ₗ[ℤ_[l]] ℤ_[l], ∃! a : c.O, ∀ x, f x = tau c (a * x) :=
  Classical.choose_spec (coef_dual_free_rank_one l c)

theorem norm_unit (c : Coef l) (u : c.Oˣ) : ‖((u : c.O) : Qbar l)‖ = 1 := by
  have h1 := CupCob.norm_le_one_of_mem c (u : c.O).2
  have h2 := CupCob.norm_le_one_of_mem c ((u⁻¹ : c.Oˣ) : c.O).2
  have h3 : ((u : c.O) : Qbar l) * (((u⁻¹ : c.Oˣ) : c.O) : Qbar l) = 1 := by
    rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
  have h4 := congrArg norm h3
  rw [norm_mul, norm_one] at h4
  nlinarith [norm_nonneg ((u : c.O) : Qbar l), norm_nonneg (((u⁻¹ : c.Oˣ) : c.O) : Qbar l)]

theorem norm_l_lt_one : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have e : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((l : ℕ) : ℚ_[l]) := by simp
  rw [e, norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem dvd_of_mem_Ik (c : Coef l) (n : ℕ) {x : c.O} (hx : x ∈ Ik c n) : ∃ y : c.O, x = (l : c.O) ^ n * y := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, by simp⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  have hl0 : (l : c.O) ≠ 0 := by
    intro h
    have : ((l : c.O) : Qbar l) = 0 := by rw [h]; rfl
    rw [SubringClass.coe_natCast] at this
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  obtain ⟨e, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have nl : ‖((l : c.O) : Qbar l)‖ = ‖((ϖ : c.O) : Qbar l)‖ ^ e := by
    rw [hw, Subalgebra.coe_mul, Subalgebra.coe_pow, norm_mul, norm_pow, norm_unit, one_mul]
  have nx : ‖((x : c.O) : Qbar l)‖ = ‖((ϖ : c.O) : Qbar l)‖ ^ k := by
    rw [hu, Subalgebra.coe_mul, Subalgebra.coe_pow, norm_mul, norm_pow, norm_unit, one_mul]
  have hlt : ‖((l : c.O) : Qbar l)‖ < 1 := by rw [SubringClass.coe_natCast]; exact norm_l_lt_one
  have hϖ1 : ‖((ϖ : c.O) : Qbar l)‖ ≤ 1 := CupCob.norm_le_one_of_mem c ϖ.2
  have he : e ≠ 0 := by
    rintro rfl
    rw [nl, pow_zero] at hlt
    exact lt_irrefl _ hlt
  have hϖlt : ‖((ϖ : c.O) : Qbar l)‖ < 1 := by
    rcases hϖ1.lt_or_eq with h | h
    · exact h
    · rw [nl, h, one_pow] at hlt; exact absurd hlt (lt_irrefl _)
  have hϖ0 : 0 < ‖((ϖ : c.O) : Qbar l)‖ := by
    rw [norm_pos_iff]
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  have hle : e * n ≤ k := by
    have h := (mem_Ik.1 hx)
    have e2 : ‖((l : ℕ) : Qbar l) ^ n‖ = ‖((ϖ : c.O) : Qbar l)‖ ^ (e * n) := by
      rw [norm_pow, ← SubringClass.coe_natCast c.O, nl, pow_mul]
    rw [nx, e2] at h
    exact (pow_le_pow_iff_right_of_lt_one₀ hϖ0 hϖlt).1 h
  refine ⟨(u : c.O) * ϖ ^ (k - e * n) * ((w⁻¹ : c.Oˣ) : c.O) ^ n, ?_⟩
  rw [hu, hw]
  have hk : k = e * n + (k - e * n) := by omega
  conv_lhs => rw [hk]
  calc (u : c.O) * ϖ ^ (e * n + (k - e * n))
      = (u : c.O) * ϖ ^ (k - e * n) * (((w : c.O) * ((w⁻¹ : c.Oˣ) : c.O)) ^ n * ϖ ^ (e * n)) := by
        rw [Units.mul_inv, one_pow, one_mul, pow_add]; ring
    _ = _ := by ring

theorem tau_red_zero (c : Coef l) (n : ℕ) {x : c.O} (hx : x ∈ Ik c n) :
    PadicInt.toZModPow n (tau c x) = 0 := by
  obtain ⟨y, rfl⟩ := dvd_of_mem_Ik c n hx
  have e : (l : c.O) ^ n * y = ((l : ℤ_[l]) ^ n) • y := by
    rw [Algebra.smul_def, map_pow, map_natCast]
  rw [e, map_smul, smul_eq_mul, map_mul, map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]

def lft (c : Coef l) (n : ℕ) : Qn c n → c.O := Function.surjInv (red_surjective c n)

theorem red_lft (c : Coef l) (n : ℕ) (b : Qn c n) : red c n (lft c n b) = b :=
  Function.surjInv_eq (red_surjective c n) b

theorem tau_congr (c : Coef l) (n : ℕ) {x y : c.O} (h : red c n x = red c n y) :
    PadicInt.toZModPow n (tau c x) = PadicInt.toZModPow n (tau c y) := by
  rw [← sub_eq_zero, ← map_sub, ← map_sub]
  refine tau_red_zero c n ?_
  rw [← red_eq_zero_iff_mem, map_sub, h, sub_self]

def tbA (c : Coef l) (n : ℕ) : Qn c n →+ ZMod (l ^ n) where
  toFun b := PadicInt.toZModPow n (tau c (lft c n b))
  map_zero' := by
    rw [← map_zero (red c n), tau_congr c n (red_lft c n _), map_zero, map_zero]
  map_add' a b := by
    obtain ⟨x, rfl⟩ := red_surjective c n a
    obtain ⟨y, rfl⟩ := red_surjective c n b
    rw [← map_add (f := _), tau_congr c n (red_lft c n _), tau_congr c n (red_lft c n _),
      tau_congr c n (red_lft c n _), map_add, map_add]

theorem tbA_red (c : Coef l) (n : ℕ) (x : c.O) : tbA c n (red c n x) = PadicInt.toZModPow n (tau c x) :=
  tau_congr c n (red_lft c n _)

def pairA (c : Coef l) (n : ℕ) (y : Mn c n) : Mn c n →+ ZMod (l ^ n) where
  toFun x := tbA c n (x 0 * y 1 - x 1 * y 0)
  map_zero' := by simp
  map_add' a b := by
    rw [← map_add (f := _)]; congr 1; simp only [Pi.add_apply]; ring

def Phi (c : Coef l) (n : ℕ) : Mn c n →ₗ[ZMod (l ^ n)] TDual (ZMod (l ^ n)) (Mn c n) :=
  (AddMonoidHom.mk' (fun y => TDual.mk ((pairA c n y).toZModLinearMap (l ^ n))) (fun a b => by
    refine DFunLike.ext _ _ fun x => ?_
    show tbA c n _ = tbA c n _ + tbA c n _
    rw [← map_add (f := _)]; congr 1; simp only [Pi.add_apply]; ring)).toZModLinearMap (l ^ n)

theorem Phi_apply (c : Coef l) (n : ℕ) (y x : Mn c n) : Phi c n y x = tbA c n (x 0 * y 1 - x 1 * y 0) := rfl

theorem red_mulVec (c : Coef l) (n : ℕ) (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (hM : ∀ i j, M i j ∈ c.O)
    (v : Fin 2 → Qbar l) (hv : ∀ i, v i ∈ c.O) (i : Fin 2) :
    red c n ⟨(M *ᵥ v) i, CupCob.mulVec_mem c M v hM hv i⟩ =
      ((Matrix.of fun i j => red c n ⟨M i j, hM i j⟩) *ᵥ fun j => red c n ⟨v j, hv j⟩) i := by
  have e : (⟨(M *ᵥ v) i, CupCob.mulVec_mem c M v hM hv i⟩ : c.O) =
      (⟨M i 0, hM i 0⟩ : c.O) * ⟨v 0, hv 0⟩ + (⟨M i 1, hM i 1⟩ : c.O) * ⟨v 1, hv 1⟩ := by
    apply Subtype.ext
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Subalgebra.coe_add, Subalgebra.coe_mul]
  rw [e, map_add (f := _), map_mul, map_mul]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply]

def lftV (c : Coef l) (n : ℕ) (y : Mn c n) : Fin 2 → Qbar l := fun i => (lft c n (y i) : Qbar l)

theorem lftV_mem (c : Coef l) (n : ℕ) (y : Mn c n) (i : Fin 2) : lftV c n y i ∈ c.O := (lft c n (y i)).2

theorem red_lftV (c : Coef l) (n : ℕ) (y : Mn c n) (i : Fin 2) : red c n ⟨lftV c n y i, lftV_mem c n y i⟩ = y i :=
  red_lft c n (y i)

theorem cg_of_red {c : Coef l} {n : ℕ} {a b : Qbar l} (ha : a ∈ c.O) (hb : b ∈ c.O)
    (h : red c n ⟨a, ha⟩ = red c n ⟨b, hb⟩) : Cg n a b := (red_eq_iff ⟨a, ha⟩ ⟨b, hb⟩).1 h

theorem red_of_cg {c : Coef l} {n : ℕ} {a b : Qbar l} (ha : a ∈ c.O) (hb : b ∈ c.O)
    (h : Cg n a b) : red c n ⟨a, ha⟩ = red c n ⟨b, hb⟩ := (red_eq_iff ⟨a, ha⟩ ⟨b, hb⟩).2 h

end GlobalTheory.Ord2.SelPerp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardOrdinaryLocalConditionModPrimePowLeConstMul
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardOrdinaryLocalConditionModPrimePowLeConstMul
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.GwIneq.CardOrd

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem span_eq_Ik (c : Coef l) (n : ℕ) : Ideal.span {((l : ℕ) : c.O) ^ n} = Ik c n := by
  ext x
  rw [Ideal.mem_span_singleton, mem_Ik]
  exact (GlobalTheory.Coef.norm_le_norm_pow_iff_dvd l c n x).symm

def levEquiv (c : Coef l) (n : ℕ) : UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n) ≃+ Qn c n :=
  (Ideal.quotEquivOfEq (span_eq_Ik c n)).toAddEquiv

theorem levEquiv_mk (c : Coef l) (n : ℕ) (x : c.O) :
    levEquiv c n (UpperTheory.V.X.Lev.mk (((l : ℕ) : c.O) ^ n) x) = red c n x := rfl

theorem card_lev (c : Coef l) (n : ℕ) :
    Nat.card (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) = Nat.card (Qn c n) :=
  Nat.card_congr (levEquiv c n).toEquiv

theorem levEquiv_smul (c : Coef l) (n : ℕ) (a : c.O) (x : UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) :
    levEquiv c n (a • x) = red c n a * levEquiv c n x := by
  obtain ⟨y, rfl⟩ := UpperTheory.V.X.Lev.mk_surjective _ x
  rw [← map_smul, smul_eq_mul, levEquiv_mk, levEquiv_mk, map_mul]

def lineInc (c : Coef l) (n : ℕ) : UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n) →+ Mn c n :=
  (AddMonoidHom.single (fun _ : Fin 2 => Qn c n) 0).comp (levEquiv c n).toAddMonoidHom

theorem lineInc_apply (c : Coef l) (n : ℕ) (x : UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) :
    lineInc c n x = Pi.single 0 (levEquiv c n x) := rfl

theorem lineInc_injective (c : Coef l) (n : ℕ) : Function.Injective (lineInc c n) :=
  fun x y h => (levEquiv c n).injective (by
    have h0 := congrFun h 0
    simpa [lineInc_apply] using h0)

variable [IsAlgClosure ℚ Ω]

theorem lineInc_equiv (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (S : Finset Pl)
    (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (B : ValuationSubring Ω)
    (hup : ∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) (θ : Dec (F := ℚ) B →* c.Oˣ)
    (hθ : ∀ g, (((θ g : c.Oˣ) : c.O) : Qbar l) = mat W g 0 0) (g : Dec (F := ℚ) B)
    (x : UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) :
    lineInc c n (Formalism.GaloisCohomology.scalRep (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) θ g x) =
      ((rhoS c n W hint S hN).comp (locHom (S : Set Pl) B)) g (lineInc c n x) := by
  have h1 : (θ g : c.O) = ⟨mat W g 0 0, hint g 0 0⟩ := Subtype.ext (hθ g)
  have h2 : matQ c n W hint g 1 0 = 0 := by
    rw [matQ_apply]
    have : (⟨mat W g 1 0, hint g 1 0⟩ : c.O) = 0 := Subtype.ext (hup g g.2)
    rw [this, map_zero]
  show lineInc c n (((θ g : c.Oˣ) : c.O) • x) = matQ c n W hint g *ᵥ lineInc c n x
  rw [lineInc_apply, lineInc_apply, levEquiv_smul, h1]
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, matQ_apply]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h2]

theorem card_ordCond_le (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (S : Finset Pl)
    (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (hcont : Continuous W) (B : ValuationSubring Ω)
    (hup : ∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) (θ : Dec (F := ℚ) B →* c.Oˣ)
    (hθ : ∀ g, (((θ g : c.Oˣ) : c.O) : Qbar l) = mat W g 0 0)
    [Finite (H1 (Formalism.GaloisCohomology.scalRep (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) θ))] :
    Nat.card (ordCond c n W hint S hN B) ≤
      Nat.card (H1 (Formalism.GaloisCohomology.scalRep (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) θ)) := by
  set τ := Formalism.GaloisCohomology.scalRep (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) θ with hτ
  set σ := (rhoS c n W hint S hN).comp (locHom (S : Set Pl) B) with hσ
  have hσa : ∀ (g : Dec (F := ℚ) B) (y : Mn c n), σ g y = matQ c n W hint g *ᵥ y := fun _ _ => rfl
  have heq := lineInc_equiv c n W hint S hN B hup θ hθ
  set Φ := UpperTheory.V.X.h1MapOfAdditive τ σ (lineInc c n) heq with hΦ
  have hsub : (ordCond c n W hint S hN B : Set (H1 σ)) ⊆ Set.range Φ := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
    obtain ⟨x, hx⟩ := (mem_ordZ _).1 (Submodule.mem_comap.1 hz)

    set m : Mn c n := Pi.single 1 x with hm
    have hbc : Continuous fun g : Dec (F := ℚ) B => σ g m - m := by
      have hc : ∀ i j, Continuous fun g : Dec (F := ℚ) B => matQ c n W hint g i j := fun i j =>
        (continuous_matQ_apply c n W hint hcont i j).comp continuous_subtype_val
      refine continuous_pi fun i => ?_
      simp only [hσa, Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      exact (((hc i 0).mul continuous_const).add ((hc i 1).mul continuous_const)).sub continuous_const
    let bZ : Z1 σ := ⟨fun g => σ g m - m, hbc, fun g h => by
      simp only [map_mul, Module.End.mul_apply, map_sub]
      abel⟩
    have hbB : bZ ∈ (B1 σ).comap (Z1 σ).subtype := (mem_coboundaries1 σ _).2 ⟨m, fun g => rfl⟩
    set zb : Z1 σ := z - bZ with hzb
    have hzb1 : ∀ g, zb.1 g 1 = 0 := by
      intro g
      show z.1 g 1 - (σ g m - m) 1 = 0
      have hx' : z.1 g 1 = matQ c n W hint g 1 1 * x - x := hx g
      rw [hσa, hx']
      have hm0 : m 0 = 0 := rfl
      have hm1 : m 1 = x := rfl
      simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hm0, hm1]
      ring
    have hzbι : ∀ g, zb.1 g = lineInc c n ((levEquiv c n).symm (zb.1 g 0)) := by
      intro g
      rw [lineInc_apply, AddEquiv.apply_symm_apply]
      ext i
      fin_cases i
      · simp
      · simp [hzb1 g]
    let w : Dec (F := ℚ) B → UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n) := fun g => (levEquiv c n).symm (zb.1 g 0)
    have hw : w ∈ Z1 τ := by
      refine ⟨(continuous_of_discreteTopology (f := fun y : Mn c n => (levEquiv c n).symm (y 0))).comp zb.2.1,
        fun g h => lineInc_injective c n ?_⟩
      rw [map_add (f := _), heq, ← hzbι, ← hzbι, ← hzbι]
      exact zb.2.2 g h
    refine ⟨Submodule.Quotient.mk ⟨w, hw⟩, ?_⟩
    rw [hΦ, UpperTheory.V.X.h1MapOfAdditive_mk]
    have e1 : UpperTheory.V.X.cocycleMapOfEquivariant τ σ (lineInc c n) heq ⟨w, hw⟩ = zb :=
      Subtype.ext (funext fun g => (hzbι g).symm)
    rw [e1, hzb, Submodule.Quotient.mk_sub, (Submodule.Quotient.mk_eq_zero _).2 hbB, sub_zero]
    rfl
  calc Nat.card (ordCond c n W hint S hN B) = Nat.card (ordCond c n W hint S hN B : Set (H1 σ)) := rfl
    _ ≤ Nat.card (Set.range Φ) := Nat.card_mono (Set.finite_range Φ) hsub
    _ ≤ Nat.card (H1 τ) := Finite.card_range_le Φ

end GlobalTheory.Ord2.GwIneq.CardOrd

namespace GlobalTheory.Ord2.GwIneq.CardOrd

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem exists_theta (c : Coef l) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hcont : Continuous W)
    (hdet : dt W ^ 2 = 1) (B : ValuationSubring Ω) (hup : ∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) :
    ∃ θ : Dec (F := ℚ) B →* c.Oˣ, Continuous (fun g => ((θ g : c.Oˣ) : c.O)) ∧
      ∀ g, (((θ g : c.Oˣ) : c.O) : Qbar l) = mat W g 0 0 := by
  have hm : Continuous fun s => mat W s := Units.continuous_val.comp hcont
  refine GlobalTheory.LocChar.unit_of_integral l Ω c B (fun s => mat W s 0 0)
    (fun s => eps l s * (mat W s 1 1 * (mat W s).det)) ((hm.matrix_elem 0 0).continuousOn) ?_ ?_
  · intro s hs
    have hdetO : (mat W s).det ∈ c.O := by
      rw [Matrix.det_fin_two]
      exact c.O.sub_mem (c.O.mul_mem (hint s 0 0) (hint s 1 1)) (c.O.mul_mem (hint s 0 1) (hint s 1 0))
    refine ⟨hint s 0 0, c.O.mul_mem (CupCob.eps_mem c s) (c.O.mul_mem (hint s 1 1) hdetO), ?_⟩
    have hd : (mat W s).det = mat W s 0 0 * mat W s 1 1 := by
      rw [Matrix.det_fin_two, hup s hs, mul_zero, sub_zero]
    have h2 := CupCob.det_sq W hdet s
    calc mat W s 0 0 * (eps l s * (mat W s 1 1 * (mat W s).det))
        = eps l s * ((mat W s 0 0 * mat W s 1 1) * (mat W s).det) := by ring
      _ = eps l s * (mat W s).det ^ 2 := by rw [← hd]; ring
      _ = eps l s := by rw [h2, mul_one]
  · intro s _ t ht
    show mat W (s * t) 0 0 = mat W s 0 0 * mat W t 0 0
    simp only [mat, map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    have := hup t ht
    simp only [mat] at this
    rw [this, mul_zero, add_zero]

variable [IsAlgClosure ℚ Ω]

theorem exists_ne_one (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (hW : Nf e S A W) :
    ∃ s ∈ Dec (F := ℚ) A, mat W s 0 0 ≠ 1 := by
  set D := Dec (F := ℚ) A with hDdef
  have hup : ∀ s ∈ D, mat W s 1 0 = 0 := hW.upper
  have h00 : ∀ s t, t ∈ D → mat W (s * t) 0 0 = mat W s 0 0 * mat W t 0 0 := by
    intro s t ht
    simp only [mat, map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    have := hup t ht
    simp only [mat] at this
    rw [this, mul_zero, add_zero]
  have hv : A.valuation (l : Ω) < 1 := by
    obtain ⟨v, hA, hlv⟩ := hW.atL
    simpa using (hA _).2 hlv
  obtain ⟨u0, hu0⟩ := GrOfKill.exists_unit_one_add l
  obtain ⟨t, htI, htu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hv u0
  have heps : eps l t = ((1 + l : ℕ) : Qbar l) := by
    simp [eps, cycBar, htu, hu0]
  obtain ⟨m, hm1, hm⟩ := hW.wt
  have htD : t ∈ D := Ine_le_Dec A htI
  have hpow00 : ∀ s ∈ D, ∀ k : ℕ, mat W (s ^ k) 0 0 = mat W s 0 0 ^ k := by
    intro s hs k
    induction k with
    | zero => simp [mat]
    | succ k ih => rw [pow_succ, h00 _ _ hs, ih, pow_succ]
  refine ⟨t ^ m, D.pow_mem htD m, fun h => ?_⟩
  have hT : mat W (t ^ m) 0 0 = (((1 + l) ^ (e * m) : ℕ) : Qbar l) := by
    rw [hpow00 t htD, hm t htI, heps]; push_cast; ring
  rw [hT] at h
  have h1 : (1 + l) ^ (e * m) = 1 := by exact_mod_cast h
  have hl1 : 1 < 1 + l := by have := (Fact.out : l.Prime).two_le; omega
  have : 1 < (1 + l) ^ (e * m) :=
    Nat.one_lt_pow (Nat.mul_ne_zero (by have := hW.e_pos; omega) (by omega)) hl1
  omega

theorem card_ord : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W →
    ∀ (c : Coef l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1),
    ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ v : S, IsPlaceOver A v.1 →
      Nat.card (Lc c n W hint S hN A v) ≤ C * Nat.card (Qn c n) := by
  intro hL l _ Ω _ _ _ e S A W hW c hint hN
  obtain ⟨θ, hθc, hθ⟩ := exists_theta c W hint hW.cont hW.det2 A hW.upper
  have h1 : ∃ g, θ g ≠ 1 := by
    obtain ⟨s, hs, hne⟩ := exists_ne_one e S A W hW
    refine ⟨⟨s, hs⟩, fun h => hne ?_⟩
    have := hθ ⟨s, hs⟩
    rw [h] at this
    exact this.symm
  have h2 : ∃ g, θ g ≠ (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype g := by
    obtain ⟨s, hs, hne⟩ := hW.ne
    refine ⟨⟨s, hs⟩, fun h => hne ?_⟩
    have := hθ ⟨s, hs⟩
    rw [h] at this
    exact this.symm
  obtain ⟨C, hC⟩ := GlobalTheory.LocChar.local_character_h1_bound hL.lf hL.lt hL.le l Ω c A hW.atL θ hθc h1 h2
  refine ⟨C, fun n hn v hv => ?_⟩
  obtain ⟨hfin, hcard⟩ := hC n hn
  have hAv : Av A S v = A := if_pos hv
  have hLc : Nat.card (Lc c n W hint S hN A v) = Nat.card (ordCond c n W hint S hN (Av A S v)) :=
    congrArg (fun p : Submodule _ _ => Nat.card p)
      (if_pos hv : Lc c n W hint S hN A v = ordCond c n W hint S hN (Av A S v))
  rw [hLc, hAv, ← card_lev]
  exact (card_ordCond_le c n W hint S hN hW.cont A hW.upper θ hθ).trans hcard

end GlobalTheory.Ord2.GwIneq.CardOrd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardOrdinaryLocalConditionModPrimePowLeConstMulStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_ordinaryLocalConditionModPrimePow_le_const_mul : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1), ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ v : S, IsPlaceOver A v.1 → Nat.card (Lc c n W hint S hN A v) ≤ C * Nat.card (Qn c n) := by
  first | exact @GlobalTheory.Ord2.GwIneq.CardOrd.card_ord | exact GlobalTheory.Ord2.GwIneq.CardOrd.card_ord | (intros; apply GlobalTheory.Ord2.GwIneq.CardOrd.card_ord <;> assumption)
end
end
