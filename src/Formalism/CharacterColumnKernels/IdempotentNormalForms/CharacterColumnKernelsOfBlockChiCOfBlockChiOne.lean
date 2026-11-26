module

public import Formalism.CharacterColumnKernels.IdempotentNormalForms.ColKerChiOne

@[expose] public section

section -- merged from Formalism.CharacterColumnKernels.IdempotentNormalForms.BlockRhoFull
open Finset Classical

noncomputable section

namespace Formalism.NG

theorem colPsiKer : StatColPsiKer := by
  intro O A T' G _ _ _ _ _ M _ _ _ _ r χ E e₁ δ ι _ D j Kc k0
  ext φ
  simp only [LinearMap.mem_ker, kerY, Submodule.mem_iInf]
  constructor
  · intro h
    have hg : ∀ g, φ (yGen r χ E e₁ δ D j Kc k0 g) = 0 := fun g => by
      have := congrArg (fun c : coZ1s (uRep O (M := M) r χ) => (c : G → M) g) h
      exact this
    have key : ∀ (x : A) (hx : x ∈ Submodule.span A (Set.range (ycoc r χ E))),
        φ (Submodule.Quotient.mk (((⟨x, hx⟩ : Ymod r χ E)),
          (0 : (l : ι) → A × (Fin (j l) → A) × A))) = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g, rfl⟩ := hx
        exact hg g
      | zero =>
        show φ (Submodule.Quotient.mk 0) = 0
        rw [Submodule.Quotient.mk_zero, map_zero]
      | add x z hx hz ihx ihz =>
        have e : (((⟨x + z, Submodule.add_mem _ hx hz⟩ : Ymod r χ E)),
            (0 : (l : ι) → A × (Fin (j l) → A) × A)) =
            (((⟨x, hx⟩ : Ymod r χ E)), (0 : (l : ι) → A × (Fin (j l) → A) × A)) +
            (((⟨z, hz⟩ : Ymod r χ E)), (0 : (l : ι) → A × (Fin (j l) → A) × A)) :=
          Prod.ext rfl (add_zero 0).symm
        rw [e, Submodule.Quotient.mk_add, map_add (f := _), ihx, ihz, add_zero]
      | smul a x hx ih =>
        have e : (((⟨a • x, Submodule.smul_mem _ a hx⟩ : Ymod r χ E)),
            (0 : (l : ι) → A × (Fin (j l) → A) × A)) =
            a • (((⟨x, hx⟩ : Ymod r χ E)), (0 : (l : ι) → A × (Fin (j l) → A) × A)) :=
          Prod.ext rfl (smul_zero a).symm
        rw [e, Submodule.Quotient.mk_smul, map_smul, ih, smul_zero]
    intro y
    exact key y.1 y.2
  · intro h
    apply Subtype.ext
    funext g
    exact h ⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩

theorem cobColumn : StatCobColumn := by
  intro O A T' G _ _ _ _ _ M _ _ _ _ _ _ r χ E e₁ δ δO ι _ D j Kc k0 s t hE hEE hEm hδ hτ
    φ v hv

  let Fl : Ymod r χ E →ₗ[A] M := φ.comp ((colRelJ r χ E e₁ δ D j Kc k0).mkQ.comp
    (LinearMap.inl A (Ymod r χ E) ((l : ι) → A × (Fin (j l) → A) × A)))
  let yg : G → Ymod r χ E := fun g => ⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩
  have hF : ∀ g, Fl (yg g) = uElt r χ g • v - v := fun g => congrFun hv g
  have huv : ∀ g, algebraMap T' A (t g * ((χ g : T'ˣ) : T')) * ((((χ g)⁻¹ : T'ˣ) : T') • r g) =
      t g • r g := by
    intro g
    rw [← Algebra.smul_def, smul_smul, mul_assoc, Units.mul_inv, mul_one]
  have hu' : ∀ g, algebraMap T' A (t g * ((χ g : T'ˣ) : T')) * uElt r χ g = t g • r g :=
    fun g => huv g
  have hterm : ∀ g, algebraMap T' A (t g * ((χ g : T'ˣ) : T')) * ycoc r χ E g =
      (t g • r g - algebraMap T' A (t g * ((χ g : T'ˣ) : T'))) * E := by
    intro g
    simp only [ycoc]
    rw [← mul_assoc, mul_sub, mul_one, huv g]
  obtain ⟨y₁, hy₁def⟩ : ∃ y : Ymod r χ E,
      y = ∑ g ∈ s, algebraMap T' A (t g * ((χ g : T'ˣ) : T')) • yg g := ⟨_, rfl⟩
  have hy₁ : ((y₁ : Ymod r χ E) : A) =
      (E - algebraMap T' A (∑ g ∈ s, t g * ((χ g : T'ˣ) : T'))) * E := by
    rw [hy₁def]
    simp only [Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul, yg, Submodule.coe_mk]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_congr rfl (fun g _ => hterm g), ← Finset.sum_mul, Finset.sum_sub_distrib, ← hE,
      ← map_sum]
  have hFy : Fl y₁ = -(δO • v) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy₁def, map_sum]
    have hgen : ∀ g ∈ s, Fl (algebraMap T' A (t g * ((χ g : T'ˣ) : T')) • yg g) =
        (t g • r g) • v - (t g * ((χ g : T'ˣ) : T')) • v := by
      intro g _
      rw [map_smul, hF g, smul_sub, smul_smul, hu' g, algebraMap_smul]
    rw [Finset.sum_congr rfl hgen, Finset.sum_sub_distrib, ← Finset.sum_smul, ← Finset.sum_smul,
      ← hE, hEm, hτ, zero_sub]
  have alg : ∀ (a b : A), E * E = a * E → E * b = b * E → a * b = b * a →
      E * ((E - b) * E) = a * ((E - b) * E) := by
    intro a b hEE' hc hab
    have h1 : E * ((E - b) * E) = a * (a * E) - b * (a * E) := by
      calc E * ((E - b) * E) = (E * E) * E - (E * b) * E := by noncomm_ring
        _ = (a * E) * E - (b * E) * E := by rw [hEE', hc]
        _ = a * (E * E) - b * (E * E) := by noncomm_ring
        _ = a * (a * E) - b * (a * E) := by rw [hEE']
    have h2 : a * ((E - b) * E) = a * (a * E) - b * (a * E) := by
      calc a * ((E - b) * E) = a * (E * E) - (a * b) * E := by noncomm_ring
        _ = a * (a * E) - (b * a) * E := by rw [hEE', hab]
        _ = a * (a * E) - b * (a * E) := by noncomm_ring
    rw [h1, h2]
  have hEE' : E * E = algebraMap T' A δ * E := by rw [hEE, Algebra.smul_def]
  have hyE := alg (algebraMap T' A δ) (algebraMap T' A (∑ g ∈ s, t g * ((χ g : T'ˣ) : T')))
    hEE' (Algebra.commutes _ E).symm (by rw [← map_mul, ← map_mul, mul_comm])
  have h1 : Fl (E • y₁) = 0 := by rw [map_smul, hEm]
  have h2 : E • y₁ = algebraMap T' A δ • y₁ := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, smul_eq_mul]
    rw [hy₁]
    exact hyE
  have h3 : Fl (algebraMap T' A δ • y₁) = -((δO * δO) • v) := by
    rw [map_smul, hFy, algebraMap_smul, hδ, smul_neg, smul_smul]
  rw [h2, h3] at h1
  exact neg_eq_zero.mp h1

theorem blockRhoFull : BlockRhoFull₂ := by
  intro O _ _ _ A T' G _ _ _ _ d _ _ _ _ _ r χ E e₁ δ δO ι _ _ ι' _ colIdx hinj D j e' Kc k0
    ℓ sE tE hE hEE hEm hk0 hδ hτ hiso hloc
  exact blockRhoColumn O A T' G d r χ E e₁ δ δO ι ι' colIdx hinj D j e' Kc k0 ℓ hEm hk0
    (fun m => by rw [algebraMap_smul]; exact hδ m) hiso hloc (uRep O (M := d → KO O) r χ)
    (colPsi (O := O) (M := d → KO O) r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0)
    (colPsiKer O A T' G (d → KO O) r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0)
    (fun h v hv => cobColumn O A T' G (d → KO O) r χ E e₁ δ δO ι (fun l => D (colIdx l))
      (fun l => j (colIdx l)) Kc k0 sE tE hE hEE hEm hδ hτ h v hv)

end Formalism.NG
end
end

section -- merged from Formalism.CharacterColumnKernels.IdempotentNormalForms.BlockChiOneFullOf
section -- merged from Formalism.CharacterColumnKernels.IdempotentNormalForms.BlockChiOneTriv
open Finset

noncomputable section

namespace Formalism.NG

namespace TrivialCharacterBlockLength

section Triv

variable {O : Type*} [CommRing O] {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module O M]

lemma length_mid_zero {H : Type*} [AddCommGroup H] [Module O H] (ρM : Representation O G M)
    (hB : ∀ x ∈ coB1 ρM, x = 0) (Ψ : H →ₗ[O] coZ1s ρM) :
    Module.length O ↥(LinearMap.range Ψ ⊓
        LinearMap.ker ((coB1 ρM).comap (coZ1s ρM).subtype).mkQ) = 0 := by
  rw [Module.length_eq_zero_iff]
  refine ⟨fun a b => ?_⟩
  have hz : ∀ z : ↥(LinearMap.range Ψ ⊓
      LinearMap.ker ((coB1 ρM).comap (coZ1s ρM).subtype).mkQ), z = 0 := by
    rintro ⟨z, hz⟩
    obtain ⟨-, hz2⟩ := Submodule.mem_inf.mp hz
    rw [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, Submodule.subtype_apply] at hz2
    have h0 := hB _ hz2
    exact Subtype.ext (Subtype.ext h0)
  rw [hz a, hz b]

end Triv

lemma blockTrivAbs {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module O M]
    {H : Type*} [AddCommGroup H] [Module O H]
    (ρM : Representation O G M) (hB : ∀ x ∈ coB1 ρM, x = 0) (Ψ : H →ₗ[O] coZ1s ρM)
    {ι : Type*} [DecidableEq ι] (what₂ cols : Finset ι) (D : ι → Subgroup G)
    (F : ∀ w, Submodule O (H1z (resRep ρM (D w))))
    (lenRow : ι → ℕ∞) (Q : Submodule O (H1z ρM)) (s : ℕ∞)
    (hrows : ∀ w ∈ what₂, ∃ A : Submodule O (H1z (resRep ρM (D w))),
      F w ≤ A ∧ Module.length O (A ⧸ (F w).comap A.subtype) ≤ lenRow w ∧
      ∀ h : H, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ A)
    (hcols : ∀ w ∈ cols, ∀ h : H,
      resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w)
    (hQ : ∀ h : H, Submodule.mkQ _ (Ψ h) ∈ Q)
    (hsel : Module.length O ↥(Q ⊓ ⨅ w ∈ what₂ ∪ cols,
      (F w).comap (resH1 ρM (D w))) ≤ s) :
    Module.length O H ≤ Module.length O (LinearMap.ker Ψ) + (s + ∑ w ∈ what₂, lenRow w) := by
  classical
  let A : ∀ w, Submodule O (H1z (resRep ρM (D w))) := fun w =>
    if hw : w ∈ what₂ then Classical.choose (hrows w hw) else F w
  have hA : ∀ w (hw : w ∈ what₂), A w = Classical.choose (hrows w hw) := fun w hw => dif_pos hw
  have hA' : ∀ w, w ∉ what₂ → A w = F w := fun w hw => dif_neg hw
  have hFA : ∀ w, F w ≤ A w := by
    intro w
    by_cases hw : w ∈ what₂
    · rw [hA w hw]; exact (Classical.choose_spec (hrows w hw)).1
    · rw [hA' w hw]
  let S : Submodule O (H1z ρM) := Q ⊓ ⨅ w ∈ what₂ ∪ cols, (A w).comap (resH1 ρM (D w))
  have hS : LinearMap.range ((Submodule.mkQ ((coB1 ρM).comap (coZ1s ρM).subtype)) ∘ₗ Ψ) ≤ S := by
    rintro _ ⟨h, rfl⟩
    refine (IdempotentNormalFormsRhoFacts.mem_sel (what₂ ∪ cols) (fun w => resH1 ρM (D w)) A Q _).mpr
      ⟨hQ h, fun w hw => ?_⟩
    by_cases hwr : w ∈ what₂
    · rw [hA w hwr]; exact (Classical.choose_spec (hrows w hwr)).2.2 h
    · rw [hA' w hwr]
      exact hcols w ((Finset.mem_union.mp hw).resolve_left hwr) h
  have hchain := lenChain O H (coZ1s ρM) (H1z ρM) Ψ _ S hS
  rw [length_mid_zero ρM hB Ψ, add_zero] at hchain
  have hSel : Module.length O S ≤ s + ∑ w ∈ what₂, lenRow w := by
    have h2 := selRelax O (H1z ρM) ι (what₂ ∪ cols) (fun w => H1z (resRep ρM (D w)))
      (fun w => resH1 ρM (D w)) F A Q hFA
    have hterm : ∀ w ∈ what₂ ∪ cols, Module.length O (A w ⧸ (F w).comap (A w).subtype) ≤
        if w ∈ what₂ then lenRow w else 0 := by
      intro w _
      by_cases hwr : w ∈ what₂
      · rw [if_pos hwr, hA w hwr]
        exact (Classical.choose_spec (hrows w hwr)).2.1
      · rw [if_neg hwr, hA' w hwr, Submodule.comap_subtype_self, Module.length_eq_zero]
    calc Module.length O S ≤ _ := h2
      _ ≤ s + ∑ w ∈ what₂ ∪ cols, (if w ∈ what₂ then lenRow w else 0) :=
          add_le_add hsel (Finset.sum_le_sum hterm)
      _ = s + ∑ w ∈ what₂, lenRow w := by
          rw [Finset.sum_ite_mem, Finset.union_inter_cancel_left]
  exact hchain.trans (add_le_add le_rfl hSel)

lemma final_arith (k X c vδ s R1 R2 : ℕ∞) (hk : k ≤ X + c * vδ) :
    k + (s + (R1 + R2)) ≤ s + X + R1 + 4 * (c + 1) * vδ + R2 := by
  calc k + (s + (R1 + R2)) ≤ (X + c * vδ) + (s + (R1 + R2)) := add_le_add hk le_rfl
    _ ≤ (X + c * vδ) + (s + (R1 + R2)) + (3 * c * vδ + 4 * vδ) := le_self_add
    _ = s + X + R1 + 4 * (c + 1) * vδ + R2 := by ring

end TrivialCharacterBlockLength

end Formalism.NG
end
end

open Finset Classical

noncomputable section

namespace Formalism.NG

universe u₁ u₂ u₃ u₄ u₅ u₆

namespace IdempotentColumnIndexImages

lemma sum_image_colIdx {ι ι' : Type*} [Fintype ι] [DecidableEq ι'] (colIdx : ι → ι')
    (hinj : Function.Injective colIdx) (f : ι' → ℕ∞) :
    ∑ w ∈ (univ : Finset ι).image colIdx, f w = ∑ l : ι, f (colIdx l) :=
  Finset.sum_image fun _ _ _ _ h => hinj h

lemma card_image_colIdx {ι ι' : Type*} [Fintype ι] [DecidableEq ι'] (colIdx : ι → ι')
    (hinj : Function.Injective colIdx) :
    (((univ : Finset ι).image colIdx).card : ℕ∞) = (Fintype.card ι : ℕ∞) := by
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]

end IdempotentColumnIndexImages

theorem blockChiCFull_of (hK : StatColKerChiC.{u₁, u₂, u₃, u₄, u₅}) :
    StatBlockChiCFull.{u₁, u₂, u₃, u₄, u₅, u₆} := by
  intro O _ _ _ A T' G _ _ _ _ d _ _ _ _ _ r χ E e₁ δ δO ι _ _ ι' _ colIdx hinj D j Kc k0 ℓ cB sE tE
    hd hE hEE he₁ hEM hk0 hδ hτ ρM Ψ lrows qs F deg vζ Q Sha H0 cols eO vδ hH0 hl hq hcols hQ hsel
  let lenRow : ι' → ℕ∞ := fun w =>
    (if w ∈ lrows then eO * (cB : ℕ∞) * ((deg w : ℕ∞) + 2) else 0) + (if w ∈ qs then vζ w else 0)
  have hrows : ∀ w ∈ lrows ∪ qs, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ lenRow w ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B := by
    intro w hw
    by_cases hwl : w ∈ lrows
    · obtain ⟨B, h1, h2, h3⟩ := hl w hwl
      refine ⟨B, h1, h2.trans ?_, h3⟩
      simp only [lenRow, if_pos hwl]
      exact le_self_add
    · have hwq : w ∈ qs := (Finset.mem_union.mp hw).resolve_left hwl
      obtain ⟨B, h1, h2, h3⟩ := hq w hwq
      refine ⟨B, h1, h2.trans ?_, h3⟩
      simp only [lenRow, if_neg hwl, if_pos hwq, zero_add, le_refl]
  have hkerEq : LinearMap.ker Ψ = kerY (O := O) (M := d → KO O) r χ E e₁ δ
      (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 :=
    colPsiKer O A T' G (d → KO O) r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l))
      Kc k0
  have hK1 := hK O A T' G d r χ E e₁ δ δO ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0
    he₁ hEM hk0 (fun m => by rw [algebraMap_smul]; exact hδ m)
  have hsumH : ∑ l : ι, Module.length O
      (LinearMap.ker (colDO (O := O) (M := d → KO O) r χ (D (colIdx l)))) ≤ ∑ w ∈ cols, H0 := by
    calc ∑ l : ι, Module.length O
          (LinearMap.ker (colDO (O := O) (M := d → KO O) r χ (D (colIdx l))))
        ≤ ∑ l : ι, H0 :=
          Finset.sum_le_sum fun l _ => hH0 (colIdx l) (Finset.mem_image_of_mem _ (Finset.mem_univ l))
      _ = ∑ w ∈ cols, H0 := (IdempotentColumnIndexImages.sum_image_colIdx colIdx hinj (fun _ => H0)).symm
  have hker' : Module.length O (LinearMap.ker Ψ) ≤
      ∑ w ∈ cols, ((((fun _ => 0 : ι' → ℕ) w : ℕ) : ℕ∞) *
        (eO * (((fun _ => 0 : ι' → ℕ) w : ℕ) : ℕ∞) + vδ) + (fun _ => H0 : ι' → ℕ∞) w) +
        (cols.card : ℕ∞) * (Fintype.card d : ℕ∞) * vδ := by
    rw [hkerEq]
    refine hK1.trans ?_
    simp only [Nat.cast_zero, zero_mul, zero_add]
    rw [show (cols.card : ℕ∞) = (Fintype.card ι : ℕ∞) from IdempotentColumnIndexImages.card_image_colIdx colIdx hinj]
    exact add_le_add hsumH le_rfl
  have hcob : ∀ (h : ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 →ₗ[A]
      (d → KO O)) (v : d → KO O), (Ψ h : G → (d → KO O)) = coD0 ρM v → (δO * δO) • v = 0 :=
    fun h v hv => cobColumn O A T' G (d → KO O) r χ E e₁ δ δO ι (fun l => D (colIdx l))
      (fun l => j (colIdx l)) Kc k0 sE tE hE hEE hEM hδ hτ h v hv
  have h := blockRhoAbs O G d ρM _ Ψ δO hcob ι' (lrows ∪ qs) cols D F lenRow Q Sha ℓ
    (fun _ => 0) (fun _ => 0) (fun _ => H0) hrows hcols hQ hsel hker'
  have hsum : ∑ w ∈ lrows ∪ qs, lenRow w =
      eO * (cB : ℕ∞) * ∑ w ∈ lrows, ((deg w : ℕ∞) + 2) + ∑ w ∈ qs, vζ w := by
    simp only [lenRow]
    rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
      Finset.union_inter_cancel_left, Finset.union_inter_cancel_right, Finset.mul_sum]
  refine h.trans (le_of_eq ?_)
  simp only [Nat.cast_zero, zero_mul, zero_add, Finset.sum_const, nsmul_eq_mul, hd, Nat.cast_one,
    mul_one]
  rw [hsum]
  ring

theorem blockChiOneFull_of (hK : StatColKerChiOne.{u₁, u₂, u₃, u₄, u₅}) :
    StatBlockChiOneFull.{u₁, u₂, u₃, u₄, u₅, u₆} := by
  intro O _ _ _ A T' G _ _ _ _ d _ _ _ _ _ r χ E e₁ δ δO ι _ _ ι' _ colIdx hinj D j e' Kc k0 ℓ cB
    hd hu he₁ hEM hδ hk0 ρM Ψ lrows qs F deg vζ Q vhE cols eO vδ hl hq hcols hQ hsel
  let lenRow : ι' → ℕ∞ := fun w =>
    (if w ∈ lrows then eO * (cB : ℕ∞) * ((deg w : ℕ∞) + 2) else 0) + (if w ∈ qs then vζ w else 0)
  have hrows : ∀ w ∈ lrows ∪ qs, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ lenRow w ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B := by
    intro w hw
    by_cases hwl : w ∈ lrows
    · obtain ⟨B, h1, h2, h3⟩ := hl w hwl
      refine ⟨B, h1, h2.trans ?_, h3⟩
      simp only [lenRow, if_pos hwl]
      exact le_self_add
    · have hwq : w ∈ qs := (Finset.mem_union.mp hw).resolve_left hwl
      obtain ⟨B, h1, h2, h3⟩ := hq w hwq
      refine ⟨B, h1, h2.trans ?_, h3⟩
      simp only [lenRow, if_neg hwl, if_pos hwq, zero_add, le_refl]
  have hB : ∀ x ∈ coB1 ρM, x = 0 := by
    rintro _ ⟨v, rfl⟩
    funext g
    exact (show uElt r χ g • v - v = 0 by rw [hu, sub_self])
  have h := TrivialCharacterBlockLength.blockTrivAbs ρM hB Ψ (lrows ∪ qs) cols D F lenRow Q vhE hrows hcols hQ hsel
  have hkerEq : LinearMap.ker Ψ = kerY (O := O) (M := d → KO O) r χ E e₁ δ
      (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 :=
    colPsiKer O A T' G (d → KO O) r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l))
      Kc k0
  have hK1 := hK O A T' G d r χ E e₁ δ δO ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0
    ℓ (fun l => e' (colIdx l)) hu he₁ hEM (fun m => by rw [algebraMap_smul]; exact hδ m) hk0
  have hker : Module.length O (LinearMap.ker Ψ) ≤
      ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ) + (cols.card : ℕ∞) * vδ := by
    rw [hkerEq]
    refine hK1.trans (le_of_eq ?_)
    rw [hd, Nat.cast_one, mul_one, IdempotentColumnIndexImages.card_image_colIdx colIdx hinj,
      IdempotentColumnIndexImages.sum_image_colIdx colIdx hinj (fun w => eO * (e' w : ℕ∞) + 2 * vδ)]
    simp only [one_mul]
    rfl
  have hsum : ∑ w ∈ lrows ∪ qs, lenRow w =
      eO * (cB : ℕ∞) * ∑ w ∈ lrows, ((deg w : ℕ∞) + 2) + ∑ w ∈ qs, vζ w := by
    simp only [lenRow]
    rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
      Finset.union_inter_cancel_left, Finset.union_inter_cancel_right, Finset.mul_sum]
  rw [hsum] at h
  exact h.trans (TrivialCharacterBlockLength.final_arith _ _ _ _ _ _ _ hker)

theorem blockChiCFull : StatBlockChiCFull := blockChiCFull_of colKerChiC

theorem blockChiOneFull : StatBlockChiOneFull := blockChiOneFull_of colKerChiOne

end Formalism.NG
end
end

open Finset Classical

noncomputable section

namespace Formalism.NG

lemma sum_range_ite_le_add_sum_Ioo (t : ℕ) (a : ℕ∞) (Sha : ℕ → ℕ∞) :
    ∑ i ∈ range t, (if i + 1 = 1 then a else Sha (i + 1 - 1)) ≤ a + ∑ e ∈ Ioo 0 t, Sha e := by
  have hsub : range t ⊆ insert 0 (Ioo 0 t) := by
    intro i hi
    rw [mem_range] at hi
    rcases Nat.eq_zero_or_pos i with h | h
    · exact mem_insert.2 (Or.inl h)
    · exact mem_insert.2 (Or.inr (mem_Ioo.2 ⟨h, hi⟩))
  have h0 : (0 : ℕ) ∉ Ioo 0 t := by simp
  calc ∑ i ∈ range t, (if i + 1 = 1 then a else Sha (i + 1 - 1))
      ≤ ∑ i ∈ insert 0 (Ioo 0 t), (if i + 1 = 1 then a else Sha (i + 1 - 1)) :=
        sum_le_sum_of_subset hsub
    _ = a + ∑ e ∈ Ioo 0 t, Sha e := by
        rw [sum_insert h0]
        congr 1
        refine sum_congr rfl fun e he => ?_
        have hne : e + 1 ≠ 1 := by
          have := (mem_Ioo.1 he).1
          omega
        rw [if_neg hne, Nat.add_sub_cancel]

lemma collectAlt (t : ℕ) (ht : 1 ≤ t) (L : Fin (t + 1) → ℕ∞) (S : Finset (Fin (t + 1))) (v : ℕ∞)
    (what₂ cols qs : Finset ℕ) (lenRow vζ h0 : ℕ → ℕ∞) (e' j deg : ℕ → ℕ) (Sha : ℕ → ℕ∞)
    (eO vδ s vhE N H0 : ℕ∞) (cB : ℕ)
    (hG : v ≤ ∑ k ∈ S, L k)
    (hL0 : L 0 ≤ ∑ w ∈ what₂, lenRow w + ∑ w ∈ cols, ((j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + h0 w) +
      s + 4 * N * ((cols.card : ℕ∞) + 1) * vδ)
    (hL1 : L ⟨1, by omega⟩ ≤ vhE + ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ) +
      eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) + 4 * ((cols.card : ℕ∞) + 1) * vδ +
      ∑ w ∈ qs, vζ w)
    (hLc : ∀ c : Fin (t + 1), 2 ≤ (c : ℕ) → L c ≤ Sha ((c : ℕ) - 1) +
      eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) + 4 * ((cols.card : ℕ∞) + 1) * vδ +
      (cols.card : ℕ∞) * H0 + ∑ w ∈ qs, vζ w) :
    v ≤ ∑ w ∈ what₂, lenRow w +
        ∑ w ∈ cols, (eO * (e' w : ℕ∞) + (j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + 2 * vδ + h0 w) + s +
        ∑ e ∈ Finset.Ioo 0 t, Sha e + vhE +
        (t : ℕ∞) * eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) +
        4 * (N + t) * ((cols.card : ℕ∞) + 1) * vδ +
        (t : ℕ∞) * (cols.card : ℕ∞) * H0 + (t : ℕ∞) * ∑ w ∈ qs, vζ w := by
  set C1 : ℕ∞ := ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ) with hC1
  set A0 : ℕ∞ := ∑ w ∈ what₂, lenRow w +
    ∑ w ∈ cols, ((j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + h0 w) + s with hA0
  set B : ℕ∞ := eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) +
    4 * ((cols.card : ℕ∞) + 1) * vδ + (cols.card : ℕ∞) * H0 + ∑ w ∈ qs, vζ w with hB
  have hsucc : ∀ i : Fin t, L i.succ ≤
      (if (i : ℕ) + 1 = 1 then vhE + C1 else Sha ((i : ℕ) + 1 - 1)) + B := by
    intro i
    by_cases hi : (i : ℕ) = 0
    · have hs : i.succ = ⟨1, by omega⟩ := Fin.ext (by simp [hi])
      rw [if_pos (by omega), hs]
      refine (hL1.trans ?_)
      rw [hB]
      calc vhE + C1 + eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) +
            4 * ((cols.card : ℕ∞) + 1) * vδ + ∑ w ∈ qs, vζ w
          ≤ vhE + C1 + eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) +
            4 * ((cols.card : ℕ∞) + 1) * vδ + ∑ w ∈ qs, vζ w + (cols.card : ℕ∞) * H0 := le_self_add
        _ = _ := by ring
    · rw [if_neg (by omega)]
      have h2 : 2 ≤ ((i.succ : Fin (t + 1)) : ℕ) := by simp [Fin.val_succ]; omega
      refine (hLc i.succ h2).trans_eq ?_
      rw [hB, Fin.val_succ]
      ring
  have hsumite : ∑ i : Fin t, (if (i : ℕ) + 1 = 1 then vhE + C1 else Sha ((i : ℕ) + 1 - 1)) ≤
      (vhE + C1) + ∑ e ∈ Ioo 0 t, Sha e := by
    rw [Fin.sum_univ_eq_sum_range (fun i => if i + 1 = 1 then vhE + C1 else Sha (i + 1 - 1)) t]
    exact sum_range_ite_le_add_sum_Ioo t (vhE + C1) Sha
  have hcol : ∑ w ∈ cols,
      (eO * (e' w : ℕ∞) + (j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + 2 * vδ + h0 w) =
      ∑ w ∈ cols, ((j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + h0 w) + C1 := by
    rw [hC1, ← sum_add_distrib]
    exact sum_congr rfl fun w _ => by ring
  rw [hcol]
  calc v ≤ ∑ k ∈ S, L k := hG
    _ ≤ ∑ k : Fin (t + 1), L k := sum_le_sum_of_subset (subset_univ _)
    _ = L 0 + ∑ i : Fin t, L i.succ := Fin.sum_univ_succ L
    _ ≤ (A0 + 4 * N * ((cols.card : ℕ∞) + 1) * vδ) +
          ∑ i : Fin t, ((if (i : ℕ) + 1 = 1 then vhE + C1 else Sha ((i : ℕ) + 1 - 1)) + B) :=
        add_le_add hL0 (sum_le_sum fun i _ => hsucc i)
    _ = (A0 + 4 * N * ((cols.card : ℕ∞) + 1) * vδ) +
          (∑ i : Fin t, (if (i : ℕ) + 1 = 1 then vhE + C1 else Sha ((i : ℕ) + 1 - 1)) +
            (t : ℕ∞) * B) := by
        rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ (A0 + 4 * N * ((cols.card : ℕ∞) + 1) * vδ) +
          (((vhE + C1) + ∑ e ∈ Ioo 0 t, Sha e) + (t : ℕ∞) * B) := by
        gcongr
    _ = _ := by
        rw [hA0, hB]
        ring


set_option maxHeartbeats 4000000 in
theorem blockRhoLat : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type) [Ring A] [CommRing T'] [Algebra T' A] [Group G] (d : Type) [Fintype d] [DecidableEq d]
    (ρ : A →+* Matrix d d O) [SMulCommClass A O (LatQ O d ρ)]
    [Module T' (LatQ O d ρ)] [IsScalarTower T' A (LatQ O d ρ)]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (δO : O) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ι' : Type) [DecidableEq ι'] (colIdx : ι → ι'), Function.Injective colIdx →
    ∀ (D : ι' → Subgroup G) (j e' : ι' → ℕ) (Kc : ∀ l, Fin (j (colIdx l)) → G → A)
      (k0 : ι → G → A) (ℓ : ℕ) (sE : Finset G) (tE : G → T'),
    E = ∑ g ∈ sE, tE g • r g → E * E = δ • E →
    (∀ m : LatQ O d ρ, E • m = 0) →
    (∀ l g, ∃ a : A, k0 l g = a * E) →
    (∀ m : LatQ O d ρ, δ • m = δO • m) →
    (∀ m : LatQ O d ρ, (∑ g ∈ sE, tE g * ((χ g : T'ˣ) : T')) • m = δO • m) →
    Nonempty (↥(LinearMap.range (DistribSMul.toLinearMap O (LatQ O d ρ) e₁)) ≃ₗ[O] KO O) →
    (∀ l (s : Fin (j (colIdx l)) → (LatQ O d ρ)),
      (∀ a, s a ∈ LinearMap.range (DistribSMul.toLinearMap O (LatQ O d ρ) e₁)) →
      (fun g : D (colIdx l) => ∑ a, Kc l a g • s a) ∈
        LinearMap.range (colDO (O := O) r χ (D (colIdx l))) →
      ∀ a, ((ℓ : O) ^ e' (colIdx l)) • s a = 0) →
    let ρM := uRep O (M := LatQ O d ρ) r χ
    let Ψ := colPsi (O := O) (M := LatQ O d ρ) r χ E e₁ δ (fun l => D (colIdx l))
      (fun l => j (colIdx l)) Kc k0
    ∀ (what₂ : Finset ι') (F : ∀ w, Submodule O (H1z (resRep ρM (D w)))) (lenRow : ι' → ℕ∞)
      (Q : Submodule O (H1z ρM)) (s : ℕ∞),
    let cols : Finset ι' := univ.image colIdx
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    let vδ : ℕ∞ := IsDiscreteValuationRing.addVal O δO
    let N : ℕ∞ := Fintype.card d
    let h0 : ι' → ℕ∞ := fun w => Module.length O (LinearMap.ker (colDO (O := O) (M := LatQ O d ρ) r χ (D w)))
    (∀ w ∈ what₂, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ lenRow w ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) →
    (∀ w ∈ cols, ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w) →
    (∀ h, Submodule.mkQ _ (Ψ h) ∈ Q) →
    Module.length O ↥(Q ⊓ ⨅ w ∈ what₂ ∪ cols, (F w).comap (resH1 ρM (D w))) ≤ s →
    Module.length O (ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 →ₗ[A]
        (LatQ O d ρ)) ≤
      ∑ w ∈ what₂, lenRow w + ∑ w ∈ cols, ((j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + h0 w) + s +
        4 * N * ((cols.card : ℕ∞) + 1) * vδ := by
  intro O _ _ _ A T' G _ _ _ _ d _ _ ρ _ _ _
  letI : Module A (d → KO O) := (inferInstance : Module A (LatQ O d ρ))
  letI : SMulCommClass A O (d → KO O) := (inferInstance : SMulCommClass A O (LatQ O d ρ))
  letI : Module T' (d → KO O) := (inferInstance : Module T' (LatQ O d ρ))
  letI : IsScalarTower T' A (d → KO O) := (inferInstance : IsScalarTower T' A (LatQ O d ρ))
  exact blockRhoFull O A T' G d


set_option maxHeartbeats 4000000 in
theorem blockChiCLat (hC : StatBlockChiCFull.{0, 0, 0, 0, 0, 0}) : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type) [Ring A] [CommRing T'] [Algebra T' A] [Group G] (d : Type) [Fintype d] [DecidableEq d]
    (ρ : A →+* Matrix d d O) [SMulCommClass A O (LatQ O d ρ)]
    [Module T' (LatQ O d ρ)] [IsScalarTower T' A (LatQ O d ρ)]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (δO : O) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ι' : Type) [DecidableEq ι'] (colIdx : ι → ι'), Function.Injective colIdx →
    ∀ (D : ι' → Subgroup G) (j : ι' → ℕ) (Kc : ∀ l, Fin (j (colIdx l)) → G → A)
      (k0 : ι → G → A) (ℓ cB : ℕ) (sE : Finset G) (tE : G → T'),
    Fintype.card d = 1 →
    E = ∑ g ∈ sE, tE g • r g → E * E = δ • E →
    (∀ m : LatQ O d ρ, e₁ • m = 0) → (∀ m : LatQ O d ρ, E • m = 0) →
    (∀ l g, ∃ a : A, k0 l g = a * E) →
    (∀ m : LatQ O d ρ, δ • m = δO • m) →
    (∀ m : LatQ O d ρ, (∑ g ∈ sE, tE g * ((χ g : T'ˣ) : T')) • m = δO • m) →
    let ρM := uRep O (M := LatQ O d ρ) r χ
    let Ψ := colPsi (O := O) (M := LatQ O d ρ) r χ E e₁ δ (fun l => D (colIdx l))
      (fun l => j (colIdx l)) Kc k0
    ∀ (lrows qs : Finset ι') (F : ∀ w, Submodule O (H1z (resRep ρM (D w)))) (deg : ι' → ℕ)
      (vζ : ι' → ℕ∞) (Q : Submodule O (H1z ρM)) (Sha H0 : ℕ∞),
    let cols : Finset ι' := univ.image colIdx
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    let vδ : ℕ∞ := IsDiscreteValuationRing.addVal O δO
    (∀ w ∈ cols, Module.length O (LinearMap.ker (colDO (O := O) (M := LatQ O d ρ) r χ (D w))) ≤ H0) →
    (∀ w ∈ lrows, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ eO * (cB : ℕ∞) * ((deg w : ℕ∞) + 2) ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) →
    (∀ w ∈ qs, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ vζ w ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) →
    (∀ w ∈ cols, ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w) →
    (∀ h, Submodule.mkQ _ (Ψ h) ∈ Q) →
    Module.length O ↥(Q ⊓ ⨅ w ∈ lrows ∪ qs ∪ cols, (F w).comap (resH1 ρM (D w))) ≤ Sha →
    Module.length O (ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 →ₗ[A]
        (LatQ O d ρ)) ≤
      Sha + eO * (cB : ℕ∞) * ∑ w ∈ lrows, ((deg w : ℕ∞) + 2) + 4 * ((cols.card : ℕ∞) + 1) * vδ +
        (cols.card : ℕ∞) * H0 + ∑ w ∈ qs, vζ w := by
  intro O _ _ _ A T' G _ _ _ _ d _ _ ρ _ _ _
  letI : Module A (d → KO O) := (inferInstance : Module A (LatQ O d ρ))
  letI : SMulCommClass A O (d → KO O) := (inferInstance : SMulCommClass A O (LatQ O d ρ))
  letI : Module T' (d → KO O) := (inferInstance : Module T' (LatQ O d ρ))
  letI : IsScalarTower T' A (d → KO O) := (inferInstance : IsScalarTower T' A (LatQ O d ρ))
  exact hC O A T' G d


set_option maxHeartbeats 4000000 in
theorem blockChiOneLat (hOne : StatBlockChiOneFull.{0, 0, 0, 0, 0, 0}) : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type) [Ring A] [CommRing T'] [Algebra T' A] [Group G] (d : Type) [Fintype d] [DecidableEq d]
    (ρ : A →+* Matrix d d O) [SMulCommClass A O (LatQ O d ρ)]
    [Module T' (LatQ O d ρ)] [IsScalarTower T' A (LatQ O d ρ)]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (δO : O) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ι' : Type) [DecidableEq ι'] (colIdx : ι → ι'), Function.Injective colIdx →
    ∀ (D : ι' → Subgroup G) (j e' : ι' → ℕ) (Kc : ∀ l, Fin (j (colIdx l)) → G → A)
      (k0 : ι → G → A) (ℓ cB : ℕ),
    Fintype.card d = 1 →
    (∀ g (m : LatQ O d ρ), uElt r χ g • m = m) →
    (∀ m : LatQ O d ρ, e₁ • m = 0) → (∀ m : LatQ O d ρ, E • m = δO • m) →
    (∀ m : LatQ O d ρ, δ • m = δO • m) →
    (∀ l, ∃ g ∈ D (colIdx l), ∃ c : O, IsUnit c ∧
      ∀ m : LatQ O d ρ, k0 l g • m = ((ℓ : O) ^ e' (colIdx l) * δO * c) • m) →
    let ρM := uRep O (M := LatQ O d ρ) r χ
    let Ψ := colPsi (O := O) (M := LatQ O d ρ) r χ E e₁ δ (fun l => D (colIdx l))
      (fun l => j (colIdx l)) Kc k0
    ∀ (lrows qs : Finset ι') (F : ∀ w, Submodule O (H1z (resRep ρM (D w)))) (deg : ι' → ℕ)
      (vζ : ι' → ℕ∞) (Q : Submodule O (H1z ρM)) (vhE : ℕ∞),
    let cols : Finset ι' := univ.image colIdx
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    let vδ : ℕ∞ := IsDiscreteValuationRing.addVal O δO
    (∀ w ∈ lrows, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ eO * (cB : ℕ∞) * ((deg w : ℕ∞) + 2) ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) →
    (∀ w ∈ qs, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ vζ w ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) →
    (∀ w ∈ cols, ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w) →
    (∀ h, Submodule.mkQ _ (Ψ h) ∈ Q) →
    Module.length O ↥(Q ⊓ ⨅ w ∈ lrows ∪ qs ∪ cols, (F w).comap (resH1 ρM (D w))) ≤ vhE →
    Module.length O (ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 →ₗ[A]
        (LatQ O d ρ)) ≤
      vhE + ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ) +
        eO * (cB : ℕ∞) * ∑ w ∈ lrows, ((deg w : ℕ∞) + 2) + 4 * ((cols.card : ℕ∞) + 1) * vδ +
        ∑ w ∈ qs, vζ w := by
  intro O _ _ _ A T' G _ _ _ _ d _ _ ρ _ _ _
  letI : Module A (d → KO O) := (inferInstance : Module A (LatQ O d ρ))
  letI : SMulCommClass A O (d → KO O) := (inferInstance : SMulCommClass A O (LatQ O d ρ))
  letI : Module T' (d → KO O) := (inferInstance : Module T' (LatQ O d ρ))
  letI : IsScalarTower T' A (d → KO O) := (inferInstance : IsScalarTower T' A (LatQ O d ρ))
  exact hOne O A T' G d

end Formalism.NG
