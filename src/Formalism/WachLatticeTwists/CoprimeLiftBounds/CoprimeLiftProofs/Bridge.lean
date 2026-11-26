module

public import Formalism.WachLatticeTwists.CoprimeLiftBounds.StatBridgeChiOne
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.FirstSummandActionMem

@[expose] public section

section -- merged from Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.KeyMul
section -- merged from Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.LengthMapQuotLe
open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG Formalism.NG.IdempotentNormalFormsRhoFacts

lemma length_map_quot_le {O X Y : Type*} [CommRing O] [AddCommGroup X] [Module O X] [AddCommGroup Y]
    [Module O Y] (f : X →ₗ[O] Y) (S S' : Submodule O X) :
    Module.length O (↥(S.map f) ⧸ (S'.map f).comap (S.map f).subtype) ≤
      Module.length O (S ⧸ S'.comap S.subtype) := by
  refine Module.length_le_of_surjective
    ((S'.comap S.subtype).mapQ ((S'.map f).comap (S.map f).subtype) (f.submoduleMap S) ?_) ?_
  · intro x hx
    exact Submodule.mem_map_of_mem hx
  · intro y
    obtain ⟨y0, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨x, rfl⟩ := LinearMap.submoduleMap_surjective f S y0
    exact ⟨Submodule.Quotient.mk x, rfl⟩

theorem rowRho : StatRowRho := by
  intro O _ _ _ Dw _ M _ _ ρM ε T₁ T₂ _ _ _ _ ρ₁ π γ C₁ CP Hc Cs _ _ cls pr Fs Im X
    hTate hIm hle hX hcup
  refine ⟨(annih pr Im).map Hc.subtype, Submodule.map_mono (annih_anti pr hle),
    (length_map_quot_le Hc.subtype (annih pr Im) (annih pr Fs)).trans
      (annColength O Hc Cs pr Fs Im hle), fun b hb => ?_⟩
  refine ⟨⟨_, hX b hb⟩, ?_, rfl⟩
  refine (mem_annih pr Im _).2 fun x hx => ?_
  obtain ⟨a, ha, hC, rfl⟩ := hIm x hx
  exact hTate a b (hX b hb) ha hC (hcup b hb a ha hC)

section PsiY
variable {O A T' G : Type*} [CommRing O] [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]
  {M : Type*} [AddCommGroup M] [Module A M] [Module O M] [IsScalarTower O A M]

def psiY (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [DecidableEq ι]
    (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A)
    (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] M) : Ymod r χ E →ₗ[O] M :=
  (φ ∘ₗ (Submodule.mkQ _) ∘ₗ (LinearMap.inl A (Ymod r χ E) _)).restrictScalars O

end PsiY

theorem rowTB : StatRowTB := by
  intro O _ _ _ A T' G _ _ _ _ _ M _ _ _ _ _ r χ E e₁ δ ι _ D j Kc k0 Dw ℓ c cB deg Hc F hFH hc hH
    htor hlen
  refine ⟨Hc ⊓ divBy F ((ℓ : O) ^ c), le_inf hFH ?_, ?_, fun φ => ⟨hH φ, ?_⟩⟩
  · intro z hz
    show ((ℓ : O) ^ c) • z ∈ F
    exact F.smul_mem _ hz
  · exact hlen.trans (mul_le_mul' (mul_le_mul' le_rfl (by exact_mod_cast hc))
      (add_le_add le_rfl one_le_two))
  · show ((ℓ : O) ^ c) • (Submodule.mkQ _ (restrictCocycles1 (uRep O (M := M) r χ) Dw
        (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ)) :
        H1z (resRep (uRep O (M := M) r χ) Dw)) ∈ F
    refine htor (psiY r χ E e₁ δ D j Kc k0 φ) ?_ _ (fun g => rfl)
    intro g _ y
    show φ (Submodule.Quotient.mk (uElt r χ g • y, 0)) =
      uElt r χ g • φ (Submodule.Quotient.mk (y, 0))
    rw [← map_smul, ← Submodule.Quotient.mk_smul, Prod.smul_mk, smul_zero]

end Formalism.RepresentationBoundsCohomology.BR
end
end

open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

lemma key_mul {O A T' G : Type*} [CommRing O] [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A]
    [Group G] (r : G →* A) (χ : G →* T'ˣ) (g : G) (c : O) (b x : A) :
    (c • (((χ g : T'ˣ) : T') • (b * r g⁻¹))) * (uElt r χ g * x) = c • (b * x) := by
  have hr : r g⁻¹ * r g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  simp only [uElt, smul_mul_assoc, mul_smul_comm, smul_smul, Units.mul_inv, one_smul]
  rw [mul_assoc, ← mul_assoc (r g⁻¹), hr, one_mul]
  rw [smul_comm (((χ g)⁻¹ : T'ˣ) : T') c, smul_smul, Units.inv_mul, one_smul]

theorem rowCup : StatRowCup := by
  intro O _ _ _ A T' G _ _ _ _ _ M _ _ _ _ _ r χ E e₁ δ ι _ D j Kc k0 Dw ε T₁ T₂ _ _ _ _ ρ₁ ρ₂
    inc π γ lam C₁ CN2 CN CA CP hinc hπ hγ hc2 hc1 hCP hH2 φ a ha hCa
  let Y := Ymod r χ E
  let ρY : Representation O Dw Y := resRep (uRep O (M := Y) r χ) Dw
  let ρA : Representation O Dw A := resRep (uRep O (M := A) r χ) Dw
  let ρM : Representation O Dw M := resRep (uRep O (M := M) r χ) Dw
  let β : T₁ →ₗ[O] Y →ₗ[O] Y := LinearMap.mk₂ O (fun b y => inc b • y)
    (fun b b' y => by rw [map_add (f := _), add_smul]) (fun c b y => by rw [map_smul, smul_assoc])
    (fun b y y' => smul_add _ _ _) (fun c b y => smul_comm _ _ _)
  let β' : T₁ →ₗ[O] A →ₗ[O] A := LinearMap.mk₂ O (fun b y => inc b • y)
    (fun b b' y => by rw [map_add (f := _), add_smul]) (fun c b y => by rw [map_smul, smul_assoc])
    (fun b y y' => smul_add _ _ _) (fun c b y => smul_comm _ _ _)
  let jm : Y →ₗ[O] A := Y.subtype.restrictScalars O
  let φ' : Y →ₗ[O] M := psiY r χ E e₁ δ D j Kc k0 φ
  have hφ' : ∀ (x : A) (y : Y), φ' (x • y) = x • φ' y := fun x y => map_smul
      (φ ∘ₗ (Submodule.mkQ _) ∘ₗ (LinearMap.inl A (Ymod r χ E) _)) x y
  exact cupKillAdm O Dw T₁ Y A Y A T₂ M (KO O) ρ₁ ρY ρA (twRep ε Y) (twRep ε A) ρ₂ ρM
    (twRep ε (KO O)) β β' γ jm jm π φ' (lam ∘ₗ φ') CN2 CN CA CP
    (fun g b y => Subtype.ext (by
      show inc (ρ₁ g b) * (uElt r χ (g : G) * (y : A)) = ((ε g : Oˣ) : O) • (inc b * (y : A))
      rw [hinc, key_mul]))
    (fun g b y => by
      show inc (ρ₁ g b) * (uElt r χ (g : G) * y) = ((ε g : Oˣ) : O) • (inc b * y)
      rw [hinc, key_mul])
    (fun g y => rfl) (fun g y => rfl) hπ (fun g y => hφ' _ y)
    (fun g y => by
      show (lam ∘ₗ φ') (((ε g : Oˣ) : O) • y) = ((ε g : Oˣ) : O) • (lam ∘ₗ φ') y
      rw [map_smul])
    (fun m n => rfl)
    (fun m n => by
      show γ (π m) (φ' n) = lam (φ' (inc m • n))
      rw [hγ, hφ'])
    (fun f hf => hCP _ f hf) hH2 a (fun h => yY r χ E (h : G)) E ha
    (fun g h => Subtype.ext (ycoc_mul r χ E (g : G) (h : G)))
    (fun g => by
      show ycoc r χ E (g : G) = uElt r χ (g : G) * E - E
      unfold ycoc uElt
      rw [sub_mul, one_mul])
    (hc2 a hCa) (hc1 a hCa)

end Formalism.RepresentationBoundsCohomology.BR
end
end

section -- merged from Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.YGenCongr
open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

lemma yGen_congr {A T' G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Group G]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [DecidableEq ι]
    (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A) (g g' : G)
    (hr : r g = r g') (hχ : χ g = χ g') :
    yGen r χ E e₁ δ D j Kc k0 g = yGen r χ E e₁ δ D j Kc k0 g' := by
  have hy : ycoc r χ E g = ycoc r χ E g' := by
    show ((((χ g)⁻¹ : T'ˣ) : T') • r g - 1) * E = ((((χ g')⁻¹ : T'ˣ) : T') • r g' - 1) * E
    rw [hr, hχ]
  unfold yGen
  congr 1
  exact Prod.ext (Subtype.ext hy) rfl

theorem qPlace : StatQPlace := by
  intro O _ A T' G _ _ _ _ M _ _ _ _ r χ E e₁ δ ι _ D j Kc k0 Dw I γ ζ ζO n hγ hquad hζ hpow
    htriv hγM
  have h1 : ∀ φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] M,
      (ζO - 1) • φ (yGen r χ E e₁ δ D j Kc k0 (γ : G)) = 0 := by
    intro φ
    have h := smul_yGen_eq_zero r χ E e₁ δ D j Kc k0 (r (γ : G) - 1) (γ : G)
      (qAlg A T' G r χ E (γ : G) ζ hquad hζ)
    have h2 := congrArg φ h
    rw [map_smul, map_zero, sub_smul, one_smul, hγM] at h2
    rw [sub_smul, one_smul]
    exact h2
  have hpw : ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] M) (k : ℕ),
      φ (yGen r χ E e₁ δ D j Kc k0 ((γ : G) ^ k)) =
        k • φ (yGen r χ E e₁ δ D j Kc k0 (γ : G)) := by
    intro φ k
    induction k with
    | zero =>
      have h0 := smul_yGen_eq_zero r χ E e₁ δ D j Kc k0 1 ((γ : G) ^ 0) (by
        unfold ycoc
        simp)
      rw [one_smul] at h0
      rw [h0, map_zero, zero_smul]
    | succ k ih =>
      have hmem : γ ^ k ∈ I := I.pow_mem hγ k
      have ht := htriv (γ ^ k) hmem (φ (yGen r χ E e₁ δ D j Kc k0 (γ : G)))
      rw [Subgroup.coe_pow] at ht
      rw [pow_succ, yGen_mul, map_add (f := _), map_smul, ih, ht, succ_nsmul]
  refine ⟨h1, ?_⟩
  set ρD := resRep (uRep O (M := M) r χ) Dw with hρD
  set ρI := resRep ρD I with hρI
  let γ' : I := ⟨γ, hγ⟩
  let ZI : Submodule O (coZ1s ρI) :=
    { carrier := {z | (ζO - 1) • (z : I → M) γ' = 0 ∧ ∀ g : I, (z : I → M) g = n g • (z : I → M) γ'}
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨?_, fun g => ?_⟩
        · show (ζO - 1) • ((a : I → M) γ' + (b : I → M) γ') = 0
          rw [smul_add, ha1, hb1, add_zero]
        · show (a : I → M) g + (b : I → M) g = n g • ((a : I → M) γ' + (b : I → M) γ')
          rw [ha2 g, hb2 g, smul_add]
      zero_mem' := ⟨smul_zero _, fun g => (smul_zero _).symm⟩
      smul_mem' := by
        rintro c a ⟨ha1, ha2⟩
        refine ⟨?_, fun g => ?_⟩
        · show (ζO - 1) • (c • (a : I → M) γ') = 0
          rw [smul_comm, ha1, smul_zero]
        · show c • (a : I → M) g = n g • (c • (a : I → M) γ')
          rw [ha2 g, smul_comm] }
  let evZ : coZ1s ρI →ₗ[O] M :=
    { toFun := fun z => (z : I → M) γ'
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : (coB1 ρI).comap (coZ1s ρI).subtype ≤ LinearMap.ker evZ := by
    rintro z ⟨v, hv⟩
    have : (z : I → M) γ' = ρI γ' v - v := (congrFun hv γ').symm
    show (z : I → M) γ' = 0
    rw [this]
    exact sub_eq_zero.mpr (htriv γ hγ v)
  let ev : H1z ρI →ₗ[O] M := Submodule.liftQ _ evZ hev
  let BI : Submodule O (H1z ρI) := ZI.map (Submodule.mkQ _)
  let B : Submodule O (H1z ρD) := BI.comap (resH1 ρD I)
  let tgt := LinearMap.ker (DistribSMul.toLinearMap O M (ζO - 1))
  have hB : ∀ b : B, ev (resH1 ρD I b) ∈ tgt := by
    rintro ⟨b, z, hz, hzb⟩
    show (ζO - 1) • ev (resH1 ρD I b) = 0
    rw [← hzb]
    exact hz.1
  let f : B →ₗ[O] tgt := LinearMap.codRestrict tgt (ev ∘ₗ resH1 ρD I ∘ₗ B.subtype) hB
  have hk1 : (unrH1 ρD I).comap B.subtype ≤ LinearMap.ker f := by
    intro b hb
    have hb' : resH1 ρD I b = 0 := hb
    refine Subtype.ext ?_
    show ev (resH1 ρD I b) = 0
    rw [hb', map_zero]
  have hk2 : LinearMap.ker f ≤ (unrH1 ρD I).comap B.subtype := by
    rintro ⟨b, z, hz, hzb⟩ hb
    have hb' : ev (resH1 ρD I b) = 0 := congrArg Subtype.val hb
    show resH1 ρD I b = 0
    rw [← hzb] at hb' ⊢
    have hz0 : (z : I → M) γ' = 0 := hb'
    have : z = 0 := Subtype.ext (funext fun g => by rw [hz.2 g, hz0, smul_zero]; rfl)
    rw [this, map_zero]
  refine ⟨B, fun x hx => ?_, ?_, fun φ => ?_⟩
  · show resH1 ρD I x ∈ BI
    rw [show resH1 ρD I x = 0 from hx]
    exact BI.zero_mem
  · refine Module.length_le_of_injective (Submodule.liftQ _ f hk1) ?_
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hk2
  · refine ⟨restrictCocycles1 ρD I (restrictCocycles1 (uRep O (M := M) r χ) Dw
      (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ)), ⟨h1 φ, fun g => ?_⟩, rfl⟩
    show φ (yGen r χ E e₁ δ D j Kc k0 ((g : Dw) : G)) =
      n g • φ (yGen r χ E e₁ δ D j Kc k0 (γ : G))
    rw [← hpw φ (n g)]
    congr 1
    refine yGen_congr r χ E e₁ δ D j Kc k0 _ _ ?_ ?_
    · rw [(hpow g g.2).1, map_pow]
    · rw [(hpow g g.2).2, map_pow]

end Formalism.RepresentationBoundsCohomology.BR
end
end

section -- merged from Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.LiftBound
open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

theorem colRho : StatColRho := by
  intro O _ _ _ A T' G _ _ _ _ M _ _ _ _ L _ _ _ r χ E e₁ δ δO ι _ D j Kc k0 ℓ e' tens v₁ κ
    htens he₁ hK hE hk0 hδ φ l
  obtain ⟨-, hσ, -, h4⟩ := rel A T' G M r χ E e₁ δ ι D j Kc k0 φ l
  choose x hx using fun a => he₁ _ (hσ a)
  have key : ∀ g ∈ D l, φ (yGen r χ E e₁ δ D j Kc k0 g) +
      (uElt r χ g • φ (nuGen r χ E e₁ δ D j Kc k0 l) - φ (nuGen r χ E e₁ δ D j Kc k0 l)) =
      (δO * (ℓ : O) ^ e' l) • ∑ a, tens (κ l a g) (x a) := by
    intro g hg
    rw [h4 g hg]
    obtain ⟨b, hb⟩ := hk0 l g
    rw [hb, mul_smul, hE, smul_zero, add_zero, hδ, mul_smul, Finset.smul_sum (r := (ℓ : O) ^ e' l)]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hx a, ← htens, hK l a g hg, map_smul, LinearMap.smul_apply]
  refine ⟨⟨x, key⟩, fun F hF => ?_⟩
  set ρM := uRep O (M := M) r χ with hρM
  set Ψφ := colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ with hΨ
  have hz := hF (restrictCocycles1 ρM (D l) Ψφ + cobZ (resRep ρM (D l)) (φ (nuGen r χ E e₁ δ D j Kc k0 l)))
    (fun a => (δO * (ℓ : O) ^ e' l) • x a) (fun g => by
      have := key g g.2
      simp only [map_smul, ← Finset.smul_sum]
      exact this)
  rw [map_add (f := _), mkQ_cobZ, add_zero] at hz
  exact hz

theorem liftBound : StatLiftBound := by
  intro O _ _ _ A T' G _ _ _ _ M _ _ _ _ L _ _ _ r χ e₁ Dl j Kc ℓ e' tens v₁ κ
    htens he₁ hidem hK hinj s hs hcob a
  have hs' : ∀ a, e₁ • s a = s a := fun a => by
    obtain ⟨m, hm⟩ := hs a
    rw [← hm, DistribSMul.toLinearMap_apply, ← mul_smul, hidem]
  choose x hx using fun a => he₁ _ (hs' a)
  have h := hinj (fun a => ((ℓ : O) ^ e') • x a) (by
    convert hcob using 1
    funext g
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hx a, ← htens, hK a g g.2, map_smul, map_smul, LinearMap.smul_apply]) a
  rw [hx a, ← map_smul]
  exact h

end Formalism.RepresentationBoundsCohomology.BR
end
end

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

theorem bridgeRho : StatBridgeRho := by
  intro O _ _ _ A T' G _ _ _ _ _ M _ _ _ _ _ r χ E e₁ δ δO ι _ _ colIdx D j e' Kc k0 ℓ what₂ s
    L _ _ _ tens v₁ κ HcG Hc F Vo Io ε T₁ T₂ _ _ _ _ ρ₁ ρ₂ inc π γ lam Cs _ _ cls pr Fs Im
    hidem hE hk0 hδ hIn
  obtain ⟨htens, he₁, hK, hBK, hC3, hcont, hres, hG4, hinc, hπ, hγ, hrow, hsel⟩ := hIn
  refine ⟨fun l => liftBound O A T' G M L r χ e₁ (D (colIdx l)) (j (colIdx l)) (Kc l) ℓ
    (e' (colIdx l)) tens v₁ (κ l) htens he₁ hidem (hK l)
    (fun x hx a => by rw [hC3 l x hx a, map_zero]), ?_⟩
  refine ⟨F, HcG ⊓ ⨅ v, unrH1 _ (Io v), ?_, ?_, ?_, hsel⟩
  · intro w hw
    obtain ⟨C₁, CN2, CN, CA, CP, c1, c2, c3, hH2, hTate, hImf, hle, hF⟩ := hrow w hw
    have hcup := rowCup O A T' G M r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 (D w) (ε.comp (D w).subtype) T₁ T₂
      (resRep ρ₁ (D w)) (resRep ρ₂ (D w)) inc π γ lam C₁ CN2 CN CA CP (fun g b => hinc g b)
      (fun g m => hπ g m) hγ c1 c2 c3 hH2
    obtain ⟨B, hB1, hB2, hB3⟩ := rowRho O (D w) M (resRep (uRep O (M := M) r χ) (D w))
      (ε.comp (D w).subtype) T₁ T₂ (resRep ρ₁ (D w)) π γ C₁ CP (Hc w) (Cs w) (cls w) (pr w)
      (Fs w) (Im w)
      (Set.range (fun φ => restrictCocycles1 (uRep O (M := M) r χ) (D w)
        (colPsi (O := O) (M := M) r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l))
          Kc k0 φ)))
      hTate hImf hle (by rintro _ ⟨φ, rfl⟩; exact hres w hw (hcont φ))
      (by rintro _ ⟨φ, rfl⟩ a ha hC; exact hcup φ a ha hC)
    exact ⟨B, hF ▸ hB1, by rw [hF]; exact hB2, fun h => hB3 _ ⟨h, rfl⟩⟩
  · intro w hw h
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hw
    exact (colRho O A T' G M L r χ E e₁ δ δO ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 ℓ (fun l => e' (colIdx l)) tens v₁ κ
      htens he₁ hK hE hk0 hδ h l).2 (F (colIdx l)) (hBK l)
  · intro h
    exact ⟨hcont h, (Submodule.mem_iInf _).2 fun v =>
      (unrOutside O A T' G M r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 (Io v) (hG4 v)).2 h⟩

theorem bridgeChiC : StatBridgeChiC := by
  intro O _ _ _ A T' G _ _ _ _ _ M _ _ _ _ _ r χ E e₁ δ ι _ _ colIdx D j Kc k0 ℓ cB what₂ qs
    deg cT s HcG Hc F Vo VS Io IS I γ ζ ζO n he₁ hE hk0 hIn
  obtain ⟨hrow, hq, hcont, hres, hG4, hG5, hsel⟩ := hIn
  refine ⟨F, (HcG ⊓ (⨅ v, unrH1 _ (Io v)) ⊓ ⨅ v, unrH1 _ (IS v)), ?_, ?_, ?_, ?_, hsel⟩
  · intro w hw
    obtain ⟨h1, h2, h3, h4⟩ := hrow w hw
    exact rowTB O A T' G M r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 (D w) ℓ (cT w) cB (deg w) (Hc w) (F w) h1 h2
      (fun φ => hres w hw (hcont φ)) h3 h4
  · intro w hw
    obtain ⟨hF, a1, a2, a3, a4, a5, a6⟩ := hq w hw
    obtain ⟨-, B, b1, b2, b3⟩ := qPlace O A T' G M r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 (D w) (I w) (γ w) (ζ w)
      (ζO w) (n w) a1 a2 a3 a4 a5 a6
    exact ⟨B, hF ▸ b1, by rw [hF]; exact b2, b3⟩
  · intro w hw h
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hw
    rw [colChiC O A T' G M r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 he₁ hE hk0 h l]
    exact (F (colIdx l)).zero_mem
  · intro h
    exact ⟨⟨hcont h, (Submodule.mem_iInf _).2 fun v =>
      (unrOutside O A T' G M r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 (Io v) (hG4 v)).2 h⟩,
      (Submodule.mem_iInf _).2 fun v =>
      (unrS O A T' G M r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 (IS v) (hG5 v) h).2⟩

theorem bridgeChiOne : StatBridgeChiOne := by
  intro O _ _ _ A T' G _ _ _ _ _ M _ _ _ _ _ r χ E e₁ δ δO ι _ _ colIdx D j e' Kc k0 ℓ cB what₂ qs
    deg cT s HcG Hc F Vo VS Io IS I γ ζ ζO n u hu he₁ hE hδ hk huI huF hFc hIn
  obtain ⟨hrow, hq, hcont, hres, hG4, hG5, hsel⟩ := hIn
  refine ⟨fun l => ?_, F, (HcG ⊓ (⨅ v, unrH1 _ (Io v)) ⊓ ⨅ v, unrH1 _ (IS v)),
    ?_, ?_, ?_, ?_, hsel⟩
  · obtain ⟨g, hg, hg1⟩ := huF l
    exact ⟨g, hg, 1, isUnit_one, fun m => by rw [hk l g hg m, hg1]⟩
  · intro w hw
    obtain ⟨h1, h2, h3, h4⟩ := hrow w hw
    exact rowTB O A T' G M r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 (D w) ℓ (cT w) cB (deg w) (Hc w) (F w) h1 h2
      (fun φ => hres w hw (hcont φ)) h3 h4
  · intro w hw
    obtain ⟨hF, a1, a2, a3, a4, a5, a6⟩ := hq w hw
    obtain ⟨-, B, b1, b2, b3⟩ := qPlace O A T' G M r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 (D w) (I w) (γ w) (ζ w)
      (ζO w) (n w) a1 a2 a3 a4 a5 a6
    exact ⟨B, hF ▸ b1, by rw [hF]; exact b2, b3⟩
  · intro w hw h
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hw
    exact hFc l ((colChiOne O A T' G M r χ E e₁ δ δO ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 ℓ (fun l => e' (colIdx l)) u
      hu he₁ hE hδ hk h l).2.2 (I (colIdx l)) (huI l))
  · intro h
    exact ⟨⟨hcont h, (Submodule.mem_iInf _).2 fun v =>
      (unrOutside O A T' G M r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 (Io v) (hG4 v)).2 h⟩,
      (Submodule.mem_iInf _).2 fun v =>
      (unrS O A T' G M r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 (IS v) (hG5 v) h).2⟩

end Formalism.RepresentationBoundsCohomology.BR
