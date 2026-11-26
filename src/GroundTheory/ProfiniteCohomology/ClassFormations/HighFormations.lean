module

public import GroundTheory.TateCohomology.CupTateShift
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation

@[expose] public section

section -- merged from GroundTheory.TateCohomology.CupTate
set_option maxSynthPendingDepth 1

open CategoryTheory MonoidalCategory groupCohomology

namespace GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

def tensorInvariants {A B : Rep.{u} k G} (x : A.ρ.invariants) (y : B.ρ.invariants) :
    (A ⊗ B).ρ.invariants :=
  ⟨x.1 ⊗ₜ[k] y.1, fun g => by
    change A.ρ g x.1 ⊗ₜ[k] B.ρ g y.1 = x.1 ⊗ₜ[k] y.1
    rw [x.2 g, y.2 g]⟩


omit [Fintype G] in
theorem cupH_zero_zero_π {A B : Rep.{u} k G} (f : (Fin 0 → G) → A) (g : (Fin 0 → G) → B)
    (hf : (inhomogeneousCochains.d A 0).hom f = 0) (hg : (inhomogeneousCochains.d B 0).hom g = 0)
    (fg : (Fin 0 → G) → (A ⊗ B : Rep k G)) (hfg : (inhomogeneousCochains.d (A ⊗ B) 0).hom fg = 0)
    (h : ∀ v, fg v = f v ⊗ₜ[k] g v) :
    cupH rfl (π A 0 (cocyclesMk f hf)) (π B 0 (cocyclesMk g hg)) = π (A ⊗ B) 0 (cocyclesMk fg hfg) := by
  rw [cupH_π]
  congr 1
  apply cocycles_ext
  rw [iCocycles_cupCocycles, iCocycles_mk, iCocycles_mk, iCocycles_mk]
  funext v
  rw [cupCochain_apply, h]
  have hv : ∀ w : Fin 0 → G, w = v := fun w => Subsingleton.elim _ _
  rw [hv (fun i : Fin 0 => v ⟨i, by omega⟩), hv (fun j : Fin 0 => v ⟨0 + j, by omega⟩)]
  simp [Fin.partialProd]


set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem tateCup_zero_zero (A B : Rep.{u} k G) (x : A.ρ.invariants) (y : B.ρ.invariants) :
    tateCup 0 0 A B 0 (add_zero 0)
        (((tateCohomologyZeroIso k G).app A).inv.hom (Submodule.Quotient.mk x))
        (((tateCohomologyZeroIso k G).app B).inv.hom (Submodule.Quotient.mk y)) =
      ((tateCohomologyZeroIso k G).app (A ⊗ B)).inv.hom
        (Submodule.Quotient.mk (tensorInvariants x y)) := by
  obtain ⟨zA, hzA⟩ := exists_tateComplex_cycles_zero A x
  obtain ⟨zB, hzB⟩ := exists_tateComplex_cycles_zero B y
  obtain ⟨zAB, hzAB⟩ := exists_tateComplex_cycles_zero (A ⊗ B) (tensorInvariants x y)
  rw [tateCohomologyZeroIso_inv_mk A zA x hzA.symm, tateCohomologyZeroIso_inv_mk B zB y hzB.symm,
    tateCohomologyZeroIso_inv_mk (A ⊗ B) zAB _ hzAB.symm]
  rw [tateCup_of_nonpos 0 le_rfl]
  apply moduleIso_hom_injective (tateLeftIso A B 0)
  rw [tateLeftIso_cupL, tateCup_of_pos_of_nonpos (by norm_num) le_rfl]
  apply moduleIso_hom_injective (tateRightIso (augIdeal k G ⊗ A) B (0 + 1))
  rw [tateRightIso_cupR]
  apply moduleIso_hom_injective (tateIsoH ((augIdeal k G ⊗ A) ⊗ (augIdeal k G ⊗ B)) (0 + 1 + 1) 2
    (by norm_num))
  have hA1 := tateIsoH_tδ_homologyπ (augSES_shortExact A) 0 zA
  have hB1 := tateIsoH_tδ_homologyπ (augSES_shortExact B) 0 zB
  have hAB1 := tateIsoH_tδ_homologyπ (augSES_tensorRight_shortExact A B) 0 zAB
  have hxA : ∀ v, ((tateComplex A).iCycles 0).hom zA v = x.1 := fun v => congrFun hzA v
  have hyB : ∀ v, ((tateComplex B).iCycles 0).hom zB v = y.1 := fun v => congrFun hzB v
  have hxyAB : ∀ v, ((tateComplex (A ⊗ B)).iCycles 0).hom zAB v = x.1 ⊗ₜ[k] y.1 :=
    fun v => congrFun hzAB v
  have hcup0 := cupH_zero_zero_π _ _ (tate_d_iCycles A 0 zA) (tate_d_iCycles B 0 zB) _
    (tate_d_iCycles (A ⊗ B) 0 zAB)
    (fun v => (hxyAB v).trans (congrArg₂ (fun a b => a ⊗ₜ[k] b) (hxA v).symm (hyB v).symm))
  have e_left := δ_cupH_left (augSES_shortExact A) B (augSES_tensorRight_shortExact A B)
    (p := 0) (q := 0) rfl rfl
    (π A 0 (cocyclesMk (((tateComplex A).iCycles 0).hom zA) (tate_d_iCycles A 0 zA)))
    (π B 0 (cocyclesMk (((tateComplex B).iCycles 0).hom zB) (tate_d_iCycles B 0 zB)))
  have e_right := δ_cupH_right (augSES_shortExact B) (augIdeal k G ⊗ A)
    (augSES_tensorLeft_shortExact (augIdeal k G ⊗ A) B) (p := 0) (q := 1) rfl rfl
    (δ (augSES_shortExact A) 0 (0 + 1) rfl
      (π A 0 (cocyclesMk (((tateComplex A).iCycles 0).hom zA) (tate_d_iCycles A 0 zA))))
    (π B 0 (cocyclesMk (((tateComplex B).iCycles 0).hom zB) (tate_d_iCycles B 0 zB)))
  have e_br := congr(($(tδ_comp_tateIsoH (augSES_tensorLeft_shortExact (augIdeal k G ⊗ A) B) 1)).hom
    ((tateLeftIso A B 0).hom.hom (((tateComplex (A ⊗ B)).homologyπ 0).hom zAB)))
  have e_base := tateIsoH_tateCup (n := 1) (m := 1) (l := 2) (p := 0 + 1) (q := 0 + 1) (r := 0 + 1 + 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (augIdeal k G ⊗ A) (augIdeal k G ⊗ B) ((augShiftδ A 0).hom (((tateComplex A).homologyπ 0).hom zA))
    ((augShiftδ B 0).hom (((tateComplex B).homologyπ 0).hom zB))
  refine Eq.trans (moduleHom_smul _ _ _) ?_
  refine Eq.trans (congrArg (tsgn k (0 + 1) • ·) e_base) ?_
  refine Eq.trans (congrArg₂ (fun s t => tsgn k (0 + 1) • cupH (show 1 + 1 = 2 by rfl) s t)
    hA1 hB1) ?_
  refine Eq.trans ?_ e_br.symm
  refine Eq.trans ?_ (congrArg (δ (augSES_tensorLeft_shortExact (augIdeal k G ⊗ A) B) 1 (1 + 1)
    rfl).hom hAB1).symm
  refine Eq.trans ?_ (congrArg (fun t => δ (augSES_tensorLeft_shortExact (augIdeal k G ⊗ A) B) 1
    (1 + 1) rfl (δ (augSES_tensorRight_shortExact A B) 0 (0 + 1) rfl t)) hcup0)
  refine Eq.trans ?_ (congrArg (δ (augSES_tensorLeft_shortExact (augIdeal k G ⊗ A) B) 1
    (1 + 1) rfl).hom e_left).symm
  refine Eq.trans ?_ e_right.symm
  have hs : tsgn k (0 + 1) = (-1 : k) ^ 1 := by
    rw [tsgn_add_one]
    simp [tsgn]
  rw [hs]
  rfl


set_option maxHeartbeats 800000 in
theorem tateCup_unique_of_agrees (μ : ∀ p q : ℤ, TateCupFam k G p q)
    (hpos : ∀ (n m l : ℕ) [NeZero n] [NeZero m] [NeZero l] (hl : n + m = l) (A B : Rep.{u} k G)
      (a : tateCohomology A n) (b : tateCohomology B m),
      (tateIsoH (A ⊗ B) l l rfl).hom.hom (μ n m A B l (by omega) a b) =
        cupH hl ((tateIsoH A n n rfl).hom.hom a) ((tateIsoH B m m rfl).hom.hom b))
    (hleft : ∀ (p q : ℤ) (A B : Rep.{u} k G) (r : ℤ) (h : p + q = r) (a : tateCohomology A p)
      (b : tateCohomology B q),
      (tδ (augSES_tensorRight_shortExact A B) r (r + 1) rfl).hom (μ p q A B r h a b) =
        μ (p + 1) q (augIdeal k G ⊗ A) B (r + 1) (by omega)
          ((tδ (augSES_shortExact A) p (p + 1) rfl).hom a) b)
    (hright : ∀ (p q : ℤ) (A B : Rep.{u} k G) (r : ℤ) (h : p + q = r) (a : tateCohomology A p)
      (b : tateCohomology B q),
      (tδ (augSES_tensorLeft_shortExact A B) r (r + 1) rfl).hom (μ p q A B r h a b) =
        tsgn k p • μ p (q + 1) A (augIdeal k G ⊗ B) (r + 1) (by omega) a
          ((tδ (augSES_shortExact B) q (q + 1) rfl).hom b))
    (m : ℕ) : ∀ (p q : ℤ), (1 - p).toNat + (1 - q).toNat = m → ∀ (A B : Rep.{u} k G) (r : ℤ)
      (h : p + q = r) (a : tateCohomology A p) (b : tateCohomology B q),
      μ p q A B r h a b = tateCup p q A B r h a b := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro p q hm A B r h a b
  by_cases hp : p ≤ 0
  · rw [tateCup_of_nonpos q hp]
    apply moduleIso_hom_injective (tateLeftIso A B r)
    rw [tateLeftIso_cupL, tateLeftIso_hom]
    refine (hleft p q A B r h a b).trans ?_
    exact ih _ (by omega) (p + 1) q rfl _ _ _ _ _ _
  by_cases hq : q ≤ 0
  · rw [tateCup_of_pos_of_nonpos (by omega) hq]
    apply moduleIso_hom_injective (tateRightIso A B r)
    rw [tateRightIso_cupR, tateRightIso_hom]
    refine (hright p q A B r h a b).trans ?_
    exact congrArg (tsgn k p • ·) (ih _ (by omega) p (q + 1) rfl _ _ _ _ _ _)
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = n := ⟨p.toNat, by omega⟩
    obtain ⟨m', rfl⟩ : ∃ m' : ℕ, q = m' := ⟨q.toNat, by omega⟩
    obtain ⟨l, rfl⟩ : ∃ l : ℕ, r = l := ⟨r.toNat, by omega⟩
    have : NeZero n := ⟨by omega⟩
    have : NeZero m' := ⟨by omega⟩
    have : NeZero l := ⟨by omega⟩
    have hl : n + m' = l := by omega
    apply moduleIso_hom_injective (tateIsoH (A ⊗ B) l l rfl)
    rw [hpos n m' l hl, tateIsoH_tateCup rfl rfl rfl h hl]

theorem tateCup_δ_left {E : ShortComplex (Rep.{u} k G)} (hE : E.ShortExact) (B : Rep.{u} k G)
    (hEB : (E.map (tensorRight B)).ShortExact) (p q r : ℤ) (h : p + q = r)
    (a : tateCohomology E.X₃ p) (b : tateCohomology B q) :
    (TateCohomology.δ hEB r).hom (tateCup p q E.X₃ B r h a b) =
      tateCup (p + 1) q E.X₁ B (r + 1) (by omega) ((TateCohomology.δ hE p).hom a) b :=
  tateCup_connecting_left _ p q rfl hE B hEB r h a b

theorem tateCup_δ_right {E : ShortComplex (Rep.{u} k G)} (hE : E.ShortExact) (A : Rep.{u} k G)
    (hAE : (E.map (tensorLeft A)).ShortExact) (p q r : ℤ) (h : p + q = r)
    (a : tateCohomology A p) (b : tateCohomology E.X₃ q) :
    (TateCohomology.δ hAE r).hom (tateCup p q A E.X₃ r h a b) =
      p.negOnePow • tateCup p (q + 1) A E.X₁ (r + 1) (by omega) a ((TateCohomology.δ hE q).hom b) := by
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul k]
  exact tateCup_connecting_right _ p q rfl hE A hAE r h a b

end GroundTheory.GroupCoh
end

section -- merged from GroundTheory.TateCohomology.TateCup
section -- merged from GroundTheory.TateCohomology.TateCupUnit
set_option maxSynthPendingDepth 1

open CategoryTheory MonoidalCategory

namespace GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G]

section Unitors

variable (E : ShortComplex (Rep.{u} k G))

noncomputable def leftUnitorSCIso : E.map (tensorLeft (𝟙_ (Rep.{u} k G))) ≅ E :=
  ShortComplex.isoMk (λ_ E.X₁) (λ_ E.X₂) (λ_ E.X₃) (leftUnitor_naturality E.f).symm
    (leftUnitor_naturality E.g).symm

noncomputable def rightUnitorSCIso : E.map (tensorRight (𝟙_ (Rep.{u} k G))) ≅ E :=
  ShortComplex.isoMk (ρ_ E.X₁) (ρ_ E.X₂) (ρ_ E.X₃) (rightUnitor_naturality E.f).symm
    (rightUnitor_naturality E.g).symm

variable {E}

theorem shortExact_tensorLeft_unit (hE : E.ShortExact) :
    (E.map (tensorLeft (𝟙_ (Rep.{u} k G)))).ShortExact :=
  ShortComplex.shortExact_of_iso (leftUnitorSCIso E).symm hE

theorem shortExact_tensorRight_unit (hE : E.ShortExact) :
    (E.map (tensorRight (𝟙_ (Rep.{u} k G)))).ShortExact :=
  ShortComplex.shortExact_of_iso (rightUnitorSCIso E).symm hE

variable [Fintype G]

theorem δ_leftUnitor_apply (hE : E.ShortExact)
    (hE' : (E.map (tensorLeft (𝟙_ (Rep.{u} k G)))).ShortExact) (i : ℤ)
    (x : tateCohomology (𝟙_ (Rep.{u} k G) ⊗ E.X₃) i) :
    (TateCohomology.δ hE i).hom (((tateCohomologyFunctor i).map (λ_ E.X₃).hom).hom x) =
      ((tateCohomologyFunctor (i + 1)).map (λ_ E.X₁).hom).hom ((TateCohomology.δ hE' i).hom x) :=
  congr(($(TateCohomology.δ_naturality hE' hE (leftUnitorSCIso E).hom i)).hom x).symm

theorem δ_rightUnitor_apply (hE : E.ShortExact)
    (hE' : (E.map (tensorRight (𝟙_ (Rep.{u} k G)))).ShortExact) (i : ℤ)
    (x : tateCohomology (E.X₃ ⊗ 𝟙_ (Rep.{u} k G)) i) :
    (TateCohomology.δ hE i).hom (((tateCohomologyFunctor i).map (ρ_ E.X₃).hom).hom x) =
      ((tateCohomologyFunctor (i + 1)).map (ρ_ E.X₁).hom).hom ((TateCohomology.δ hE' i).hom x) :=
  congr(($(TateCohomology.δ_naturality hE' hE (rightUnitorSCIso E).hom i)).hom x).symm

end Unitors

variable [Fintype G]


variable (k G) in
noncomputable def tateOne : tateCohomology (𝟙_ (Rep.{u} k G)) 0 :=
  ((tateCohomologyZeroIso k G).app (𝟙_ (Rep.{u} k G))).inv.hom
    (Submodule.Quotient.mk ⟨(1 : k), fun _ => rfl⟩)


set_option maxHeartbeats 800000 in
theorem leftUnitor_tateCup_tateOne_zero (B : Rep.{u} k G) (b : tateCohomology B 0) :
    ((tateCohomologyFunctor 0).map (λ_ B).hom).hom
      (tateCup 0 0 (𝟙_ (Rep.{u} k G)) B 0 (zero_add 0) (tateOne k G) b) = b := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _
    (((tateCohomologyZeroIso k G).app B).hom.hom b)
  have hb : b = ((tateCohomologyZeroIso k G).app B).inv.hom (Submodule.Quotient.mk y) := by
    rw [hy]
    exact (((tateCohomologyZeroIso k G).app B).hom_inv_id_apply b).symm
  subst hb
  have h0 := tateCup_zero_zero (𝟙_ (Rep.{u} k G)) B ⟨(1 : k), fun _ => rfl⟩ y
  refine (congrArg (((tateCohomologyFunctor 0).map (λ_ B).hom).hom) h0).trans ?_
  have hn := congr(($((tateCohomologyZeroIso k G).inv.naturality (λ_ B).hom)).hom
    (Submodule.Quotient.mk (tensorInvariants (⟨(1 : k), fun _ => rfl⟩ :
      (𝟙_ (Rep.{u} k G)).ρ.invariants) y)))
  refine hn.symm.trans ?_
  change ((tateCohomologyZeroIso k G).inv.app B).hom (Submodule.Quotient.mk _) = _
  congr 2
  apply Subtype.ext
  change (λ_ B).hom.hom ((1 : k) ⊗ₜ[k] (y : B)) = y
  rw [leftUnitor_hom_tmul, one_smul]

theorem leftUnitor_tateCup_tateOne_down (q q' : ℤ) (hq : q + 1 = q')
    (h : ∀ (B : Rep.{u} k G) (b : tateCohomology B q'),
      ((tateCohomologyFunctor q').map (λ_ B).hom).hom
        (tateCup 0 q' (𝟙_ (Rep.{u} k G)) B q' (zero_add _) (tateOne k G) b) = b)
    (B : Rep.{u} k G) (b : tateCohomology B q) :
    ((tateCohomologyFunctor q).map (λ_ B).hom).hom
        (tateCup 0 q (𝟙_ (Rep.{u} k G)) B q (zero_add _) (tateOne k G) b) = b := by
  subst hq
  have hE := augSES_shortExact B
  have hAE := augSES_tensorLeft_shortExact (𝟙_ (Rep.{u} k G)) B
  have hiso : IsIso (TateCohomology.δ hE q) :=
    isIso_δ_of_tateAcyclic hE (tateAcyclic_leftRegular_tensor B) q
  apply moduleIso_hom_injective (@asIso _ _ _ _ _ hiso)
  refine (δ_leftUnitor_apply hE hAE q _).trans ?_
  have hr := tateCup_δ_right hE (𝟙_ (Rep.{u} k G)) hAE 0 q q (zero_add q) (tateOne k G) b
  rw [Int.negOnePow_zero, one_smul] at hr
  refine (congrArg (((tateCohomologyFunctor (q + 1)).map (λ_ _).hom).hom) hr).trans ?_
  exact h _ _

theorem leftUnitor_tateCup_tateOne_up (q q' : ℤ) (hq : q + 1 = q')
    (h : ∀ (B : Rep.{u} k G) (b : tateCohomology B q),
      ((tateCohomologyFunctor q).map (λ_ B).hom).hom
        (tateCup 0 q (𝟙_ (Rep.{u} k G)) B q (zero_add _) (tateOne k G) b) = b)
    (B : Rep.{u} k G) (b : tateCohomology B q') :
    ((tateCohomologyFunctor q').map (λ_ B).hom).hom
        (tateCup 0 q' (𝟙_ (Rep.{u} k G)) B q' (zero_add _) (tateOne k G) b) = b := by
  subst hq
  have hE := coindSES_shortExact B
  have hAE := shortExact_tensorLeft_unit hE
  have hiso : IsIso (TateCohomology.δ hE q) := isIso_δ_coindSES B q
  obtain ⟨c, rfl⟩ : ∃ c, (TateCohomology.δ hE q).hom c = b :=
    ⟨(@asIso _ _ _ _ _ hiso).inv.hom b, (@asIso _ _ _ _ _ hiso).inv_hom_id_apply b⟩
  have hr := tateCup_δ_right hE (𝟙_ (Rep.{u} k G)) hAE 0 q q (zero_add q) (tateOne k G) c
  rw [Int.negOnePow_zero, one_smul] at hr
  refine (congrArg (((tateCohomologyFunctor (q + 1)).map (λ_ _).hom).hom) hr.symm).trans ?_
  refine (δ_leftUnitor_apply hE hAE q _).symm.trans ?_
  exact congrArg (TateCohomology.δ hE q).hom (h _ _)

theorem leftUnitor_tateCup_tateOne (q : ℤ) (B : Rep.{u} k G) (b : tateCohomology B q) :
    ((tateCohomologyFunctor q).map (λ_ B).hom).hom
        (tateCup 0 q (𝟙_ (Rep.{u} k G)) B q (zero_add _) (tateOne k G) b) = b := by
  induction q using Int.induction_on generalizing B with
  | zero => exact leftUnitor_tateCup_tateOne_zero B b
  | succ i ih => exact leftUnitor_tateCup_tateOne_up (i : ℤ) _ rfl ih B b
  | pred i ih => exact leftUnitor_tateCup_tateOne_down _ (-(i : ℤ)) (by ring) ih B b

end GroundTheory.GroupCoh
end

set_option maxSynthPendingDepth 1

open CategoryTheory MonoidalCategory Limits Rep

namespace GroundTheory.GroupCoh

section Transport

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem tateCup_eqToHom_left {A B : Rep.{u} k G} {p p' q r r' : ℤ} (hp : p = p') (hr : r = r')
    (h : p + q = r) (h' : p' + q = r') (a : tateCohomology A p) (b : tateCohomology B q) :
    (eqToHom (congrArg (tateCohomology (A ⊗ B)) hr)).hom (tateCup p q A B r h a b) =
      tateCup p' q A B r' h' ((eqToHom (congrArg (tateCohomology A) hp)).hom a) b := by
  subst hp hr
  simp

theorem eqToHom_tateMap_apply {X Y : Rep.{u} k G} (f : X ⟶ Y) {i j : ℤ} (hij : i = j)
    (x : tateCohomology X i) :
    (eqToHom (congrArg (tateCohomology Y) hij)).hom (((tateCohomologyFunctor i).map f).hom x) =
      ((tateCohomologyFunctor j).map f).hom ((eqToHom (congrArg (tateCohomology X) hij)).hom x) := by
  subst hij
  simp

theorem tateIsoH_eqToHom_apply (A : Rep.{u} k G) {p₀ p p' : ℤ} (n : ℕ) [NeZero n] (e : p₀ = p)
    (e' : p₀ = p') (hp : p = n) (hp' : p' = n) (w : tateCohomology A p₀) :
    (tateIsoH A p n hp).hom.hom ((eqToHom (congrArg (tateCohomology A) e)).hom w) =
      (tateIsoH A p' n hp').hom.hom ((eqToHom (congrArg (tateCohomology A) e')).hom w) := by
  subst e e'
  rfl

end Transport

section Tate

variable {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) (u : groupCohomology M 2)
  (S : Subgroup G) [Fintype S]

noncomputable def tateResClass : tateCohomology (res S.subtype M) 2 :=
  (tateIsoH (res S.subtype M) 2 2 (by norm_num)).inv.hom
    (groupCohomology.map S.subtype (𝟙 (res S.subtype M)) 2 u)

variable (h1 : ∀ S : Subgroup G, IsZero (groupCohomology (res S.subtype M) 1))
  (h2 : ∀ S : Subgroup G,
    addOrderOf (groupCohomology.map S.subtype (𝟙 (res S.subtype M)) 2 u) = Nat.card S)
  (h3 : ∀ (S : Subgroup G) (y : groupCohomology (res S.subtype M) 2),
    ∃ m : ℤ, y = m • groupCohomology.map S.subtype (𝟙 (res S.subtype M)) 2 u)

include h1 h2 h3

theorem tateTheorem_δ_δ_tateOne :
    (eqToHom (congrArg (tateCohomology (res S.subtype M)) (show (0 : ℤ) + 1 + 1 = 2 by norm_num))).hom
      ((TateCohomology.δ ((shortExact_res S.subtype).2 (splittingSES_shortExact M u)) (0 + 1)).hom
        ((TateCohomology.δ (augTrivSES_res_shortExact ℤ S.subtype) 0).hom (tateOne ℤ S))) =
      tateResClass M u S := by
  apply moduleIso_hom_injective (tateIsoH (res S.subtype M) 2 2 (by norm_num))
  rw [tateResClass, Iso.inv_hom_id_apply]
  refine (tateIsoH_eqToHom_apply (res S.subtype M) 2 (show (0 : ℤ) + 1 + 1 = 2 by norm_num)
    (show (0 : ℤ) + 1 + 1 = 0 + 2 by norm_num) (by norm_num) (by norm_num) _).trans ?_
  exact tateTheoremIso_zero_apply M u h1 h2 h3 S


set_option maxHeartbeats 1600000 in
theorem tateTheoremIso_hom_apply (n : ℤ) (x : tateCohomology (Rep.trivial ℤ S ℤ) n) :
    (tateTheoremIso M u h1 h2 h3 S n).hom.hom x =
      ((tateCohomologyFunctor (n + 2)).map (ρ_ (res S.subtype M)).hom).hom
        (tateCup 2 n (res S.subtype M) (Rep.trivial ℤ S ℤ) (n + 2) (add_comm 2 n)
          (tateResClass M u S) x) := by
  have hE1 := augTrivSES_res_shortExact ℤ S.subtype
  have hE2 := (shortExact_res S.subtype).2 (splittingSES_shortExact M u)
  have hE1R := shortExact_tensorRight_unit hE1
  have hE2R := shortExact_tensorRight_unit hE2
  have hx : ((tateCohomologyFunctor n).map (ρ_ (𝟙_ (Rep ℤ S))).hom).hom
      (tateCup 0 n (𝟙_ (Rep ℤ S)) (𝟙_ (Rep ℤ S)) n (zero_add n) (tateOne ℤ S) x) = x := by
    rw [← unitors_equal]
    exact leftUnitor_tateCup_tateOne n _ x
  have s1 : (TateCohomology.δ hE1 n).hom x =
      ((tateCohomologyFunctor (n + 1)).map (ρ_ (res S.subtype (augIdeal ℤ G))).hom).hom
        (tateCup (0 + 1) n (res S.subtype (augIdeal ℤ G)) (𝟙_ (Rep ℤ S)) (n + 1) (by omega)
          ((TateCohomology.δ hE1 0).hom (tateOne ℤ S)) x) :=
    (congrArg (TateCohomology.δ hE1 n).hom hx.symm).trans ((δ_rightUnitor_apply hE1 hE1R n _).trans
      (congrArg _ (tateCup_δ_left hE1 (𝟙_ (Rep ℤ S)) hE1R 0 n n (zero_add n) (tateOne ℤ S) x)))
  have s2 : (TateCohomology.δ hE2 (n + 1)).hom
      (((tateCohomologyFunctor (n + 1)).map (ρ_ (res S.subtype (augIdeal ℤ G))).hom).hom
        (tateCup (0 + 1) n (res S.subtype (augIdeal ℤ G)) (𝟙_ (Rep ℤ S)) (n + 1) (by omega)
          ((TateCohomology.δ hE1 0).hom (tateOne ℤ S)) x)) =
      ((tateCohomologyFunctor (n + 1 + 1)).map (ρ_ (res S.subtype M)).hom).hom
        (tateCup (0 + 1 + 1) n (res S.subtype M) (𝟙_ (Rep ℤ S)) (n + 1 + 1) (by omega)
          ((TateCohomology.δ hE2 (0 + 1)).hom ((TateCohomology.δ hE1 0).hom (tateOne ℤ S))) x) :=
    (δ_rightUnitor_apply hE2 hE2R (n + 1) _).trans
      (congrArg _ (tateCup_δ_left hE2 (𝟙_ (Rep ℤ S)) hE2R (0 + 1) n (n + 1) (by omega) _ x))
  have hT : (tateTheoremIso M u h1 h2 h3 S n).hom.hom x =
      (eqToHom (congrArg (tateCohomology (res S.subtype M)) (show n + 1 + 1 = n + 2 by ring))).hom
        ((TateCohomology.δ hE2 (n + 1)).hom ((TateCohomology.δ hE1 n).hom x)) := rfl
  rw [hT, s1, s2]
  refine (eqToHom_tateMap_apply (ρ_ (res S.subtype M)).hom (show n + 1 + 1 = n + 2 by ring) _).trans ?_
  refine congrArg _ ((tateCup_eqToHom_left (show (0 : ℤ) + 1 + 1 = 2 by norm_num)
    (show n + 1 + 1 = n + 2 by ring) _ (add_comm 2 n) _ x).trans ?_)
  exact congrArg (fun t => tateCup 2 n (res S.subtype M) (Rep.trivial ℤ S ℤ) (n + 2) (add_comm 2 n) t x)
    (tateTheorem_δ_δ_tateOne M u S h1 h2 h3)

end Tate

end GroundTheory.GroupCoh
end

section -- merged from GroundTheory.TateCohomology.CupTateNatural
set_option maxSynthPendingDepth 1

open CategoryTheory MonoidalCategory groupCohomology

namespace GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

section Naturality





theorem tateIsoH_map_apply {X Y : Rep.{u} k G} (φ : X ⟶ Y) (n : ℕ) [NeZero n]
    (x : tateCohomology X n) :
    (tateIsoH Y n n rfl).hom.hom (((tateCohomologyFunctor n).map φ).hom x) =
      groupCohomology.map (MonoidHom.id G) φ n ((tateIsoH X n n rfl).hom.hom x) :=
  congr(($((TateCohomology.isoGroupCohomology n).hom.naturality φ)).hom x)

end Naturality

end GroundTheory.GroupCoh
end

section -- merged from GroundTheory.TateCohomology.CupFunctorial
set_option maxSynthPendingDepth 1

noncomputable section

universe u

open CategoryTheory MonoidalCategory TensorProduct groupCohomology Rep

namespace GroundTheory.GroupCoh

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

theorem partialProd_comp {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) {m : ℕ}
    (x : Fin m → M) (i : Fin (m + 1)) :
    Fin.partialProd (f ∘ x) i = f (Fin.partialProd x i) := by
  simp [Fin.partialProd, ← List.map_ofFn, ← List.map_take, map_list_prod]

variable (f : G →* H) {A₁ A₂ : Rep k H} {B₁ B₂ : Rep k G} {p q n : ℕ}

def resTensorHom (φ₁ : res f A₁ ⟶ B₁) (φ₂ : res f A₂ ⟶ B₂) : res f (A₁ ⊗ A₂) ⟶ B₁ ⊗ B₂ :=
  ConcreteCategory.ofHom (C := Rep k G)
    { toLinearMap := TensorProduct.map φ₁.hom.toLinearMap φ₂.hom.toLinearMap
      isIntertwining' := fun g => TensorProduct.ext' fun a b => by
        change φ₁.hom (A₁.ρ (f g) a) ⊗ₜ[k] φ₂.hom (A₂.ρ (f g) b) =
          B₁.ρ g (φ₁.hom a) ⊗ₜ[k] B₂.ρ g (φ₂.hom b)
        rw [← Rep.hom_comm_apply φ₁, ← Rep.hom_comm_apply φ₂]
        rfl }

theorem resTensorHom_tmul (φ₁ : res f A₁ ⟶ B₁) (φ₂ : res f A₂ ⟶ B₂) (a : A₁) (b : A₂) :
    (resTensorHom f φ₁ φ₂).hom (a ⊗ₜ[k] b : (A₁ ⊗ A₂ : Rep k H)) = φ₁.hom a ⊗ₜ[k] φ₂.hom b :=
  rfl

theorem resTensorHom_cupCochain (φ₁ : res f A₁ ⟶ B₁) (φ₂ : res f A₂ ⟶ B₂) (h : p + q = n)
    (x : (Fin p → H) → A₁) (y : (Fin q → H) → A₂) (g : Fin n → G) :
    (resTensorHom f φ₁ φ₂).hom (cupCochain h x y (f ∘ g)) =
      cupCochain h (fun v => φ₁.hom (x (f ∘ v))) (fun v => φ₂.hom (y (f ∘ v))) g := by
  rw [cupCochain_apply, resTensorHom_tmul, cupCochain_apply, partialProd_comp]
  exact congrArg _ (Rep.hom_comm_apply φ₂ _ _)

theorem map_π_apply' {A : Rep k H} {B : Rep k G} (φ : res f A ⟶ B) (z : cocycles A n) :
    map f φ n (π A n z) = π B n (cocyclesMap f φ n z) := by
  change (π A n ≫ map f φ n).hom z = (cocyclesMap f φ n ≫ π B n).hom z
  rw [π_map]

theorem iCocycles_cocyclesMap' {A : Rep k H} {B : Rep k G} (φ : res f A ⟶ B)
    (z : cocycles A n) :
    iCocycles B n (cocyclesMap f φ n z) = fun g => φ.hom (iCocycles A n z (f ∘ g)) := by
  change (cocyclesMap f φ n ≫ iCocycles B n).hom z = _
  rw [HomologicalComplex.cyclesMap_i]
  rfl

theorem map_resTensorHom_cupH (φ₁ : res f A₁ ⟶ B₁) (φ₂ : res f A₂ ⟶ B₂) (h : p + q = n)
    (a : groupCohomology A₁ p) (b : groupCohomology A₂ q) :
    map f (resTensorHom f φ₁ φ₂) n (cupH h a b) = cupH h (map f φ₁ p a) (map f φ₂ q b) := by
  refine groupCohomology_induction_on a fun z => ?_
  refine groupCohomology_induction_on b fun w => ?_
  have key : cocyclesMap (A := A₁ ⊗ A₂) f (resTensorHom f φ₁ φ₂) n (cupCocycles h z w) =
      cupCocycles h (cocyclesMap f φ₁ p z) (cocyclesMap f φ₂ q w) := by
    refine cocycles_ext ?_
    rw [iCocycles_cocyclesMap', iCocycles_cupCocycles, iCocycles_cupCocycles,
      iCocycles_cocyclesMap', iCocycles_cocyclesMap']
    funext g
    exact resTensorHom_cupCochain f φ₁ φ₂ h _ _ g
  rw [cupH_π, map_π_apply', map_π_apply', map_π_apply', cupH_π, key]

end GroundTheory.GroupCoh
end
end

section -- merged from GroundTheory.ProfiniteCohomology.ClassFormations.SubsingletonCohomologyTopOfThreeLeInt
section -- merged from GroundTheory.ProfiniteCohomology.ClassFormations.HighFinite
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.GroupCoh

open CategoryTheory MonoidalCategory groupCohomology Rep

section Top

variable {k : Type} [CommRing k] {Γ : Type} [Group Γ]

abbrev topHom (Γ : Type) [Group Γ] : Γ →* (⊤ : Subgroup Γ) :=
  (Subgroup.topEquiv (G := Γ)).symm.toMonoidHom

def topBackHom (A : Rep k Γ) : res (topHom Γ) (res (⊤ : Subgroup Γ).subtype A) ⟶ A :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

def topBackTrivialHom : res (topHom Γ) (Rep.trivial k (⊤ : Subgroup Γ) k) ⟶ Rep.trivial k Γ k :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

theorem map_topBackHom_map_subtype (A : Rep k Γ) (n : ℕ) (x : groupCohomology A n) :
    map (topHom Γ) (topBackHom A) n (map (⊤ : Subgroup Γ).subtype (𝟙 _) n x) = x := by
  have h := map_comp (⊤ : Subgroup Γ).subtype (topHom Γ) (𝟙 (res (⊤ : Subgroup Γ).subtype A))
    (topBackHom A) n
  have h' : map ((⊤ : Subgroup Γ).subtype.comp (topHom Γ))
      ((resFunctor (topHom Γ)).map (𝟙 (res (⊤ : Subgroup Γ).subtype A)) ≫ topBackHom A) n =
      map (MonoidHom.id Γ) (𝟙 A) n :=
    map_congr (MonoidHom.ext fun _ => rfl) rfl n
  rw [h', map_id] at h
  exact (congrArg (fun f => f.hom x) h).symm

theorem topBack_rightUnitor (A : Rep k Γ) :
    ((resFunctor (topHom Γ)).map (ρ_ (res (⊤ : Subgroup Γ).subtype A)).hom ≫
        topBackHom A).hom.toLinearMap =
      ((resFunctor (MonoidHom.id Γ)).map (resTensorHom (topHom Γ) (topBackHom A) topBackTrivialHom) ≫
        (ρ_ A).hom).hom.toLinearMap :=
  TensorProduct.ext' fun _ _ => rfl

end Top

section Tate

variable {Γ : Type} [Group Γ] [Fintype Γ] (M : Rep ℤ Γ) (u : groupCohomology M 2)
  (h1 : ∀ S : Subgroup Γ, Limits.IsZero (groupCohomology (res S.subtype M) 1))
  (h2 : ∀ S : Subgroup Γ,
    addOrderOf (groupCohomology.map S.subtype (𝟙 (res S.subtype M)) 2 u) = Nat.card S)
  (h3 : ∀ (S : Subgroup Γ) (y : groupCohomology (res S.subtype M) 2),
    ∃ m : ℤ, y = m • groupCohomology.map S.subtype (𝟙 (res S.subtype M)) 2 u)


omit [Fintype Γ] in
theorem tateIsoH_map_apply' {X Y : Rep ℤ Γ} [Fintype Γ] (φ : X ⟶ Y) {p : ℤ} (n : ℕ) [NeZero n]
    (hp : p = n) (x : tateCohomology X p) :
    (tateIsoH Y p n hp).hom.hom (((tateCohomologyFunctor p).map φ).hom x) =
      groupCohomology.map (MonoidHom.id Γ) φ n ((tateIsoH X p n hp).hom.hom x) := by
  subst hp
  exact tateIsoH_map_apply φ n x

include h1 h2 h3

theorem exists_cupH_top (n : ℕ) [NeZero n] [Fintype (⊤ : Subgroup Γ)]
    (x : groupCohomology (res (⊤ : Subgroup Γ).subtype M) (n + 2)) :
    ∃ y : groupCohomology (Rep.trivial ℤ (⊤ : Subgroup Γ) ℤ) n, (∃ m : ℕ, m ≠ 0 ∧ m • y = 0) ∧
      x = map (MonoidHom.id _) (ρ_ (res (⊤ : Subgroup Γ).subtype M)).hom (n + 2)
        (cupH (add_comm 2 n) (map (⊤ : Subgroup Γ).subtype (𝟙 (res (⊤ : Subgroup Γ).subtype M)) 2 u)
          y) := by
  have hp : ((n : ℤ) + 2) = ((n + 2 : ℕ) : ℤ) := by push_cast; ring
  let T := tateTheoremIso M u h1 h2 h3 ⊤ (n : ℤ)
  let s : tateCohomology (res (⊤ : Subgroup Γ).subtype M) ((n : ℤ) + 2) :=
    (tateIsoH (res (⊤ : Subgroup Γ).subtype M) _ (n + 2) hp).inv.hom x
  let y0 := T.inv.hom s
  refine ⟨(tateIsoH (Rep.trivial ℤ (⊤ : Subgroup Γ) ℤ) n n rfl).hom.hom y0,
    ⟨Fintype.card (⊤ : Subgroup Γ), Fintype.card_ne_zero, ?_⟩, ?_⟩
  · rw [← map_nsmul, card_smul_tateCohomology, map_zero]
  · have hs : T.hom.hom y0 = s := T.inv_hom_id_apply s
    have hx : x = (tateIsoH (res (⊤ : Subgroup Γ).subtype M) _ (n + 2) hp).hom.hom s :=
      ((tateIsoH (res (⊤ : Subgroup Γ).subtype M) _ (n + 2) hp).inv_hom_id_apply x).symm
    rw [hx, ← hs, tateTheoremIso_hom_apply M u ⊤ h1 h2 h3 (n : ℤ) y0, tateIsoH_map_apply' _ _ hp]
    erw [tateIsoH_tateCup (show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num) rfl hp (add_comm 2 (n : ℤ))
        (add_comm 2 n)]
    exact congrArg (fun t => (groupCohomology.map (MonoidHom.id _)
      (ρ_ (res (⊤ : Subgroup Γ).subtype M)).hom (n + 2)) (cupH (add_comm 2 n) t
        ((tateIsoH (Rep.trivial ℤ (⊤ : Subgroup Γ) ℤ) n n rfl).hom.hom y0)))
      ((tateIsoH (res (⊤ : Subgroup Γ).subtype M) 2 2 (by norm_num)).inv_hom_id_apply
        (map (⊤ : Subgroup Γ).subtype (𝟙 (res (⊤ : Subgroup Γ).subtype M)) 2 u))

theorem exists_cupH_of_tate (n : ℕ) [NeZero n] (x : groupCohomology M (n + 2)) :
    ∃ y : groupCohomology (Rep.trivial ℤ Γ ℤ) n, (∃ m : ℕ, m ≠ 0 ∧ m • y = 0) ∧
      x = map (MonoidHom.id Γ) (ρ_ M).hom (n + 2) (cupH (add_comm 2 n) u y) := by
  classical
  obtain ⟨y, ⟨m, hm, hmy⟩, hx⟩ := exists_cupH_top M u h1 h2 h3 n
    (map (⊤ : Subgroup Γ).subtype (𝟙 _) (n + 2) x)
  refine ⟨map (topHom Γ) topBackTrivialHom n y, ⟨m, hm, by rw [← map_nsmul, hmy, map_zero]⟩, ?_⟩
  have hback := map_topBackHom_map_subtype M (n + 2) x
  rw [hx] at hback
  rw [← hback]
  have e1 := map_comp (MonoidHom.id (⊤ : Subgroup Γ)) (topHom Γ)
    (ρ_ (res (⊤ : Subgroup Γ).subtype M)).hom (topBackHom M) (n + 2)
  have e2 := map_comp (topHom Γ) (MonoidHom.id Γ)
    (resTensorHom (topHom Γ) (topBackHom M) topBackTrivialHom) (ρ_ M).hom (n + 2)
  have e3 : map ((MonoidHom.id (⊤ : Subgroup Γ)).comp (topHom Γ))
      ((resFunctor (topHom Γ)).map (ρ_ (res (⊤ : Subgroup Γ).subtype M)).hom ≫ topBackHom M) (n + 2) =
      map ((topHom Γ).comp (MonoidHom.id Γ))
      ((resFunctor (MonoidHom.id Γ)).map (resTensorHom (topHom Γ) (topBackHom M) topBackTrivialHom) ≫
        (ρ_ M).hom) (n + 2) := by
    exact map_congr (MonoidHom.ext fun _ => rfl) (topBack_rightUnitor M) (n + 2)
  have e4 := congrArg (fun f => f.hom (cupH (add_comm 2 n)
    (map (⊤ : Subgroup Γ).subtype (𝟙 (res (⊤ : Subgroup Γ).subtype M)) 2 u) y)) (e1.symm.trans (e3.trans e2))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e4
  rw [e4, map_resTensorHom_cupH, map_topBackHom_map_subtype]

end Tate

end GroundTheory.GroupCoh
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory Limits MonoidalCategory groupCohomology

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]


omit [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem subsingleton_cohomology_of_top {k : Type} [CommRing k] (A : Rep.{0} k G) [IsDiscreteRep A]
    (r : ℕ) (h : Subsingleton (cohomology (Rep.res (⊤ : Subgroup G).subtype A) r)) :
    Subsingleton (cohomology A r) := by
  let φ := cohomologyMapAlong (Subgroup.topEquiv (G := G)).toMonoidHom continuous_subtype_val
    (B := Rep.res (⊤ : Subgroup G).subtype A) (Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩) r
  have hi : IsIso φ := isIso_cohomologyMapAlong_of_mulEquiv (Subgroup.topEquiv (G := G))
    continuous_subtype_val (continuous_id.subtype_mk _) (B := Rep.res (⊤ : Subgroup G).subtype A)
    (Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩) Function.bijective_id r
  exact ((ModuleCat.mono_iff_injective φ).1 inferInstance).subsingleton

section Int

variable {C : Rep.{0} ℤ G} [IsDiscreteRep C] (F : ClassFormation C)


include F in
theorem ClassFormation.exists_cupH_quot (U : OpenSubgroup G) (N : Subgroup (U : Subgroup G))
    [N.Normal] (hN : IsOpen (N : Set (U : Subgroup G))) (n : ℕ) [NeZero n]
    (w : groupCohomology ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants N) (n + 2)) :
    ∃ (a : groupCohomology ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants N) 2)
      (y : groupCohomology (Rep.trivial ℤ ((U : Subgroup G) ⧸ N) ℤ) n),
      (∃ m : ℕ, m ≠ 0 ∧ m • y = 0) ∧
        w = map (MonoidHom.id _) (ρ_ _).hom (n + 2) (GroundTheory.GroupCoh.cupH (add_comm 2 n) a y) := by
  obtain ⟨V, hVU, rfl⟩ := exists_openSubgroup_subgroupOf_eq U N hN
  have : ((V : Subgroup G).subgroupOf U).FiniteIndex :=
    finiteIndex_openSubgroup (⟨_, hN⟩ : OpenSubgroup (U : Subgroup G))
  have : Finite ((U : Subgroup G) ⧸ (V : Subgroup G).subgroupOf U) :=
    Subgroup.finite_quotient_of_finiteIndex
  let : Fintype ((U : Subgroup G) ⧸ (V : Subgroup G).subgroupOf U) := Fintype.ofFinite _
  exact ⟨_, GroundTheory.GroupCoh.exists_cupH_of_tate _ (F.groupFundamentalClass U V)
    (fun S => (F.tate_hypotheses (U := U) (V := V) hVU S).1) (fun S => (F.tate_hypotheses (U := U) (V := V) hVU S).2.1)
    (fun S => (F.tate_hypotheses (U := U) (V := V) hVU S).2.2) n w⟩

def trivialToInvariantsHom {k H : Type} [CommRing k] [Group H] (N : Subgroup H) [N.Normal] :
    Rep.trivial k (H ⧸ N) k ⟶ (Rep.trivial k H k).quotientToInvariants N :=
  Rep.ofHom ⟨⟨⟨fun a => ⟨a, fun _ => rfl⟩, fun _ _ => rfl⟩, fun _ _ => rfl⟩, fun g => by
    induction g using QuotientGroup.induction_on
    rfl⟩

theorem rightUnitor_quotientToInvariants {k H : Type} [CommRing k] [Group H] (A : Rep.{0} k H)
    (N : Subgroup H) [N.Normal] :
    ((𝟙 (A.quotientToInvariants N) ⊗ₘ trivialToInvariantsHom (k := k) N) ≫
        invariantsTensorHom A (Rep.trivial k H k) N ≫
        (Rep.quotientToInvariantsFunctor k N).map (ρ_ A).hom).hom.toLinearMap =
      (ρ_ (A.quotientToInvariants N)).hom.hom.toLinearMap :=
  TensorProduct.ext' fun _ _ => Subtype.ext rfl


include F in
theorem ClassFormation.subsingleton_cohomology_of_three_le_int (U : OpenSubgroup G) {r : ℕ}
    (hr : 3 ≤ r) : Subsingleton (cohomology (Rep.res (U : Subgroup G).subtype C) r) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 2 := ⟨r - 2, by omega⟩
  have : NeZero n := ⟨by omega⟩
  suffices h : ∀ z : cohomology (Rep.res (U : Subgroup G).subtype C) (n + 2), z = 0 from
    ⟨fun a b => by rw [h a, h b]⟩
  intro z
  set A := Rep.res (U : Subgroup G).subtype C
  set B := Rep.trivial ℤ (U : Subgroup G) ℤ
  obtain ⟨W, w, rfl⟩ := exists_inflation_eq A (n + 2) z
  obtain ⟨a, y, ⟨m, hm, hmy⟩, hw⟩ :=
    F.exists_cupH_quot U (W : Subgroup (U : Subgroup G)) W.isOpen n w

  change inflation A W (n + 2) w = 0
  set t := inflation B W n
    (map (MonoidHom.id _) (trivialToInvariantsHom (W : Subgroup (U : Subgroup G))) n y) with ht
  have hmt : m • t = 0 := by
    rw [ht, ← map_nsmul, ← map_nsmul, hmy, map_zero, map_zero]

  have hz : inflation A W (n + 2) w =
      cohomologyMap (ρ_ A).hom (n + 2) (cup (add_comm 2 n) (inflation A W 2 a) t) := by
    have key := map_congr (f := MonoidHom.id ((U : Subgroup G) ⧸ (W : Subgroup (U : Subgroup G))))
      (g := MonoidHom.id _)
      (φ := (𝟙 (A.quotientToInvariants (W : Subgroup (U : Subgroup G))) ⊗ₘ
          trivialToInvariantsHom (k := ℤ) (W : Subgroup (U : Subgroup G))) ≫
        invariantsTensorHom A B (W : Subgroup (U : Subgroup G)) ≫
        (Rep.quotientToInvariantsFunctor ℤ (W : Subgroup (U : Subgroup G))).map (ρ_ A).hom)
      (ψ := (ρ_ (A.quotientToInvariants (W : Subgroup (U : Subgroup G)))).hom) rfl
      (rightUnitor_quotientToInvariants A (W : Subgroup (U : Subgroup G))) (n + 2)
    have hc := GroundTheory.GroupCoh.map_cupH (𝟙 (A.quotientToInvariants (W : Subgroup (U : Subgroup G))))
      (trivialToInvariantsHom (k := ℤ) (W : Subgroup (U : Subgroup G))) (add_comm 2 n) a y
    simp only [map_id, ModuleCat.hom_id, LinearMap.id_apply] at hc
    rw [ht, cup_inflation W A B (add_comm 2 n) a, cohomologyMap_inflation W (A := A ⊗ B) (A' := A) (ρ_ A).hom, hw, ← hc]
    congr 1
    refine (congrArg (fun f => f.hom (GroundTheory.GroupCoh.cupH (add_comm 2 n) a y)) key).symm.trans ?_
    have e1 := map_id_comp
      (𝟙 (A.quotientToInvariants (W : Subgroup (U : Subgroup G))) ⊗ₘ
          trivialToInvariantsHom (k := ℤ) (W : Subgroup (U : Subgroup G)))
      (invariantsTensorHom A B (W : Subgroup (U : Subgroup G)) ≫
        (Rep.quotientToInvariantsFunctor ℤ (W : Subgroup (U : Subgroup G))).map (ρ_ A).hom) (n + 2)
    have e2 := map_id_comp (invariantsTensorHom A B (W : Subgroup (U : Subgroup G)))
        ((Rep.quotientToInvariantsFunctor ℤ (W : Subgroup (U : Subgroup G))).map (ρ_ A).hom) (n + 2)
    refine (congrArg (fun f => f.hom (GroundTheory.GroupCoh.cupH (add_comm 2 n) a y)) e1).trans ?_
    exact congrArg (fun g => (map (MonoidHom.id _) (𝟙 (A.quotientToInvariants
      (W : Subgroup (U : Subgroup G))) ⊗ₘ trivialToInvariantsHom (k := ℤ) (W : Subgroup (U : Subgroup G)))
        (n + 2) ≫ g).hom (GroundTheory.GroupCoh.cupH (add_comm 2 n) a y)) e2

  obtain ⟨q, hq⟩ := QZ.exists_nsmul_eq hm (F.inv U (inflation A W 2 a))
  obtain ⟨β, rfl⟩ := (F.inv_bijective U).2 q
  have hβ : m • β = inflation A W 2 a :=
    (F.inv_bijective U).1 (by rw [map_nsmul, hq])
  rw [hz, ← hβ, map_nsmul, LinearMap.smul_apply, ← map_nsmul, hmt, map_zero, map_zero]


include F in
theorem ClassFormation.subsingleton_cohomology_top_of_three_le_int {r : ℕ} (hr : 3 ≤ r) :
    Subsingleton (cohomology C r) :=
  subsingleton_cohomology_of_top C r (F.subsingleton_cohomology_of_three_le_int ⊤ hr)

end Int

section ULift

variable {C : Rep.{0} (ULift.{0} ℤ) G} [IsDiscreteRep C] (F : ClassFormation C)


include F in
theorem ClassFormation.subsingleton_cohomology_of_three_le (U : OpenSubgroup G) {r : ℕ}
    (hr : 3 ≤ r) : Subsingleton (cohomology (Rep.res (U : Subgroup G).subtype C) r) := by
  let _ := (ClassFormation.toInt C F).subsingleton_cohomology_of_three_le_int U hr
  exact (cohomologyULiftIntAddEquiv (Rep.res (U : Subgroup G).subtype C) r).injective.subsingleton


include F in
theorem ClassFormation.subsingleton_cohomology_top_of_three_le {r : ℕ} (hr : 3 ≤ r) :
    Subsingleton (cohomology C r) :=
  subsingleton_cohomology_of_top C r (F.subsingleton_cohomology_of_three_le ⊤ hr)

end ULift

end GroundTheory.ProfCoh
end
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

section Local

variable (K Ksep : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

theorem subsingleton_cohomology_galUnits_of_three_le {r : ℕ} (hr : 3 ≤ r) :
    Subsingleton (cohomology (galUnits.{0} K Ksep) r) :=
  (localClassFormationOfIsSepClosure K Ksep).subsingleton_cohomology_top_of_three_le hr

end Local

section Global

open GroundTheory.Global

theorem subsingleton_cohomology_classLimitRep_of_three_le (K : FiniteSubfield) {r : ℕ}
    (hr : 3 ≤ r) : Subsingleton (cohomology (classLimitRep K) r) :=
  (globalClassFormation K).subsingleton_cohomology_top_of_three_le_int hr

end Global

end GroundTheory.ProfCoh
