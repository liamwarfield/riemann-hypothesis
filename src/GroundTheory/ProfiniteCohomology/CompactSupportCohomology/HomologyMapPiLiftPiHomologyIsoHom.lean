module

public import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.HomApplyHomApplyEqOfCompEq

@[expose] public section

section -- merged from GroundTheory.ProfiniteCohomology.CompactSupportCohomology.HomologyMapPiLiftPiHomologyIsoHom
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

variable {k : Type u} [CommRing k]

section Pi

variable {ι : Type u} (K : ι → CochainComplex (ModuleCat.{u} k) ℕ)

theorem piComplex_d_hom_apply' (i j : ℕ) (x : (piComplex K).X i) (v : ι) :
    ((piComplex K).d i j).hom x v = ((K v).d i j).hom (x v) := by
  by_cases h : i + 1 = j
  · subst h
    exact piComplex_d_hom_apply K i x v
  · rw [(piComplex K).shape i j h, (K v).shape i j h]
    rfl

noncomputable def piProj (v : ι) : piComplex K ⟶ K v :=
  CochainComplex.ofHom (fun _ => ModuleCat.ofHom (LinearMap.proj v)) fun n =>
    ModuleCat.hom_ext (LinearMap.ext fun x => (piComplex_d_hom_apply K n x v).symm)

theorem piProj_f_hom_apply (v : ι) (n : ℕ) (x : (piComplex K).X n) :
    ((piProj K v).f n).hom x = x v :=
  rfl

theorem piLift_piProj {M : CochainComplex (ModuleCat.{u} k) ℕ} (g : ∀ v, M ⟶ K v) (v : ι) :
    piLift g ≫ piProj K v = g v :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

noncomputable def piHomologyToPi (n : ℕ) :
    (piComplex K).homology n ⟶ ModuleCat.of k (∀ v, (K v).homology n) :=
  ModuleCat.ofHom (LinearMap.pi fun v => (HomologicalComplex.homologyMap (piProj K v) n).hom)

theorem piHomologyToPi_hom_apply (n : ℕ) (h : (piComplex K).homology n) (v : ι) :
    (piHomologyToPi K n).hom h v = (HomologicalComplex.homologyMap (piProj K v) n).hom h :=
  rfl

theorem piHomologyToPi_bijective (n : ℕ) : Function.Bijective (piHomologyToPi K n).hom := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro h hh
    obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective ((piComplex K).homologyπ n)).1 inferInstance h
    have hv : ∀ v, ∃ y : (K v).X ((ComplexShape.up ℕ).prev n),
        ((K v).d _ n).hom y =
          ((K v).iCycles n).hom ((HomologicalComplex.cyclesMap (piProj K v) n).hom c) := by
      intro v
      refine (homologyπ_eq_zero_iff _ _).1 ?_
      rw [← homologyMap_homologyπ_apply]
      exact congrFun hh v
    choose y hy using hv
    refine (homologyπ_eq_zero_iff _ c).2 ⟨show (piComplex K).X _ from y, funext fun v => ?_⟩
    rw [piComplex_d_hom_apply', hy v, iCycles_cyclesMap_apply]
    rfl
  · intro h
    have hv : ∀ v, ∃ c : (K v).cycles n, ((K v).homologyπ n).hom c = h v :=
      fun v => (ModuleCat.epi_iff_surjective ((K v).homologyπ n)).1 inferInstance (h v)
    choose c hc using hv
    obtain ⟨c', hc'⟩ := exists_iCycles_eq (K := piComplex K)
      (show (piComplex K).X n from fun v => ((K v).iCycles n).hom (c v)) (by
        rw [CochainComplex.next]
        funext v
        rw [piComplex_d_hom_apply]
        exact iCycles_d_apply _ n (n + 1) (c v))
    refine ⟨((piComplex K).homologyπ n).hom c', funext fun v => ?_⟩
    rw [piHomologyToPi_hom_apply, homologyMap_homologyπ_apply, ← hc v]
    congr 1
    apply (ModuleCat.mono_iff_injective ((K v).iCycles n)).1 inferInstance
    rw [iCycles_cyclesMap_apply, hc']
    rfl

noncomputable def piHomologyIso (n : ℕ) :
    (piComplex K).homology n ≅ ModuleCat.of k (∀ v, (K v).homology n) :=
  (LinearEquiv.ofBijective (piHomologyToPi K n).hom (piHomologyToPi_bijective K n)).toModuleIso

theorem piHomologyIso_hom_apply (n : ℕ) (h : (piComplex K).homology n) (v : ι) :
    (piHomologyIso K n).hom.hom h v = (HomologicalComplex.homologyMap (piProj K v) n).hom h :=
  rfl

theorem homologyMap_piLift_piHomologyIso_hom {M : CochainComplex (ModuleCat.{u} k) ℕ}
    (g : ∀ v, M ⟶ K v) (n : ℕ) :
    HomologicalComplex.homologyMap (piLift g) n ≫ (piHomologyIso K n).hom =
      ModuleCat.ofHom (LinearMap.pi fun v => (HomologicalComplex.homologyMap (g v) n).hom) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun h => funext fun v => ?_)
  change (HomologicalComplex.homologyMap (piProj K v) n).hom
    ((HomologicalComplex.homologyMap (piLift g) n).hom h) = _
  rw [hom_apply_hom_apply_of_comp_eq (HomologicalComplex.homologyMap_comp _ _ n).symm h,
    piLift_piProj]
  rfl

end Pi

end GroundTheory.ProfCoh
end

section -- merged from GroundTheory.ProfiniteCohomology.CompactSupportCohomology.Pairing
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

variable {k : Type u} [CommRing k]

section Elements

variable (K : CochainComplex (ModuleCat.{u} k) ℕ)

theorem iCycles_hom_injective (n : ℕ) : Function.Injective (K.iCycles n).hom :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

theorem homologyπ_hom_surjective (n : ℕ) : Function.Surjective (K.homologyπ n).hom :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

theorem iCycles_toCycles_hom_apply (i n : ℕ) (a : K.X i) :
    (K.iCycles n).hom ((K.toCycles i n).hom a) = (K.d i n).hom a :=
  hom_apply_hom_apply_of_comp_eq (K.toCycles_i i n) a

theorem homologyπ_toCycles_hom_apply (i n : ℕ) (a : K.X i) :
    (K.homologyπ n).hom ((K.toCycles i n).hom a) = 0 :=
  hom_apply_hom_apply_of_comp_eq (K.toCycles_comp_homologyπ i n) a

noncomputable def descHomologyNat {r : ℕ} {T : Type u} [AddCommGroup T] [Module k T]
    (L : K.cycles r →ₗ[k] T) (hL : ∀ i, i + 1 = r → ∀ a, L ((K.toCycles i r).hom a) = 0) :
    K.homology r →ₗ[k] T :=
  ((K.homologyIsCokernel _ r rfl).desc (CokernelCofork.ofπ (ModuleCat.ofHom L) (by
    by_cases hr : (ComplexShape.up ℕ).Rel ((ComplexShape.up ℕ).prev r) r
    · exact ModuleCat.hom_ext (LinearMap.ext fun a => hL _ hr a)
    · rw [K.toCycles_eq_zero hr]
      exact zero_comp))).hom

theorem descHomologyNat_homologyπ {r : ℕ} {T : Type u} [AddCommGroup T] [Module k T]
    (L : K.cycles r →ₗ[k] T) (hL : ∀ i, i + 1 = r → ∀ a, L ((K.toCycles i r).hom a) = 0)
    (x : K.cycles r) : descHomologyNat K L hL ((K.homologyπ r).hom x) = L x :=
  ConcreteCategory.congr_hom (Cofork.IsColimit.π_desc (K.homologyIsCokernel _ r rfl)) x

end Elements

structure LeibnizPairing (M N P : CochainComplex (ModuleCat.{u} k) ℕ) where

  μ : ∀ {r s n : ℕ}, r + s = n → M.X r →ₗ[k] N.X s →ₗ[k] P.X n

  leibniz : ∀ {r s n : ℕ} (h : r + s = n) (x : M.X r) (y : N.X s),
    (P.d n (n + 1)).hom (μ h x y) =
      μ (by omega) ((M.d r (r + 1)).hom x) y + (-1 : k) ^ r • μ (by omega) x ((N.d s (s + 1)).hom y)

namespace LeibnizPairing

variable {M N P : CochainComplex (ModuleCat.{u} k) ℕ} (μ : LeibnizPairing M N P)

theorem d_μ_cycles {r s n : ℕ} (h : r + s = n) (x : M.cycles r) (y : N.cycles s) :
    (P.d n (n + 1)).hom (μ.μ h ((M.iCycles r).hom x) ((N.iCycles s).hom y)) = 0 := by
  rw [μ.leibniz, iCycles_d_apply, iCycles_d_apply, map_zero, LinearMap.zero_apply, map_zero,
    smul_zero, add_zero]

noncomputable def cyclesProduct {r s n : ℕ} (h : r + s = n) (x : M.cycles r) (y : N.cycles s) :
    P.cycles n :=
  P.cyclesMk (μ.μ h ((M.iCycles r).hom x) ((N.iCycles s).hom y)) (n + 1) (by simp)
    (μ.d_μ_cycles h x y)

theorem iCycles_cyclesProduct {r s n : ℕ} (h : r + s = n) (x : M.cycles r) (y : N.cycles s) :
    (P.iCycles n).hom (μ.cyclesProduct h x y) = μ.μ h ((M.iCycles r).hom x) ((N.iCycles s).hom y) :=
  P.i_cyclesMk _ _ _ _

noncomputable def cycles {r s n : ℕ} (h : r + s = n) :
    M.cycles r →ₗ[k] N.cycles s →ₗ[k] P.cycles n :=
  LinearMap.mk₂ k (μ.cyclesProduct h)
    (fun x x' y => iCycles_hom_injective P n (by simp [iCycles_cyclesProduct]))
    (fun c x y => iCycles_hom_injective P n (by simp [iCycles_cyclesProduct]))
    (fun x y y' => iCycles_hom_injective P n (by simp [iCycles_cyclesProduct]))
    (fun c x y => iCycles_hom_injective P n (by simp [iCycles_cyclesProduct]))

@[simp]
theorem iCycles_cycles {r s n : ℕ} (h : r + s = n) (x : M.cycles r) (y : N.cycles s) :
    (P.iCycles n).hom (μ.cycles h x y) = μ.μ h ((M.iCycles r).hom x) ((N.iCycles s).hom y) :=
  μ.iCycles_cyclesProduct h x y

theorem cycles_toCycles_left {r s n i m : ℕ} (h : r + s = n) (hi : i + 1 = r) (hm : i + s = m)
    (hmn : m + 1 = n) (a : M.X i) (y : N.cycles s) :
    μ.cycles h ((M.toCycles i r).hom a) y =
      (P.toCycles m n).hom (μ.μ hm a ((N.iCycles s).hom y)) := by
  subst hi hmn
  apply iCycles_hom_injective P
  rw [iCycles_cycles, iCycles_toCycles_hom_apply, iCycles_toCycles_hom_apply, μ.leibniz hm,
    iCycles_d_apply, map_zero, smul_zero, add_zero]

theorem cycles_toCycles_right {r s n j m : ℕ} (h : r + s = n) (hj : j + 1 = s) (hm : r + j = m)
    (hmn : m + 1 = n) (x : M.cycles r) (b : N.X j) :
    μ.cycles h x ((N.toCycles j s).hom b) =
      (-1 : k) ^ r • (P.toCycles m n).hom (μ.μ hm ((M.iCycles r).hom x) b) := by
  subst hj hmn
  apply iCycles_hom_injective P
  rw [iCycles_cycles, map_smul, iCycles_toCycles_hom_apply, iCycles_toCycles_hom_apply,
    μ.leibniz hm, iCycles_d_apply, map_zero, LinearMap.zero_apply, zero_add, smul_smul,
    ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

noncomputable def homologyPairing {r s n : ℕ} (h : r + s = n) :
    N.homology s →ₗ[k] M.cycles r →ₗ[k] P.homology n :=
  descHomologyNat N ((μ.cycles h).compr₂ (P.homologyπ n).hom).flip fun j hj b => by
    ext x
    change (P.homologyπ n).hom (μ.cycles h x ((N.toCycles j s).hom b)) = 0
    rw [μ.cycles_toCycles_right h hj rfl (by omega), map_smul, homologyπ_toCycles_hom_apply,
      smul_zero]

theorem homologyPairing_homology_class {r s n : ℕ} (h : r + s = n) (x : M.cycles r) (y : N.cycles s) :
    μ.homologyPairing h ((N.homologyπ s).hom y) x = (P.homologyπ n).hom (μ.cycles h x y) := by
  rw [homologyPairing, descHomologyNat_homologyπ]
  rfl

noncomputable def homology {r s n : ℕ} (h : r + s = n) :
    M.homology r →ₗ[k] N.homology s →ₗ[k] P.homology n :=
  descHomologyNat M (μ.homologyPairing h).flip fun i hi a => by
    ext z
    obtain ⟨y, rfl⟩ := homologyπ_hom_surjective N s z
    change μ.homologyPairing h ((N.homologyπ s).hom y) ((M.toCycles i r).hom a) = 0
    rw [homologyPairing_homology_class, μ.cycles_toCycles_left h hi rfl (by omega),
      homologyπ_toCycles_hom_apply]

@[simp]
theorem homology_homologyπ {r s n : ℕ} (h : r + s = n) (x : M.cycles r) (y : N.cycles s) :
    μ.homology h ((M.homologyπ r).hom x) ((N.homologyπ s).hom y) =
      (P.homologyπ n).hom (μ.cycles h x y) := by
  rw [homology, descHomologyNat_homologyπ, LinearMap.flip_apply, homologyPairing_homology_class]

end LeibnizPairing

section TwoSequences

variable {SM SN : ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ)}
  {P : CochainComplex (ModuleCat.{u} k) ℕ}

theorem δ_homologyπ_of_lift (hS : SM.ShortExact) (r : ℕ) (x₃ : SM.X₃.cycles r)
    (x₂ : SM.X₂.X r) (hx₂ : (SM.g.f r).hom x₂ = (SM.X₃.iCycles r).hom x₃)
    (x₁ : SM.X₁.cycles (r + 1))
    (hx₁ : (SM.f.f (r + 1)).hom ((SM.X₁.iCycles (r + 1)).hom x₁) = (SM.X₂.d r (r + 1)).hom x₂) :
    hS.δ r (r + 1) rfl ((SM.X₃.homologyπ r).hom x₃) = (SM.X₁.homologyπ (r + 1)).hom x₁ := by
  have hx₃ : (SM.X₃.d r (r + 1)).hom ((SM.X₃.iCycles r).hom x₃) = 0 :=
    iCycles_d_apply _ r (r + 1) x₃
  have key := hS.δ_apply r (r + 1) rfl ((SM.X₃.iCycles r).hom x₃) hx₃ x₂ hx₂
    ((SM.X₁.iCycles (r + 1)).hom x₁) hx₁ (r + 1 + 1) (by simp)
  have e3 : SM.X₃.cyclesMk ((SM.X₃.iCycles r).hom x₃) (r + 1)
      ((ComplexShape.up ℕ).next_eq' rfl) hx₃ = x₃ :=
    iCycles_hom_injective _ r (SM.X₃.i_cyclesMk _ _ _ _)
  have e1 : SM.X₁.cyclesMk ((SM.X₁.iCycles (r + 1)).hom x₁) (r + 1 + 1) (by simp)
      (hS.d_eq_zero_of_f_eq_d_apply r (r + 1) x₂ ((SM.X₁.iCycles (r + 1)).hom x₁) hx₁
        (r + 1 + 1)) = x₁ :=
    iCycles_hom_injective _ (r + 1) (SM.X₁.i_cyclesMk _ _ _ _)
  rw [← e3, ← e1]
  exact key

theorem exists_cycles_f_eq_d (hS : SM.ShortExact) (r : ℕ) (x₃ : SM.X₃.cycles r)
    (x₂ : SM.X₂.X r) (hx₂ : (SM.g.f r).hom x₂ = (SM.X₃.iCycles r).hom x₃) :
    ∃ x₁ : SM.X₁.cycles (r + 1),
      (SM.f.f (r + 1)).hom ((SM.X₁.iCycles (r + 1)).hom x₁) = (SM.X₂.d r (r + 1)).hom x₂ := by
  have hn := (HomologicalComplex.shortExact_iff_degreewise_shortExact SM).1 hS (r + 1)
  have e := hn.exact
  rw [ShortComplex.moduleCat_exact_iff] at e
  obtain ⟨y, hy⟩ := e ((SM.X₂.d r (r + 1)).hom x₂) (by
    change (SM.g.f (r + 1)).hom ((SM.X₂.d r (r + 1)).hom x₂) = 0
    rw [← hom_apply_hom_apply_eq_of_comp_eq (SM.g.comm r (r + 1)) x₂, hx₂, iCycles_d_apply])
  have hy' : (SM.X₁.d (r + 1) (r + 1 + 1)).hom y = 0 :=
    hS.d_eq_zero_of_f_eq_d_apply r (r + 1) x₂ y hy (r + 1 + 1)
  obtain ⟨x₁, hx₁⟩ := exists_iCycles_eq (K := SM.X₁) y (by rw [CochainComplex.next]; exact hy')
  exact ⟨x₁, by rw [hx₁]; exact hy⟩

variable (μ : LeibnizPairing SM.X₂ SN.X₂ P) (μ₁ : LeibnizPairing SM.X₁ SN.X₃ P)
  (μ₃ : LeibnizPairing SM.X₃ SN.X₁ P)

theorem LeibnizPairing.homology_δ_add_homology_δ
    (h₁₂ : ∀ {r s n : ℕ} (h : r + s = n) (x : SM.X₁.X r) (y : SN.X₂.X s),
      μ.μ h ((SM.f.f r).hom x) y = μ₁.μ h x ((SN.g.f s).hom y))
    (h₂₃ : ∀ {r s n : ℕ} (h : r + s = n) (x : SM.X₂.X r) (y : SN.X₁.X s),
      μ.μ h x ((SN.f.f s).hom y) = μ₃.μ h ((SM.g.f r).hom x) y)
    (hSM : SM.ShortExact) (hSN : SN.ShortExact) {r s n : ℕ} (h₁ : r + 1 + s = n + 1)
    (h₃ : r + (s + 1) = n + 1) (x : SM.X₃.homology r) (y : SN.X₃.homology s) :
    μ₁.homology h₁ (hSM.δ r (r + 1) rfl x) y +
      (-1 : k) ^ r • μ₃.homology h₃ x (hSN.δ s (s + 1) rfl y) = 0 := by
  obtain ⟨x₃, rfl⟩ := homologyπ_hom_surjective _ r x
  obtain ⟨y₃, rfl⟩ := homologyπ_hom_surjective _ s y
  have hSMr := (HomologicalComplex.shortExact_iff_degreewise_shortExact SM).1 hSM r
  have hSNs := (HomologicalComplex.shortExact_iff_degreewise_shortExact SN).1 hSN s
  obtain ⟨x₂, hx₂⟩ : ∃ x₂ : SM.X₂.X r, (SM.g.f r).hom x₂ = (SM.X₃.iCycles r).hom x₃ :=
    (ModuleCat.epi_iff_surjective _).1 hSMr.epi_g _
  obtain ⟨y₂, hy₂⟩ : ∃ y₂ : SN.X₂.X s, (SN.g.f s).hom y₂ = (SN.X₃.iCycles s).hom y₃ :=
    (ModuleCat.epi_iff_surjective _).1 hSNs.epi_g _
  obtain ⟨x₁, hx₁⟩ := exists_cycles_f_eq_d hSM r x₃ x₂ hx₂
  obtain ⟨y₁, hy₁⟩ := exists_cycles_f_eq_d hSN s y₃ y₂ hy₂
  rw [δ_homologyπ_of_lift hSM r x₃ x₂ hx₂ x₁ hx₁, δ_homologyπ_of_lift hSN s y₃ y₂ hy₂ y₁ hy₁,
    μ₁.homology_homologyπ, μ₃.homology_homologyπ, ← map_smul, ← map_add]
  have hn : n = r + s := by omega
  subst hn
  have e : μ₁.cycles h₁ x₁ y₃ + (-1 : k) ^ r • μ₃.cycles h₃ x₃ y₁ =
      (P.toCycles (r + s) (r + s + 1)).hom (μ.μ rfl x₂ y₂) := by
    apply iCycles_hom_injective P
    rw [map_add (f := _), map_smul, LeibnizPairing.iCycles_cycles, LeibnizPairing.iCycles_cycles,
      iCycles_toCycles_hom_apply, μ.leibniz, ← hx₁, ← hy₁, h₁₂, h₂₃, hx₂, hy₂]
  rw [e, homologyπ_toCycles_hom_apply]

end TwoSequences

end GroundTheory.ProfCoh
end

section -- merged from GroundTheory.ProfiniteCohomology.CompactSupportCohomology.ShiftNegOneHomologyIsoSymmHom
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

variable {k : Type u} [CommRing k]

section Shift

variable (L : CochainComplex (ModuleCat.{u} k) ℕ)

noncomputable def shiftNegOneSuccHom (n : ℕ) : L.X n ⟶ (shiftNegOne L).X (n + 1) :=
  ModuleCat.ofHom (shiftNegOneSucc L n)

instance (n : ℕ) : IsIso (shiftNegOneSuccHom L n) :=
  (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun _ _ h => h, fun y => ⟨y, rfl⟩⟩

theorem shiftNegOne_d_succ_hom_apply (n : ℕ) (y : L.X n) :
    ((shiftNegOne L).d (n + 1) (n + 1 + 1)).hom (shiftNegOneSucc L n y) =
      shiftNegOneSucc L (n + 1) (-(L.d n (n + 1)).hom y) := by
  rw [shiftNegOne_d]
  rfl

theorem shiftNegOneSuccHom_d (n : ℕ) :
    shiftNegOneSuccHom L n ≫ (shiftNegOne L).d (n + 1) (n + 1 + 1) =
      -(L.d n (n + 1) ≫ shiftNegOneSuccHom L (n + 1)) :=
  ModuleCat.hom_ext (LinearMap.ext fun y => shiftNegOne_d_succ_hom_apply L n y)

def prevNat : ℕ → ℕ
  | 0 => 0
  | n + 1 => n

theorem up_prev_eq_prevNat (n : ℕ) : (ComplexShape.up ℕ).prev n = prevNat n := by
  cases n with
  | zero => exact CochainComplex.prev_nat_zero
  | succ n => exact CochainComplex.prev_nat_succ n

noncomputable def shiftNegOneτ₁ : ∀ n, L.X (prevNat n) ⟶ (shiftNegOne L).X n
  | 0 => 0
  | n + 1 => -shiftNegOneSuccHom L n

noncomputable def shiftNegOneψ (n : ℕ) :
    L.sc' (prevNat n) n (n + 1) ⟶ (shiftNegOne L).sc' n (n + 1) (n + 1 + 1) where
  τ₁ := shiftNegOneτ₁ L n
  τ₂ := shiftNegOneSuccHom L n
  τ₃ := -shiftNegOneSuccHom L (n + 1)
  comm₁₂ := by
    cases n with
    | zero =>
      change (0 : L.X 0 ⟶ (shiftNegOne L).X 0) ≫ (shiftNegOne L).d 0 (0 + 1) =
        L.d 0 0 ≫ shiftNegOneSuccHom L 0
      rw [L.shape 0 0 (by simp), zero_comp, zero_comp]
    | succ n =>
      change (-shiftNegOneSuccHom L n) ≫ (shiftNegOne L).d (n + 1) (n + 1 + 1) =
        L.d n (n + 1) ≫ shiftNegOneSuccHom L (n + 1)
      rw [Preadditive.neg_comp, shiftNegOneSuccHom_d, neg_neg]
  comm₂₃ := by
    change shiftNegOneSuccHom L n ≫ (shiftNegOne L).d (n + 1) (n + 1 + 1) =
      L.d n (n + 1) ≫ (-shiftNegOneSuccHom L (n + 1))
    rw [shiftNegOneSuccHom_d, Preadditive.comp_neg]

theorem epi_shiftNegOneτ₁ (n : ℕ) : Epi (shiftNegOneτ₁ L n) := by
  cases n with
  | zero => exact (ModuleCat.epi_iff_surjective _).2 fun (_ : PUnit) => ⟨0, rfl⟩
  | succ n =>
    refine (ModuleCat.epi_iff_surjective _).2 fun (y : L.X n) => ⟨-y, ?_⟩
    change -(-y) = y
    exact neg_neg y

theorem mono_neg_shiftNegOneSuccHom (n : ℕ) : Mono (-shiftNegOneSuccHom L n) :=
  (ModuleCat.mono_iff_injective _).2 fun (a b : L.X n) h => by
    have h' : -a = -b := h
    exact neg_injective h'

noncomputable def shiftNegOneHomologyHom (n : ℕ) :
    L.homology n ⟶ (shiftNegOne L).homology (n + 1) :=
  (L.homologyIsoSc' (prevNat n) n (n + 1) (up_prev_eq_prevNat n) (CochainComplex.next ℕ n)).hom ≫
    ShortComplex.homologyMap (shiftNegOneψ L n) ≫
    ((shiftNegOne L).homologyIsoSc' n (n + 1) (n + 1 + 1) (CochainComplex.prev_nat_succ n)
      (CochainComplex.next ℕ (n + 1))).inv

instance isIso_shiftNegOneHomologyHom (n : ℕ) : IsIso (shiftNegOneHomologyHom L n) := by
  have := ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono' (shiftNegOneψ L n)
    (epi_shiftNegOneτ₁ L n) (inferInstanceAs (IsIso (shiftNegOneSuccHom L n)))
    (mono_neg_shiftNegOneSuccHom L (n + 1))
  unfold shiftNegOneHomologyHom
  infer_instance

noncomputable def shiftNegOneHomologyIso (n : ℕ) :
    (shiftNegOne L).homology (n + 1) ≅ L.homology n :=
  (asIso (shiftNegOneHomologyHom L n)).symm

theorem iCycles_shiftNegOneSuccHom_d (n : ℕ) :
    (L.iCycles n ≫ shiftNegOneSuccHom L n) ≫ (shiftNegOne L).d (n + 1) (n + 1 + 1) = 0 := by
  rw [Category.assoc, shiftNegOneSuccHom_d, Preadditive.comp_neg, L.iCycles_d_assoc, zero_comp,
    neg_zero]

@[reassoc]
theorem homologyπ_shiftNegOneHomologyHom (n : ℕ) :
    L.homologyπ n ≫ shiftNegOneHomologyHom L n =
      (shiftNegOne L).liftCycles (L.iCycles n ≫ shiftNegOneSuccHom L n) (n + 1 + 1)
        (CochainComplex.next ℕ (n + 1)) (iCycles_shiftNegOneSuccHom_d L n) ≫
        (shiftNegOne L).homologyπ (n + 1) := by
  rw [shiftNegOneHomologyHom, HomologicalComplex.π_homologyIsoSc'_hom_assoc,
    ShortComplex.homologyπ_naturality_assoc, HomologicalComplex.π_homologyIsoSc'_inv]
  simp only [← Category.assoc]
  congr 1
  rw [← cancel_mono ((shiftNegOne L).iCycles (n + 1))]
  simp only [Category.assoc, HomologicalComplex.cyclesIsoSc'_inv_iCycles,
    HomologicalComplex.liftCycles_i]
  rw [← HomologicalComplex.cyclesIsoSc'_hom_iCycles L (prevNat n) n (n + 1) (up_prev_eq_prevNat n)
    (CochainComplex.next ℕ n)]
  exact (congrArg (_ ≫ ·) (ShortComplex.cyclesMap_i (shiftNegOneψ L n))).trans
    (Category.assoc _ _ _).symm

end Shift

namespace mappingCoconeNat

variable {K L : CochainComplex (ModuleCat.{u} k) ℕ} (f : K ⟶ L)

theorem inr_fst : inr f ≫ fst f = 0 :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

noncomputable abbrev shortComplex : ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ) :=
  ShortComplex.mk (inr f) (fst f) (inr_fst f)

theorem shortExact : (shortComplex f).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => {
    exact := by
      rw [ShortComplex.moduleCat_exact_iff]
      intro (p : K.X n × shiftNegOneX L n) hp
      exact ⟨p.2, Prod.ext hp.symm rfl⟩
    mono_f := (ModuleCat.mono_iff_injective _).2 fun _ _ h => congrArg Prod.snd h
    epi_g := (ModuleCat.epi_iff_surjective _).2 fun (x : K.X n) => ⟨((x, 0) : K.X n × _), rfl⟩ }

noncomputable def inlX (n : ℕ) : K.X n ⟶ (mappingCoconeNat f).X n :=
  ModuleCat.ofHom (LinearMap.inl k (K.X n) (shiftNegOneX L n))

theorem inlX_fst (n : ℕ) : inlX f n ≫ (fst f).f n = 𝟙 _ :=
  ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

theorem inlX_d (n : ℕ) :
    inlX f n ≫ (mappingCoconeNat f).d n (n + 1) =
      K.d n (n + 1) ≫ inlX f (n + 1) + f.f n ≫ shiftNegOneSuccHom L n ≫ (inr f).f (n + 1) := by
  rw [mappingCoconeNat_d]
  refine ModuleCat.hom_ext (LinearMap.ext fun x => Prod.ext ?_ ?_)
  · change (K.d n (n + 1)).hom x = (K.d n (n + 1)).hom x + 0
    rw [add_zero]
  · change shiftNegOneSucc L n ((f.f n).hom x) + (shiftNegOneD L n).hom 0 =
      0 + shiftNegOneSucc L n ((f.f n).hom x)
    rw [map_zero, add_zero, zero_add]

theorem δ_eq (n : ℕ) :
    (shortExact f).δ n (n + 1) rfl =
      HomologicalComplex.homologyMap f n ≫ shiftNegOneHomologyHom L n := by
  refine (cancel_epi (K.homologyπ n)).1 ?_
  have h := (shortExact f).δ_eq n (n + 1) rfl (K.iCycles n) (K.iCycles_d n (n + 1))
    (K.iCycles n ≫ inlX f n) (by
      change (K.iCycles n ≫ inlX f n) ≫ (fst f).f n = K.iCycles n
      rw [Category.assoc, inlX_fst, Category.comp_id])
    (K.iCycles n ≫ f.f n ≫ shiftNegOneSuccHom L n) (by
      change (K.iCycles n ≫ f.f n ≫ shiftNegOneSuccHom L n) ≫ (inr f).f (n + 1) =
        (K.iCycles n ≫ inlX f n) ≫ (mappingCoconeNat f).d n (n + 1)
      simp only [Category.assoc]
      rw [inlX_d, Preadditive.comp_add, K.iCycles_d_assoc, zero_comp, zero_add])
    (n + 1 + 1) (CochainComplex.next ℕ (n + 1))
  have hl : K.liftCycles (K.iCycles n) (n + 1) (CochainComplex.next ℕ n) (K.iCycles_d n (n + 1)) =
      𝟙 _ := by
    rw [← cancel_mono (K.iCycles n), HomologicalComplex.liftCycles_i, Category.id_comp]
  have h2 : K.homologyπ n ≫ (shortExact f).δ n (n + 1) rfl =
      (shiftNegOne L).liftCycles (K.iCycles n ≫ f.f n ≫ shiftNegOneSuccHom L n) (n + 1 + 1)
        (CochainComplex.next ℕ (n + 1)) (by
          rw [← HomologicalComplex.cyclesMap_i_assoc, Category.assoc,
            iCycles_shiftNegOneSuccHom_d, comp_zero]) ≫
        (shiftNegOne L).homologyπ (n + 1) := by
    calc K.homologyπ n ≫ (shortExact f).δ n (n + 1) rfl =
        K.liftCycles (K.iCycles n) (n + 1) (CochainComplex.next ℕ n) (K.iCycles_d n (n + 1)) ≫
          K.homologyπ n ≫ (shortExact f).δ n (n + 1) rfl := by rw [hl, Category.id_comp]
      _ = _ := h
  rw [h2, HomologicalComplex.homologyπ_naturality_assoc, homologyπ_shiftNegOneHomologyHom]
  simp only [← Category.assoc]
  congr 1
  rw [← cancel_mono ((shiftNegOne L).iCycles (n + 1))]
  simp only [Category.assoc, HomologicalComplex.liftCycles_i, HomologicalComplex.cyclesMap_i_assoc]

noncomputable def homologyδ (n : ℕ) : L.homology n ⟶ (mappingCoconeNat f).homology (n + 1) :=
  shiftNegOneHomologyHom L n ≫ HomologicalComplex.homologyMap (inr f) (n + 1)

theorem homologyMap_homologyδ (n : ℕ) :
    HomologicalComplex.homologyMap f n ≫ homologyδ f n = 0 := by
  rw [homologyδ, ← Category.assoc, ← δ_eq]
  exact (shortExact f).δ_comp n (n + 1) rfl

@[reassoc (attr := simp)]
theorem homologyδ_homologyMap_fst (n : ℕ) :
    homologyδ f n ≫ HomologicalComplex.homologyMap (fst f) (n + 1) = 0 := by
  rw [homologyδ, Category.assoc, ← HomologicalComplex.homologyMap_comp, inr_fst,
    HomologicalComplex.homologyMap_zero, comp_zero]

@[reassoc (attr := simp)]
theorem homologyMap_fst_homologyMap (n : ℕ) :
    HomologicalComplex.homologyMap (fst f) n ≫ HomologicalComplex.homologyMap f n = 0 := by
  rw [← cancel_mono (shiftNegOneHomologyHom L n), Category.assoc, ← δ_eq, zero_comp]
  exact (shortExact f).comp_δ n (n + 1) rfl

theorem homology_exact₁ (n : ℕ) :
    (ShortComplex.mk _ _ (homologyMap_homologyδ f n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).2 ((shortExact f).homology_exact₁ n (n + 1) rfl)
  exact ShortComplex.isoMk (Iso.refl _) (shiftNegOneHomologyIso L n).symm (Iso.refl _)
    (by simp [δ_eq, shiftNegOneHomologyIso]) (by simp [homologyδ, shiftNegOneHomologyIso])

theorem homology_exact₂ (n : ℕ) :
    (ShortComplex.mk _ _ (homologyδ_homologyMap_fst f n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).2 ((shortExact f).homology_exact₂ (n + 1))
  exact ShortComplex.isoMk (shiftNegOneHomologyIso L n).symm (Iso.refl _) (Iso.refl _)
    (by simp [homologyδ, shiftNegOneHomologyIso]) (by simp)

theorem homology_exact₃ (n : ℕ) :
    (ShortComplex.mk _ _ (homologyMap_fst_homologyMap f n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).2 ((shortExact f).homology_exact₃ n (n + 1) rfl)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (shiftNegOneHomologyIso L n).symm
    (by simp) (by simp [δ_eq, shiftNegOneHomologyIso])

theorem mono_homologyMap_fst_zero : Mono (HomologicalComplex.homologyMap (fst f) 0) := by
  have hz : IsZero ((shiftNegOne L).homology 0) :=
    ShortComplex.isZero_homology_of_isZero_X₂ _ (ModuleCat.isZero_of_subsingleton
      (ModuleCat.of k PUnit))
  exact ((shortExact f).homology_exact₂ 0).mono_g (hz.eq_of_src _ _)

end mappingCoconeNat

end GroundTheory.ProfCoh
end
