module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameOfFrobeniusDense
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TameAnyAtOfIsConjPl

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameAnyAtPlace
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameAnyAtFixed
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.IneAway
open GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
end GlobalTheory.IneAway
namespace GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels
theorem tameAnyAt_fixed_alt_alt : ∀ D : D7, _root_.UpperTheory.GalS.GalAwayN D → FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → D.naut.ralg π → _root_.UpperTheory.GalS.FullLabS D [⟨D.R.r, π, 1⟩] → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → ∀ v : D.nd.PlG k, TameAnyAt D i [⟨D.R.r, π, 1⟩] ρ k (D.naut.plGw k v) := by
  intro D hA hF i π ρ hc hr hfull hρ k hk v
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨ι, hinj, hred⟩ := GlobalTheory.T.exists_reduction_teichmullerEmbedding_at_localisation D i k hk
  have hpol := _root_.GlobalTheory.IneAway.ineAt' D hA hF i π ρ hc hr hfull hρ k v _ rfl (tameAnyFix_not_over D i k hk v) _ (D.ntypes.tg_mem k v)
  have hlab := D.ntypes.inertiaCharpoly_type k v _ (_root_.UpperTheory.GalS.fl0' hfull k v)
  rw [← tameAnyFix_isoLoc D π, hlab] at hpol
  have h1 := hred _ _ hpol
  have hchar : Matrix.charpoly ((redF D i ρ (D.nd.gam0 i (D.naut.plGw k v)) : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) =
      ((Formalism.CyclotomicNorms.rootsBar (labSig D [⟨D.R.r, π, 1⟩] k v)).map
        fun x => X - C (ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x) ^ (1 : ℤ))).prod := by
    rw [D.ntypes.heckeLoc_gamma_places]
    simp only [zpow_one, tameAnyFix_map_primeToPart]
    rw [← h1, ← Matrix.charpoly_map]
    rfl
  have hval : ∀ y : Fb (D.host.g k) (D.host.g_prime k),
      iotaO D.nd D.naut i (chi1 D.nd i (D.ntypes.tg k v)) = D.ntypes.teichC k y →
      D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i (D.naut.plGw k v)))) = ι y := by
    intro y hy
    have h2 := hred (X - C (chi1 D.nd i (D.ntypes.tg k v))) {y} (by simp [hy])
    rw [D.ntypes.heckeLoc_gamma_places]
    simpa using h2
  rcases D.ntypes.chiT_tg i k v hk with h | h
  · refine ⟨v, ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, ι, 1, 1, Or.inl rfl, Or.inl rfl, hinj, hchar, ?_⟩
    rw [zpow_one, tameAnyFix_map_primeToPart]
    exact hval _ h
  · refine ⟨v, ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, ι, 1, -1, Or.inl rfl, Or.inr rfl, hinj, hchar, ?_⟩
    rw [zpow_neg_one, tameAnyFix_map_primeToPart, hval _ h]
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
end GlobalTheory.TypeLeaf
namespace GlobalTheory.TypeLeaf.ConjPlace
end GlobalTheory.TypeLeaf.ConjPlace
namespace GlobalTheory.AdmTame
end GlobalTheory.AdmTame
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_any_at_pl_gw : ∀ D : D7, _root_.UpperTheory.GalS.GalAwayN D → FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → D.naut.ralg π → _root_.UpperTheory.GalS.FullLabS D [⟨D.R.r, π, 1⟩] → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → ∀ v : D.nd.PlG k, TameAnyAt D i [⟨D.R.r, π, 1⟩] ρ k (D.naut.plGw k v) := by
  first | exact @_root_.GlobalTheory.TypeLeaf.tameAnyAt_fixed_alt_alt | exact _root_.GlobalTheory.TypeLeaf.tameAnyAt_fixed_alt_alt | (intros; apply _root_.GlobalTheory.TypeLeaf.tameAnyAt_fixed_alt_alt <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameSumOfInputs
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameOfFrobeniusDense
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameAnyAtOfIsConjPl
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.IneAway
open GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
end GlobalTheory.IneAway
namespace GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels
end GlobalTheory.TypeLeaf
namespace GlobalTheory.TypeLeaf.ConjPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels GlobalTheory.AntiRamConj GlobalTheory.TwistDet
open scoped Pointwise
theorem tame_any_at_of_is_conj_pl_tame_gen : ∀ D : D7, WildOne D → (∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k), D.nd.l i ≠ D.host.g k → ∀ s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)), D.nd.chi i 1 s = 1) → _root_.UpperTheory.GalS.GalAwayN D → FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → D.naut.ralg π → _root_.UpperTheory.GalS.FullLabS D [⟨D.R.r, π, 1⟩] → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → ∀ (v : D.nd.PlG k) (w : PlE D.host), IsConjPl D.host (D.naut.plGw k v) w → TameGen D.nd (D.nd.plOm.1 w) (D.nd.gam0 i w) → TameAnyAt D i [⟨D.R.r, π, 1⟩] ρ k w := by
  intro D hW hχ hG hF i π ρ hc ha hfull hρ k hl v w hvw hgen
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hP := not_mem_of_ne (D := D) (v := v) (D.nd.lPrime i).out hl
  have hw : w ∉ placesOver D.host.E (D.nd.l i) := fun h => hP (mem_placesOver_conj (isConjPl_symm hvw) h)
  have hγ0 : TameGenAt (D.nd.plOm.1 (D.naut.plGw k v)) (D.nd.gam0 i (D.naut.plGw k v)) := by
    refine D.nd.restN_tameGenerator_generates i _ (Or.inl ((D.nd.S_def i _).2 ⟨?_, hP⟩))
    have hv := D.naut.plGw_over k v
    fin_cases k
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
  have hγw : TameGenAt (D.nd.plOm.1 w) (D.nd.gam0 i w) := ⟨D.nd.locNd_chebotarevPlace_mem i w, hgen⟩
  obtain ⟨g, hg⟩ := exists_tameGenAt_conj D hvw hγw
  have hkill : ∀ s : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om,
      (∀ y : D.nd.Om, y ≠ 0 → (D.nd.plOm.1 (D.naut.plGw k v)).valuation (s y / y - 1) < 1) →
      ((redF D i ρ).prod (chiBar D i)) s = 1 := by
    intro u hu
    have huI := mem_ine_of_wild hu
    obtain ⟨ι, -, hred⟩ := GlobalTheory.T.exists_reduction_teichmullerEmbedding_at_localisation D i k hl
    have hf := _root_.UpperTheory.GalS.fl0' hfull k v
    unfold labSig at hf
    rw [isoLoc_single] at hf
    have h1 := (_root_.GlobalTheory.IneAway.ineAt' D hG hF i π ρ hc ha hfull hρ k v _ rfl hP u huI).trans (hW k v _ hf u huI hu)
    rw [D.naut.locG_dim] at h1
    have h2 : ((redF D i ρ u : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))).charpoly = (X - 1) ^ D.R.r := by
      rw [charpoly_redF, hred _ (Multiset.replicate D.R.r 1) (by rw [h1]; simp)]
      simp
    have hgv : (D.nd.plOm.1 (D.naut.plGw k v)).valuation ((D.host.g k : ℕ) : D.nd.Om) < 1 := by
      have h4 := D.nd.plOm.2 (D.naut.plGw k v)
      have h5 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
      simpa using (h4 _).2 h5
    have h3 := GlobalTheory.T.wild_eq_one_of_charpoly_unipotent_mod_l _ _ _ (D.host.g k) (D.nd.l i) D.R.r hl hgv _ (redF D i ρ)
      (GlobalTheory.T.residualRep_ker_isOpen D i ρ hρ.1) u hu h2
    refine Prod.ext h3 ?_
    change Units.map _ (D.nd.chi i 1 u) = 1
    rw [hχ i k v hl u hu, map_one]
  have hopen : IsOpen ((((redF D i ρ).prod (chiBar D i)).ker : Subgroup _) : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)) := by
    rw [MonoidHom.ker_prod, Subgroup.coe_inf]
    exact (GlobalTheory.T.residualRep_ker_isOpen D i ρ hρ.1).inter (isOpen_ker_chiBar D i)
  obtain ⟨n, hn, hM, hpow⟩ := GlobalTheory.T.tameGenerator_image_eq_coprime_pow _ _ _ _ _ hγ0 hg _ _ hopen hkill
  set γ0 := D.nd.gam0 i (D.naut.plGw k v) with hγ0def
  set M := orderOf (((redF D i ρ).prod (chiBar D i)) γ0) with hMdef
  have hone : ((redF D i ρ).prod (chiBar D i)) γ0 ^ M = 1 := pow_orderOf_eq_one _
  have hinv : ((redF D i ρ).prod (chiBar D i)) (g * cConj D.ntw (D.nd.gam0 i w) * g⁻¹)⁻¹ =
      ((redF D i ρ).prod (chiBar D i)) γ0 ^ (n * (M - 1)) := by
    rw [map_inv, hpow, inv_eq_iff_mul_eq_one, ← pow_add, ← mul_one_add, show 1 + (M - 1) = M by omega, mul_comm, pow_mul,
      hone, one_pow]
  have hn' : (n * (M - 1)).Coprime M := hn.mul_left ((Nat.coprime_self_sub_left hM).2 (Nat.coprime_one_left _))
  obtain ⟨θ, hθ, hθo, hθn⟩ := GlobalTheory.T.exists_order_preserving_power_hom_algClosure_primeField (D.host.g k) M _ hM hn'
  obtain ⟨hcp, hcχ⟩ := GlobalTheory.T.inertia_compatible_conjugation_representation D hF i π ρ hc hρ w _ hw (D.nd.plOm.2 w) _ (Subgroup.inv_mem _ hγw.1)
    (cConj D.ntw (D.nd.gam0 i w)⁻¹) (fun y => by rw [cConj_apply, RingEquiv.symm_apply_apply])
  rw [inv_inv] at hcp hcχ
  have econj : (g * cConj D.ntw (D.nd.gam0 i w) * g⁻¹)⁻¹ = g * cConj D.ntw (D.nd.gam0 i w)⁻¹ * g⁻¹ := by
    rw [map_inv]
    group
  rw [econj] at hinv
  have hρ1 : redF D i ρ (g * cConj D.ntw (D.nd.gam0 i w)⁻¹ * g⁻¹) = redF D i ρ γ0 ^ (n * (M - 1)) :=
    congrArg Prod.fst hinv
  have hχ1 : chiBar D i (g * cConj D.ntw (D.nd.gam0 i w)⁻¹ * g⁻¹) = chiBar D i γ0 ^ (n * (M - 1)) :=
    congrArg Prod.snd hinv
  have hρM : redF D i ρ γ0 ^ M = 1 := congrArg Prod.fst hone
  have hχM : chiBar D i γ0 ^ M = 1 := congrArg Prod.snd hone
  obtain ⟨v', j, ι, e₁, e₂, he₁, he₂, hι, hch, hχ0⟩ := _root_.GlobalTheory.T.tame_any_at_pl_gw D hG hF i π ρ hc ha hfull hρ k hl v
  refine ⟨v', j, ι.comp θ, e₁, e₂, he₁, he₂, injPrimeTo_comp hι hθ hθo, ?_, ?_⟩
  · have h1 := charpoly_pow_of_prod _ _ _ hch (n * (M - 1))
    rw [← Units.val_pow_eq_pow_val, ← hρ1, map_mul, map_mul, map_inv _ g, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
      Matrix.charpoly_units_conj, charpoly_redF, hcp, ← charpoly_redF] at h1
    rw [h1]
    refine congrArg _ (Multiset.map_congr rfl fun x hx => ?_)
    rw [comp_pow_eq (D.nd.lPrime i).out hM hι hθ hθn he₁ x
      (pow_eq_one_of_prod _ _ _ hch (by rw [← Units.val_pow_eq_pow_val, hρM, Units.val_one]) hx)]
  · rw [← chiBar_val] at hχ0
    rw [comp_pow_eq (D.nd.lPrime i).out hM hι hθ hθn he₂ _
      (by rw [← hχ0, ← Units.val_pow_eq_pow_val, hχM, Units.val_one]), ← hχ0, ← Units.val_pow_eq_pow_val, ← hχ1,
      map_mul, map_mul, map_inv _ g, mul_inv_cancel_comm, chiBar_val, chi1, chi1, hcχ]
end GlobalTheory.TypeLeaf.ConjPlace
namespace GlobalTheory.AdmTame
end GlobalTheory.AdmTame
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_any_at_conj_of_frobenius_dense : ∀ D : D7, WildOne D → (∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k), D.nd.l i ≠ D.host.g k → ∀ s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)), D.nd.chi i 1 s = 1) → _root_.UpperTheory.GalS.GalAwayN D → FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → D.naut.ralg π → _root_.UpperTheory.GalS.FullLabS D [⟨D.R.r, π, 1⟩] → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → ∀ (v : D.nd.PlG k) (w : PlE D.host), IsConjPl D.host (D.naut.plGw k v) w → TameGen D.nd (D.nd.plOm.1 w) (D.nd.gam0 i w) → TameAnyAt D i [⟨D.R.r, π, 1⟩] ρ k w := by
  first | exact @_root_.GlobalTheory.TypeLeaf.ConjPlace.tame_any_at_of_is_conj_pl_tame_gen | exact _root_.GlobalTheory.TypeLeaf.ConjPlace.tame_any_at_of_is_conj_pl_tame_gen | (intros; apply _root_.GlobalTheory.TypeLeaf.ConjPlace.tame_any_at_of_is_conj_pl_tame_gen <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameFixedAway
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameFixedOfType
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.IneAway
open GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
end GlobalTheory.IneAway
namespace GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels
theorem tame_fixed_of_type_alt : ∀ D : D7, WildOne D → _root_.UpperTheory.GalS.GalAwayN D → FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → D.naut.ralg π → _root_.UpperTheory.GalS.FullLabS D [⟨D.R.r, π, 1⟩] → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → TameFixed D i [⟨D.R.r, π, 1⟩] ρ k := by
  intro D hW hG hF i π ρ hc ha hfull hρ k hl v
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : Fact (D.nd.l i).Prime := D.nd.lPrime i
  have hw := not_mem_of_ne (D := D) (v := v) (D.nd.lPrime i).out hl
  have hine := _root_.GlobalTheory.IneAway.ineAt' D hG hF i π ρ hc ha hfull hρ k v _ rfl hw
  obtain ⟨ι, hι, hred⟩ := GlobalTheory.T.exists_reduction_teichmullerEmbedding_at_localisation D i k hl
  have hf := _root_.UpperTheory.GalS.fl0' hfull k v
  unfold labSig at hf ⊢
  rw [isoLoc_single] at hf ⊢
  refine ⟨ι, hι, ?_, ?_⟩
  · have h1 := (hine _ (D.ntypes.tg_mem k v)).trans (D.ntypes.inertiaCharpoly_type k v _ hf)
    change _ = ((rts (k := k) (v := v) (D.naut.locG π _)).map fun x => X - C (D.ntypes.teichC k x)).prod at h1
    change _ = ((rts (k := k) (v := v) (D.naut.locG π _)).map fun x =>
      X - C (ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x))).prod
    set m := rts (k := k) (v := v) (D.naut.locG π _) with hm
    have hne : ∀ x ∈ m, x ≠ 0 := by
      rintro x hx rfl
      have h2 : (X : ℂ[X]) ∣ (m.map fun x => X - C (D.ntypes.teichC k x)).prod := by
        refine Multiset.dvd_prod (Multiset.mem_map.2 ⟨0, hx, ?_⟩)
        rw [teich_zero _ (D.ntypes.teichC_inj k), map_zero, sub_zero]
      rw [← h1, ← Matrix.charpoly_map, X_dvd_iff] at h2
      have h3 := Matrix.det_eq_sign_charpoly_coeff
        (((ρ (D.ntypes.tg k v) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map (iotaO D.nd D.naut i))
      rw [h2, mul_zero] at h3
      exact (Matrix.GeneralLinearGroup.map (iotaO D.nd D.naut i) (ρ (D.ntypes.tg k v))).det_ne_zero h3
    rw [charpoly_redF, hred _ m h1]
    refine congrArg _ (Multiset.map_congr rfl fun x hx => ?_)
    rw [map_primeToPart ι (isOfFinOrder_of_ne_zero (hne x hx))]
  · obtain ⟨φ, hφ⟩ := exists_isFrob (D.nd.plOm.2 (D.naut.plGw k v))
    rw [normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) (D.naut.plGw_over k v)] at hφ
    refine ⟨φ, ?_⟩
    set t := D.ntypes.tg k v with ht
    have hu := wild_of_frob (D.ntypes.tg_mem k v) hφ
    have huI : (t ^ D.host.g k)⁻¹ * (φ * t * φ⁻¹) ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ (D.ntypes.tg_mem k v) _))
        (conj_mem_Ine hφ.1 (D.ntypes.tg_mem k v))
    set u := (t ^ D.host.g k)⁻¹ * (φ * t * φ⁻¹) with hudef
    have h1 := (hine u huI).trans (hW k v _ hf u huI hu)
    rw [D.naut.locG_dim] at h1
    have h2 : ((redF D i ρ u : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))).charpoly = (X - 1) ^ D.R.r := by
      rw [charpoly_redF, hred _ (Multiset.replicate D.R.r 1) (by rw [h1]; simp)]
      simp
    have hg : (D.nd.plOm.1 (D.naut.plGw k v)).valuation ((D.host.g k : ℕ) : D.nd.Om) < 1 := by
      have h4 := D.nd.plOm.2 (D.naut.plGw k v)
      have h5 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
      simpa using (h4 _).2 h5
    have h3 := GlobalTheory.T.wild_eq_one_of_charpoly_unipotent_mod_l _ _ _ (D.host.g k) (D.nd.l i) D.R.r hl hg _ (redF D i ρ)
      (GlobalTheory.T.residualRep_ker_isOpen D i ρ hρ.1) u hu h2
    rw [hudef, map_mul, map_inv, inv_mul_eq_one, map_pow] at h3
    exact h3.symm
end GlobalTheory.TypeLeaf
namespace GlobalTheory.TypeLeaf.ConjPlace
end GlobalTheory.TypeLeaf.ConjPlace
namespace GlobalTheory.AdmTame
end GlobalTheory.AdmTame
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_fixed_of_l_ne_g : ∀ D : D7, WildOne D → _root_.UpperTheory.GalS.GalAwayN D → FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → D.naut.ralg π → _root_.UpperTheory.GalS.FullLabS D [⟨D.R.r, π, 1⟩] → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → TameFixed D i [⟨D.R.r, π, 1⟩] ρ k := by
  first | exact @_root_.GlobalTheory.TypeLeaf.tame_fixed_of_type_alt | exact _root_.GlobalTheory.TypeLeaf.tame_fixed_of_type_alt | (intros; apply _root_.GlobalTheory.TypeLeaf.tame_fixed_of_type_alt <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameSum
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
def TameSumAlt (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)), (∃ x, HasParamX D.nd D.naut i x Sig) → _root_.UpperTheory.GalS.FullLabS D Sig →
    IsCuspIso D.nd D.naut Sig →
    ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i), IsRepOfSig D.nd D.naut i Sig ρ →
    ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → TameFixed D i Sig ρ k ∧
      ∀ w ∈ placesOver D.host.E (D.host.g k), TameGen D.nd (D.nd.plOm.1 w) (D.nd.gam0 i w) → TameAnyAt D i Sig ρ k w
end GlobalTheory.TypeLeaf
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
theorem tameSum_of_inputs_alt : ∀ D : D7, WildOne D →
    (∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k), D.nd.l i ≠ D.host.g k →
      ∀ s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)), D.nd.chi i 1 s = 1) →
    _root_.UpperTheory.GalS.GalAwayN D → FrobDense D → PointPar D → _root_.GlobalTheory.TypeLeaf.TameSumAlt D := by
  intro D hW hχ hG hF hP i Sig hx hfull hc ρ hρ k hk
  obtain ⟨x, hx⟩ := hx
  obtain ⟨π, rfl⟩ := hc
  obtain ⟨h1, h2⟩ := hP i x π hx
  refine ⟨_root_.GlobalTheory.T.tame_fixed_of_l_ne_g D hW hG hF i π ρ h1 h2 hfull hρ k hk, fun w hw ht => ?_⟩
  obtain ⟨v, hv | hv⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
  · subst hv
    exact _root_.GlobalTheory.T.tame_any_at_pl_gw D hG hF i π ρ h1 h2 hfull hρ k hk v
  · exact _root_.GlobalTheory.T.tame_any_at_conj_of_frobenius_dense D hW hχ hG hF i π ρ h1 h2 hfull hρ k hk v w hv ht
end GlobalTheory.TypeLeaf
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.IneAway
open GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
end GlobalTheory.IneAway
namespace GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels
end GlobalTheory.TypeLeaf
namespace GlobalTheory.TypeLeaf.ConjPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels GlobalTheory.AntiRamConj GlobalTheory.TwistDet
open scoped Pointwise
end GlobalTheory.TypeLeaf.ConjPlace
namespace GlobalTheory.AdmTame
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
theorem main_alt_alt_alt : ∀ D : D7, SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → SumRepresentations.adm5 D → UpperTheory.GalS.LabTameS D.nd D.naut → UpperTheory.GalS.AdmissibleResidualTameEigenvalues D := by
  intro D h0 hG hA hL
  obtain ⟨hLP, hAut, -⟩ := h0
  have hW : GlobalTheory.TypeLeaf.WildOne D := hL.1
  have hGal : _root_.UpperTheory.GalS.GalAwayN D := _root_.GlobalTheory.AdmTame.galAwayOfS' hG
  have hF : GlobalTheory.TypeLeaf.FrobDense D := by
    intro T hT
    rw [dense_iff_closure_eq]
    exact hA.2.2.1 T hT
  have hCL : GlobalTheory.TypeLeaf.CharLaws D := by
    intro w a χ χ' hχ hχ'
    obtain ⟨-, -, -, h4, h5, -⟩ := hLP w a a χ χ' 0 hχ hχ'
    exact ⟨h4, h5⟩
  have hM : GlobalTheory.TypeLeaf.MultOne D := by
    intro a π π' ha h
    have hp := hA.1 [⟨a, π, 1⟩] [⟨a, π', 1⟩] (by simp [ha]) (by simp [ha])
      (Filter.Eventually.of_forall fun w => by simp [isoLoc, spehLoc, h w])
    rw [List.singleton_perm_singleton] at hp
    simp only [Formalism.BasicNotions.Part.mk.injEq, heq_eq_eq, true_and] at hp
    exact hp.1
  have hT : GlobalTheory.TypeLeaf.TwistInv D := GlobalTheory.TypeLeaf.twistInv_of_charLaws_multOne D hCL hM
  have hz : ∀ τ : D.host.E →+* ℂ, ∀ z ∈ D.naut.infG D.naut.etaTinv τ,
      ∃ k : ℤ, z + ((-(D.R.t : ℝ) / 2 : ℝ) : ℂ) = (k : ℂ) := by
    intro τ z hz
    obtain ⟨m, hm⟩ := D.R.t_odd
    obtain ⟨h1, h2⟩ := hAut.2.1 τ
    rw [h2] at hz
    rcases h1 with h1 | h1 <;> rw [h1] at hz <;> simp at hz <;> subst hz
    · refine ⟨-(m : ℤ) - 1, ?_⟩
      rw [hm]; push_cast; ring
    · refine ⟨-(m : ℤ), ?_⟩
      rw [hm]; push_cast; ring
  have hP : GlobalTheory.TypeLeaf.PointPar D := GlobalTheory.TypeLeaf.pointPar_of_twist D hT hAut.1.1 hz
  intro i Sig hx hf hsq hc ρ hρ
  exact _root_.GlobalTheory.TypeLeaf.tameSum_of_inputs_alt D hW (GlobalTheory.T.firstCharacter_trivial_wildInertia_typePrime D) hGal hF hP i Sig hx
    (_root_.UpperTheory.GalS.fullLabS_of_fullLabS_trivial ⟨hf, fun k v => hL.2 k v _ (hf k v) (hsq k v) (DiscreteGroups.sglob.DzType.big_of_le_nV D k (by
      obtain ⟨π, rfl⟩ := hc
      rw [GlobalTheory.InertialTypesCmp.lpDim_isoLoc]
      simp [rankIso, Ranks.nV]))⟩) hc ρ hρ
end GlobalTheory.AdmTame
end
end
