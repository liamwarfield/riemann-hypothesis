module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTransport

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankCharacterEigenspaceInfKerLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeIdempotentLeOfEmbedsInRegular
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeIdempotentLeOfEmbedsInRegular
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

theorem finrank_range_idem_le_of_embReg : ∀ (K Γ V : Type) [Field K] [CharZero K] [Group Γ] [Finite Γ] [AddCommGroup V]
    [Module K V] (ρ : Representation K Γ V) (H : Subgroup Γ) (n : ℕ), EmbReg ρ H n → ∀ a : MonoidAlgebra K Γ,
    (∀ g, a.coeff g ≠ 0 → g ∈ H) → a * a = a → ∃ r : ℕ, (r : K) = (Nat.card H : K) * a.coeff 1 ∧
      finrank K (LinearMap.range (ρ.asAlgebraHom a)) ≤ n * r := by
  intro K Γ V _ _ _ _ _ _ ρ H n hE a ha hidem
  obtain ⟨j, hj, hjρ⟩ := hE
  classical
  let ψ := MonoidAlgebra.mapDomainAlgHom K K H.subtype
  have hψinj : Function.Injective ψ := MonoidAlgebra.mapDomain_injective Subtype.val_injective
  let a' : MonoidAlgebra K H :=
    MonoidAlgebra.ofCoeff (Finsupp.comapDomain Subtype.val a.coeff Subtype.val_injective.injOn)
  have hψa : ψ a' = a := by
    apply MonoidAlgebra.coeff_injective
    show Finsupp.mapDomain Subtype.val (Finsupp.comapDomain Subtype.val a.coeff Subtype.val_injective.injOn) = a.coeff
    apply Finsupp.mapDomain_comapDomain _ Subtype.val_injective
    intro g hg
    exact ⟨⟨g, ha g (by simpa using hg)⟩, rfl⟩
  have hidem' : a' * a' = a' := hψinj (by rw [map_mul, hψa, hidem])
  have hc1 : a'.coeff 1 = a.coeff 1 := rfl
  have key : ∀ (b : MonoidAlgebra K H) (v : V) (i : Fin n), j (ρ.asAlgebraHom (ψ b) v) i = b * j v i := by
    intro b
    induction b using MonoidAlgebra.induction_on with
    | of h =>
      intro v i
      have : ψ (MonoidAlgebra.of K H h) = MonoidAlgebra.of K Γ (h : Γ) := by
        simp [ψ]
      rw [this, Representation.asAlgebraHom_of, hjρ h v i]
      rfl
    | add b c hb hc => intro v i; simp [map_add (f := _), LinearMap.add_apply, hb, hc, add_mul]
    | smul r b hb => intro v i; simp [map_smul, LinearMap.smul_apply, hb, smul_mul_assoc]
  refine ⟨finrank K (LinearMap.range (LinearMap.mulLeft K a')), ?_, ?_⟩
  · rw [GlobalTheory.T.finrank_range_mulLeft_idempotent_groupAlgebra K H a' hidem', hc1]
  · let R := LinearMap.range (LinearMap.mulLeft K a')
    let g : LinearMap.range (ρ.asAlgebraHom a) →ₗ[K] (Fin n → R) :=
      LinearMap.pi fun i => LinearMap.codRestrict R
        ((LinearMap.proj i).comp (j.comp (LinearMap.range (ρ.asAlgebraHom a)).subtype)) (by
          rintro ⟨x, v, rfl⟩
          refine ⟨j v i, ?_⟩
          simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.proj_apply, LinearMap.mulLeft_apply]
          rw [← hψa, key])
    have hg : Function.Injective g := by
      intro x y hxy
      apply Subtype.val_injective
      apply hj
      funext i
      have := congrArg (fun f => ((f i : R) : MonoidAlgebra K H)) hxy
      simpa [g] using this
    have := LinearMap.finrank_le_finrank_of_injective hg
    rw [Module.finrank_pi_fintype] at this
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using this

end GlobalTheory.BadCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeIdempotentLeOfEmbedsInRegularStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_range_idempotent_le_of_embedsInRegular : ∀ (K Γ V : Type) [Field K] [CharZero K] [Group Γ] [Finite Γ] [AddCommGroup V] [Module K V] (ρ : Representation K Γ V) (H : Subgroup Γ) (n : ℕ), EmbReg ρ H n → ∀ a : MonoidAlgebra K Γ, (∀ g, a.coeff g ≠ 0 → g ∈ H) → a * a = a → ∃ r : ℕ, (r : K) = (Nat.card H : K) * a.coeff 1 ∧ finrank K (LinearMap.range (ρ.asAlgebraHom a)) ≤ n * r := by
  first | exact @GlobalTheory.BadCount.finrank_range_idem_le_of_embReg | exact GlobalTheory.BadCount.finrank_range_idem_le_of_embReg | (intros; apply GlobalTheory.BadCount.finrank_range_idem_le_of_embReg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankCharacterEigenspaceInfKerLe
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

theorem lvlIdem_apply_of_mem_eig {Γ V : Type} [Group Γ] [Fintype Γ] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Γ V) (Hb : Subgroup Γ) (lam : Hb →* ℂˣ) (x : V) (hx : x ∈ eig ρ Hb lam) :
    ρ.asAlgebraHom (Formalism.L2.DIV.lvlIdem Hb lam) x = x := by
  classical
  rw [mem_eig] at hx
  have hc : (Nat.card Hb : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  unfold Formalism.L2.DIV.lvlIdem
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, LinearMap.sum_apply]
  simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply, hx, smul_smul]
  have e1 : ∀ h : Hb, (Nat.card Hb : ℂ)⁻¹ * ((lam h⁻¹ : ℂˣ) : ℂ) * ((lam h : ℂˣ) : ℂ) = (Nat.card Hb : ℂ)⁻¹ := fun h => by
    rw [mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, mul_one]
  simp only [e1, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem finrank_eig_inf_ker_le : ∀ (Γ V : Type) [Group Γ] [Fintype Γ] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ Γ V) (Hb : Subgroup Γ) (lam : Hb →* ℂˣ) (H : Fin 2 → Subgroup Γ) (n : Fin 2 → ℕ) (e : MonoidAlgebra ℂ Γ) (b : Fin 2 → MonoidAlgebra ℂ Γ) (s : Fin 2 → ℝ) (c : ℝ), (∀ k, EmbReg ρ (H k) (n k)) → (∀ k, (n k : ℝ) * Nat.card (H k) ≤ c * Nat.card Hb * finrank ℂ (eig ρ Hb lam)) → (∀ k, b k * b k = b k) → (∀ k, b k * Formalism.L2.DIV.lvlIdem Hb lam = Formalism.L2.DIV.lvlIdem Hb lam * b k) → 1 - e = b 0 + b 1 - b 0 * b 1 → (∀ k g, (b k * Formalism.L2.DIV.lvlIdem Hb lam).coeff g ≠ 0 → g ∈ H k) → (∀ k, (b k * Formalism.L2.DIV.lvlIdem Hb lam).coeff 1 = (s k : ℂ) / (Nat.card Hb : ℂ)) → (finrank ℂ (eig ρ Hb lam ⊓ LinearMap.ker (ρ.asAlgebraHom e) : Submodule ℂ V) : ℝ) ≤ c * (s 0 + s 1) * finrank ℂ (eig ρ Hb lam) := by
  intro Γ V _ _ _ _ _ ρ Hb lam H n e b s c hemb hcard hidem hcomm he hsupp hcoeff
  set p := Formalism.L2.DIV.lvlIdem Hb lam with hp
  set W : Submodule ℂ V := eig ρ Hb lam ⊓ LinearMap.ker (ρ.asAlgebraHom e) with hW
  let f : W →ₗ[ℂ] LinearMap.range (ρ.asAlgebraHom (b 0 * p)) × LinearMap.range (ρ.asAlgebraHom (b 1 * p)) :=
    ((ρ.asAlgebraHom (b 0 * p)).rangeRestrict.comp W.subtype).prod
      ((ρ.asAlgebraHom (b 1 * p)).rangeRestrict.comp W.subtype)
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, hxe, hxk⟩ hx0
    have h0 : ρ.asAlgebraHom (b 0 * p) x = 0 := by
      have := congrArg (fun z => ((z.1 : _) : V)) hx0; simpa [f] using this
    have h1 : ρ.asAlgebraHom (b 1 * p) x = 0 := by
      have := congrArg (fun z => ((z.2 : _) : V)) hx0; simpa [f] using this
    have hpx : ρ.asAlgebraHom p x = x := lvlIdem_apply_of_mem_eig ρ Hb lam x hxe
    have hb : ∀ k, ρ.asAlgebraHom (b k) x = ρ.asAlgebraHom (b k * p) x := fun k => by
      rw [map_mul, Module.End.mul_apply, hpx]
    have hb0 : ρ.asAlgebraHom (b 0) x = 0 := (hb 0).trans h0
    have hb1 : ρ.asAlgebraHom (b 1) x = 0 := (hb 1).trans h1
    have hek : ρ.asAlgebraHom e x = 0 := hxk
    have hx1 : x = ρ.asAlgebraHom (1 - e) x := by
      rw [map_sub, map_one, LinearMap.sub_apply, hek, sub_zero]; rfl
    have : x = 0 := by
      rw [hx1, he, map_sub, map_add (f := _), map_mul]
      simp [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, hb0, hb1]
    exact Subtype.ext this
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod] at hdim
  have hbnd : ∀ k, (finrank ℂ (LinearMap.range (ρ.asAlgebraHom (b k * p))) : ℝ) ≤
      c * s k * finrank ℂ (eig ρ Hb lam) := by
    intro k
    have hid : b k * p * (b k * p) = b k * p := by
      calc b k * p * (b k * p) = b k * (p * b k) * p := by simp only [mul_assoc]
        _ = b k * (b k * p) * p := by rw [hcomm k]
        _ = (b k * b k) * (p * p) := by simp only [mul_assoc]
        _ = b k * p := by rw [hidem k, Formalism.L2.DIV.lvlIdem_idem]
    obtain ⟨r, hr, hle⟩ := GlobalTheory.T.finrank_range_idempotent_le_of_embedsInRegular ℂ Γ V ρ (H k) (n k) (hemb k) (b k * p) (hsupp k) hid
    rw [hcoeff k] at hr
    have hHb : (0 : ℝ) < Nat.card Hb := by exact_mod_cast Nat.card_pos
    have hH : (0 : ℝ) < Nat.card (H k) := by exact_mod_cast Nat.card_pos
    have hrR : (r : ℝ) * Nat.card Hb = Nat.card (H k) * s k := by
      have hHbC : (Nat.card Hb : ℂ) ≠ 0 := by exact_mod_cast hHb.ne'
      have : ((r : ℝ) * Nat.card Hb : ℝ) = ((Nat.card (H k) * s k : ℝ) : ℂ) := by
        push_cast; rw [hr]; field_simp
      exact_mod_cast this
    have hs : 0 ≤ s k := by
      have : 0 ≤ (Nat.card (H k) : ℝ) * s k := by rw [← hrR]; positivity
      exact le_of_mul_le_mul_left (by simpa using this) hH
    have hd : (0 : ℝ) ≤ finrank ℂ (eig ρ Hb lam) := by positivity
    have hleR : (finrank ℂ (LinearMap.range (ρ.asAlgebraHom (b k * p))) : ℝ) ≤ n k * r := by exact_mod_cast hle
    have key : ((n k : ℝ) * r) * Nat.card Hb ≤ (c * s k * finrank ℂ (eig ρ Hb lam)) * Nat.card Hb := by
      calc ((n k : ℝ) * r) * Nat.card Hb = ((n k : ℝ) * Nat.card (H k)) * s k := by rw [mul_assoc, hrR]; ring
        _ ≤ (c * Nat.card Hb * finrank ℂ (eig ρ Hb lam)) * s k := mul_le_mul_of_nonneg_right (hcard k) hs
        _ = (c * s k * finrank ℂ (eig ρ Hb lam)) * Nat.card Hb := by ring
    exact hleR.trans (le_of_mul_le_mul_right key hHb)
  have hdimR : (finrank ℂ W : ℝ) ≤ (finrank ℂ (LinearMap.range (ρ.asAlgebraHom (b 0 * p))) : ℝ) +
      finrank ℂ (LinearMap.range (ρ.asAlgebraHom (b 1 * p))) := by exact_mod_cast hdim
  calc (finrank ℂ W : ℝ) ≤ _ := hdimR
    _ ≤ c * s 0 * finrank ℂ (eig ρ Hb lam) + c * s 1 * finrank ℂ (eig ρ Hb lam) := add_le_add (hbnd 0) (hbnd 1)
    _ = c * (s 0 + s 1) * finrank ℂ (eig ρ Hb lam) := by ring

end GlobalTheory.BadCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankCharacterEigenspaceInfKerLeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_characterEigenspace_inf_ker_le : ∀ (Γ V : Type) [Group Γ] [Fintype Γ] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ Γ V) (Hb : Subgroup Γ) (lam : Hb →* ℂˣ) (H : Fin 2 → Subgroup Γ) (n : Fin 2 → ℕ) (e : MonoidAlgebra ℂ Γ) (b : Fin 2 → MonoidAlgebra ℂ Γ) (s : Fin 2 → ℝ) (c : ℝ), (∀ k, EmbReg ρ (H k) (n k)) → (∀ k, (n k : ℝ) * Nat.card (H k) ≤ c * Nat.card Hb * finrank ℂ (eig ρ Hb lam)) → (∀ k, b k * b k = b k) → (∀ k, b k * Formalism.L2.DIV.lvlIdem Hb lam = Formalism.L2.DIV.lvlIdem Hb lam * b k) → 1 - e = b 0 + b 1 - b 0 * b 1 → (∀ k g, (b k * Formalism.L2.DIV.lvlIdem Hb lam).coeff g ≠ 0 → g ∈ H k) → (∀ k, (b k * Formalism.L2.DIV.lvlIdem Hb lam).coeff 1 = (s k : ℂ) / (Nat.card Hb : ℂ)) → (finrank ℂ (eig ρ Hb lam ⊓ LinearMap.ker (ρ.asAlgebraHom e) : Submodule ℂ V) : ℝ) ≤ c * (s 0 + s 1) * finrank ℂ (eig ρ Hb lam) := by
  first | exact @GlobalTheory.BadCount.finrank_eig_inf_ker_le | exact GlobalTheory.BadCount.finrank_eig_inf_ker_le | (intros; apply GlobalTheory.BadCount.finrank_eig_inf_ker_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEigenInfKerLeOfSemidirectSplit
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

noncomputable section

namespace GlobalTheory.BadCount.Lift

open scoped Classical

variable {G Γ : Type} [Group G] [Group Γ]

theorem isSplit_injective {π : Γ →* G} {ι : G →* Γ} (h : IsSplit π ι) : Function.Injective ι := by
  intro a b hab
  have := congrArg π hab
  rwa [h.1, h.1] at this

theorem inv_mul_mem_ker {π : Γ →* G} {ι : G →* Γ} (h : IsSplit π ι) (γ : Γ) :
    (ι (π γ))⁻¹ * γ ∈ π.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, h.1, inv_mul_cancel]

theorem commute_single {π : Γ →* G} {ι : G →* Γ} (h : IsSplit π ι) (x : MonoidAlgebra ℂ G)
    (r : Γ) (hr : r ∈ π.ker) (c : ℂ) :
    Commute (MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι x) (MonoidAlgebra.single r c) := by
  refine MonoidAlgebra.induction_on (motive := fun x =>
    Commute (MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι x) (MonoidAlgebra.single r c)) x ?_ ?_ ?_
  · intro m
    show _ * _ = _ * _
    simp [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, h.2 m r hr]
  · intro x y hx hy
    rw [map_add (f := _)]
    exact hx.add_left hy
  · intro a x hx
    rw [map_smul]
    exact hx.smul_left a

theorem asAlgebraHom_map {V : Type} [AddCommGroup V] [Module ℂ V] (ι : G →* Γ)
    (ρ : Representation ℂ Γ V) (e : MonoidAlgebra ℂ G) :
    ρ.asAlgebraHom (MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι e) =
      Representation.asAlgebraHom (ρ.comp ι : Representation ℂ G V) e := by
  refine MonoidAlgebra.induction_on (motive := fun e =>
    ρ.asAlgebraHom (MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι e) =
      Representation.asAlgebraHom (ρ.comp ι : Representation ℂ G V) e) e ?_ ?_ ?_
  · intro m
    simp [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single]
  · intro x y hx hy
    rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  · intro a x hx
    rw [map_smul, map_smul, map_smul, hx]

variable [Fintype Γ]

def eR (π : Γ →* G) : MonoidAlgebra ℂ Γ :=
  ∑ r : π.ker, MonoidAlgebra.single (r : Γ) ((Nat.card π.ker : ℂ)⁻¹)

theorem coeff_map_mul_eR {π : Γ →* G} {ι : G →* Γ} (h : IsSplit π ι) (x : MonoidAlgebra ℂ G)
    (γ : Γ) :
    (MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι x * eR π).coeff γ =
      x.coeff (π γ) * (Nat.card π.ker : ℂ)⁻¹ := by
  unfold eR
  rw [Finset.mul_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp_rw [MonoidAlgebra.mul_single_apply]
  let r0 : π.ker := ⟨(ι (π γ))⁻¹ * γ, inv_mul_mem_ker h γ⟩
  have key : ∀ r : π.ker, (MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι x).coeff (γ * (r : Γ)⁻¹) =
      if r = r0 then x.coeff (π γ) else 0 := by
    intro r
    rw [MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.coeff_mapDomain]
    split_ifs with hr
    · have : γ * (r : Γ)⁻¹ = ι (π γ) := by
        subst hr
        simp [r0]
      rw [this, Finsupp.mapDomain_apply_of_injective (isSplit_injective h)]
    · apply Finsupp.mapDomain_notin_range
      rintro ⟨g, hg⟩
      apply hr
      have hr1 : π (r : Γ) = 1 := r.2
      have hg' : g = π γ := by
        have := congrArg π hg
        rwa [h.1, map_mul, map_inv, hr1, inv_one, mul_one] at this
      subst hg'
      apply Subtype.ext
      show (r : Γ) = (ι (π γ))⁻¹ * γ
      rw [hg]
      group
  simp_rw [key, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

def comapEquiv {π : Γ →* G} {ι : G →* Γ} (h : IsSplit π ι) (P : Subgroup G) :
    P × π.ker ≃ P.comap π where
  toFun x := ⟨ι x.1 * x.2, by
    have hr1 : π (x.2 : Γ) = 1 := x.2.2
    simp [Subgroup.mem_comap, h.1, hr1]⟩
  invFun γ := (⟨π γ, γ.2⟩, ⟨(ι (π γ))⁻¹ * γ, inv_mul_mem_ker h γ⟩)
  left_inv x := by
    have hr1 : π (x.2 : Γ) = 1 := x.2.2
    ext <;> simp [h.1, hr1]
  right_inv γ := by
    ext
    simp

theorem card_comap {π : Γ →* G} {ι : G →* Γ} (h : IsSplit π ι) (P : Subgroup G) :
    Nat.card (P.comap π) = Nat.card P * Nat.card π.ker := by
  rw [← Nat.card_prod]
  exact (Nat.card_congr (comapEquiv h P)).symm

end GlobalTheory.BadCount.Lift

namespace GlobalTheory.BadCount.Lift

open scoped Classical

variable {G Γ : Type} [Group G] [Group Γ] [Fintype Γ]

theorem lvlIdem_comap [Fintype G] {π : Γ →* G} {ι : G →* Γ} (h : IsSplit π ι) (P : Subgroup G)
    (lam : P →* ℂˣ) (lamb : P.comap π →* ℂˣ) (hl : ∀ γ : P.comap π, lamb γ = lam ⟨π γ, γ.2⟩) :
    Formalism.L2.DIV.lvlIdem (P.comap π) lamb =
      MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι (Formalism.L2.DIV.lvlIdem P lam) * eR π := by
  have hcard := card_comap h P
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.L2.DIV.lvlIdem, eR, map_sum, MonoidAlgebra.mapDomainAlgHom_apply,
    MonoidAlgebra.mapDomain_single, Finset.sum_mul_sum, MonoidAlgebra.single_mul_single]
  rw [← Fintype.sum_prod_type' (f := fun (i : P) (j : π.ker) =>
    MonoidAlgebra.single (ι (i : G) * (j : Γ))
      ((Nat.card P : ℂ)⁻¹ * ((lam i⁻¹ : ℂˣ) : ℂ) * (Nat.card π.ker : ℂ)⁻¹))]
  refine (Fintype.sum_equiv (comapEquiv h P) _ _ (fun x => ?_)).symm
  have hr1 : π (x.2 : Γ) = 1 := x.2.2
  have hx : lamb ((comapEquiv h P) x)⁻¹ = lam x.1⁻¹ := by
    rw [hl]
    congr 1
    apply Subtype.ext
    simp [comapEquiv, h.1, hr1]
  simp only [hx, hcard, Nat.cast_mul, mul_inv]
  congr 1
  ring

end GlobalTheory.BadCount.Lift


open scoped Classical in
theorem GlobalTheory.BadCount.finrank_eig_inf_ker_le_of_isSplit : ∀ (G Γ V : Type) [Group G] [Fintype G] [Group Γ] [Fintype Γ] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (π : Γ →* G) (ι : G →* Γ), IsSplit π ι → ∀ (ρ : Representation ℂ Γ V) (P : Subgroup G) (lam : P →* ℂˣ) (lamb : P.comap π →* ℂˣ), (∀ γ : P.comap π, lamb γ = lam ⟨π γ, γ.2⟩) → ∀ (H : Fin 2 → Subgroup G) (n : Fin 2 → ℕ) (e : MonoidAlgebra ℂ G) (b : Fin 2 → MonoidAlgebra ℂ G) (s : Fin 2 → ℝ) (c : ℝ), (∀ k, EmbReg ρ ((H k).comap π) (n k)) → (∀ k, (n k : ℝ) * Nat.card ((H k).comap π) ≤ c * Nat.card (P.comap π) * finrank ℂ (eig ρ (P.comap π) lamb)) → (∀ k, b k * b k = b k) → (∀ k a, b k * a = a * b k) → 1 - e = b 0 + b 1 - b 0 * b 1 → (∀ k g, (b k * Formalism.L2.DIV.lvlIdem P lam).coeff g ≠ 0 → g ∈ H k) → (∀ k, (b k * Formalism.L2.DIV.lvlIdem P lam).coeff 1 = (s k : ℂ) / (Nat.card P : ℂ)) → (finrank ℂ (eig ρ (P.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp ι : Representation ℂ G V) e) : Submodule ℂ V) : ℝ) ≤ c * (s 0 + s 1) * finrank ℂ (eig ρ (P.comap π) lamb) := by
  intro G Γ V _ _ _ _ _ _ _ π ι h ρ P lam lamb hl H n e b s c hEmb hcard hidem hcent hsum hsupp hcoeff
  let ιA := MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι
  have hL := GlobalTheory.BadCount.Lift.lvlIdem_comap h P lam lamb hl
  have hR : (Nat.card π.ker : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hP : (Nat.card P : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hprod : ∀ k, ιA (b k) * Formalism.L2.DIV.lvlIdem (P.comap π) lamb =
      ιA (b k * Formalism.L2.DIV.lvlIdem P lam) * GlobalTheory.BadCount.Lift.eR π := by
    intro k
    rw [hL, map_mul, mul_assoc]
  have hco : ∀ k γ, (ιA (b k) * Formalism.L2.DIV.lvlIdem (P.comap π) lamb).coeff γ =
      (b k * Formalism.L2.DIV.lvlIdem P lam).coeff (π γ) * (Nat.card π.ker : ℂ)⁻¹ := by
    intro k γ
    rw [hprod]
    exact GlobalTheory.BadCount.Lift.coeff_map_mul_eR h _ γ
  have key := GlobalTheory.T.finrank_characterEigenspace_inf_ker_le Γ V ρ (P.comap π) lamb (fun k => (H k).comap π) n (ιA e) (fun k => ιA (b k)) s c
    hEmb hcard
    (fun k => by rw [← map_mul, hidem])
    (fun k => by
      rw [hL]
      refine Commute.mul_right ?_ ?_
      · exact Commute.map (show Commute (b k) (Formalism.L2.DIV.lvlIdem P lam) from hcent k _) ιA
      · unfold GlobalTheory.BadCount.Lift.eR
        refine Commute.sum_right _ _ _ (fun r _ => ?_)
        exact GlobalTheory.BadCount.Lift.commute_single h _ r r.2 _)
    (by rw [← map_one ιA, ← map_sub, hsum, map_sub, map_add (f := _), map_mul])
    (fun k γ hne => by
      rw [hco] at hne
      show π γ ∈ H k
      apply hsupp k
      intro h0
      apply hne
      rw [h0, zero_mul])
    (fun k => by
      rw [hco, map_one, hcoeff, GlobalTheory.BadCount.Lift.card_comap h P, Nat.cast_mul]
      field_simp)
  rwa [GlobalTheory.BadCount.Lift.asAlgebraHom_map] at key
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEigenInfKerLeOfSemidirectSplitStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_eigen_inf_ker_le_of_semidirect_split : ∀ (G Γ V : Type) [Group G] [Fintype G] [Group Γ] [Fintype Γ] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (π : Γ →* G) (ι : G →* Γ), IsSplit π ι → ∀ (ρ : Representation ℂ Γ V) (P : Subgroup G) (lam : P →* ℂˣ) (lamb : P.comap π →* ℂˣ), (∀ γ : P.comap π, lamb γ = lam ⟨π γ, γ.2⟩) → ∀ (H : Fin 2 → Subgroup G) (n : Fin 2 → ℕ) (e : MonoidAlgebra ℂ G) (b : Fin 2 → MonoidAlgebra ℂ G) (s : Fin 2 → ℝ) (c : ℝ), (∀ k, EmbReg ρ ((H k).comap π) (n k)) → (∀ k, (n k : ℝ) * Nat.card ((H k).comap π) ≤ c * Nat.card (P.comap π) * finrank ℂ (eig ρ (P.comap π) lamb)) → (∀ k, b k * b k = b k) → (∀ k a, b k * a = a * b k) → 1 - e = b 0 + b 1 - b 0 * b 1 → (∀ k g, (b k * Formalism.L2.DIV.lvlIdem P lam).coeff g ≠ 0 → g ∈ H k) → (∀ k, (b k * Formalism.L2.DIV.lvlIdem P lam).coeff 1 = (s k : ℂ) / (Nat.card P : ℂ)) → (finrank ℂ (eig ρ (P.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp ι : Representation ℂ G V) e) : Submodule ℂ V) : ℝ) ≤ c * (s 0 + s 1) * finrank ℂ (eig ρ (P.comap π) lamb) := by
  first | exact @GlobalTheory.BadCount.finrank_eig_inf_ker_le_of_isSplit | exact GlobalTheory.BadCount.finrank_eig_inf_ker_le_of_isSplit | (intros; apply GlobalTheory.BadCount.finrank_eig_inf_ker_le_of_isSplit <;> assumption)
end
