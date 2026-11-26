module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PSurjF

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNG
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNF
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNE
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdND
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNC
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNB
noncomputable section

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

theorem oSmulW {W : Type*} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (o : 𝓞 E) (w : W) : o • w = (o : E) • w := by
  first
  | exact (algebraMap_smul E o w).symm
  | rfl
  | simp [Algebra.smul_def]

private theorem coe_ne_zero_of_ne_zero (o : 𝓞 E) (h : o ≠ 0) : (o : E) ≠ 0 := by
  intro h'
  apply h
  first
  | exact_mod_cast h'
  | exact RingOfIntegers.ext h'
  | simpa using h'

private theorem inv_smul_apply_smul_eq_of_smul_mem {W : Type*} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (P : Submodule (𝓞 E) S.V) (f : P →ₗ[𝓞 E] W) (u : S.V) (a b : 𝓞 E) (ha : a ≠ 0) (hb : b ≠ 0)
    (hau : a • u ∈ P) (hbu : b • u ∈ P) :
    ((a : E))⁻¹ • f ⟨a • u, hau⟩ = ((b : E))⁻¹ • f ⟨b • u, hbu⟩ := by
  have ha' := coe_ne_zero_of_ne_zero a ha
  have hb' := coe_ne_zero_of_ne_zero b hb
  have h1 : (b : E) • f ⟨a • u, hau⟩ = (a : E) • f ⟨b • u, hbu⟩ := by
    rw [← oSmulW, ← oSmulW, ← map_smul, ← map_smul]
    congr 1
    apply Subtype.ext
    exact smul_comm b a u
  calc ((a : E))⁻¹ • f ⟨a • u, hau⟩ = (((a : E))⁻¹ * ((b : E))⁻¹) • ((b : E) • f ⟨a • u, hau⟩) := by
        rw [smul_smul, mul_assoc, inv_mul_cancel₀ hb', mul_one]
    _ = (((a : E))⁻¹ * ((b : E))⁻¹) • ((a : E) • f ⟨b • u, hbu⟩) := by rw [h1]
    _ = ((b : E))⁻¹ • f ⟨b • u, hbu⟩ := by
        rw [smul_smul, mul_comm ((a : E))⁻¹, mul_assoc, inv_mul_cancel₀ ha', mul_one]

theorem ext_lat {W : Type*} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (U : Submodule E S.V) (P : Submodule (𝓞 E) S.V) (hPU : ∀ x ∈ P, x ∈ U)
    (hfull : ∀ u ∈ U, ∃ d : 𝓞 E, d ≠ 0 ∧ d • u ∈ P) (f : P →ₗ[𝓞 E] W) :
    ∃ F : U →ₗ[E] W, ∀ (x : S.V) (hx : x ∈ P), F ⟨x, hPU x hx⟩ = f ⟨x, hx⟩ := by
  classical
  choose d hd0 hdP using hfull
  have hmul : ∀ (u : S.V) (a b : 𝓞 E), a • u ∈ P → (b * a) • u ∈ P := by
    intro u a b h
    rw [mul_smul]
    exact P.smul_mem b h
  have hal : ∀ o : 𝓞 E, algebraMap (𝓞 E) E o = (o : E) := fun o => by first | rfl | simp
  refine ⟨{ toFun := fun x => ((d x.1 x.2 : E))⁻¹ • f ⟨d x.1 x.2 • x.1, hdP x.1 x.2⟩,
            map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    have e0 : d y.1 y.2 * d x.1 x.2 ≠ 0 := mul_ne_zero (hd0 _ _) (hd0 _ _)
    have hex : (d y.1 y.2 * d x.1 x.2) • x.1 ∈ P := hmul _ _ _ (hdP x.1 x.2)
    have hey : (d y.1 y.2 * d x.1 x.2) • y.1 ∈ P := by
      rw [mul_comm]
      exact hmul _ _ _ (hdP y.1 y.2)
    have hexy : (d y.1 y.2 * d x.1 x.2) • (x + y).1 ∈ P := by
      rw [Submodule.coe_add, smul_add]
      exact P.add_mem hex hey
    rw [inv_smul_apply_smul_eq_of_smul_mem S P f (x + y).1 _ _ (hd0 _ _) e0 (hdP _ _) hexy,
      inv_smul_apply_smul_eq_of_smul_mem S P f x.1 _ _ (hd0 _ _) e0 (hdP _ _) hex,
      inv_smul_apply_smul_eq_of_smul_mem S P f y.1 _ _ (hd0 _ _) e0 (hdP _ _) hey, ← smul_add, ← map_add]
    congr 2
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_add, smul_add]
  · intro c x
    simp only [RingHom.id_apply]
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq' := coe_ne_zero_of_ne_zero q hq0
    have ha' := coe_ne_zero_of_ne_zero _ (hd0 x.1 x.2)
    have e0 : q * d x.1 x.2 ≠ 0 := mul_ne_zero hq0 (hd0 _ _)
    have hcq : (q * d x.1 x.2) • ((algebraMap (𝓞 E) E p / algebraMap (𝓞 E) E q) • x.1) =
        p • (d x.1 x.2 • x.1) := by
      rw [oSmulW, oSmulW, oSmulW (o := d x.1 x.2), smul_smul, smul_smul, hal, hal]
      congr 1
      push_cast
      field_simp
    have hmem : (q * d x.1 x.2) • (((algebraMap (𝓞 E) E p / algebraMap (𝓞 E) E q) • x : U) : S.V) ∈ P := by
      rw [Submodule.coe_smul, hcq]
      exact P.smul_mem p (hdP x.1 x.2)
    rw [inv_smul_apply_smul_eq_of_smul_mem S P f _ _ _ (hd0 _ _) e0 (hdP _ _) hmem]
    have hsub : (⟨(q * d x.1 x.2) • (((algebraMap (𝓞 E) E p / algebraMap (𝓞 E) E q) • x : U) : S.V), hmem⟩ : P) =
        p • ⟨d x.1 x.2 • x.1, hdP x.1 x.2⟩ := by
      apply Subtype.ext
      simp only [Submodule.coe_smul]
      exact hcq
    rw [hsub, map_smul, oSmulW (o := p), smul_smul, smul_smul, hal, hal]
    congr 1
    push_cast
    field_simp
  · intro x hx
    have h1 : (1 : 𝓞 E) • x ∈ P := by
      rw [one_smul]
      exact hx
    refine (inv_smul_apply_smul_eq_of_smul_mem S P f x _ 1 (hd0 _ _) one_ne_zero (hdP _ _) h1).trans ?_
    have h2 : (⟨(1 : 𝓞 E) • x, h1⟩ : P) = ⟨x, hx⟩ := Subtype.ext (one_smul _ x)
    rw [h2]
    simp

theorem ext_top {W : Type*} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (P : Submodule (𝓞 E) S.V) (hfull : ∀ u : S.V, ∃ d : 𝓞 E, d ≠ 0 ∧ d • u ∈ P) (f : P →ₗ[𝓞 E] W) :
    ∃ F : S.V →ₗ[E] W, ∀ (x : S.V) (hx : x ∈ P), F x = f ⟨x, hx⟩ := by
  obtain ⟨G, hG⟩ := ext_lat S ⊤ P (fun _ _ => Submodule.mem_top) (fun u _ => hfull u) f
  refine ⟨G.comp (LinearMap.codRestrict ⊤ LinearMap.id (fun _ => Submodule.mem_top)), fun x hx => ?_⟩
  exact hG x hx

theorem dual_sum (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) (hSD : SD S Λ) (U : Submodule E S.V)
    (v : S.V) (hv : ∀ m ∈ Λ, m ∈ U → IsIntegral ℤ (S.hT m v)) : ∃ w ∈ Λ, v - w ∈ orth S U := by
  have hfull : ∀ u : S.V, ∃ d : 𝓞 E, d ≠ 0 ∧ d • u ∈ Λ := by
    intro u
    obtain ⟨s, hs⟩ := hΛ.fg
    obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) s (fun x => S.hT x u)
    let P : Submodule (𝓞 E) S.V := {
      carrier := {x | IsIntegral ℤ (((a : 𝓞 E) : E) * S.hT x u)}
      zero_mem' := by simpa using (isIntegral_zero : IsIntegral ℤ (0 : E))
      add_mem' := by
        intro x y hx hy
        simpa [map_add, LinearMap.add_apply, mul_add] using hx.add hy
      smul_mem' := by
        intro c x hx
        have hc : IsIntegral ℤ (star (c : E)) := isInt_star c.2
        have := hc.mul hx
        change IsIntegral ℤ (((a : 𝓞 E) : E) * S.hT (c • x) u)
        rw [oSmul, hT_smulL]
        convert this using 1 <;> ring }
    have hsP : (s : Set S.V) ⊆ P := by
      intro x hx
      obtain ⟨b, hb⟩ := ha x hx
      change IsIntegral ℤ (((a : 𝓞 E) : E) * S.hT x u)
      rw [← show (b : E) = ((a : 𝓞 E) : E) * S.hT x u by simpa [Algebra.smul_def] using hb]
      exact b.2
    refine ⟨a, nonZeroDivisors.ne_zero a.2, ?_⟩
    apply (hSD _).2
    intro x hx
    have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
    change IsIntegral ℤ (((a : 𝓞 E) : E) * S.hT x u) at hxP
    rw [oSmul, map_smul, smul_eq_mul]
    exact hxP
  obtain ⟨π, hπ, hπU⟩ := retract S Λ hΛ.fg U
  let g : Λ →ₗ[𝓞 E] E := ((S.hT v).restrictScalars (𝓞 E)) ∘ₗ π
  obtain ⟨G, hG⟩ := ext_top S (W := E) Λ (fun u => hfull u) g
  obtain ⟨w, hw⟩ := riesz S G
  have hgw : ∀ (m : S.V) (hm : m ∈ Λ), S.hT m w = star (S.hT v (π ⟨m, hm⟩)) := fun m hm => by
    rw [hsw S w m, hw, hG m hm]
    rfl
  refine ⟨w, (hSD w).2 fun y hy => ?_, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).2 fun u hu => ?_⟩
  · rw [hgw y hy, hsw S (π ⟨y, hy⟩) v, star_star]
    exact hv _ (hπ ⟨y, hy⟩).1 (hπ ⟨y, hy⟩).2
  · have hm : ∀ m ∈ Λ, m ∈ U → S.hT m (v - w) = 0 := fun m hmΛ hmU => by
      rw [map_sub, hgw m hmΛ, hπU ⟨m, hmΛ⟩ hmU, hsw S m v, star_star]
      simp
    obtain ⟨d, hd, hdu⟩ := hfull u
    have h1 := hm _ hdu (by rw [oSmul]; exact U.smul_mem _ hu)
    rw [oSmul, hT_smulL] at h1
    have hd' : star ((d : E)) ≠ 0 := by
      rw [star_ne_zero]; exact coe_ne_zero hd
    exact (mul_eq_zero.1 h1).resolve_left hd'

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA
end
end

noncomputable section

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

theorem X_le_orth (X : Submodule E S.V) (hXiso : ∀ x ∈ X, ∀ y ∈ X, S.hT x y = 0) : X ≤ orth S X :=
  fun x hx => (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).2 fun y hy => hXiso y hy x hx

theorem orth_X {X : Submodule E S.V} {u x : S.V} (hu : u ∈ orth S X) (hx : x ∈ X) : S.hT x u = 0 :=
  (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).1 hu x hx

theorem orth_X' {X : Submodule E S.V} {u x : S.V} (hu : u ∈ orth S X) (hx : x ∈ X) : S.hT u x = 0 := by
  rw [hsw S x u, orth_X S hu hx, star_zero]

theorem stepB (X : Submodule E S.V) (hXiso : ∀ x ∈ X, ∀ y ∈ X, S.hT x y = 0) (z : S.V) (hzX : z ∈ orth S X)
    (Λ Λ₂ : Submodule (𝓞 E) S.V) (hΛ₂ : Submodule.IsLattice E Λ₂) (hSD₂ : SD S Λ₂)
    (hX : ∀ x ∈ X, x ∈ Λ₂ → x ∈ Λ) (hz : z ∈ Λ) (hz₂ : z ∈ Λ₂)
    (hL : ∀ x ∈ Λ₂, x ∈ orth S X → ∃ y ∈ Λ, y - x ∈ X)
    (hy : ∃ y ∈ Λ₂, y ∈ orth S X ∧ S.hT y z = 1) :
    ∃ A : orth S X →ₗ[E] S.V, (∀ u, A u ∈ X) ∧ (∀ u : orth S X, (u : S.V) ∈ X → A u = 0) ∧
      A ⟨z, hzX⟩ = 0 ∧ ∀ (x : S.V) (hx : x ∈ orth S X), x ∈ Λ₂ → x + A ⟨x, hx⟩ ∈ Λ := by
  classical
  obtain ⟨y, hyΛ, hyX, hyz⟩ := hy
  let M₂ : Submodule (𝓞 E) S.V := Λ₂ ⊓ (orth S X).restrictScalars (𝓞 E)
  have hM₂fg : M₂.FG := Submodule.FG.of_le hΛ₂.fg inf_le_left
  have hXo := X_le_orth S X hXiso
  obtain ⟨δ, hδX, hδ0, hδΛ⟩ := glift S M₂ Λ hM₂fg X X (fun x hx hxX => hX x hxX hx.1)
    (fun x hx => hL x hx.1 hx.2)
  let z₂ : M₂ := ⟨z, hz₂, hzX⟩
  let κ : M₂ →ₗ[𝓞 E] E := ((S.hT y).restrictScalars (𝓞 E)) ∘ₗ M₂.subtype
  let δ' : M₂ →ₗ[𝓞 E] S.V := δ - κ.smulRight (δ z₂)
  have hδ'app : ∀ m, δ' m = δ m - S.hT y m • δ z₂ := fun m => rfl
  have hδ'X : ∀ m, δ' m ∈ X := fun m => by
    rw [hδ'app]; exact X.sub_mem (hδX m) (X.smul_mem _ (hδX z₂))
  have hδ'0 : ∀ m : M₂, (m : S.V) ∈ X → δ' m = 0 := fun m hm => by
    rw [hδ'app, hδ0 m hm, orth_X' S hyX hm, zero_smul, sub_zero]
  have hδ'z : δ' z₂ = 0 := by
    rw [hδ'app]; show δ z₂ - S.hT y z • δ z₂ = 0; rw [hyz, one_smul, sub_self]
  have hδzΛ : δ z₂ ∈ Λ := by
    have := Λ.sub_mem (hδΛ z₂) hz
    have e : (z₂ : S.V) + δ z₂ - z = δ z₂ := by show z + δ z₂ - z = δ z₂; abel
    rwa [e] at this
  have hδ'Λ : ∀ m : M₂, (m : S.V) + δ' m ∈ Λ := fun m => by
    rw [hδ'app, ← add_sub_assoc]
    exact Λ.sub_mem (hδΛ m) (int_smul_mem (sd_int hSD₂ m.2.1 hyΛ) hδzΛ)
  have hden : ∀ u : S.V, ∃ d : 𝓞 E, d ≠ 0 ∧ d • u ∈ Λ₂ := by
    intro u
    obtain ⟨s, hs⟩ := hΛ₂.fg
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) s (fun x => S.hT x u)
    let P : Submodule (𝓞 E) S.V := {
      carrier := {x | IsIntegral ℤ ((d : 𝓞 E) • S.hT x u)}
      zero_mem' := by simpa using (isIntegral_zero : IsIntegral ℤ (0 : E))
      add_mem' := by
        intro x y hx hy
        simpa [map_add, LinearMap.add_apply, smul_add] using hx.add hy
      smul_mem' := by
        intro a x hx
        change IsIntegral ℤ ((d : 𝓞 E) • S.hT x u) at hx
        change IsIntegral ℤ ((d : 𝓞 E) • S.hT (a • x) u)
        rw [oSmul S a x, hT_smulL S, oSmulW, smul_eq_mul]
        have ha : IsIntegral ℤ (star (a : E)) := isInt_star a.2
        convert ha.mul hx using 1 <;> rw [oSmulW, smul_eq_mul] <;> ring }
    have hsP : (s : Set S.V) ⊆ P := by
      intro x hx
      obtain ⟨b, hb⟩ := hd x hx
      change IsIntegral ℤ ((d : 𝓞 E) • S.hT x u)
      rw [← hb]
      exact b.2
    have hdu : (d : 𝓞 E) • u ∈ Λ₂ := by
      apply (hSD₂ _).2
      intro x hx
      have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
      change IsIntegral ℤ ((d : 𝓞 E) • S.hT x u) at hxP
      rw [oSmul S, map_smul]
      simpa only [oSmulW] using hxP
    exact ⟨d, nonZeroDivisors.ne_zero d.2, hdu⟩
  have hfull : ∀ u ∈ orth S X, ∃ d : 𝓞 E, d ≠ 0 ∧ d • u ∈ M₂ := fun u hu => by
    obtain ⟨d, hd, hdu⟩ := hden u
    exact ⟨d, hd, hdu, by show d • u ∈ orth S X; rw [oSmul]; exact (orth S X).smul_mem _ hu⟩
  obtain ⟨A, hA⟩ := ext_lat S (W := S.V) (orth S X) M₂ (fun x hx => hx.2) hfull δ'
  have hscale : ∀ u : orth S X, ∃ d : 𝓞 E, d ≠ 0 ∧ ∃ hm : ((d : E) • (u : S.V)) ∈ M₂,
      (d : E) • A u = δ' ⟨_, hm⟩ := fun u => by
    obtain ⟨d, hd, hdu⟩ := hfull u u.2
    rw [oSmul] at hdu
    refine ⟨d, hd, hdu, ?_⟩
    rw [← map_smul, ← hA _ hdu]
    rfl
  refine ⟨A, fun u => ?_, fun u hu => ?_, ?_, fun x hx hxΛ => ?_⟩
  · obtain ⟨d, hd, hm, he⟩ := hscale u
    have h1 : (d : E) • A u ∈ X := by rw [he]; exact hδ'X _
    have h2 := X.smul_mem ((d : E)⁻¹) h1
    rwa [smul_smul, inv_mul_cancel₀ (coe_ne_zero hd), one_smul] at h2
  · obtain ⟨d, hd, hm, he⟩ := hscale u
    rw [hδ'0 _ (X.smul_mem _ hu)] at he
    exact (smul_eq_zero.1 he).resolve_left (coe_ne_zero hd)
  · rw [hA z ⟨hz₂, hzX⟩]; exact hδ'z
  · rw [hA x ⟨hxΛ, hx⟩]; exact hδ'Λ ⟨x, hxΛ, hx⟩

theorem stepW (X : Submodule E S.V) (hXiso : ∀ x ∈ X, ∀ y ∈ X, S.hT x y = 0) (A : orth S X →ₗ[E] S.V)
    (hA : ∀ u, A u ∈ X) (hA0 : ∀ u : orth S X, (u : S.V) ∈ X → A u = 0) :
    ∃ g : S.V ≃ₗ[E] S.V, (∀ a b, S.hT (g a) (g b) = S.hT a b) ∧ ∀ u : orth S X, g u = u + A u := by
  let f : orth S X →ₗ[E] S.V := (orth S X).subtype + A
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro u hu
    rw [LinearMap.mem_ker] at hu
    have h1 : (u : S.V) = -A u := eq_neg_of_add_eq_zero_left hu
    have h2 : (u : S.V) ∈ X := by rw [h1]; exact X.neg_mem (hA u)
    have h3 := hA0 u h2
    rw [h3, neg_zero] at h1
    exact (Submodule.mem_bot E).2 (Subtype.ext h1)
  have hiso : ∀ u v : orth S X, S.hT (f u) (f v) = S.hT u v := fun u v => by
    show S.hT ((u : S.V) + A u) ((v : S.V) + A v) = S.hT u v
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, orth_X' S u.2 (hA v), orth_X S v.2 (hA u),
      hXiso _ (hA u) _ (hA v)]
    ring
  obtain ⟨g, hg, hgf⟩ := witt_extension_theorem E S.V S.hT (fun x y => by rw [hsw S x y])
    (fun x hx => S.nondeg.1 x hx) (orth S X) f hinj hiso
  exact ⟨g, hg, fun u => hgf u⟩

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA
end
end

noncomputable section

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

theorem stepD (X : Submodule E S.V) (hXiso : ∀ x ∈ X, ∀ y ∈ X, S.hT x y = 0)
    (Λ Λ₃ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) (hSD : SD S Λ) (hΛ₃fg : Λ₃.FG)
    (hfull₃ : ∀ u : S.V, ∃ d : 𝓞 E, d ≠ 0 ∧ d • u ∈ Λ₃) (hSD₃ : SD S Λ₃)
    (hM : ∀ x ∈ orth S X, x ∈ Λ₃ ↔ x ∈ Λ) (htr : ∃ c : E, IsIntegral ℤ c ∧ c + star c = 1) :
    ∃ n : S.V ≃ₗ[E] S.V, (∀ a b, S.hT (n a) (n b) = S.hT a b) ∧ (∀ x ∈ orth S X, n x = x) ∧
      (n : S.V → S.V) '' Λ₃ = Λ := by
  classical
  obtain ⟨c, hcI, hc⟩ := htr
  have hXo := X_le_orth S X hXiso

  have hsurj : ∀ x ∈ Λ₃, ∃ y ∈ Λ, y - x ∈ X := fun x hx => by
    obtain ⟨w, hw, hxw⟩ := dual_sum S Λ hΛ hSD (orth S X) x
      (fun m hmΛ hmU => sd_int hSD₃ hx ((hM m hmU).2 hmΛ))
    refine ⟨w, hw, ?_⟩
    have : x - w ∈ X := mem_of_orth_orth S X fun u hu => by
      rw [hsw S u (x - w), orth_X S hxw hu, star_zero]
    have h2 := X.neg_mem this
    rwa [neg_sub] at h2
  obtain ⟨δ, hδX, hδ0, hδΛ⟩ := glift S Λ₃ Λ hΛ₃fg X (orth S X) (fun x hx hxo => (hM x hxo).1 hx) hsurj
  obtain ⟨B₀, hB₀⟩ := ext_top S (W := S.V) Λ₃ hfull₃ δ
  have hscale : ∀ v : S.V, ∃ d : 𝓞 E, d ≠ 0 ∧ ∃ hm : ((d : E) • v) ∈ Λ₃, (d : E) • B₀ v = δ ⟨_, hm⟩ := fun v => by
    obtain ⟨d, hd, hdv⟩ := hfull₃ v
    rw [oSmul] at hdv
    exact ⟨d, hd, hdv, by rw [← map_smul, hB₀ _ hdv]⟩
  have hB₀X : ∀ v, B₀ v ∈ X := fun v => by
    obtain ⟨d, hd, hm, he⟩ := hscale v
    have h1 : (d : E) • B₀ v ∈ X := by rw [he]; exact hδX _
    have h2 := X.smul_mem ((d : E)⁻¹) h1
    rwa [smul_smul, inv_mul_cancel₀ (coe_ne_zero hd), one_smul] at h2
  have hB₀o : ∀ u ∈ orth S X, B₀ u = 0 := fun u hu => by
    obtain ⟨d, hd, hm, he⟩ := hscale u
    rw [hδ0 _ ((orth S X).smul_mem _ hu)] at he
    exact (smul_eq_zero.1 he).resolve_left (coe_ne_zero hd)

  let b := S.frame
  obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis S.hT S.nondeg b
  let σL : Fin S.rank → S.V →ₗ[E] E := fun k => S.hT (B₀ (b k)) + S.hT (b k) ∘ₗ B₀
  let B₁ : S.V →ₗ[E] S.V := ∑ k, ((-c) • σL k).smulRight (bs k)
  have hB₁app : ∀ v, B₁ v = ∑ k, (-c * (S.hT (B₀ (b k)) v + S.hT (b k) (B₀ v))) • bs k := fun v => by
    show (∑ k, ((-c) • σL k).smulRight (bs k)) v = _
    rw [LinearMap.sum_apply]
    rfl
  have hB₁ : ∀ v v', S.hT (B₁ v) v' = -(star c) * (S.hT (B₀ v) v' + S.hT v (B₀ v')) := fun v v' => by
    have key : S.hT (B₁ v) = -(star c) • (S.hT (B₀ v) + S.hT v ∘ₗ B₀) := by
      apply b.ext
      intro k'
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hB₁app, map_sum, LinearMap.sum_apply]
      simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul,
        LinearMap.add_apply, LinearMap.comp_apply]
      rw [Finset.sum_eq_single k']
      · rw [hsw S (b k') (bs k'), hbs k' k', if_pos rfl, star_one, mul_one, star_mul, star_neg, star_add,
          ← hsw S (B₀ (b k')) v, ← hsw S (b k') (B₀ v)]
        ring
      · intro k _ hk
        rw [hsw S (b k') (bs k), hbs k' k, if_neg (Ne.symm hk), star_zero, mul_zero]
      · simp
    rw [key]
    rfl
  let B : S.V →ₗ[E] S.V := B₀ + B₁
  have hBapp : ∀ v, B v = B₀ v + B₁ v := fun v => rfl
  have hB₁X : ∀ v, B₁ v ∈ X := fun v => mem_of_orth_orth S X fun u hu => by
    rw [hB₁, hB₀o u hu, map_zero, orth_X S hu (hB₀X v)]
    ring
  have hB₁o : ∀ u ∈ orth S X, B₁ u = 0 := fun u hu => S.nondeg.1 _ fun v' => by
    rw [hB₁, hB₀o u hu, map_zero, LinearMap.zero_apply, orth_X' S hu (hB₀X v')]
    ring
  have hBX : ∀ v, B v ∈ X := fun v => by rw [hBapp]; exact X.add_mem (hB₀X v) (hB₁X v)
  have hBo : ∀ u ∈ orth S X, B u = 0 := fun u hu => by rw [hBapp, hB₀o u hu, hB₁o u hu, add_zero]
  have hBB : ∀ v, B (B v) = 0 := fun v => hBo _ (hXo (hBX v))
  have hBiso : ∀ v v', S.hT (v + B v) (v' + B v') = S.hT v v' := fun v v' => by
    have expand : S.hT (v + B v) (v' + B v') = S.hT v v' + S.hT (B v) v' + S.hT v (B v') + S.hT (B v) (B v') := by
      simp only [map_add (f := _), LinearMap.add_apply]; ring
    have f1 : S.hT (B v) v' = S.hT (B₀ v) v' + (-(star c) * (S.hT (B₀ v) v' + S.hT v (B₀ v'))) := by
      rw [hBapp, map_add (f := _), LinearMap.add_apply, hB₁]
    have f2 : S.hT v (B v') = S.hT v (B₀ v') + (-c * (S.hT (B₀ v) v' + S.hT v (B₀ v'))) := by
      rw [hBapp, map_add (f := _), hsw S (B₁ v') v, hB₁, star_mul, star_neg, star_add, ← hsw S (B₀ v') v,
        ← hsw S v' (B₀ v), star_star]
      ring
    rw [expand, hXiso _ (hBX v) _ (hBX v'), f1, f2]
    linear_combination (-(S.hT (B₀ v) v' + S.hT v (B₀ v'))) * hc
  let n : S.V ≃ₗ[E] S.V := LinearEquiv.ofLinear (LinearMap.id + B) (LinearMap.id - B)
    (by ext v; simp [hBB]) (by ext v; simp [hBB])
  have hnapp : ∀ v, n v = v + B v := fun v => rfl
  have hniso : ∀ a b, S.hT (n a) (n b) = S.hT a b := fun a b => by rw [hnapp, hnapp, hBiso]
  have hnin : ∀ x ∈ Λ₃, n x ∈ Λ := fun x hx => by
    rw [hnapp, hBapp, ← add_assoc]
    refine Λ.add_mem (by rw [hB₀ x hx]; exact hδΛ ⟨x, hx⟩) ((hM _ (hXo (hB₁X x))).1 ?_)
    refine (hSD₃ _).2 fun y hy => ?_
    have hσ : IsIntegral ℤ (S.hT (B₀ x) y + S.hT x (B₀ y)) := by
      have h1 : IsIntegral ℤ (S.hT (x + B₀ x) (y + B₀ y)) := by
        rw [hB₀ x hx, hB₀ y hy]; exact sd_int hSD (hδΛ ⟨y, hy⟩) (hδΛ ⟨x, hx⟩)
      have h2 : IsIntegral ℤ (S.hT x y) := sd_int hSD₃ hy hx
      have e : S.hT (B₀ x) y + S.hT x (B₀ y) = S.hT (x + B₀ x) (y + B₀ y) - S.hT x y := by
        rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hXiso _ (hB₀X x) _ (hB₀X y)]
        ring
      rw [e]; exact h1.sub h2
    rw [hsw S (B₁ x) y, hB₁, star_mul, star_neg, star_star]
    exact (isInt_star hσ).mul hcI.neg
  refine ⟨n, hniso, fun x hx => by rw [hnapp, hBo x hx, add_zero], ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hnin y hy
  · intro hx
    refine ⟨n.symm x, (hSD₃ _).2 fun y hy => ?_, n.apply_symm_apply x⟩
    rw [← hniso y (n.symm x), n.apply_symm_apply]
    exact sd_int hSD hx (hnin y hy)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA
end
end

noncomputable section

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

theorem main (X : Submodule E S.V) (hXiso : ∀ x ∈ X, ∀ y ∈ X, S.hT x y = 0) (z : S.V) (hzX : z ∈ orth S X)
    (Λ Λ₂ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) (hΛ₂ : Submodule.IsLattice E Λ₂)
    (hSD : SD S Λ) (hSD₂ : SD S Λ₂) (hX : ∀ x ∈ X, x ∈ Λ₂ ↔ x ∈ Λ) (hz : z ∈ Λ) (hz₂ : z ∈ Λ₂)
    (hL : ∀ x ∈ Λ₂, x ∈ orth S X → ∃ y ∈ Λ, y - x ∈ X)
    (hL' : ∀ y ∈ Λ, y ∈ orth S X → ∃ x ∈ Λ₂, x ∈ orth S X ∧ y - x ∈ X)
    (hy : ∃ y ∈ Λ₂, y ∈ orth S X ∧ S.hT y z = 1) (htr : ∃ c : E, IsIntegral ℤ c ∧ c + star c = 1) :
    ∃ n : S.V ≃ₗ[E] S.V, (∀ a b, S.hT (n a) (n b) = S.hT a b) ∧ (∀ x ∈ X, n x = x) ∧ n z = z ∧
      (∀ x ∈ orth S X, n x - x ∈ X) ∧ (n : S.V → S.V) '' Λ₂ = Λ := by
  classical
  have hXo := X_le_orth S X hXiso
  obtain ⟨A, hAX, hA0, hAz, hAΛ⟩ :=
    stepB S X hXiso z hzX Λ Λ₂ hΛ₂ hSD₂ (fun x hx h => (hX x hx).1 h) hz hz₂ hL hy
  obtain ⟨g, hg, hgA⟩ := stepW S X hXiso A hAX hA0
  have hgX : ∀ x ∈ X, g x = x := fun x hx => by
    have e : g x = x + A ⟨x, hXo hx⟩ := hgA ⟨x, hXo hx⟩
    rw [e, hA0 ⟨x, hXo hx⟩ hx, add_zero]
  let Λ₃ : Submodule (𝓞 E) S.V := Λ₂.map ((g : S.V →ₗ[E] S.V).restrictScalars (𝓞 E))
  have hmem₃ : ∀ x, x ∈ Λ₃ ↔ g.symm x ∈ Λ₂ := fun x => by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro h
      exact ⟨g.symm x, h, by simp⟩
  have hfg₃ : Λ₃.FG := hΛ₂.fg.map _
  have hfull₃ : ∀ u : S.V, ∃ d : 𝓞 E, d ≠ 0 ∧ d • u ∈ Λ₃ := fun u => by
    have hfull₂ : ∀ v : S.V, ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ Λ₂ := by
      intro v
      obtain ⟨s, hs⟩ := hΛ₂.fg
      obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) s (fun x => S.hT x v)
      let P : Submodule (𝓞 E) S.V := {
        carrier := {x | IsIntegral ℤ (((a : 𝓞 E) : E) * S.hT x v)}
        zero_mem' := by simpa using (isIntegral_zero : IsIntegral ℤ (0 : E))
        add_mem' := by
          intro x y hx hy
          simpa [map_add, LinearMap.add_apply, mul_add] using hx.add hy
        smul_mem' := by
          intro c x hx
          have hc : IsIntegral ℤ (star (c : E)) := isInt_star c.2
          have := hc.mul hx
          change IsIntegral ℤ (((a : 𝓞 E) : E) * S.hT (c • x) v)
          rw [oSmul, hT_smulL]
          convert this using 1 <;> ring }
      have hsP : (s : Set S.V) ⊆ P := by
        intro x hx
        obtain ⟨b, hb⟩ := ha x hx
        change IsIntegral ℤ (((a : 𝓞 E) : E) * S.hT x v)
        rw [← show (b : E) = ((a : 𝓞 E) : E) * S.hT x v by simpa [Algebra.smul_def] using hb]
        exact b.2
      refine ⟨a, nonZeroDivisors.ne_zero a.2, ?_⟩
      apply (hSD₂ _).2
      intro x hx
      have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
      change IsIntegral ℤ (((a : 𝓞 E) : E) * S.hT x v) at hxP
      rw [oSmul, map_smul, smul_eq_mul]
      exact hxP
    obtain ⟨d, hd, hdu⟩ := hfull₂ (g.symm u)
    refine ⟨d, hd, (hmem₃ _).2 ?_⟩
    rw [oSmul, map_smul, ← oSmul]
    exact hdu
  have hSD₃ : SD S Λ₃ := fun x => by
    rw [hmem₃, hSD₂]
    constructor
    · intro h y hy
      have := h (g.symm y) ((hmem₃ y).1 hy)
      rwa [← hg (g.symm y) (g.symm x), g.apply_symm_apply, g.apply_symm_apply] at this
    · intro h y hy
      rw [← hg y (g.symm x), g.apply_symm_apply]
      exact h (g y) ((hmem₃ _).2 (by simpa using hy))
  have hM : ∀ x ∈ orth S X, x ∈ Λ₃ ↔ x ∈ Λ := fun x hx => by
    rw [hmem₃]
    constructor
    · intro h
      obtain ⟨l, rfl⟩ : ∃ l, g l = x := ⟨g.symm x, g.apply_symm_apply x⟩
      rw [g.symm_apply_apply] at h
      have hlo : l ∈ orth S X := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).2 fun x' hx' => by
        rw [← hg x' l, hgX x' hx']
        exact orth_X S hx hx'
      have e : g l = l + A ⟨l, hlo⟩ := hgA ⟨l, hlo⟩
      rw [e]
      exact hAΛ l hlo h
    · intro h
      obtain ⟨x₂, hx₂, hx₂o, hxx₂⟩ := hL' x h hx
      have hAx₂ := hAΛ x₂ hx₂o hx₂
      obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ = x - (x₂ + A ⟨x₂, hx₂o⟩) := ⟨_, rfl⟩
      have hξX : ξ ∈ X := by
        have e : ξ = (x - x₂) - A ⟨x₂, hx₂o⟩ := by rw [hξ]; abel
        rw [e]
        exact X.sub_mem hxx₂ (hAX _)
      have hξΛ : ξ ∈ Λ := by rw [hξ]; exact Λ.sub_mem h hAx₂
      have hξΛ₂ : ξ ∈ Λ₂ := (hX ξ hξX).2 hξΛ
      have hlo : x₂ + ξ ∈ orth S X := (orth S X).add_mem hx₂o (hXo hξX)
      have e : g (x₂ + ξ) = x := by
        have h1 : g (x₂ + ξ) = (x₂ + ξ) + A ⟨x₂ + ξ, hlo⟩ := hgA ⟨x₂ + ξ, hlo⟩
        have h2 : A ⟨x₂ + ξ, hlo⟩ = A ⟨x₂, hx₂o⟩ + A ⟨ξ, hXo hξX⟩ := by
          rw [← map_add (f := _)]
          rfl
        rw [h1, h2, hA0 ⟨ξ, hXo hξX⟩ hξX, add_zero, hξ]
        abel
      rw [← e, g.symm_apply_apply]
      exact Λ₂.add_mem hx₂ hξΛ₂
  obtain ⟨n₂, hn₂, hn₂o, hn₂img⟩ := stepD S X hXiso Λ Λ₃ hΛ hSD hfg₃ hfull₃ hSD₃ hM htr
  refine ⟨g.trans n₂, fun a b => ?_, fun x hx => ?_, ?_, fun x hx => ?_, ?_⟩
  · show S.hT (n₂ (g a)) (n₂ (g b)) = S.hT a b
    rw [hn₂, hg]
  · show n₂ (g x) = x
    rw [hgX x hx, hn₂o x (hXo hx)]
  · have e : g z = z + A ⟨z, hzX⟩ := hgA ⟨z, hzX⟩
    show n₂ (g z) = z
    rw [e, hAz, add_zero, hn₂o z hzX]
  · have e : g x = x + A ⟨x, hx⟩ := hgA ⟨x, hx⟩
    have ho : g x ∈ orth S X := by rw [e]; exact (orth S X).add_mem hx (hXo (hAX _))
    show n₂ (g x) - x ∈ X
    rw [hn₂o _ ho, e, add_sub_cancel_left]
    exact hAX _
  · have h3 : (g : S.V → S.V) '' (Λ₂ : Set S.V) = (Λ₃ : Set S.V) := by
      rw [Submodule.map_coe]
      rfl
    have e : ((g.trans n₂ : S.V ≃ₗ[E] S.V) : S.V → S.V) = n₂ ∘ g := rfl
    rw [e, Set.image_comp, h3, hn₂img]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

theorem mem_of_bcP {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsFullLattice D.host.E Λ) {x : (VS D).V}
    (h : ∀ p, baseChange₂ D p x ∈ lattice₂ D Zd.M p Λ) : x ∈ Λ := by
  refine PI.UnitaryGroupMassFormula.UJClassMass.interLocF (F := D.host.F) Λ hΛ.toIsLattice x fun v => ?_
  have := v.isPrime
  letI := hΛ
  have h2 := (Formalism.L2.SG.Pf.LocalDenominators.baseChangeAt_mem_localLattice_iff Zd v (Λ := Λ) (by infer_instance) x).1 (h v)
  exact (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF v.asIdeal Λ x).1 h2

theorem baseChange_mem_localLattice {Λ : Submodule (𝓞 D.host.E) (VS D).V} {x : (VS D).V} (hx : x ∈ Λ) (p : PlF D) :
    baseChange₂ D p x ∈ lattice₂ D Zd.M p Λ := Submodule.subset_span ⟨x, hx, rfl⟩

theorem iE_intD (p : PlF D) {y : D.host.E} (hy : IsIntegral ℤ y) : (D.s.atP p).ιE y ∈ (Zd.M p).L.O := by
  rw [LocFacts.lf_hO Zd p]
  exact Formalism.L2.SG.Pf.StabIntSh.lg_iota_int p ⟨y, hy⟩

theorem int_of_loc {y : D.host.E} (h : ∀ p, (D.s.atP p).ιE y ∈ (Zd.M p).L.O) : IsIntegral ℤ y :=
  Formalism.L2.SG.Pf.StabIntSh.lg_int_of_loc y fun p => by rw [← LocFacts.lf_hO Zd p]; exact h p

theorem localForm_baseChange (p : PlF D) (x y : (VS D).V) :
    (locH Zd p).h (baseChange₂ D p x) (baseChange₂ D p y) = (D.s.atP p).ιE ((VS D).hT y x) :=
  baseChangeAt_form Zd.M p (Zd.hcj p) x y

theorem h_eq (p : PlF D) : (locH Zd p).h = LocFacts₂ Zd.M p := rfl

theorem sd_of_loc {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsFullLattice D.host.E Λ)
    (hloc : ∀ p, (locH Zd p).IsSelfDual (lattice₂ D Zd.M p Λ)) : BwdNA.SD (VS D) Λ := by
  intro x
  constructor
  · intro hx y hy
    refine int_of_loc Zd fun p => ?_
    rw [← localForm_baseChange]
    exact ((hloc p).2.2 (baseChange₂ D p x)).1 (baseChange_mem_localLattice Zd hx p) (baseChange₂ D p y) (baseChange_mem_localLattice Zd hy p)
  · intro h
    refine mem_of_bcP Zd hΛ fun p => ((hloc p).2.2 _).2 fun w hw => ?_
    rw [h_eq]
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      rw [← h_eq, localForm_baseChange]
      exact iE_intD Zd p (h y hy)
    | zero => rw [LocFacts.localForm_zero_right]; exact zero_mem _
    | add a b _ _ ha hb => rw [LocFacts.localForm_add_right]; exact add_mem ha hb
    | smul o w _ hw =>
      change LocFacts₂ Zd.M p (baseChange₂ D p x) ((o : (D.s.atP p).Ep) • w) ∈ _
      rw [LocFacts.localForm_smul_right]
      exact mul_mem (LocFacts.lf_cjM_mem Zd p _ o.2) hw

variable {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem tf (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (a : Fin (D.R.rS + 1)) :
    (tLoc Zd p γ).f a = (TermLoc.sgnP D p a * frFac Zd.δ p a) • baseChange₂ D p (frame (lf D F0) a) := rfl

theorem sgnP_last (p : PlF D) : TermLoc.sgnP D p (Fin.last D.R.rS) = 1 := by
  unfold TermLoc.sgnP
  split
  · simp
  · rfl

theorem frFac_last' (p : PlF D) : frFac Zd.δ p (Fin.last D.R.rS) = 1 := by
  unfold frFac; simp

theorem tf_last (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) :
    (tLoc Zd p γ).f (Fin.last D.R.rS) = baseChange₂ D p F0.z := by
  rw [tf, sgnP_last, frFac_last', one_mul, one_smul]
  congr 1
  simp [frame, FlagG.fvec]

theorem frame_cs (i : Fin D.R.rS) : frame (lf D F0) i.castSucc = F0.e i := by
  simp [frame, FlagG.fvec]

theorem unit_of_frame (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) {L : Submodule (Zd.M p).L.O (Vp D p)}
    {T : (D.s.atP p).Fp} (hfr : (locH Zd p).IsFrame L D.R.rS (tLoc Zd p γ).f T) (a : Fin (D.R.rS + 1)) :
    IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a) := by
  have hs : IsUnit (TermLoc.sgnP D p a) := ⟨⟨TermLoc.sgnP D p a, TermLoc.sgnP D p a, TermLoc.localSign_sq p a, TermLoc.localSign_sq p a⟩, rfl⟩
  refine hs.mul ?_
  by_cases h : IsUnit ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^
      (D.R.rS - a.val))
  · obtain ⟨w, hw⟩ := h
    unfold frFac
    rw [← hw, Ring.inverse_unit]
    exact Units.isUnit _
  · exfalso
    have h0 : frFac Zd.δ p a = 0 := by unfold frFac; exact Ring.inverse_non_unit _ h
    have hne := hfr.1.2.1.ne_zero a
    apply hne
    rw [tf, h0, mul_zero, zero_smul]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNP
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

section Place

variable (p : PlF D) (γ : TermDef.Term D u u' F0 what₂)
  (hu : ∀ a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a))

include hu in
theorem baseChangeAt_frame_eq (a : Fin (D.R.rS + 1)) :
    baseChange₂ D p (frame (lf D F0) a) = ((hu a).unit⁻¹ : ((D.s.atP p).Ep)ˣ) • (tLoc Zd p γ).f a := by
  rw [tf, Units.smul_def, smul_smul, (hu a).val_inv_mul, one_smul]

include hu in
theorem bcP_X {x : (VS D).V} (hx : x ∈ Xsp (lf D F0)) : baseChange₂ D p x ∈ (locH Zd p).X (tLoc Zd p γ).f := by
  change x ∈ Submodule.span D.host.E (Set.range F0.e) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [← frame_cs, baseChangeAt_frame_eq Zd p γ hu, Units.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [(baseChange₂ D p).map_add]; exact add_mem ha hb
  | smul c x _ hx => rw [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]; exact Submodule.smul_mem _ _ hx

theorem baseChange_mem_perp_sup {m : (VS D).V} (hm : m ∈ orth (VS D) (Xsp (lf D F0))) :
    baseChange₂ D p m ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f) := by
  show ∀ w ∈ (locH Zd p).X (tLoc Zd p γ).f, (locH Zd p).h (baseChange₂ D p m) w = 0
  intro w hw
  rw [h_eq]
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    simp only
    rw [tf, frame_cs, LocFacts.localForm_smul_right, ← h_eq, localForm_baseChange,
      (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hm _ (Submodule.subset_span ⟨i, rfl⟩), map_zero, mul_zero]
  | zero => exact LocFacts.localForm_zero_right Zd p _
  | add a b _ _ ha hb => rw [LocFacts.localForm_add_right, ha, hb, add_zero]
  | smul c w _ hw => rw [LocFacts.localForm_smul_right, hw, mul_zero]

theorem h_X_perp {w v : Vp D p} (hw : w ∈ (locH Zd p).X (tLoc Zd p γ).f)
    (hv : v ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f)) : (locH Zd p).h w v = 0 := by
  rw [(locH Zd p).h_herm v w, (show (locH Zd p).h v w = 0 from hv w hw), map_zero]

end Place

theorem pair_int (γ : TermDef.Term D u u' F0 what₂) {Λ₁ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    (hSD₁ : ∀ p, (locH Zd p).IsSelfDual (lattice₂ D Zd.M p Λ₁))
    (hL : ∀ p, (locH Zd p).Lset (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f ⊆
      (locH Zd p).Lset (lattice₂ D Zd.M p Λ₁) (tLoc Zd p γ).f)
    {x m : (VS D).V} (hx : x ∈ Λ₂) (hxo : x ∈ orth (VS D) (Xsp (lf D F0))) (hm : m ∈ Λ₁)
    (hmo : m ∈ orth (VS D) (Xsp (lf D F0))) : IsIntegral ℤ ((VS D).hT m x) := by
  refine int_of_loc Zd fun p => ?_
  rw [← localForm_baseChange]
  have hv := baseChange_mem_perp_sup Zd p γ hxo
  have hmem : (locH Zd p).mkW (tLoc Zd p γ).f ⟨baseChange₂ D p x, hv⟩ ∈
      (locH Zd p).Lset (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f := ⟨⟨baseChange₂ D p x, hv⟩, baseChange_mem_localLattice Zd hx p, rfl⟩
  obtain ⟨x'', hx''Λ, hx''eq⟩ := hL p hmem
  have hdiff : (baseChange₂ D p x) - (x'' : Vp D p) ∈ (locH Zd p).X (tLoc Zd p γ).f := by
    have := (Submodule.Quotient.eq _).1 hx''eq.symm
    simpa using this
  have e : baseChange₂ D p x = (x'' : Vp D p) + ((baseChange₂ D p x) - (x'' : Vp D p)) := by abel
  rw [e, (locH Zd p).h_add_left, h_X_perp Zd p γ hdiff (baseChange_mem_perp_sup Zd p γ hmo), add_zero]
  exact ((hSD₁ p).2.2 x'').1 hx''Λ (baseChange₂ D p m) (baseChange_mem_localLattice Zd hm p)

theorem memX (γ : TermDef.Term D u u' F0 what₂) {Λa Λb : Submodule (𝓞 D.host.E) (VS D).V}
    (ha : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λa) (tLoc Zd p γ).f)
    (hb : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λb) (tLoc Zd p γ).f) (hΛb : Submodule.IsFullLattice D.host.E Λb)
    (hu : ∀ p a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a)) {x : (VS D).V} (hx : x ∈ Xsp (lf D F0))
    (hxa : x ∈ Λa) : x ∈ Λb := by
  refine mem_of_bcP Zd hΛb fun p => ?_
  have h1 : baseChange₂ D p x ∈ Submodule.span (D.s.atP p).Ep (Set.range (tLoc Zd p γ).f) :=
    Submodule.span_mono (Set.range_comp_subset_range _ _) (bcP_X Zd p γ (hu p) hx)
  have h2 := (ha p).2.2 _ (baseChange_mem_localLattice Zd hxa p) h1
  exact Submodule.span_le.2 (Set.range_subset_iff.2 fun a => (hb p).1 a) h2

theorem z_mem (γ : TermDef.Term D u u' F0 what₂) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : Submodule.IsFullLattice D.host.E Λ) (h : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ) (tLoc Zd p γ).f) :
    F0.z ∈ Λ :=
  mem_of_bcP Zd hΛ fun p => by rw [← tf_last Zd p γ]; exact (h p).1 _

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNP
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem coef_int (γ : TermDef.Term D u u' F0 what₂) {Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    (hprim : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f)
    (hu : ∀ p a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a)) (c : Fin (D.R.rS + 1) → D.host.E)
    (hc : ∑ a, c a • frame (lf D F0) a ∈ Λ₂) : IsIntegral ℤ (c (Fin.last D.R.rS)) := by
  refine int_of_loc Zd fun p => ?_
  set m := ∑ a, c a • frame (lf D F0) a with hm
  have hbm : baseChange₂ D p m = ∑ a, ((D.s.atP p).ιE (c a) * (((hu p a).unit⁻¹ : ((D.s.atP p).Ep)ˣ) : (D.s.atP p).Ep)) •
      (tLoc Zd p γ).f a := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hm, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂, baseChangeAt_frame_eq Zd p γ (hu p), Units.smul_def, smul_smul]
  have hspan : baseChange₂ D p m ∈ Submodule.span (D.s.atP p).Ep (Set.range (tLoc Zd p γ).f) := by
    rw [hbm]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have h2 := (hprim p).2.2 _ (baseChange_mem_localLattice Zd hc p) hspan
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h2
  have hli := (hprim p).2.1
  have hz : ∑ a, (((o a : (Zd.M p).L.O) : (D.s.atP p).Ep) -
      (D.s.atP p).ιE (c a) * (((hu p a).unit⁻¹ : ((D.s.atP p).Ep)ˣ) : (D.s.atP p).Ep)) • (tLoc Zd p γ).f a = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← hbm, ← ho]
    simp only [sub_eq_zero]
    rfl
  have h3 := Fintype.linearIndependent_iff.1 hli _ hz (Fin.last D.R.rS)
  have key : ∀ {a : (D.s.atP p).Ep} (h : IsUnit a), a = 1 →
      (((h.unit⁻¹ : ((D.s.atP p).Ep)ˣ)) : (D.s.atP p).Ep) = 1 := by
    intro a h ha
    subst ha
    have : h.unit = 1 := Units.ext (IsUnit.unit_spec h)
    rw [this, inv_one, Units.val_one]
  have hone := key (hu p (Fin.last D.R.rS)) (by rw [sgnP_last, frFac_last', mul_one])
  rw [hone, mul_one, sub_eq_zero] at h3
  rw [← h3]
  exact (o (Fin.last D.R.rS)).2

theorem exists_y (γ : TermDef.Term D u u' F0 what₂) {Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ₂ : Submodule.IsLattice D.host.E Λ₂) (hSD₂ : BwdNA.SD (VS D) Λ₂)
    (hprim : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f)
    (hu : ∀ p a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a)) (hzX : F0.z ∉ Xsp (lf D F0)) :
    ∃ y ∈ Λ₂, y ∈ orth (VS D) (Xsp (lf D F0)) ∧ (VS D).hT y F0.z = 1 := by
  obtain ⟨f, hfz, hfX⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hzX inferInstance
  let ρ : Module.Dual D.host.E (VS D).V := (f F0.z)⁻¹ • f
  have hρz : ρ F0.z = 1 := by
    simp only [ρ, LinearMap.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hfz
  have hρX : ∀ x ∈ Xsp (lf D F0), ρ x = 0 := fun x hx => by
    have h1 : f x ∈ (Xsp (lf D F0)).map f := ⟨x, hx, rfl⟩
    rw [hfX, Submodule.mem_bot] at h1
    simp only [ρ, LinearMap.smul_apply, smul_eq_mul, h1, mul_zero]
  have hρe : ∀ i : Fin D.R.rS, ρ (frame (lf D F0) i.castSucc) = 0 := fun i => by
    rw [frame_cs]; exact hρX _ (Submodule.subset_span ⟨i, rfl⟩)
  have hρl : ρ (frame (lf D F0) (Fin.last D.R.rS)) = 1 := by
    have : frame (lf D F0) (Fin.last D.R.rS) = F0.z := by simp [frame, FlagG.fvec]
    rw [this, hρz]
  obtain ⟨v, hv⟩ := BwdNA.riesz (VS D) ρ
  let U : Submodule D.host.E (VS D).V := Submodule.span D.host.E (Set.range (frame (lf D F0)))
  have hint : ∀ m ∈ Λ₂, m ∈ U → IsIntegral ℤ ((VS D).hT m v) := fun m hm hmU => by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hmU
    have hρm : ρ m = c (Fin.last D.R.rS) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hc, map_sum, Fin.sum_univ_castSucc]
      simp only [map_smul, smul_eq_mul, hρe, mul_zero, Finset.sum_const_zero, zero_add, hρl, mul_one]
    rw [BwdNA.hsw (VS D) v m, hv, hρm]
    exact BwdNA.isInt_star (coef_int Zd γ hprim hu c (by rw [hc]; exact hm))
  obtain ⟨w, hwΛ, hvw⟩ := BwdNA.dual_sum (VS D) Λ₂ hΛ₂ hSD₂ U v hint
  have hw : ∀ a, (VS D).hT w (frame (lf D F0) a) = ρ (frame (lf D F0) a) := fun a => by
    have h0 := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hvw _ (Submodule.subset_span ⟨a, rfl⟩)
    rw [map_sub, sub_eq_zero] at h0
    rw [BwdNA.hsw (VS D) (frame (lf D F0) a) w, ← h0, ← BwdNA.hsw (VS D) (frame (lf D F0) a) v, hv]
  refine ⟨w, hwΛ, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => ?_, ?_⟩
  · change x ∈ Submodule.span D.host.E (Set.range F0.e) at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [BwdNA.hsw (VS D) w (F0.e i), ← frame_cs, hw, hρe, star_zero]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add (f := _), LinearMap.add_apply, ha, hb, add_zero]
    | smul c x _ hx => rw [BwdNA.hT_smulL, hx, mul_zero]
  · have : frame (lf D F0) (Fin.last D.R.rS) = F0.z := by simp [frame, FlagG.fvec]
    rw [← this, hw, hρl]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNP
