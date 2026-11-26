module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TypeSlice
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ApartOfNotMem
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PackExOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PTracePow

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.AuxiliaryPrimeFunction
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCx GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp cj)
open UpperTheory.Gal.LocalSmoothExtension UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.Int.Geo (Integ IsFnL)
open Formalism.UG (Hecke conv)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Spc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime]

instance algAt (S : Setup A n p) (w : Plc E) : Algebra S.G.F (w.adicCompletion E) := inferInstanceAs (Algebra E (w.adicCompletion E))

def Spl (E : Type) [Field E] [NumberField E] [IsCMField E] (p : ℕ) : Type := {w : Plc E // IsSplitAt w ∧ (p : 𝓞 E) ∉ w.asIdeal}

abbrev fac {S : Setup A n p} (T : Tr S) (hc : LocComm) (w : Spl E p) : Loc S.G.GAf (GL (Fin n) (w.1.adicCompletion E)) :=
  T.at hc w.1 w.2.1 w.2.2

structure Half (q : ℕ) (W : Finset (Spl E p)) : Prop where
  above : ∀ w ∈ W, (q : 𝓞 E) ∈ w.1.asIdeal
  all : ∀ u : Plc E, (q : 𝓞 E) ∈ u.asIdeal → ∃ w ∈ W, w.1 = u ∨ cj w.1 = u
  apart : ∀ w ∈ W, ∀ w' ∈ W, w ≠ w' → GlobalTheory.Cong.Apart w.1 w'.1

def AdmCusp : Prop :=
  ∀ (X : Type) [Group X] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k] (n : ℕ) (Ty : TyLev X (GL (Fin n) k)),
    IsOpen (Ty.J : Set (GL (Fin n) k)) → IsCompact (Ty.J : Set (GL (Fin n) k)) → IsOpen (Ty.ψ.ker : Set Ty.J) →
    (∀ (σ : SmIrr (GL (Fin n) k)) (v : σ.V), v ≠ 0 → (∀ g : Ty.J, σ.ρ g v = ((Ty.ψ g : ℂˣ) : ℂ) • v) → GlobalTheory.SmGL.IsCuspidal σ.ρ) →
    ∀ f, Ty.admitted f → ∀ h : X, Ty.L.pr h = 1 → NoConst fun g => f (Ty.L.loc g * h)

end UpperTheory.Gal.Spc
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.OrbZero
set_option autoImplicit false

noncomputable section

open MeasureTheory Matrix Polynomial GlobalTheory.BCT GlobalTheory.BCT.OrbProd GlobalTheory.LKCount GlobalTheory.LKCount.OrbKProd GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid
open Formalism.UG (Hecke)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.Spc

section Abstract

variable {A B : Type} [Group A] [Group B]

theorem finsum_mul_eq_zero {ι : Type} (w : ℂ) (g : ι → ℂ) (h : ∑ᶠ i, g i = 0) :
    ∑ᶠ i, w * g i = 0 := by
  have := smul_finsum (R := ℂ) (M := ℂ) w g
  simp only [smul_eq_mul] at this
  rw [← this, h, mul_zero]

theorem map_conj_inf_of_comm (T L : Subgroup A) (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) {t : A} (ht : t ∈ T) :
    (T ⊓ L).map (MulAut.conj t).toMonoidHom = T ⊓ L := by
  have hfix : ∀ y ∈ T ⊓ L, (MulAut.conj t).toMonoidHom y = y := by
    intro y hy
    have hc := hT t ht y (Subgroup.mem_inf.mp hy).1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hc, mul_inv_cancel_right]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [hfix y hy]
    exact hy
  · intro hx
    exact ⟨x, hx, hfix x hx⟩

theorem oTerm_inv_of_comm (K C : Subgroup A) (δ : A) (f : A → ℂ)
    (hf : ∀ k ∈ K, ∀ y, f (k⁻¹ * y * MonoidHom.id A k) = f y)
    (hT : ∀ a ∈ twCent (MonoidHom.id A) δ, ∀ b ∈ twCent (MonoidHom.id A) δ, a * b = b * a)
    {t k : A} (ht : t ∈ twCent (MonoidHom.id A) δ) (hk : k ∈ K) (x : A) :
    oTerm (MonoidHom.id A) K C δ f (t * x * k) = oTerm (MonoidHom.id A) K C δ f x := by
  unfold oTerm
  rw [f_inv _ K δ f hf ht hk x, map_conj_mul_three_subgroup_of_mem K hk, inf_map_conj _ _ ht, map_conj_inf_of_comm _ _ hT ht]

theorem orbK_prod_eq_zero_of_slices (K₁ : Subgroup A) (K₂ : Subgroup B) (a : A) (b : B) (F : A × B → ℂ)
    (h₁ : ∀ s ∈ twCent (MonoidHom.id A) a, ∀ c ∈ twCent (MonoidHom.id A) a, s * c = c * s)
    (h₂ : ∀ s ∈ twCent (MonoidHom.id B) b, ∀ c ∈ twCent (MonoidHom.id B) b, s * c = c * s)
    (hF : ∀ k ∈ K₁.prod K₂, ∀ y, F (k⁻¹ * y * MonoidHom.id (A × B) k) = F y)
    (h0 : ∀ z : B, orbK (MonoidHom.id A) K₁ a (fun v => F (v, z)) = 0) :
    orbK (MonoidHom.id (A × B)) (K₁.prod K₂) (a, b) F = 0 := by
  have hTeq : twCent (MonoidHom.id (A × B)) (a, b) =
      (twCent (MonoidHom.id A) a).prod (twCent (MonoidHom.id B) b) := by
    ext g
    rw [Subgroup.mem_prod]
    show g * (a, b) = (a, b) * g ↔ g.1 * a = a * g.1 ∧ g.2 * b = b * g.2
    exact Prod.ext_iff
  have hcomm : ∀ s ∈ twCent (MonoidHom.id (A × B)) (a, b), ∀ c ∈ twCent (MonoidHom.id (A × B)) (a, b),
      s * c = c * s := by
    rw [hTeq]
    intro s hs c hc
    rw [Subgroup.mem_prod] at hs hc
    exact Prod.ext (h₁ _ hs.1 _ hc.1) (h₂ _ hs.2 _ hc.2)
  have hinv : ∀ x : A × B,
      oTerm (MonoidHom.id (A × B)) (K₁.prod K₂) (twCent (MonoidHom.id (A × B)) (a, b) ⊓ K₁.prod K₂) (a, b) F
        (DoubleCoset.mk (twCent (MonoidHom.id (A × B)) (a, b)) (K₁.prod K₂) x).out =
      oTerm (MonoidHom.id (A × B)) (K₁.prod K₂) (twCent (MonoidHom.id (A × B)) (a, b) ⊓ K₁.prod K₂) (a, b) F x := by
    intro x
    obtain ⟨t, ht, k, hk, he⟩ := DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id (A × B)) (a, b)) (K₁.prod K₂) x
    rw [he]
    exact oTerm_inv_of_comm _ _ _ F hF hcomm ht hk x
  have hsplit : ∀ (x : A) (y : B),
      oTerm (MonoidHom.id (A × B)) (K₁.prod K₂) (twCent (MonoidHom.id (A × B)) (a, b) ⊓ K₁.prod K₂) (a, b) F (x, y) =
      ((vol (twCent (MonoidHom.id B) b ⊓ K₂)
          (twCent (MonoidHom.id B) b ⊓ K₂.map (MulAut.conj y).toMonoidHom) : ℚ) : ℂ)⁻¹ *
        oTerm (MonoidHom.id A) K₁ (twCent (MonoidHom.id A) a ⊓ K₁) a (fun v => F (v, y⁻¹ * b * y)) x := by
    intro x y
    unfold oTerm
    rw [hTeq, map_conj_prod, prod_inf_prod, prod_inf_prod, vol_prod]
    simp only [Rat.cast_mul, mul_inv, MonoidHom.id_apply, Prod.inv_mk, Prod.mk_mul_mk]
    ring
  have hbij : Function.Bijective (fun z : DoubleCoset.Quotient (twCent (MonoidHom.id A) a : Set A) K₁ ×
      DoubleCoset.Quotient (twCent (MonoidHom.id B) b : Set B) K₂ =>
        DoubleCoset.mk (twCent (MonoidHom.id (A × B)) (a, b)) (K₁.prod K₂) (z.1.out, z.2.out)) := by
    rw [hTeq]
    exact dcPair_bij _ _ _ _
  unfold orbK
  rw [orbC_eq, ← finsum_comp_equiv (Equiv.ofBijective _ hbij)]
  simp only [Equiv.ofBijective_apply, hinv, hsplit]
  rw [← finsum_comp_equiv (Equiv.prodComm _ _)]
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  have hin : ∀ q : DoubleCoset.Quotient (twCent (MonoidHom.id B) b : Set B) K₂,
      ∑ᶠ p : DoubleCoset.Quotient (twCent (MonoidHom.id A) a : Set A) K₁,
        ((vol (twCent (MonoidHom.id B) b ⊓ K₂)
          (twCent (MonoidHom.id B) b ⊓ K₂.map (MulAut.conj q.out).toMonoidHom) : ℚ) : ℂ)⁻¹ *
        oTerm (MonoidHom.id A) K₁ (twCent (MonoidHom.id A) a ⊓ K₁) a
          (fun v => F (v, q.out⁻¹ * b * q.out)) p.out = 0 := by
    intro q
    apply finsum_mul_eq_zero
    have := h0 (q.out⁻¹ * b * q.out)
    unfold orbK at this
    rwa [orbC_eq] at this
  rcases Set.finite_or_infinite (Function.support fun z :
      DoubleCoset.Quotient (twCent (MonoidHom.id B) b : Set B) K₂ ×
        DoubleCoset.Quotient (twCent (MonoidHom.id A) a : Set A) K₁ =>
      ((vol (twCent (MonoidHom.id B) b ⊓ K₂)
          (twCent (MonoidHom.id B) b ⊓ K₂.map (MulAut.conj z.1.out).toMonoidHom) : ℚ) : ℂ)⁻¹ *
        oTerm (MonoidHom.id A) K₁ (twCent (MonoidHom.id A) a ⊓ K₁) a
          (fun v => F (v, z.1.out⁻¹ * b * z.1.out)) z.2.out) with hfin | hinf
  · rw [finsum_curry _ hfin]
    simp only [hin, finsum_zero]
  · exact finsum_of_infinite_support hinf

end Abstract

section Topology

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

theorem isLocallyConstant_of_right_inv (K₀ : Subgroup Γ) (ho : IsOpen (K₀ : Set Γ)) (f : Γ → ℂ)
    (hf : ∀ g, ∀ c ∈ K₀, f (g * c) = f g) : IsLocallyConstant f := by
  refine fun s => ?_
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (K₀ : Set Γ), ?_, ho.preimage (by fun_prop), ?_⟩
  · intro y hy
    simp only [Set.mem_preimage, SetLike.mem_coe] at hx hy ⊢
    have := hf x (x⁻¹ * y) hy
    rw [mul_inv_cancel_left] at this
    rw [this]
    exact hx
  · simp [K₀.one_mem]

theorem hasCompactSupport_of_doubleCosets (K₀ : Subgroup Γ) (hc : IsCompact (K₀ : Set Γ)) (f : Γ → ℂ) (S : Finset Γ)
    (hf : ∀ g, f g ≠ 0 → ∃ s ∈ S, ∃ a ∈ K₀, ∃ b ∈ K₀, g = a * s * b) : HasCompactSupport f := by
  let U : Set Γ := ⋃ s ∈ S, (fun q : Γ × Γ => q.1 * s * q.2) '' ((K₀ : Set Γ) ×ˢ (K₀ : Set Γ))
  have hU : IsCompact U := by
    refine S.isCompact_biUnion fun s _ => ?_
    exact (hc.prod hc).image (by fun_prop)
  have hsub : Function.support f ⊆ U := by
    intro g hg
    obtain ⟨s, hs, a, ha, b, hb, rfl⟩ := hf g hg
    exact Set.mem_biUnion hs ⟨(a, b), ⟨ha, hb⟩, rfl⟩
  exact IsCompact.of_isClosed_subset hU.closure isClosed_closure (closure_mono hsub)

end Topology

section Split

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem orbK_eq_zero_of_cuspSlices {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] [Algebra G.F k] {P : Pl G k}
    {K : Subgroup G.GAf} {H : Type} [Group H] [TopologicalSpace H] (S : Split P K H) (f : G.GAf → ℂ)
    (hf : f ∈ Hecke ℂ K) (hC : S.Cusp f) (γ : G.GAf) (hs : (P.at γ).charpoly.Separable)
    (hi : ¬ Irreducible (P.at γ).charpoly)
    (hcomm : ∀ a ∈ twCent (MonoidHom.id G.GAf) γ, ∀ b ∈ twCent (MonoidHom.id G.GAf) γ, a * b = b * a) :
    orbK (MonoidHom.id G.GAf) K γ f = 0 := by
  have : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
  obtain ⟨hbi, hfin⟩ := hf
  set F : GL (Fin G.n) k × H → ℂ := fun z => f (S.e.symm z) with hFdef
  have hFbi : ∀ k₁ ∈ S.K₀.prod S.K', ∀ k₂ ∈ S.K₀.prod S.K', ∀ y, F (k₁ * y * k₂) = F y := by
    intro k₁ hk₁ k₂ hk₂ y
    rw [← S.map_eq] at hk₁ hk₂
    obtain ⟨a, ha, rfl⟩ := hk₁
    obtain ⟨b, hb, rfl⟩ := hk₂
    simp only [hFdef, MulEquiv.coe_toMonoidHom, map_mul, MulEquiv.symm_apply_apply]
    exact hbi ⟨a, ha⟩ ⟨b, hb⟩ _
  have hcommB : ∀ s ∈ twCent (MonoidHom.id (GL (Fin G.n) k × H)) (S.e γ),
      ∀ c ∈ twCent (MonoidHom.id (GL (Fin G.n) k × H)) (S.e γ), s * c = c * s := by
    intro s hs c hc
    rw [← GlobalTheory.VanishNonEll.map_twCent_id] at hs hc
    obtain ⟨s', hs', rfl⟩ := hs
    obtain ⟨c', hc', rfl⟩ := hc
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hcomm s' hs' c' hc']
  have hF' : ∀ q ∈ Subgroup.map S.e.toMonoidHom K, ∀ y,
      F (q⁻¹ * y * MonoidHom.id (GL (Fin G.n) k × H) q) = F y := by
    rw [S.map_eq]
    intro q hq y
    exact hFbi q⁻¹ ((S.K₀.prod S.K').inv_mem hq) q hq y
  rw [GlobalTheory.VanishNonEll.orbK_congr_equiv S.e K γ f
    (fun t ht q hq x => oTerm_inv_of_comm _ _ _ F hF' hcommB ht hq x)]
  rw [S.map_eq]
  have hsep : (((S.e γ).1 : GL (Fin G.n) k) : Matrix (Fin G.n) (Fin G.n) k).charpoly.Separable := by
    rw [S.e_at]
    exact hs
  have hirr : ¬ Irreducible (((S.e γ).1 : GL (Fin G.n) k) : Matrix (Fin G.n) (Fin G.n) k).charpoly := by
    rw [S.e_at]
    exact hi
  have h₁ : ∀ s ∈ twCent (MonoidHom.id (GL (Fin G.n) k)) (S.e γ).1,
      ∀ c ∈ twCent (MonoidHom.id (GL (Fin G.n) k)) (S.e γ).1, s * c = c * s :=
    fun s hs c hc => GlobalTheory.CentSep.centraliser_comm_of_separable k (Fin G.n) (S.e γ).1 s c hsep hs hc
  have hmem2 : ∀ s ∈ twCent (MonoidHom.id H) (S.e γ).2,
      ((1 : GL (Fin G.n) k), s) ∈ twCent (MonoidHom.id (GL (Fin G.n) k × H)) (S.e γ) := by
    intro s hs
    show ((1 : GL (Fin G.n) k), s) * S.e γ = S.e γ * ((1 : GL (Fin G.n) k), s)
    refine Prod.ext ?_ hs
    simp
  have h₂ : ∀ s ∈ twCent (MonoidHom.id H) (S.e γ).2,
      ∀ c ∈ twCent (MonoidHom.id H) (S.e γ).2, s * c = c * s := by
    intro s hs c hc
    have := congrArg Prod.snd (hcommB _ (hmem2 s hs) _ (hmem2 c hc))
    simpa using this
  have h0 : ∀ z : H, orbK (MonoidHom.id (GL (Fin G.n) k)) S.K₀ (S.e γ).1 (fun v => F (v, z)) = 0 := by
    intro z
    have hbi0 : ∀ a ∈ S.K₀, ∀ b ∈ S.K₀, ∀ g, F (a * g * b, z) = F (g, z) := by
      intro a ha b hb g
      have := hFbi (a, 1) ⟨ha, S.K'.one_mem⟩ (b, 1) ⟨hb, S.K'.one_mem⟩ (g, z)
      simpa using this
    have hlc : IsLocallyConstant (fun v => F (v, z)) :=
      isLocallyConstant_of_right_inv S.K₀ S.open₀ _ (fun g c hc => by
        have := hbi0 1 S.K₀.one_mem c hc g
        simpa using this)
    have hcs : HasCompactSupport (fun v => F (v, z)) := by
      obtain ⟨T, hT⟩ := hfin
      refine hasCompactSupport_of_doubleCosets S.K₀ S.cpt₀ _ (T.image fun s => (S.e s).1) ?_
      intro v hv
      obtain ⟨s, hsT, a, b, hab⟩ := hT (S.e.symm (v, z)) hv
      have ha : S.e a ∈ S.K₀.prod S.K' := by
        rw [← S.map_eq]
        exact ⟨a, a.2, rfl⟩
      have hb : S.e b ∈ S.K₀.prod S.K' := by
        rw [← S.map_eq]
        exact ⟨b, b.2, rfl⟩
      have hv' : (v, z) = S.e a * S.e s * S.e b := by
        rw [← map_mul, ← map_mul, ← hab, MulEquiv.apply_symm_apply]
      refine ⟨(S.e s).1, Finset.mem_image_of_mem _ hsT, (S.e a).1, ha.1, (S.e b).1, hb.1, ?_⟩
      have := congrArg Prod.fst hv'
      simpa using this
    exact orbK_eq_zero_of_cusp k (Fin G.n) (fun v => F (v, z)) hlc hcs (hC z) (S.e γ).1 hsep hirr
      S.K₀ S.open₀ S.cpt₀ hbi0
  exact orbK_prod_eq_zero_of_slices S.K₀ S.K' (S.e γ).1 (S.e γ).2 F h₁ h₂ (fun q hq y => hFbi q⁻¹
    ((S.K₀.prod S.K').inv_mem hq) q hq y) h0

end Split

end UpperTheory.Gal.Spc
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.PolySupp
set_option autoImplicit false

open Formalism.UG (Hecke conv IsCommensurated)
open UpperTheory.Gal.LocalSmoothExtension (wordFn polyFn)

namespace UpperTheory.Gal.Spc

section Abstract

variable {H J : Type} [Group H] {K : Subgroup H}

private theorem word_mem (hK : IsCommensurated K) {ψ : J → H → ℂ} (hψ : ∀ j, ψ j ∈ Hecke ℂ K) {f : H → ℂ}
    (hf : f ∈ Hecke ℂ K) (w : List J) : wordFn K ψ w f ∈ Hecke ℂ K := by
  induction w with
  | nil => exact hf
  | cons j w ih => exact Formalism.UG.Final.HeckeConvMem H K ℂ hK _ (hψ j) _ ih

private theorem poly_mem (hK : IsCommensurated K) {ψ : J → H → ℂ} (hψ : ∀ j, ψ j ∈ Hecke ℂ K) {f : H → ℂ}
    (hf : f ∈ Hecke ℂ K) (s : List J →₀ ℂ) : polyFn K ψ s f ∈ Hecke ℂ K := by
  unfold UpperTheory.Gal.LocalSmoothExtension.polyFn
  exact Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _ (word_mem hK hψ hf w)

private theorem pow_mem (hK : IsCommensurated K) {u e : H → ℂ} (hu : u ∈ Hecke ℂ K) (he : e ∈ Hecke ℂ K) (n : ℕ) :
    powFn K u e n ∈ Hecke ℂ K := by
  induction n with
  | zero => exact he
  | succ n ih =>
    rw [powFn, Function.iterate_succ_apply']
    exact Formalism.UG.Final.HeckeConvMem H K ℂ hK _ hu _ ih

private theorem fix_step (hK : IsCommensurated K) {e t x : H → ℂ} (he : e ∈ Hecke ℂ K) (ht : t ∈ Hecke ℂ K)
    (hx : x ∈ Hecke ℂ K) (hte : conv K e (conv K t e) = conv K t e) (hex : conv K e x = x) :
    conv K e (conv K t x) = conv K t x := by
  have A := Formalism.UG.Final.HeckeAssoc H K ℂ hK
  have M := Formalism.UG.Final.HeckeConvMem H K ℂ hK
  calc conv K e (conv K t x) = conv K e (conv K t (conv K e x)) := by rw [hex]
    _ = conv K e (conv K (conv K t e) x) := by rw [A t ht e he x hx]
    _ = conv K (conv K e (conv K t e)) x := by rw [A e he (conv K t e) (M t ht e he) x hx]
    _ = conv K (conv K t e) x := by rw [hte]
    _ = conv K t (conv K e x) := by rw [A t ht e he x hx]
    _ = conv K t x := by rw [hex]

private theorem pow_fix (hK : IsCommensurated K) {u e : H → ℂ} (hu : u ∈ Hecke ℂ K) (he : e ∈ Hecke ℂ K)
    (hidem : conv K e e = e) (heu : conv K e (conv K u e) = conv K u e) (n : ℕ) :
    conv K e (powFn K u e n) = powFn K u e n := by
  induction n with
  | zero => exact hidem
  | succ n ih =>
    rw [powFn, Function.iterate_succ_apply']
    exact fix_step hK he hu (pow_mem hK hu he n) heu ih

private theorem word_fix (hK : IsCommensurated K) {ψ : J → H → ℂ} (hψ : ∀ j, ψ j ∈ Hecke ℂ K) {e f : H → ℂ}
    (he : e ∈ Hecke ℂ K) (hf : f ∈ Hecke ℂ K) (heT : ∀ j, conv K e (conv K (ψ j) e) = conv K (ψ j) e)
    (hef : conv K e f = f) (w : List J) : conv K e (wordFn K ψ w f) = wordFn K ψ w f := by
  induction w with
  | nil => exact hef
  | cons j w ih => exact fix_step hK he (hψ j) (word_mem hK hψ hf w) (heT j) ih

private theorem comm_fix (hK : IsCommensurated K) {e a b x : H → ℂ} (he : e ∈ Hecke ℂ K) (ha : a ∈ Hecke ℂ K)
    (hb : b ∈ Hecke ℂ K) (hx : x ∈ Hecke ℂ K) (hab : conv K a (conv K b e) = conv K b (conv K a e))
    (hex : conv K e x = x) : conv K a (conv K b x) = conv K b (conv K a x) := by
  have A := Formalism.UG.Final.HeckeAssoc H K ℂ hK
  have M := Formalism.UG.Final.HeckeConvMem H K ℂ hK
  calc conv K a (conv K b x) = conv K a (conv K b (conv K e x)) := by rw [hex]
    _ = conv K a (conv K (conv K b e) x) := by rw [A b hb e he x hx]
    _ = conv K (conv K a (conv K b e)) x := by rw [A a ha (conv K b e) (M b hb e he) x hx]
    _ = conv K (conv K b (conv K a e)) x := by rw [hab]
    _ = conv K b (conv K (conv K a e) x) := by rw [A b hb (conv K a e) (M a ha e he) x hx]
    _ = conv K b (conv K a (conv K e x)) := by rw [A a ha e he x hx]
    _ = conv K b (conv K a x) := by rw [hex]

private theorem conv_supp {a f : H → ℂ} {g : H} (h : conv K a f g ≠ 0) : ∃ x : H, a x ≠ 0 ∧ f (x⁻¹ * g) ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  unfold Formalism.UG.conv
  apply finsum_eq_zero_of_forall_eq_zero
  intro q
  by_cases ha : a (Quotient.out q) = 0
  · rw [ha, zero_mul]
  · rw [hc _ ha, mul_zero]

private theorem word_supp {ψ : J → H → ℂ} {f : H → ℂ} {R : Set H} (hR : ∀ j a, ψ j a ≠ 0 → ∀ g ∈ R, a * g ∈ R)
    (hf : ∀ g, f g ≠ 0 → g ∈ R) (w : List J) : ∀ g, wordFn K ψ w f g ≠ 0 → g ∈ R := by
  induction w with
  | nil => exact hf
  | cons j w ih =>
    intro g hg
    obtain ⟨x, hx1, hx2⟩ := conv_supp (K := K) (a := ψ j) (f := wordFn K ψ w f) hg
    have hx := hR j x hx1 _ (ih _ hx2)
    simpa using hx

private theorem poly_supp {ψ : J → H → ℂ} {f : H → ℂ} {R : Set H} (hR : ∀ j a, ψ j a ≠ 0 → ∀ g ∈ R, a * g ∈ R)
    (hf : ∀ g, f g ≠ 0 → g ∈ R) (s : List J →₀ ℂ) (g : H) (hg : polyFn K ψ s f g ≠ 0) : g ∈ R := by
  by_contra hgR
  apply hg
  unfold UpperTheory.Gal.LocalSmoothExtension.polyFn
  rw [Finsupp.sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro w _
  rw [Pi.smul_apply, smul_eq_mul]
  have hw : wordFn K ψ w f g = 0 := by
    by_contra hne
    exact hgR (word_supp (K := K) hR hf w g hne)
  rw [hw, mul_zero]

end Abstract

theorem words : Words := by
  intro p _ G Lv J ψ e u u' hψ he hu hrel n
  have hK : IsCommensurated (Lv.K : Subgroup G.GAf) :=
    PI.UnitaryGroupMassFormula.AdIndexEq.commensurated_of_isOpen_isCompact _ Lv.K.isOpen Lv.compact
  have hP := pow_mem hK hu he n
  have hfix := pow_fix hK hu he hrel.idem hrel.eu n
  refine ⟨hP, fun s => poly_mem hK hψ hP s, fun j j' w => ?_, fun R hR hf s g hg => poly_supp hR hf s g hg⟩
  exact comm_fix hK he (hψ j) (hψ j') (word_mem hK hψ hP w) (hrel.TT j j') (word_fix hK hψ he hP hrel.eT hfix w)

end UpperTheory.Gal.Spc
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.SpecAlg
open Module UpperTheory.Gal.CertificateRingHomMap

namespace UpperTheory.Gal.Spc

private def diag {Q : Type} (W : Q → Type) [∀ q, AddCommGroup (W q)] [∀ q, Module ℂ (W q)] :
    (∀ q, End ℂ (W q)) →ₐ[ℂ] End ℂ (∀ q, W q) where
  toFun f := LinearMap.pi fun q => f q ∘ₗ LinearMap.proj q
  map_one' := LinearMap.ext fun _ => funext fun _ => rfl
  map_mul' _ _ := LinearMap.ext fun _ => funext fun _ => rfl
  map_zero' := LinearMap.ext fun _ => funext fun _ => rfl
  map_add' _ _ := LinearMap.ext fun _ => funext fun _ => rfl
  commutes' _ := LinearMap.ext fun _ => funext fun _ => rfl

private theorem diag_apply {Q : Type} (W : Q → Type) [∀ q, AddCommGroup (W q)] [∀ q, Module ℂ (W q)]
    (f : ∀ q, End ℂ (W q)) (x : ∀ q, W q) (q : Q) : diag W f x q = f q (x q) := rfl

end UpperTheory.Gal.Spc

private theorem commute_wop_of_forall_commute {A J : Type} [Ring A] [Algebra ℂ A] (T : J → A) (Z : A)
    (h : ∀ j, Commute (T j) Z) (s : List J →₀ ℂ) : Commute (wop T s) Z := by
  unfold wop Finsupp.sum
  refine Commute.sum_left _ _ _ fun w _ => (Commute.list_prod_left _ _ ?_).smul_left _
  intro x hx
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  exact h j

private theorem algHom_map_wop {A B J : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (T : J → A) (s : List J →₀ ℂ) : f (wop T s) = wop (fun j => f (T j)) s := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [wop, Finsupp.sum, map_sum, map_smul, map_list_prod, List.map_map]
  rfl

private theorem wop_apply_eq_wop_smul_of_apply_eq_smul {M J : Type} [AddCommGroup M] [Module ℂ M] (T : J → End ℂ M) (θ : J → ℂ)
    (x : M) (h : ∀ j, T j x = θ j • x) (s : List J →₀ ℂ) : wop T s x = wop θ s • x := by
  have hw : ∀ w : List J, (List.map T w).prod x = (List.map θ w).prod • x := by
    intro w
    induction w with
    | nil => simp
    | cons j w ih => simp [Module.End.mul_apply, ih, h, smul_smul, mul_comm]
  simp only [wop, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, hw,
    Finset.sum_smul, smul_smul, smul_eq_mul]

private theorem trace_list_prod_mul_eq_prod_mul_trace_of_pow_sub_mul_zero {M J : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (T : J → End ℂ M) (θ : J → ℂ) (hc : ∀ i j, Commute (T i) (T j)) (P : End ℂ M)
    (hP : IsIdempotentElem P) (hTP : ∀ j, Commute (T j) P)
    (hN : ∀ j, ∃ N : ℕ, (T j - algebraMap ℂ (End ℂ M) (θ j)) ^ N * P = 0) (w : List J) :
    ∀ Z : End ℂ M, (∀ j, Commute (T j) Z) → Commute Z P →
      LinearMap.trace ℂ M ((List.map T w).prod * Z * P) =
        (List.map θ w).prod * LinearMap.trace ℂ M (Z * P) := by
  induction w with
  | nil => intro Z _ _; simp
  | cons j w ih =>
    intro Z hZ hZP
    have hY : ∀ i, Commute (T i) ((List.map T w).prod * Z) := fun i =>
      (Commute.list_prod_right _ _ (by
        intro x hx
        obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
        exact hc i k)).mul_right (hZ i)
    have hYP : Commute ((List.map T w).prod * Z) P :=
      (Commute.list_prod_left _ _ (by
        intro x hx
        obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
        exact (hTP k))).mul_left hZP
    obtain ⟨N, hN⟩ := hN j
    have hDY : Commute (T j - algebraMap ℂ (End ℂ M) (θ j)) ((List.map T w).prod * Z) :=
      (hY j).sub_left (Algebra.commutes _ _)
    have hDP : Commute (T j - algebraMap ℂ (End ℂ M) (θ j)) P :=
      (hTP j).sub_left (Algebra.commutes _ _)
    have hnil : IsNilpotent ((T j - algebraMap ℂ (End ℂ M) (θ j)) * P * ((List.map T w).prod * Z)) := by
      have h1 : IsNilpotent ((T j - algebraMap ℂ (End ℂ M) (θ j)) * P) :=
        ⟨N + 1, by rw [hDP.mul_pow, hP.pow_succ_eq, pow_succ', mul_assoc, hN, mul_zero]⟩
      exact (Commute.mul_left hDY hYP.symm).isNilpotent_mul_right h1
    have h0 := (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero
    have e1 : (T j - algebraMap ℂ (End ℂ M) (θ j)) * P * ((List.map T w).prod * Z) =
        T j * ((List.map T w).prod * Z * P) - θ j • ((List.map T w).prod * Z * P) := by
      rw [mul_assoc, ← hYP.eq]
      simp only [sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    rw [e1, map_sub, map_smul, sub_eq_zero, smul_eq_mul] at h0
    simp only [List.map_cons, List.prod_cons]
    rw [show T j * (List.map T w).prod * Z * P = T j * ((List.map T w).prod * Z * P) by
      simp only [mul_assoc], h0, ih Z hZ hZP, mul_assoc]

private theorem trace_wop_mul_eq_wop_mul_trace_of_pow_sub_mul_zero {M J : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (T : J → End ℂ M) (θ : J → ℂ) (hc : ∀ i j, Commute (T i) (T j)) (P : End ℂ M)
    (hP : IsIdempotentElem P) (hTP : ∀ j, Commute (T j) P)
    (hN : ∀ j, ∃ N : ℕ, (T j - algebraMap ℂ (End ℂ M) (θ j)) ^ N * P = 0) (Z : End ℂ M)
    (hZ : ∀ j, Commute (T j) Z) (hZP : Commute Z P) (s : List J →₀ ℂ) :
    LinearMap.trace ℂ M (wop T s * Z * P) = wop θ s * LinearMap.trace ℂ M (Z * P) := by
  have hw := fun w => trace_list_prod_mul_eq_prod_mul_trace_of_pow_sub_mul_zero T θ hc P hP hTP hN w Z hZ hZP
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [wop, Finsupp.sum, Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, hw, smul_eq_mul]
  exact Finset.sum_congr rfl fun w _ => by ring

private theorem commute_mul_and_idempotent_of_rel_mul {A J : Type} [Ring A] {T : J → A} {e u u' : A}
    (h : UpperTheory.Gal.Spc.Rel (fun x1 x2 : A => x1 * x2) T e u u') :
    (∀ i j, Commute (T i * e) (T j * e)) ∧ (∀ j, Commute (T j * e) (u * e)) ∧
      (∀ j, Commute (T j * e) e) ∧ Commute (u * e) e ∧ u' * (u * e) = e ∧ e * e = e := by
  have idem : e * e = e := h.idem
  have eT : ∀ j, e * (T j * e) = T j * e := h.eT
  have eu : e * (u * e) = u * e := h.eu
  have TT : ∀ i j, T i * (T j * e) = T j * (T i * e) := h.TT
  have uT : ∀ j, u * (T j * e) = T j * (u * e) := h.uT
  refine ⟨fun i j => ?_, fun j => ?_, fun j => ?_, ?_, h.inv, idem⟩
  · show T i * e * (T j * e) = T j * e * (T i * e)
    rw [mul_assoc, eT, mul_assoc, eT, TT]
  · show T j * e * (u * e) = u * e * (T j * e)
    rw [mul_assoc, eu, mul_assoc, eT, uT]
  · show T j * e * e = e * (T j * e)
    rw [mul_assoc, idem, eT]
  · show u * e * e = e * (u * e)
    rw [mul_assoc, idem, eu]

private theorem list_prod_map_mul_eq_prod_map_mul_right_of_left_fixed {A J : Type} [Ring A] (T : J → A) (e : A)
    (eT : ∀ j, e * (T j * e) = T j * e) (X : A) (hX : e * X = X) (w : List J) :
    (List.map T w).prod * X = (List.map (fun j => T j * e) w).prod * X ∧
      e * ((List.map (fun j => T j * e) w).prod * X) = (List.map (fun j => T j * e) w).prod * X := by
  induction w with
  | nil => simp [hX]
  | cons j w ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [List.map_cons, List.prod_cons]
    constructor
    · calc T j * (List.map T w).prod * X = T j * ((List.map T w).prod * X) := mul_assoc _ _ _
        _ = T j * (e * ((List.map (fun j => T j * e) w).prod * X)) := by rw [h1, h2]
        _ = T j * e * (List.map (fun j => T j * e) w).prod * X := by simp only [mul_assoc]
    · calc e * (T j * e * (List.map (fun j => T j * e) w).prod * X)
          = e * (T j * e) * ((List.map (fun j => T j * e) w).prod * X) := by simp only [mul_assoc]
        _ = T j * e * (List.map (fun j => T j * e) w).prod * X := by rw [eT]; simp only [mul_assoc]

private theorem wop_mul_eq_wop_mul_right_mul_of_left_fixed {A J : Type} [Ring A] [Algebra ℂ A] (T : J → A) (e : A)
    (eT : ∀ j, e * (T j * e) = T j * e) (X : A) (hX : e * X = X) (s : List J →₀ ℂ) :
    wop T s * X = wop (fun j => T j * e) s * X ∧
      e * (wop (fun j => T j * e) s * X) = wop (fun j => T j * e) s * X := by
  simp only [wop, Finsupp.sum, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  exact ⟨Finset.sum_congr rfl fun w _ => by rw [(list_prod_map_mul_eq_prod_map_mul_right_of_left_fixed T e eT X hX w).1],
    Finset.sum_congr rfl fun w _ => by rw [(list_prod_map_mul_eq_prod_map_mul_right_of_left_fixed T e eT X hX w).2]⟩

private theorem pow_mul_eq_mul_pow_mul_of_idempotent_of_commute {A : Type} [Ring A] (e u : A) (idem : e * e = e)
    (hc : Commute (u * e) e) (n : ℕ) :
    e * ((u * e) ^ n * e) = (u * e) ^ n * e ∧ u ^ n * e = (u * e) ^ n * e := by
  have h1 : ∀ m : ℕ, e * ((u * e) ^ m * e) = (u * e) ^ m * e := fun m => by
    rw [← mul_assoc, (hc.symm.pow_right m).eq, mul_assoc, idem]
  refine ⟨h1 n, ?_⟩
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_assoc, ih, pow_succ', mul_assoc, mul_assoc, h1 m]

private theorem trace_diag_eq_sum_trace {Q : Type} [Fintype Q] (W : Q → Type) [∀ q, AddCommGroup (W q)]
    [∀ q, Module ℂ (W q)] [∀ q, FiniteDimensional ℂ (W q)] (f : ∀ q, End ℂ (W q)) :
    LinearMap.trace ℂ (∀ q, W q) (UpperTheory.Gal.Spc.diag W f) = ∑ q, LinearMap.trace ℂ (W q) (f q) := by
  classical
  let b : ∀ q, Basis (Fin (Module.finrank ℂ (W q))) ℂ (W q) := fun q => Module.finBasis ℂ (W q)
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basis b)]
  simp only [fun q => LinearMap.trace_eq_matrix_trace ℂ (b q) (f q), Matrix.trace, Matrix.diag,
    LinearMap.toMatrix_apply, Fintype.sum_sigma, Pi.basis_apply, Pi.basis_repr]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
  rw [UpperTheory.Gal.Spc.diag_apply, Pi.single_eq_same]

open UpperTheory.Gal.Spc in
theorem UpperTheory.Gal.Spc.specAlg :
    UpperTheory.Gal.Spc.SpecAlg := by
  classical
  intro Q J _ W _ _ _ T e u u' θ hrel hex
  obtain ⟨q0, x0, hx0, hex0, hTx0⟩ := hex
  have F := fun q => commute_mul_and_idempotent_of_rel_mul (hrel q)
  let D := UpperTheory.Gal.Spc.diag W
  let t : J → ∀ q, End ℂ (W q) := fun j q => T q j * e q
  let v : ∀ q, End ℂ (W q) := fun q => u q * e q
  have hc : ∀ i j, Commute (D (t i)) (D (t j)) := fun i j =>
    Commute.map (show t i * t j = t j * t i from funext fun q => ((F q).1 i j).eq) D
  have hV : ∀ j, Commute (D (t j)) (D v) := fun j =>
    Commute.map (show t j * v = v * t j from funext fun q => ((F q).2.1 j).eq) D
  have hE : ∀ j, Commute (D (t j)) (D e) := fun j =>
    Commute.map (show t j * e = e * t j from funext fun q => ((F q).2.2.1 j).eq) D
  have hVE : Commute (D v) (D e) :=
    Commute.map (show v * e = e * v from funext fun q => (F q).2.2.2.1.eq) D
  have hUV : D u' * D v = D e := by
    rw [← map_mul]
    exact congrArg D (funext fun q => (F q).2.2.2.2.1)
  have hEi : IsIdempotentElem (D e) := by
    show D e * D e = D e
    rw [← map_mul]
    exact congrArg D (funext fun q => (F q).2.2.2.2.2)
  obtain ⟨a, hθa, hPi, hN⟩ := pProjOne_holds ℂ (End ℂ (∀ q, W q)) J (fun j => D (t j)) hc θ
  have hTP : ∀ j, Commute (D (t j)) (wop (fun j => D (t j)) a) := fun j =>
    (commute_wop_of_forall_commute _ _ (fun i => hc i j) a).symm
  have hPE : Commute (wop (fun j => D (t j)) a) (D e) := commute_wop_of_forall_commute _ _ hE a
  have hPV : Commute (wop (fun j => D (t j)) a) (D v) := commute_wop_of_forall_commute _ _ hV a
  have hTX : ∀ j, D (t j) (Pi.single q0 x0) = θ j • Pi.single q0 x0 := by
    intro j
    funext q
    rw [UpperTheory.Gal.Spc.diag_apply, Pi.smul_apply]
    by_cases hq : q = q0
    · subst hq
      simp only [t, Pi.single_eq_same, Module.End.mul_apply, hex0, hTx0]
    · simp [Pi.single_eq_of_ne hq]
  have hEX : D e (Pi.single q0 x0) = Pi.single q0 x0 := by
    funext q
    rw [UpperTheory.Gal.Spc.diag_apply]
    by_cases hq : q = q0
    · subst hq
      simp only [Pi.single_eq_same, hex0]
    · simp [Pi.single_eq_of_ne hq]
  have hPX : wop (fun j => D (t j)) a (Pi.single q0 x0) = Pi.single q0 x0 := by
    rw [wop_apply_eq_wop_smul_of_apply_eq_smul _ θ _ hTX a, hθa, one_smul]
  have hQ0 : wop (fun j => D (t j)) a * D e ≠ 0 := by
    intro h
    have h2 := congrArg (fun f => f (Pi.single q0 x0)) h
    simp only [Module.End.mul_apply, hEX, hPX, LinearMap.zero_apply] at h2
    exact hx0 (by simpa using congrFun h2 q0)
  have hinj : ∀ x, D v ((wop (fun j => D (t j)) a * D e) x) = 0 →
      (wop (fun j => D (t j)) a * D e) x = 0 := by
    intro x hx
    have h1 : D e ((wop (fun j => D (t j)) a * D e) x) = (wop (fun j => D (t j)) a * D e) x := by
      rw [← Module.End.mul_apply, ← mul_assoc, ← hPE.eq, mul_assoc, hEi.eq]
    calc (wop (fun j => D (t j)) a * D e) x = D e ((wop (fun j => D (t j)) a * D e) x) := h1.symm
      _ = D u' (D v ((wop (fun j => D (t j)) a * D e) x)) :=
        (congrArg (fun f : End ℂ (∀ q, W q) => f ((wop (fun j => D (t j)) a * D e) x)) hUV).symm
      _ = 0 := by rw [hx, map_zero]
  obtain ⟨n, hn1, hn⟩ := pTracePow_holds ℂ (∀ q, W q) _ (D v) (hPi.mul_of_commute hPE hEi) hQ0
    (hPV.mul_left hVE.symm) hinj 1
  refine ⟨n, hn1, a, fun s hs => ?_⟩
  have key : ∀ q, LinearMap.trace ℂ (W q) (wop (T q) (wmul a s) * (u q ^ n * e q)) =
      LinearMap.trace ℂ (W q) (wop (fun j => T q j * e q) a *
        (wop (fun j => T q j * e q) s * ((u q * e q) ^ n * e q))) := by
    intro q
    have h9 := pow_mul_eq_mul_pow_mul_of_idempotent_of_commute (e q) (u q) (F q).2.2.2.2.2 (F q).2.2.2.1 n
    have eT : ∀ j, e q * (T q j * e q) = T q j * e q := (hrel q).eT
    have h8 := wop_mul_eq_wop_mul_right_mul_of_left_fixed (T q) (e q) eT _ h9.1 s
    rw [wop_wmul, h9.2, mul_assoc, h8.1, (wop_mul_eq_wop_mul_right_mul_of_left_fixed (T q) (e q) eT _ h8.2 a).1]
  rw [Finset.sum_congr rfl fun q _ => key q]
  have ev : ∀ q (r : List J →₀ ℂ), (wop t r) q = wop (fun j => T q j * e q) r := fun q r =>
    algHom_map_wop (Pi.evalAlgHom ℂ (fun q => End ℂ (W q)) q) t r
  rw [← trace_diag_eq_sum_trace W (fun q => wop (fun j => T q j * e q) a *
    (wop (fun j => T q j * e q) s * ((u q * e q) ^ n * e q)))]
  have hD : (fun q => wop (fun j => T q j * e q) a *
      (wop (fun j => T q j * e q) s * ((u q * e q) ^ n * e q))) = wop t a * (wop t s * (v ^ n * e)) := by
    funext q
    rw [Pi.mul_apply, Pi.mul_apply, Pi.mul_apply, Pi.pow_apply, ev, ev]
  rw [hD]
  show LinearMap.trace ℂ _ (D (wop t a * (wop t s * (v ^ n * e)))) ≠ 0
  rw [map_mul D, map_mul D, map_mul D, map_pow D, algHom_map_wop D t a, algHom_map_wop D t s,
    LinearMap.trace_mul_comm ℂ]
  have hZ : ∀ j, Commute (D (t j)) (D v ^ n * D e) := fun j => ((hV j).pow_right n).mul_right (hE j)
  have hZP : Commute (D v ^ n * D e) (wop (fun j => D (t j)) a) :=
    (hPV.pow_right n).symm.mul_left hPE.symm
  rw [trace_wop_mul_eq_wop_mul_trace_of_pow_sub_mul_zero (fun j => D (t j)) θ hc _ hPi hTP hN (D v ^ n * D e) hZ hZP s]
  refine mul_ne_zero hs ?_
  rwa [LinearMap.trace_mul_comm ℂ, (hVE.pow_left n).eq, ← mul_assoc]
end
