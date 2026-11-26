module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BcParamEqOfSatUEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSplitPlaceHermitianFrameGLEmbedding
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairVrGramPRatPosDef
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingZeroMeanNormalizedSubgroup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalHeckeOperatorEqSmulOfLocalParameter
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalHeckeOperatorEqSmulOfLocalParameter
noncomputable section

namespace GlobalTheory.LFun.EigLoc

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
open Formalism.MainNotions.SchurIrreducible (IsSplit)

section General

variable {G H : Type} [Group G] [Group H]

theorem comp_symm_mem_hecke (e : G ≃* H) {K : Subgroup G} {K' : Subgroup H} (hK : ∀ g, g ∈ K ↔ e g ∈ K')
    {φ : G → ℂ} (hφ : φ ∈ Hecke ℂ K) : φ ∘ e.symm ∈ Hecke ℂ K' := by
  classical
  have hφ' : IsBiInv K φ ∧ FinDosetSupp K φ := hφ
  obtain ⟨hb, S, hS⟩ := hφ'
  have hsymm : ∀ y : H, y ∈ K' → e.symm y ∈ K := fun y hy => by
    rw [hK, MulEquiv.apply_symm_apply]; exact hy
  show IsBiInv K' (φ ∘ e.symm) ∧ FinDosetSupp K' (φ ∘ e.symm)
  refine ⟨fun a b g => ?_, ⟨S.image e, fun g hg => ?_⟩⟩
  · have := hb ⟨_, hsymm a a.2⟩ ⟨_, hsymm b b.2⟩ (e.symm g)
    simpa only [Function.comp_apply, map_mul] using this
  · obtain ⟨s, hs, a, b, hab⟩ := hS (e.symm g) hg
    refine ⟨e s, ?_, ⟨e a, (hK _).1 a.2⟩, ⟨e b, (hK _).1 b.2⟩, ?_⟩
    · exact Finset.mem_image_of_mem _ hs
    · have := congrArg e hab
      simpa only [MulEquiv.apply_symm_apply, map_mul] using this

theorem heckeVec_eq_comp_symm {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    (e : G ≃* H) {K : Subgroup G} {K' : Subgroup H} (hK : ∀ g, g ∈ K ↔ e g ∈ K')
    {φ : G → ℂ} (hφ : φ ∈ Hecke ℂ K) {x : V} (hx : x ∈ fixed ρ K) :
    heckeVec ρ K φ x = heckeVec (ρ.comp e.symm.toMonoidHom) K' (φ ∘ e.symm) x := by
  classical
  have hfix : ∀ k, k ∈ K → ρ k x = x := fun k hk => by
    have hx' : ∀ h : K, ρ h x = ((1 : K →* ℂˣ) h : ℂ) • x := hx
    simpa using hx' ⟨k, hk⟩
  have hT : ∀ g k, k ∈ K → φ (g * k) • ρ (g * k) x = φ g • ρ g x := by
    intro g k hk
    have hb : IsBiInv K φ := hφ.1
    have h1 : φ (g * k) = φ g := by simpa using hb 1 ⟨k, hk⟩ g
    rw [h1, map_mul, mul_apply_eq_comp, hfix k hk]
  let Q : G ⧸ K ≃ H ⧸ K' := Quotient.congr e.toEquiv (fun a b => by
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, hK]
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, map_mul, map_inv])
  have hQ : ∀ g : G, Q (g : G ⧸ K) = ((e g : H) : H ⧸ K') := fun g => rfl
  unfold heckeVec
  rw [← finsum_comp_equiv Q]
  refine finsum_congr fun c => ?_
  have h1 : (((Q c).out : H) : H ⧸ K') = ((e c.out : H) : H ⧸ K') := by
    rw [QuotientGroup.out_eq', ← hQ, QuotientGroup.out_eq']
  have h2 : (e c.out)⁻¹ * (Q c).out ∈ K' := QuotientGroup.eq.1 h1.symm
  have h3 : c.out⁻¹ * e.symm (Q c).out ∈ K := by
    rw [hK]
    simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using h2
  have h4 := hT c.out _ h3
  rw [mul_inv_cancel_left] at h4
  exact h4.symm

private theorem cell_unif_lemma {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {c : L →+* L}
    {n q m : ℕ} {ϖ ϖ' : L} (hU : IsUnramInv ϖ c q) (hU' : IsUnramInv ϖ' c q) (hm : 2 * m ≤ n)
    (a : Fin m → ℤ) (y : GU c n)
    (H : ∃ u : GU c n, IsUnipU u ∧ ∃ k ∈ KU c n,
      (((y : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        tMat ϖ n m a * (((u : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          (((k : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) :
    ∃ u : GU c n, IsUnipU u ∧ ∃ k ∈ KU c n,
      (((y : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        tMat ϖ' n m a * (((u : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          (((k : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
  obtain ⟨u, hu, k, hk, hy⟩ := H
  have hne : ∀ t : L, IsUnramInv t c q → t ≠ 0 := fun t ht h0 => by
    have h := ht.2.2.2.1
    simp [h0] at h
  have hg0 : ∀ t : L, t ≠ 0 → ∀ i, tMat t n m a i i ≠ 0 := by
    intro t ht i
    simp only [tMat, Matrix.diagonal_apply_eq]
    split_ifs <;> first | exact zpow_ne_zero _ ht | exact one_ne_zero
  have hvv : Valued.v ϖ = Valued.v ϖ' := hU.2.2.2.1.trans hU'.2.2.2.1.symm
  have hgv : ∀ i, Valued.v (tMat ϖ n m a i i) = Valued.v (tMat ϖ' n m a i i) := by
    intro i
    simp only [tMat, Matrix.diagonal_apply_eq]
    split_ifs <;> simp only [map_zpow₀, hvv]
  have htm : ∀ t : L, tMat t n m a = Matrix.diagonal (fun i => tMat t n m a i i) := by
    intro t
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Matrix.diagonal_apply_ne _ hij]
      simp only [tMat, Matrix.diagonal_apply_ne _ hij]
  set e : Fin n → L := fun i => tMat ϖ n m a i i / tMat ϖ' n m a i i with he_def
  have he0 : ∀ i, e i ≠ 0 := fun i => div_ne_zero (hg0 ϖ (hne ϖ hU) i) (hg0 ϖ' (hne ϖ' hU') i)
  obtain ⟨t, ht⟩ := Formalism.UG.P.fSatake_tMat_exists hU hm a
  obtain ⟨t', ht'⟩ := Formalism.UG.P.fSatake_tMat_exists hU' hm a
  have hb : ∀ i, c (tMat ϖ n m a i i) * tMat ϖ n m a i.rev i.rev = 1 := fun i => by
    have := Formalism.UG.P.fSatake_unit_diag (Formalism.UG.P.fSatake_borel_tMat ht) i
    rwa [ht] at this
  have hb' : ∀ i, c (tMat ϖ' n m a i i) * tMat ϖ' n m a i.rev i.rev = 1 := fun i => by
    have := Formalism.UG.P.fSatake_unit_diag (Formalism.UG.P.fSatake_borel_tMat ht') i
    rwa [ht'] at this
  have hce : ∀ i, c (e i) * e i.rev = 1 := fun i => by
    simp only [he_def, map_div₀]
    rw [div_mul_div_comm, hb i, hb' i, div_one]
  obtain ⟨D, hD, hD'⟩ := Formalism.UG.P.fSatake_diag_exists e hce
  have hev : ∀ i, Valued.v (e i) = 1 := fun i => by
    simp only [he_def]
    rw [map_div₀, hgv i, div_self]
    exact (Valuation.ne_zero_iff _).2 (hg0 ϖ' (hne ϖ' hU') i)
  have hDK : D ∈ KU c n := Formalism.UG.P.fSatake_diag_mem_K hD hD' hev
  have hDD : (((D⁻¹ : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      (((D : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  have hsplit : tMat ϖ n m a = tMat ϖ' n m a * (((D : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    rw [hD, htm ϖ, htm ϖ', Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [mul_div_cancel₀ _ (hg0 ϖ' (hne ϖ' hU') i)]
  obtain ⟨hub, hud⟩ := hu
  refine ⟨D * u * D⁻¹, ?_, D * k, Subgroup.mul_mem _ hDK hk, ?_⟩
  · have hmat : ∀ i j, (((D * u * D⁻¹ : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
        e i * (((u : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j * (e j)⁻¹ := by
      intro i j
      simp only [Subgroup.coe_mul, Units.val_mul, hD, hD', Matrix.mul_diagonal, Matrix.diagonal_mul]
    unfold IsUnipU IsBorelU
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hmat, hub i j hij, mul_zero, zero_mul]
    · rw [hmat, hud i, mul_one, mul_inv_cancel₀ (he0 i)]
  · rw [hy, hsplit]
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (((D⁻¹ : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L), hDD, Matrix.one_mul]

private theorem satU_eq_of_isUnramInv {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {c : L →+* L}
    {n q m : ℕ} {ϖ ϖ' : L} (hU : IsUnramInv ϖ c q) (hU' : IsUnramInv ϖ' c q) (hm : 2 * m ≤ n)
    (f : GU c n → ℂ) (α : Fin m → ℂ) : SatU ϖ q f α = SatU ϖ' q f α := by
  unfold SatU
  refine finsum_congr fun a => ?_
  congr 1
  refine finsum_congr fun x => ?_
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (cell_unif_lemma hU hU' hm a _ h1) h2
  · exact absurd (cell_unif_lemma hU' hU hm a _ h2) h1
  · rfl

end General

theorem heckeVec_eq_smul_of_isParamVec : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v) (B : Multiset ℂˣ), ∀ φ ∈ Hecke ℂ (stabLoc σ J L v), ∃ z : ℂ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLoc σ J v) V) (x : V), IsParamVec σ J L h ρ x B → heckeVec ρ (stabLoc σ J L v) φ x = z • x := by
  intro F E _ _ _ _ _ σ n J L v w h B φ hφ
  classical
  by_cases hsp : IsSplit (E := E) v ∧
      ∃ e : GLoc σ J v ≃* GL (Fin n) (w.adicCompletion E), IsSplitChart σ J L h e
  · obtain ⟨hv, e0, he0⟩ := hsp
    obtain ⟨z, hz⟩ := GlobalTheory.T.satake_determines_sphericalHeckeCharacter_GL E w n B (φ ∘ e0.symm) (comp_symm_mem_hecke e0 he0.2 hφ)
    refine ⟨z, fun V _ _ ρ x hx => ?_⟩
    rw [heckeVec_eq_comp_symm e0 he0.2 hφ hx.mem_fixed]
    exact hz V (ρ.comp e0.symm.toMonoidHom) x (hx.isSatVecGL hv he0)
  by_cases hin : ∃ (c : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E)
      (e : GLoc σ J v ≃* GU c n) (α : Fin (n / 2) → ℂˣ),
      IsUnramInv ϖ c (qV F v) ∧ IsInertChart σ J L h c e ∧ B = GlobalTheory.LGrp.bcParam n α
  · obtain ⟨c0, ϖ0, e0, α0, hU0, hC0, hB0⟩ := hin
    have hmem := comp_symm_mem_hecke e0 hC0.2.2 hφ
    refine ⟨SatU ϖ0 (qV F v) (φ ∘ e0.symm) (fun i => (α0 i : ℂ)), fun V _ _ ρ x hx => ?_⟩
    have hfx := hx.mem_fixed
    rcases hx with ⟨hv, e, he, -⟩ | ⟨-, c, ϖ, e, α, hU, hC, hS, hB⟩
    · exact (hsp ⟨hv, e, he⟩).elim
    · obtain rfl : c = c0 := IsConjAt.unique hC.1 hC0.1
      have hS0 := IsSatVecU.of_chart hC hC0 hS
      rw [heckeVec_eq_comp_symm e0 hC0.2.2 hφ hfx, hS0.2.2 _ hmem]
      congr 1
      rw [satU_eq_of_isUnramInv hU hU0 (Nat.mul_div_le n 2)]
      exact GlobalTheory.T.unitarySatakeTransform_eq_of_baseChangeSatakeParameter_eq _ ϖ0 c (qV F v) n hU0 α α0 (hB.symm.trans hB0) _ hmem
  · refine ⟨0, fun V _ _ ρ x hx => ?_⟩
    rcases hx with ⟨hv, e, he, -⟩ | ⟨-, c, ϖ, e, α, hU, hC, -, hB⟩
    · exact (hsp ⟨hv, e, he⟩).elim
    · exact (hin ⟨c, ϖ, e, α, hU, hC, hB⟩).elim

end GlobalTheory.LFun.EigLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalHeckeOperatorEqSmulOfLocalParameterStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalHeckeOperator_eq_smul_of_localParameter : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v) (B : Multiset ℂˣ), ∀ φ ∈ Hecke ℂ (stabLoc σ J L v), ∃ z : ℂ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLoc σ J v) V) (x : V), IsParamVec σ J L h ρ x B → heckeVec ρ (stabLoc σ J L v) φ x = z • x := by
  first | exact @GlobalTheory.LFun.EigLoc.heckeVec_eq_smul_of_isParamVec | exact GlobalTheory.LFun.EigLoc.heckeVec_eq_smul_of_isParamVec | (intros; apply GlobalTheory.LFun.EigLoc.heckeVec_eq_smul_of_isParamVec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StableRangeOneAdelesCmField
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StableRangeOneAdelesCmField
noncomputable section

namespace GlobalTheory.StableRange

open IsDedekindDomain NumberField

theorem exists_inv_mod_maximal {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]
    [Algebra.IsIntegral B S]
    (hB : ∀ x : B, ∃ y : B, ∀ z : B, IsUnit (x * (1 - x * y) * z + 1)) (b : S) :
    ∃ y : S, ∀ m : Ideal S, m.IsMaximal → b ∈ m ∨ 1 - b * y ∈ m := by
  let I : Ideal S := (Ideal.jacobson (⊥ : Ideal B)).map (algebraMap B S)
  have hI : ∀ m : Ideal S, m.IsMaximal → I ≤ m := by
    intro m hm
    rw [Ideal.map_le_iff_le_comap]
    have : (m.comap (algebraMap B S)).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := B) m
    exact sInf_le ⟨bot_le, this⟩
  have hp : ∀ p : Ideal S, p.IsPrime → I ≤ p → p.IsMaximal := by
    intro p hp hIp
    rw [Ideal.map_le_iff_le_comap] at hIp
    have hq : (p.comap (algebraMap B S)).IsPrime := Ideal.comap_isPrime _ _
    have hmax : (p.comap (algebraMap B S)).IsMaximal := by
      rw [Ideal.isMaximal_iff]
      refine ⟨(Ideal.ne_top_iff_one _).1 hq.ne_top, fun J x hJ hx hxJ => ?_⟩
      obtain ⟨y, hy⟩ := hB x
      have h1 : x * (1 - x * y) ∈ p.comap (algebraMap B S) :=
        hIp (Ideal.mem_jacobson_bot.2 hy)
      have h2 := (hq.mem_or_mem h1).resolve_left hx
      have := J.add_mem (hJ h2) (J.mul_mem_right y hxJ)
      simpa using this
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := B) p hmax
  let M : Submonoid S :=
    { carrier := {s | ∃ (n : ℕ) (y : S), s = b ^ n * (1 - b * y)}
      one_mem' := ⟨0, 0, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨n, y, rfl⟩ ⟨k, w, rfl⟩
        exact ⟨n + k, y + w - b * y * w, by ring⟩ }
  by_cases hd : Disjoint (I : Set S) (M : Set S)
  · exfalso
    obtain ⟨p, hpp, hIp, hdis⟩ := Ideal.exists_le_prime_disjoint I M hd
    have hm := hp p hpp hIp
    have hb : b ∉ p := fun h => Set.disjoint_left.1 hdis h ⟨1, 0, by simp⟩
    obtain ⟨y, i, hi, hy⟩ := hm.exists_inv hb
    refine Set.disjoint_left.1 hdis hi ⟨0, y, ?_⟩
    rw [← hy]; ring
  · obtain ⟨s, hsI, n, y, rfl⟩ := Set.not_disjoint_iff.1 hd
    refine ⟨y, fun m hm => ?_⟩
    rcases hm.isPrime.mem_or_mem (hI m hm hsI) with h | h
    · exact Or.inl (hm.isPrime.mem_of_pow_mem n h)
    · exact Or.inr h

theorem stable_of_isIntegral {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]
    [Algebra.IsIntegral B S]
    (hB : ∀ x : B, ∃ y : B, ∀ z : B, IsUnit (x * (1 - x * y) * z + 1)) (a b : S)
    (h : IsCoprime a b) : ∃ t : S, IsUnit (a + t * b) := by
  obtain ⟨y, hy⟩ := exists_inv_mod_maximal hB b
  obtain ⟨u, w, huw⟩ := h
  refine ⟨y * (1 - a), ?_⟩
  by_contra hn
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits (a := a + y * (1 - a) * b) hn
  apply hm.ne_top
  rw [Ideal.eq_top_iff_one]
  rcases hy m hm with hb | hb
  · have e : (1 : S) = u * (a + y * (1 - a) * b) + (w - u * (y * (1 - a))) * b := by
      linear_combination -huw
    rw [e]
    exact m.add_mem (m.mul_mem_left _ hmem) (m.mul_mem_left _ hb)
  · have e : (1 : S) = (a + y * (1 - a) * b) + (1 - a) * (1 - b * y) := by ring
    rw [e]
    exact m.add_mem hmem (m.mul_mem_left _ hb)

theorem stable_of_subrings {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    [Algebra.IsIntegral A R]
    (hA : ∀ s : Finset A, ∃ B : Subring A, (s : Set A) ⊆ B ∧
      ∀ x : B, ∃ y : B, ∀ z : B, IsUnit (x * (1 - x * y) * z + 1))
    (a b : R) (h : IsCoprime a b) : ∃ t : R, IsUnit (a + t * b) := by
  classical
  obtain ⟨u, w, huw⟩ := h
  choose p hpm hp using fun r : R => (Algebra.IsIntegral.isIntegral (R := A) r)
  obtain ⟨B, hs, hB⟩ := hA ((p a).coeffs ∪ (p b).coeffs ∪ (p u).coeffs ∪ (p w).coeffs)
  have key : ∀ r : R, ((p r).coeffs : Set A) ⊆ B → IsIntegral B r := by
    intro r hr
    refine ⟨(p r).toSubring B hr, (Polynomial.monic_toSubring _ _ hr).2 (hpm r), ?_⟩
    have e : algebraMap B R = (algebraMap A R).comp B.subtype := rfl
    rw [e, ← Polynomial.eval₂_map, Polynomial.map_toSubring]
    exact hp r
  simp only [Finset.coe_union, Set.union_subset_iff] at hs
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hs
  obtain ⟨t, ht⟩ := stable_of_isIntegral (S := integralClosure B R) hB ⟨a, key a h1⟩ ⟨b, key b h2⟩
    ⟨⟨u, key u h3⟩, ⟨w, key w h4⟩, Subtype.ext huw⟩
  exact ⟨t, ht.map (integralClosure B R).val⟩

variable (K : Type*) [Field K] [NumberField K]

def intOutside (T : Set (HeightOneSpectrum (𝓞 K))) : Subring (AdeleRing (𝓞 K) K) where
  carrier := {x | ∀ v ∉ T, x.2 v ∈ v.adicCompletionIntegers K}
  mul_mem' ha hb v hv := mul_mem (ha v hv) (hb v hv)
  one_mem' v _ := one_mem (v.adicCompletionIntegers K)
  add_mem' ha hb v hv := add_mem (ha v hv) (hb v hv)
  zero_mem' v _ := zero_mem (v.adicCompletionIntegers K)
  neg_mem' ha v hv := neg_mem (ha v hv)

def mkAdele {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T.Finite)
    (f : ∀ w : InfinitePlace K, w.Completion) (g : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K)
    (hg : ∀ v ∉ T, g v ∈ v.adicCompletionIntegers K) : intOutside K T :=
  ⟨(f, ⟨g, hT.subset fun v hv => by
    by_contra h
    exact hv (hg v h)⟩), hg⟩

theorem isUnit_intOutside {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T.Finite) (x : intOutside K T)
    (h1 : ∀ w, x.1.1 w ≠ 0) (h2 : ∀ v, x.1.2 v ≠ 0) (h3 : ∀ v ∉ T, Valued.v (x.1.2 v) = 1) :
    IsUnit x := by
  refine IsUnit.of_mul_eq_one (mkAdele K hT (fun w => (x.1.1 w)⁻¹) (fun v => (x.1.2 v)⁻¹)
    fun v hv => ?_) ?_
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h3 v hv, inv_one]
  · refine Subtype.ext (Prod.ext (funext fun w => ?_) (FiniteAdeleRing.ext _ fun v => ?_))
    · exact mul_inv_cancel₀ (h1 w)
    · exact mul_inv_cancel₀ (h2 v)

theorem mul_one_sub_mul_inv {L : Type*} [Field L] (x : L) : x * (1 - x * x⁻¹) = 0 := by
  by_cases h : x = 0
  · simp [h]
  · simp [h]

open Classical in
theorem regular_intOutside {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T.Finite)
    (x : intOutside K T) :
    ∃ y : intOutside K T, ∀ z : intOutside K T, IsUnit (x * (1 - x * y) * z + 1) := by
  refine ⟨mkAdele K hT (fun w => (x.1.1 w)⁻¹)
    (fun v => if v ∈ T ∨ Valued.v (x.1.2 v) = 1 then (x.1.2 v)⁻¹ else 0) fun v hv => ?_, fun z => ?_⟩
  · split_ifs with h
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h.resolve_left hv, inv_one]
    · exact zero_mem _
  · have hv : ∀ v, Valued.v (x.1.2 v * (1 - x.1.2 v *
        (if v ∈ T ∨ Valued.v (x.1.2 v) = 1 then (x.1.2 v)⁻¹ else 0)) * z.1.2 v + 1) = 1 := by
      intro v
      split_ifs with h
      · rw [mul_one_sub_mul_inv]; simp
      · obtain ⟨hT', h1⟩ := not_or.1 h
        have hx : Valued.v (x.1.2 v) ≤ 1 := x.2 v hT'
        have hz : Valued.v (z.1.2 v) ≤ 1 := z.2 v hT'
        rw [mul_zero, sub_zero, mul_one, add_comm]
        apply Valuation.map_one_add_of_lt
        rw [map_mul]
        exact (mul_le_of_le_one_right' hz).trans_lt (lt_of_le_of_ne hx h1)
    refine isUnit_intOutside K hT _ (fun w => ?_) (fun v => ?_) (fun v _ => hv v)
    · change x.1.1 w * (1 - x.1.1 w * (x.1.1 w)⁻¹) * z.1.1 w + 1 ≠ 0
      rw [mul_one_sub_mul_inv]; simp
    · intro h0
      have h1 := hv v
      have h2 : x.1.2 v * (1 - x.1.2 v *
        (if v ∈ T ∨ Valued.v (x.1.2 v) = 1 then (x.1.2 v)⁻¹ else 0)) * z.1.2 v + 1 = 0 := h0
      rw [h2] at h1
      simp at h1

theorem stable_adele {R : Type*} [CommRing R] [Algebra (AdeleRing (𝓞 K) K) R]
    [Algebra.IsIntegral (AdeleRing (𝓞 K) K) R] (a b : R) (h : IsCoprime a b) :
    ∃ t : R, IsUnit (a + t * b) := by
  refine stable_of_subrings (A := AdeleRing (𝓞 K) K) (fun s => ?_) a b h
  have hT : (⋃ x ∈ (s : Set (AdeleRing (𝓞 K) K)),
      {v : HeightOneSpectrum (𝓞 K) | x.2 v ∉ v.adicCompletionIntegers K}).Finite :=
    s.finite_toSet.biUnion fun x _ => x.2.2
  refine ⟨intOutside K _, fun x hx v hv => ?_, regular_intOutside K hT⟩
  by_contra h
  exact hv (Set.mem_biUnion hx h)

end GlobalTheory.StableRange

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem GlobalTheory.StableRange.adeles_stableRange_one :
    ∀ (D : D7) (a b : AE D), IsCoprime a b → ∃ t : AE D, IsUnit (a + t * b) :=
  fun D a b h => GlobalTheory.StableRange.stable_adele D.host.F a b h
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StableRangeOneAdelesCmFieldStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stableRangeOne_adeles_cmField : ∀ (D : D7) (a b : AE D), IsCoprime a b → ∃ t : AE D, IsUnit (a + t * b) := by
  first | exact @GlobalTheory.StableRange.adeles_stableRange_one | exact GlobalTheory.StableRange.adeles_stableRange_one | (intros; apply GlobalTheory.StableRange.adeles_stableRange_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOpenAddSubgroupFinitePoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOpenAddSubgroupFinitePoints
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Topology

namespace GlobalTheory.FinSubgroup

theorem exists_openAddSubgroup_finite_points :
    ∀ (D : D7) (V : Set (AE D)), V ∈ nhds (0 : AE D) →
      ∃ U : AddSubgroup (AE D), IsOpen (U : Set (AE D)) ∧ ∀ a ∈ U, infPart D a = 0 → a ∈ V := by
  intro D V hV
  obtain ⟨e, he, hc, hcs⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  letI : TopologicalSpace (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)
  letI : TopologicalSpace (InfiniteAdeleRing D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (InfiniteAdeleRing D.host.F) (InfiniteAdeleRing D.host.F ⊗[D.host.F] D.host.E)
  have h0 : e.symm 0 = 0 := map_zero _
  have hV' : (e.symm : _ → AE D) ⁻¹' V ∈ 𝓝 ((0 : InfiniteAdeleRing D.host.F ⊗[D.host.F] D.host.E),
      (0 : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) := by
    apply hcs.continuousAt.preimage_mem_nhds
    have : (e.symm : _ → AE D) (0, 0) = 0 := h0
    rw [this]
    exact hV
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 hV'
  obtain ⟨N, hN, hNB⟩ := (GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat D.host.F D.host.E 0 ⊤ (Subsingleton.elim _ _)).2 B hB
  let W : AddSubgroup (GlobalTheory.AdLat.RA D.host.F D.host.E) :=
    (GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E))).map (nsmulAddMonoidHom N)
  have hW : IsOpen (W : Set (GlobalTheory.AdLat.RA D.host.F D.host.E)) := by
    have := GlobalTheory.IdeleParts.isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E N hN
    convert this using 1
    ext z
    simp only [W, AddSubgroup.coe_map, Set.mem_image, SetLike.mem_coe, nsmulAddMonoidHom_apply, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  let f : AE D →+ GlobalTheory.AdLat.RA D.host.F D.host.E := (AddMonoidHom.snd _ _).comp e.toAddMonoidHom
  have hf : Continuous f := continuous_snd.comp hc
  refine ⟨W.comap f, hW.preimage hf, fun a ha hinf => ?_⟩
  have h1 : (e a).1 = 0 := by rw [(he a).1]; exact hinf
  have h2 : (e a).2 ∈ B := by
    obtain ⟨y, hy, hya⟩ := AddSubgroup.mem_map.1 (AddSubgroup.mem_comap.1 ha)
    have : f a = (e a).2 := rfl
    rw [← this, ← hya]
    exact hNB y hy
  have h3 : e a ∈ A ×ˢ B := ⟨by rw [h1]; exact mem_of_mem_nhds hA, h2⟩
  have := hAB h3
  simpa using this

end GlobalTheory.FinSubgroup
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOpenAddSubgroupFinitePointsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_openAddSubgroup_finite_points_alt : ∀ (D : D7) (V : Set (AE D)), V ∈ nhds (0 : AE D) → ∃ U : AddSubgroup (AE D), IsOpen (U : Set (AE D)) ∧ ∀ a ∈ U, infPart D a = 0 → a ∈ V := by
  first | exact @GlobalTheory.FinSubgroup.exists_openAddSubgroup_finite_points | exact GlobalTheory.FinSubgroup.exists_openAddSubgroup_finite_points | (intros; apply GlobalTheory.FinSubgroup.exists_openAddSubgroup_finite_points <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralCompAddEquivEqSmul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HalfTwist

theorem integral_comp_addEquiv_eq_smul {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsAddHaarMeasure] (T : G ≃+ G) (hc : Continuous T) (hc' : Continuous T.symm) :
    ∃ r : ℝ, 0 < r ∧ ∀ φ : G → ℂ, ∫ x, φ (T x) ∂ν = r * ∫ x, φ x ∂ν := by
  haveI : (ν.map T).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map ν T hc hc'
  let hT : G ≃ₜ G := { toEquiv := T.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  have hemb : MeasurableEmbedding T := hT.measurableEmbedding
  refine ⟨((ν.map T).addHaarScalarFactor ν : ℝ), NNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _), ?_⟩
  intro φ
  have e := Measure.isAddLeftInvariant_eq_smul (ν.map T) ν
  rw [← hemb.integral_map φ]
  refine (congrArg (fun μ : Measure G => ∫ y, φ y ∂μ) e).trans ?_
  show ∫ y, φ y ∂(((ν.map T).addHaarScalarFactor ν) • ν) = _
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem isClosed_fix (D : D7) (m n : ℕ) (c : AE D) : IsClosed {x : Mx D m n | ∀ i j, c * x i j = x i j} := by
  obtain ⟨i1, i2, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  have : {x : Mx D m n | ∀ i j, c * x i j = x i j} = ⋂ i, ⋂ j, {x : Mx D m n | c * x i j = x i j} := by
    ext x; simp
  rw [this]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq ?_ ?_
  · exact continuous_const.mul ((continuous_apply j).comp (continuous_apply i))
  · exact (continuous_apply j).comp (continuous_apply i)

theorem integral_twist_fix_eq_smul : ∀ (D : D7) (m n : ℕ) (c : AE D) (H : AddSubgroup (Mx D m n)), (∀ x, x ∈ H ↔ ∀ i j, c * x i j = x i j) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsAddHaarMeasure] (h : GL (Fin m) (AE D)) (a : GL (Fin n) (AE D)), ∃ r : ℝ, 0 < r ∧ ∀ φ : Mx D m n → ℂ, ∫ x : H, φ (h.1 ⬝ x.1 ⬝ a.1) ∂ν = r * ∫ x : H, φ x.1 ∂ν := by
  intro D m n c H hH _ _ ν _ h a
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D m n
  have key : ∀ y : Mx D m n, y ∈ H ↔ c • y = y := by
    intro y
    rw [hH]
    constructor
    · intro hy; ext i j; simpa using hy i j
    · intro hy i j; simpa using congrFun (congrFun hy i) j
  have mem : ∀ (g : GL (Fin m) (AE D)) (b : GL (Fin n) (AE D)) (y : Mx D m n), y ∈ H → g.1 ⬝ y ⬝ b.1 ∈ H := by
    intro g b y hy
    rw [key] at hy ⊢
    show c • (g.1 * y * b.1) = g.1 * y * b.1
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hy]
  have hcl : IsClosed (H : Set (Mx D m n)) := by
    have : (H : Set (Mx D m n)) = {x : Mx D m n | ∀ i j, c * x i j = x i j} := by
      ext x; exact hH x
    rw [this]; exact isClosed_fix D m n c
  haveI : LocallyCompactSpace H := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := Topology.IsInducing.subtypeVal.secondCountableTopology
  let T : H ≃+ H :=
    { toFun := fun x => ⟨h.1 ⬝ x.1 ⬝ a.1, mem h a x.1 x.2⟩
      invFun := fun x => ⟨(h⁻¹).1 ⬝ x.1 ⬝ (a⁻¹).1, mem h⁻¹ a⁻¹ x.1 x.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        show (h⁻¹).1 * (h.1 * x.1 * a.1) * (a⁻¹).1 = x.1
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv,
          Matrix.mul_one]
      right_inv := fun x => by
        apply Subtype.ext
        show h.1 * ((h⁻¹).1 * x.1 * (a⁻¹).1) * a.1 = x.1
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul,
          Matrix.mul_one]
      map_add' := fun x y => by
        apply Subtype.ext
        show h.1 * (x.1 + y.1) * a.1 = h.1 * x.1 * a.1 + h.1 * y.1 * a.1
        rw [Matrix.mul_add, Matrix.add_mul] }
  have hc : Continuous T := by
    show Continuous fun x : H => (⟨h.1 ⬝ x.1 ⬝ a.1, mem h a x.1 x.2⟩ : H)
    exact Continuous.subtype_mk ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _
  have hc' : Continuous T.symm := by
    show Continuous fun x : H => (⟨(h⁻¹).1 ⬝ x.1 ⬝ (a⁻¹).1, mem h⁻¹ a⁻¹ x.1 x.2⟩ : H)
    exact Continuous.subtype_mk ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _
  obtain ⟨r, hr, hφ⟩ := integral_comp_addEquiv_eq_smul ν T hc hc'
  exact ⟨r, hr, fun φ => hφ (fun x : H => φ x.1)⟩

end GlobalTheory.HalfTwist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralTsumNormalEigenfunctionsEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralTsumNormalEigenfunctionsEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
namespace GlobalTheory.CutSum

open Filter Topology

theorem measurable_tsum_of_summable {X I : Type} [MeasurableSpace X] [Countable I]
    (F : I → X → ℂ) (hF : ∀ i, Measurable (F i)) (hs : ∀ x, Summable fun i => F i x) :
    Measurable fun x => ∑' i, F i x :=
  measurable_of_tendsto_metrizable' (atTop : Filter (Finset I))
    (f := fun s x => ∑ i ∈ s, F i x) (fun s => Finset.measurable_sum s fun i _ => hF i)
    (tendsto_pi_nhds.2 fun x => (hs x).hasSum)

theorem summable_of_tsum_enorm_ne_top {I : Type} (f : I → ℂ) (h : ∑' i, ‖f i‖ₑ ≠ ⊤) :
    Summable f := by
  refine Summable.of_norm ?_
  simp only [enorm_eq_nnnorm] at h
  exact NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 h)

theorem integrableOn_of_enorm_le {X : Type} [MeasurableSpace X] {μ : Measure X} {s : Set X}
    (hs : μ s ≠ ⊤) {φ : X → ℂ} (hφ : Measurable φ) (B : NNReal) (hb : ∀ x, ‖φ x‖ₑ ≤ B) :
    IntegrableOn φ s μ := by
  refine ⟨hφ.aestronglyMeasurable, ?_⟩
  show ∫⁻ x in s, ‖φ x‖ₑ ∂μ < ⊤
  exact (lintegral_mono hb).trans_lt
    ((setLIntegral_const s _).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hs.lt_top))

end GlobalTheory.CutSum


open GlobalTheory.CutSum in
theorem GlobalTheory.CutSum.integral_tsum_eq_zero : ∀ (N : Type) [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N] [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N] (ν : Measure N) [ν.IsHaarMeasure] (Γ M : Subgroup N), Countable Γ → DiscreteTopology Γ → M.Normal → IsClosed (M : Set N) → (∃ K : Set M, IsCompact K ∧ ∀ m, ∃ γ ∈ Γ.subgroupOf M, ∃ k ∈ K, m = γ * k) → ∀ 𝓝 : Set N, IsFundamentalDomain Γ 𝓝 ν → ν 𝓝 ≠ ⊤ → ∀ (I C : Type) [Countable I] (κ : I → C) (F : I → N → ℂ), (∀ i, Measurable (F i)) → (∃ B : NNReal, ∀ n, ∑' i, ‖F i n‖ₑ ≤ B) → (∀ γ ∈ Γ, ∀ n, ∑' i, F i (γ * n) = ∑' i, F i n) → (∀ c, ∀ γ ∈ Γ, γ ∈ M → ∀ n, ∑' i : {i // κ i = c}, F i (γ * n) = ∑' i : {i // κ i = c}, F i n) → (∀ c, ∃ u ∈ M, ∃ a : ℂ, a ≠ 1 ∧ ∀ i, κ i = c → ∀ m ∈ M, ∀ n, F i (m * u * n) = a * F i (m * n)) → ∫ n in 𝓝, ∑' i, F i n ∂ν = 0 := by
  intro N _ _ _ _ _ _ _ _ ν _ Γ M hΓc hΓd hMn hMc hK 𝓝 h𝓝 h𝓝fin I C _ cl F hFm hB hΓ hcl heig
  classical
  haveI := hΓd
  haveI : LocallyCompactSpace M := hMc.locallyCompactSpace
  haveI : SecondCountableTopology M := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : BorelSpace M := Subtype.borelSpace _
  obtain ⟨B, hB⟩ := hB

  have hinj : Function.Injective fun γ : Γ.subgroupOf M =>
      (⟨(γ : M), Subgroup.mem_subgroupOf.1 γ.2⟩ : Γ) :=
    fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : Γ => (x : N)) h))
  haveI : Countable (Γ.subgroupOf M) := hinj.countable
  haveI : DiscreteTopology (Γ.subgroupOf M) := DiscreteTopology.of_continuous_injective
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) hinj
  let μM : Measure M := Measure.haar
  obtain ⟨D, -, -, hD⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (Γ.subgroupOf M)
  have hDf : μM D ≠ ⊤ := by
    obtain ⟨K, hKc, hKcov⟩ := hK
    refine ne_top_of_le_ne_top hKc.measure_lt_top.ne
      (GlobalTheory.measure_le_of_isFundamentalDomain_of_ae_covers (hD μM) (D' := K)
        (Filter.Eventually.of_forall fun m => ?_))
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hKcov m
    refine ⟨⟨γ, hγ⟩⁻¹, ?_⟩
    show ((⟨γ, hγ⟩⁻¹ : Γ.subgroupOf M) : M) * (γ * k) ∈ K
    rw [Subgroup.coe_inv, Subgroup.coe_mk, inv_mul_cancel_left]
    exact hk
  have hR : ∀ u : M, μM.map (· * u) = μM :=
    GlobalTheory.haar_map_mul_right_eq_of_fundamentalDomain N Γ M hΓc hMc μM D inferInstance (hD μM) hDf

  have hs : ∀ n, Summable fun i => F i n := fun n =>
    summable_of_tsum_enorm_ne_top _ (ne_top_of_le_ne_top ENNReal.coe_ne_top (hB n))
  let g : I → Set.range cl := Set.rangeFactorization cl
  haveI : Countable (Set.range cl) := (Set.countable_range cl).to_subtype
  let G : Set.range cl → N → ℂ := fun c n => ∑' i : {i // cl i = c.1}, F i n
  have hfib : ∀ c n, ∑' b : ↑(g ⁻¹' {c}), F b n = G c n := fun c n =>
    (Equiv.subtypeEquivRight (fun i => by
      simp [g, Set.rangeFactorization, Subtype.ext_iff])).tsum_eq
      (fun j : {i // cl i = c.1} => F j.1 n)
  have hsplit : ∀ n, ∑' i, F i n = ∑' c, G c n := fun n =>
    (((hs n).hasSum.tsum_fiberwise g).tsum_eq).symm.trans (tsum_congr fun c => hfib c n)
  have hGle : ∀ n, ∑' c, ‖G c n‖ₑ ≤ B := fun n => by
    calc ∑' c, ‖G c n‖ₑ ≤ ∑' c, ∑' b : ↑(g ⁻¹' {c}), ‖F b n‖ₑ :=
          ENNReal.tsum_le_tsum fun c => by rw [← hfib c n]; exact enorm_tsum_le_tsum_enorm
      _ = ∑' i, ‖F i n‖ₑ := ENNReal.tsum_fiberwise (fun i => ‖F i n‖ₑ) g
      _ ≤ B := hB n
  have hGm : ∀ c, Measurable (G c) := fun c =>
    measurable_tsum_of_summable (fun i : {i // cl i = c.1} => F i) (fun i => hFm i)
      (fun n => (hs n).comp_injective Subtype.val_injective)
  have hfm : Measurable fun n => ∑' i, F i n := measurable_tsum_of_summable F hFm hs

  have hzero : ∀ c (h : N), ∫ m in D, G c ((m : N) * h) ∂μM = 0 := by
    intro c h
    obtain ⟨u, huM, a, ha1, hu⟩ := heig c.1
    set φ : M → ℂ := fun m => G c ((m : N) * h) with hφ
    have hφm : Measurable φ := (hGm c).comp (measurable_subtype_coe.mul_const h)
    have hφint : IntegrableOn φ D μM :=
      integrableOn_of_enorm_le hDf hφm B fun m => (ENNReal.le_tsum c).trans (hGle _)
    have hinv : ∀ γ ∈ Γ.subgroupOf M, ∀ m : M, φ (γ * m) = φ m := by
      intro γ hγ m
      show G c (((γ * m : M) : N) * h) = G c ((m : N) * h)
      rw [Subgroup.coe_mul, mul_assoc]
      exact hcl c.1 γ (Subgroup.mem_subgroupOf.1 hγ) γ.2 _
    have hshift : ∀ m : M, φ (m * ⟨u, huM⟩) = a * φ m := by
      intro m
      show G c (((m * ⟨u, huM⟩ : M) : N) * h) = a * G c ((m : N) * h)
      rw [Subgroup.coe_mul, Subgroup.coe_mk]
      show ∑' i : {i // cl i = c.1}, F i ((m : N) * u * h)
        = a * ∑' i : {i // cl i = c.1}, F i ((m : N) * h)
      rw [← tsum_mul_left]
      exact tsum_congr fun i => hu i i.2 m m.2 h
    have key := (GlobalTheory.fundamentalDomain_setIntegral_mul_right (Γ.subgroupOf M) μM D (hD μM)
      ⟨u, huM⟩ (hR _) φ hinv hφint).2
    simp only [hshift, integral_const_mul] at key
    have h2 : (a - 1) * ∫ m in D, φ m ∂μM = 0 := by rw [sub_mul, one_mul, key, sub_self]
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 ha1)

  have hmean : ∀ h : N, ∫ m in D, (∑' i, F i ((m : N) * h)) ∂μM = 0 := by
    intro h
    have hm : ∀ c, Measurable fun m : M => G c ((m : N) * h) := fun c =>
      (hGm c).comp (measurable_subtype_coe.mul_const h)
    simp_rw [hsplit]
    rw [integral_tsum (fun c => (hm c).aestronglyMeasurable) ?_]
    · simp [hzero]
    · rw [← lintegral_tsum (fun c => (hm c).enorm.aemeasurable)]
      refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.coe_ne_top (r := B)) hDf) ?_
      exact (lintegral_mono fun m => hGle _).trans_eq (setLIntegral_const D _)
  have hfin := GlobalTheory.UnfoldNormal.unfold_zero_mean N ν Γ M hΓc hMc
    (fun γ _ n hn => hMn.conj_mem n hn γ) μM D inferInstance (hD μM) hDf
    (fun _ => 1) (fun n => ∑' i, F i n) measurable_const hfm (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) (fun γ hγ n => hΓ γ hγ n) hmean 𝓝 h𝓝
    (integrableOn_of_enorm_le h𝓝fin (measurable_const.mul hfm) B fun n => by
      simpa using enorm_tsum_le_tsum_enorm.trans (hB n))
  simpa using hfin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralTsumNormalEigenfunctionsEqZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_tsum_normal_eigenfunctions_eq_zero : ∀ (N : Type) [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N] [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N] (ν : Measure N) [ν.IsHaarMeasure] (Γ M : Subgroup N), Countable Γ → DiscreteTopology Γ → M.Normal → IsClosed (M : Set N) → (∃ K : Set M, IsCompact K ∧ ∀ m, ∃ γ ∈ Γ.subgroupOf M, ∃ k ∈ K, m = γ * k) → ∀ 𝓝 : Set N, IsFundamentalDomain Γ 𝓝 ν → ν 𝓝 ≠ ⊤ → ∀ (I C : Type) [Countable I] (κ : I → C) (F : I → N → ℂ), (∀ i, Measurable (F i)) → (∃ B : NNReal, ∀ n, ∑' i, ‖F i n‖ₑ ≤ B) → (∀ γ ∈ Γ, ∀ n, ∑' i, F i (γ * n) = ∑' i, F i n) → (∀ c, ∀ γ ∈ Γ, γ ∈ M → ∀ n, ∑' i : {i // κ i = c}, F i (γ * n) = ∑' i : {i // κ i = c}, F i n) → (∀ c, ∃ u ∈ M, ∃ a : ℂ, a ≠ 1 ∧ ∀ i, κ i = c → ∀ m ∈ M, ∀ n, F i (m * u * n) = a * F i (m * n)) → ∫ n in 𝓝, ∑' i, F i n ∂ν = 0 := by
  first | exact @GlobalTheory.CutSum.integral_tsum_eq_zero | exact GlobalTheory.CutSum.integral_tsum_eq_zero | (intros; apply GlobalTheory.CutSum.integral_tsum_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DependentFrameFirstColumnRelation
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DependentFrameFirstColumnRelation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.DepFrame

variable {E : Type} [Field E] {n ρ : ℕ}

def FirstRel (x : Matrix (Fin n) (Fin ρ) E) (j : Fin ρ) : Prop :=
  (∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧
    ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0

theorem mulVec_apply_eq_zero_of_upper {u : Matrix (Fin ρ) (Fin ρ) E}
    (hu : ∀ i k, k < i → u i k = 0) {a : Fin ρ → E} {i : Fin ρ}
    (ha : ∀ k, i ≤ k → a k = 0) : (u *ᵥ a) i = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge k i with h | h
  · simp [hu i k h]
  · simp [ha k h]

theorem mulVec_apply_eq_of_upper {u : Matrix (Fin ρ) (Fin ρ) E}
    (hu : ∀ i k, k < i → u i k = 0) (hd : ∀ i, u i i = 1) {a : Fin ρ → E} {j : Fin ρ}
    (ha : ∀ i, j < i → a i = 0) : (u *ᵥ a) j = a j := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single j]
  · simp [hd]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · simp [hu j k h]
    · simp [ha k h]
  · simp

theorem sum_smul_transpose (x : Matrix (Fin n) (Fin ρ) E) (a : Fin ρ → E) :
    ∑ i, a i • x.transpose i = x *ᵥ a := by
  ext r
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem not_linearIndependent_iff_exists (x : Matrix (Fin n) (Fin ρ) E) :
    ¬ LinearIndependent E x.transpose ↔ ∃ j, FirstRel x j := by
  classical
  have key : LinearIndependent E xᵀ ↔ ∀ g : Fin ρ → E, x *ᵥ g = 0 → ∀ i, g i = 0 := by
    refine (Fintype.linearIndependent_iff (R := E)
      (v := (fun i => xᵀ i : Fin ρ → Fin n → E))).trans ?_
    simp only [sum_smul_transpose]
  rw [key]
  constructor
  · intro h
    push_neg at h
    obtain ⟨g, hg, i₀, hi₀⟩ := h
    let S : Finset (Fin ρ) := Finset.univ.filter fun j =>
      ∃ a : Fin ρ → E, a j ≠ 0 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0
    have hlast : ∀ b : Fin ρ → E, x *ᵥ b = 0 → ∀ i, b i ≠ 0 → ∃ k ∈ S, b k ≠ 0 := by
      intro b hb i hi
      let T : Finset (Fin ρ) := Finset.univ.filter fun k => b k ≠ 0
      have hT : T.Nonempty := ⟨i, by simp [T, hi]⟩
      have hk : T.max' hT ∈ T := Finset.max'_mem T hT
      have hbk : b (T.max' hT) ≠ 0 := by simpa [T] using hk
      refine ⟨T.max' hT, ?_, hbk⟩
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨b, hbk, fun l hl => ?_, hb⟩
      by_contra hne
      have : l ≤ T.max' hT := T.le_max' l (by simp [T, hne])
      exact absurd hl (not_lt.mpr this)
    obtain ⟨k, hkS, -⟩ := hlast g hg i₀ hi₀
    have hS : S.Nonempty := ⟨k, hkS⟩
    have hjS : S.min' hS ∈ S := Finset.min'_mem S hS
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hjS
    obtain ⟨a, haj, hagt, hax⟩ := hjS
    refine ⟨S.min' hS, ?_, ?_⟩
    · intro b hb hbx
      by_contra hne
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      obtain ⟨k, hkS, hbk⟩ := hlast b hbx i hi
      have hkj : k < S.min' hS := by
        by_contra h
        exact hbk (hb k (not_lt.mp h))
      exact absurd (S.min'_le k hkS) (not_le.mpr hkj)
    · refine ⟨(a (S.min' hS))⁻¹ • a, by simp only [Pi.smul_apply, smul_eq_mul]; exact inv_mul_cancel₀ haj, fun i hi => by simp [hagt i hi], ?_⟩
      rw [Matrix.mulVec_smul, hax, smul_zero]
  · rintro ⟨j, -, a, haj, -, hax⟩ h
    have := h a hax j
    rw [haj] at this
    exact one_ne_zero this

theorem firstRel_unique (x : Matrix (Fin n) (Fin ρ) E) {j j' : Fin ρ}
    (h : FirstRel x j) (h' : FirstRel x j') : j = j' := by
  have key : ∀ {j j' : Fin ρ}, FirstRel x j → FirstRel x j' → ¬ j < j' := by
    rintro j j' ⟨-, a, haj, hagt, hax⟩ ⟨h1, -⟩ hlt
    have h0 := h1 a (fun i hi => hagt i (lt_of_lt_of_le hlt hi)) hax
    simp [h0] at haj
  rcases lt_trichotomy j j' with hl | he | hg
  · exact absurd hl (key h h')
  · exact he
  · exact absurd hg (key h' h)

theorem firstRel_mul (x : Matrix (Fin n) (Fin ρ) E) (j : Fin ρ) {u v : Matrix (Fin ρ) (Fin ρ) E}
    (hu : ∀ i k, k < i → u i k = 0) (hv : ∀ i k, k < i → v i k = 0) (hvd : ∀ i, v i i = 1)
    (huv : u * v = 1) (hvu : v * u = 1) (h : FirstRel x j) : FirstRel (x * u) j := by
  obtain ⟨h1, a, haj, hagt, hax⟩ := h
  have hmv : ∀ b, (x * u) *ᵥ b = x *ᵥ (u *ᵥ b) := fun b => (Matrix.mulVec_mulVec b x u).symm
  refine ⟨fun b hb hbx => ?_, v *ᵥ a, ?_, fun i hi => ?_, ?_⟩
  · have hub : u *ᵥ b = 0 :=
      h1 _ (fun i hi => mulVec_apply_eq_zero_of_upper hu (fun k hk => hb k (le_trans hi hk)))
        (by rw [← hmv]; exact hbx)
    calc b = (v * u) *ᵥ b := by rw [hvu, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, hub, Matrix.mulVec_zero]
  · rw [mulVec_apply_eq_of_upper hv hvd hagt, haj]
  · exact mulVec_apply_eq_zero_of_upper hv (fun k hk => hagt k (lt_of_lt_of_le hi hk))
  · rw [hmv, Matrix.mulVec_mulVec a u v, huv, Matrix.one_mulVec, hax]

theorem firstRel_mul_iff (x : Matrix (Fin n) (Fin ρ) E) (j : Fin ρ) (u : Matrix (Fin ρ) (Fin ρ) E)
    (hd : ∀ i, u i i = 1) (hu : ∀ i k, k < i → u i k = 0) :
    FirstRel x j ↔ FirstRel (x * u) j := by
  have hdet : u.det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i k h => hu i k h)]
    simp [hd]
  have hunit : IsUnit u.det := by rw [hdet]; exact isUnit_one
  letI : Invertible u := Matrix.invertibleOfIsUnitDet u hunit
  have huv : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv u hunit
  have hvu : u⁻¹ * u = 1 := Matrix.nonsing_inv_mul u hunit
  have hv : ∀ i k, k < i → u⁻¹ i k = 0 := fun i k h =>
    Matrix.blockTriangular_inv_of_blockTriangular (b := id) (fun i k h => hu i k h) h
  have hvd : ∀ i, u⁻¹ i i = 1 := by
    intro i
    have e := congrFun (congrFun hvu i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at e
    · simpa [hd] using e
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · simp [hv i k h]
      · simp [hu k i h]
    · simp
  constructor
  · exact firstRel_mul x j hu hv hvd huv hvu
  · intro h
    have := firstRel_mul (x * u) j hv hu hd hvu huv h
    rwa [Matrix.mul_assoc, huv, Matrix.mul_one] at this

theorem dependent_frame_first_relation : ∀ (E : Type) [Field E] (n ρ : ℕ) (x : Matrix (Fin n) (Fin ρ) E), (¬ LinearIndependent E x.transpose ↔ ∃ j : Fin ρ, (∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0) ∧ (∀ j j' : Fin ρ, ((∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0) → ((∀ a : Fin ρ → E, (∀ i, j' ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j' = 1 ∧ (∀ i, j' < i → a i = 0) ∧ x *ᵥ a = 0) → j = j') ∧ ∀ (j : Fin ρ) (u : Matrix (Fin ρ) (Fin ρ) E), (∀ i, u i i = 1) → (∀ i k, k < i → u i k = 0) → (((∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0) ↔ ((∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → (x * u) *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ (x * u) *ᵥ a = 0)) := by
  intro E _ n ρ x
  exact ⟨not_linearIndependent_iff_exists x, fun j j' h h' => firstRel_unique x h h',
    fun j u hd hu => firstRel_mul_iff x j u hd hu⟩

end GlobalTheory.DepFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DependentFrameFirstColumnRelationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dependent_frame_first_column_relation : ∀ (E : Type) [Field E] (n ρ : ℕ) (x : Matrix (Fin n) (Fin ρ) E), (¬ LinearIndependent E x.transpose ↔ ∃ j : Fin ρ, (∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0) ∧ (∀ j j' : Fin ρ, ((∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0) → ((∀ a : Fin ρ → E, (∀ i, j' ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j' = 1 ∧ (∀ i, j' < i → a i = 0) ∧ x *ᵥ a = 0) → j = j') ∧ ∀ (j : Fin ρ) (u : Matrix (Fin ρ) (Fin ρ) E), (∀ i, u i i = 1) → (∀ i k, k < i → u i k = 0) → (((∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0) ↔ ((∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → (x * u) *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ (x * u) *ᵥ a = 0)) := by
  first | exact @GlobalTheory.DepFrame.dependent_frame_first_relation | exact GlobalTheory.DepFrame.dependent_frame_first_relation | (intros; apply GlobalTheory.DepFrame.dependent_frame_first_relation <;> assumption)
end
end
