module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZAbs

@[expose] public section

section -- merged from Formalism.SelfDualUnimodular.LocalLatticeDictionary.UnimodOfSelfDual
noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.LatDictZ.Z0.BR

open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA PIW.AdelClassFin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

def hJ (J : Matrix (Fin n) (Fin n) E) : (Fin n → E) →ₗ⋆[E] (Fin n → E) →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (starRingEnd E) (RingHom.id E) (fun x y => Formalism.UG.hform (starRingEnd E) J x y)
    (by
      intro x y z
      simp only [Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib])
    (by
      intro c x y
      simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
    (by
      intro x y z
      simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (by
      intro c x y
      simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)

theorem hJ_apply (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hJ J x y = Formalism.UG.hform (starRingEnd E) J x y := rfl

theorem hJ_symm {J : Matrix (Fin n) (Fin n) E} (hJh : Formalism.UG.IsHerm (starRingEnd E) J) :
    (hJ J).IsSymm := by
  have hJij : ∀ i j, starRingEnd E (J j i) = J i j := fun i j => by
    have := congrFun (congrFun hJh i) j
    simpa [Formalism.UG.cT] using this
  refine ⟨fun x y => ?_⟩
  change starRingEnd E (Formalism.UG.hform (starRingEnd E) J x y) = Formalism.UG.hform (starRingEnd E) J y x
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.UG.hform, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_self_apply, hJij]
  ring

theorem hJ_single (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (j : Fin n) :
    hJ J x (Pi.single j 1) = (Matrix.vecMul (fun i => starRingEnd E (x i)) J) j := by
  rw [hJ_apply, Formalism.UG.hform, Matrix.vecMul, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

theorem hJ_nondeg {J : Matrix (Fin n) (Fin n) E} (hdet : J.det ≠ 0) (x : Fin n → E)
    (hx : ∀ y, hJ J x y = 0) : x = 0 := by
  have h0 : Matrix.vecMul (fun i => starRingEnd E (x i)) J = 0 := by
    funext j; rw [← hJ_single]; exact hx _
  have h1 := Matrix.eq_zero_of_vecMul_eq_zero hdet h0
  funext i
  have := congrFun h1 i
  simpa using this

theorem star_int (r : 𝓞 E) : star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) :=
  ⟨conjO E r, algebraMap_conjO r⟩

theorem unimod_of_selfDual {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
    (hL : SelfDual J L) : Formalism.HermitianLatticesTheory.IsUnimodular (hJ J) L := by
  unfold Formalism.HermitianLatticesTheory.IsUnimodular Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
  ext x
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]
  rw [hL x]
  constructor
  · intro h y hy
    obtain ⟨r, hr⟩ := h y hy
    exact ⟨r, hr⟩
  · intro h y hy
    obtain ⟨r, hr⟩ := h y hy
    exact ⟨r, hr⟩

theorem selfDualMod_loc {J : Matrix (Fin n) (Fin n) E} (hJh : Formalism.UG.IsHerm (starRingEnd E) J)
    {L : Submodule (𝓞 E) (Fin n → E)} (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hL : SelfDual J L) {p : Ideal (𝓞 E)} (hp : p.IsMaximal) :
    IsSelfDualMod (locRing p) (hJ J) (Formalism.HermitianLatticesTheory.loc (K := E) p L).toAddSubgroup := by
  have hu := (Formalism.HermitianLatticesTheory.locDual (𝓞 E) E (Fin n → E) (hJ J) (hJ_symm hJh) star_int L hfg).2.1
    (unimod_of_selfDual hL) p hp
  have hfull : Submodule.IsFullLattice E L :=
    { toIsLattice := Submodule.IsLattice.of_fg E hfg
      span_eq_top := hsp }
  exact isSelfDualMod_loc hfull hp.isPrime hu

theorem gl_of_isom {J : Matrix (Fin n) (Fin n) E} (g : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (hg : ∀ x y, hJ J (g x) (g y) = hJ J x y) :
    ∃ γ : GL (Fin n) E, γ ∈ Formalism.UG.UJ (starRingEnd E) J ∧ ∀ w, (γ : Matrix (Fin n) (Fin n) E) *ᵥ w = g w := by
  let A := LinearMap.toMatrix' (g : (Fin n → E) →ₗ[E] (Fin n → E))
  let B := LinearMap.toMatrix' (g.symm : (Fin n → E) →ₗ[E] (Fin n → E))
  have hAB : A * B = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have : (g : (Fin n → E) →ₗ[E] (Fin n → E)) ∘ₗ (g.symm : (Fin n → E) →ₗ[E] (Fin n → E)) = LinearMap.id := by
      ext x; simp
    rw [this, LinearMap.toMatrix'_id]
  have hBA : B * A = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have : (g.symm : (Fin n → E) →ₗ[E] (Fin n → E)) ∘ₗ (g : (Fin n → E) →ₗ[E] (Fin n → E)) = LinearMap.id := by
      ext x; simp
    rw [this, LinearMap.toMatrix'_id]
  let γ : GL (Fin n) E := ⟨A, B, hAB, hBA⟩
  have hmul : ∀ w, (γ : Matrix (Fin n) (Fin n) E) *ᵥ w = g w := fun w => by
    change A *ᵥ w = g w
    rw [LinearMap.toMatrix'_mulVec]; rfl
  refine ⟨γ, ?_, hmul⟩
  change Formalism.UG.cT (starRingEnd E) A * J * A = J
  ext i j
  have e1 := hg (Pi.single i 1) (Pi.single j 1)
  have hsingle : ∀ k l, hJ J (Pi.single k 1) (Pi.single l 1) = J k l := by
    intro k l
    rw [hJ_single, Matrix.vecMul, dotProduct]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  rw [hsingle] at e1
  rw [← e1, hJ_apply, Formalism.UG.hform]
  simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  have hcol : ∀ k l, A k l = g (Pi.single l 1) k := fun k l => by
    simp [A, LinearMap.toMatrix'_apply]
  simp only [hcol, Finset.sum_mul]
  rw [Finset.sum_comm]

end Formalism.L2.SG.Pf.LatDictZ.Z0.BR
end
end

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.LatDictZ.Z0.BR

open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA PIW.AdelClassFin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem loc_iff_of_isom (g : (Fin n → E) ≃ₗ[E] (Fin n → E))
    {L M : Submodule (𝓞 E) (Fin n → E)} {p : Ideal (𝓞 E)}
    (hm : ∀ x, x ∈ Formalism.HermitianLatticesTheory.loc (K := E) p L ↔ g x ∈ Formalism.HermitianLatticesTheory.loc (K := E) p M)
    (γ : GL (Fin n) E) (hγg : ∀ w, (γ : Matrix (Fin n) (Fin n) E) *ᵥ w = g w) (v : Fin n → E) :
    v ∈ Formalism.HermitianLatticesTheory.loc (K := E) p M ↔ ∃ w ∈ Formalism.HermitianLatticesTheory.loc (K := E) p L, (γ : Matrix (Fin n) (Fin n) E) *ᵥ w = v := by
  constructor
  · intro hv
    refine ⟨g.symm v, (hm _).2 (by rw [LinearEquiv.apply_symm_apply]; exact hv), ?_⟩
    rw [hγg, LinearEquiv.apply_symm_apply]
  · rintro ⟨w, hw, rfl⟩
    rw [hγg]; exact (hm w).1 hw

theorem semiGenus_of (hG : SemiGenusLoc) : SemiGenus := by
  intro E _ _ _ n J hK hJh hdet L M hLfg hMfg hLsp hMsp hLd hMd p hp
  obtain ⟨g, hg, hm⟩ := hG E (Fin n → E) (hJ J) hK (hJ_symm hJh) (hJ_nondeg hdet) p hp
    (Formalism.HermitianLatticesTheory.loc (K := E) p L).toAddSubgroup (Formalism.HermitianLatticesTheory.loc (K := E) p M).toAddSubgroup
    (selfDualMod_loc hJh hLfg hLsp hLd hp) (selfDualMod_loc hJh hMfg hMsp hMd hp)
  obtain ⟨γ, hγ, hγg⟩ := gl_of_isom g hg
  exact ⟨γ, hγ, loc_iff_of_isom g hm γ hγg⟩

theorem algebraMap_ne_zero' {p : Ideal (𝓞 E)} (hp : p.IsPrime) {t : 𝓞 E}
    (ht : t ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) p) : algebraMap (𝓞 E) E t ≠ 0 :=
  algebraMap_ne_zero_of_mem_hcompl hp ht

theorem smul_eq_alg (t : 𝓞 E) (v : Fin n → E) : t • v = (algebraMap (𝓞 E) E t) • v := by
  rw [algebraMap_smul]

theorem semiGenusZ_of (hZ : SemiGenusZLoc) : SemiGenusZ := by
  intro E _ _ _ n J hK hJh hdet r s z L M hLfg hMfg hLsp hMsp hLd hMd hsz hU hSL hSM hzL hzM hPL hPM p hp
  have hpP := hp.isPrime

  have hU' : ∀ w ∈ Submodule.span E (Set.range s),
      w ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p L).toAddSubgroup ↔ w ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p M).toAddSubgroup := by
    intro w hw
    change w ∈ Formalism.HermitianLatticesTheory.loc (K := E) p L ↔ w ∈ Formalism.HermitianLatticesTheory.loc (K := E) p M
    constructor
    · rintro ⟨t, ht, htw⟩
      refine ⟨t, ht, (hU _ ?_).1 htw⟩
      rw [smul_eq_alg]; exact Submodule.smul_mem _ _ hw
    · rintro ⟨t, ht, htw⟩
      refine ⟨t, ht, (hU _ ?_).2 htw⟩
      rw [smul_eq_alg]; exact Submodule.smul_mem _ _ hw
  have hsplit : ∀ N : Submodule (𝓞 E) (Fin n → E),
      (∀ w ∈ N, ∃ w₁ ∈ N, w₁ ∈ Submodule.span E (Set.range s) ∧
        ∀ a, Formalism.UG.hform (starRingEnd E) J (s a) (w - w₁) = 0) →
      ∀ w ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p N).toAddSubgroup, ∃ w₁ ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p N).toAddSubgroup,
        w₁ ∈ Submodule.span E (Set.range s) ∧ ∀ a, hJ J (s a) (w - w₁) = 0 := by
    intro N hN w hw
    obtain ⟨t, ht, htw⟩ := hw
    obtain ⟨u, huN, hus, hu0⟩ := hN _ htw
    have ht0 := algebraMap_ne_zero' hpP ht
    refine ⟨(algebraMap (𝓞 E) E t)⁻¹ • u, ⟨t, ht, ?_⟩, Submodule.smul_mem _ _ hus, fun a => ?_⟩
    · rw [smul_eq_alg, smul_smul, mul_inv_cancel₀ ht0, one_smul]; exact huN
    · have e : w - (algebraMap (𝓞 E) E t)⁻¹ • u = (algebraMap (𝓞 E) E t)⁻¹ • (t • w - u) := by
        rw [smul_eq_alg, smul_sub, smul_smul, inv_mul_cancel₀ ht0, one_smul]
      rw [e, map_smul, smul_eq_mul, hJ_apply, hu0 a, mul_zero]
  have hprim : ∀ N : Submodule (𝓞 E) (Fin n → E),
      (∀ c : E, c • z ∈ N → c ∈ (algebraMap (𝓞 E) E).range) →
      ∀ c : E, c • z ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p N).toAddSubgroup → c ∈ locRing p := by
    intro N hN c hc
    obtain ⟨t, ht, htc⟩ := hc
    rw [smul_eq_alg, smul_smul] at htc
    obtain ⟨r, hr⟩ := hN _ htc
    have ht0 := algebraMap_ne_zero' hpP ht
    rw [mem_locRing, mem_locR_iff hpP]
    refine ⟨r, t, ht, ?_⟩
    rw [hr]; field_simp
  have hzloc : ∀ N : Submodule (𝓞 E) (Fin n → E), z ∈ N → z ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p N).toAddSubgroup :=
    fun N hz => ⟨1, one_mem _, by rw [one_smul]; exact hz⟩
  obtain ⟨g, hg, hgs, hgz, hm⟩ := hZ E (Fin n → E) (hJ J) hK (hJ_symm hJh) (hJ_nondeg hdet) p hp s z
    (Formalism.HermitianLatticesTheory.loc (K := E) p L).toAddSubgroup (Formalism.HermitianLatticesTheory.loc (K := E) p M).toAddSubgroup
    (selfDualMod_loc hJh hLfg hLsp hLd hp) (selfDualMod_loc hJh hMfg hMsp hMd hp)
    hsz hU' (hsplit L hSL) (hsplit M hSM) (hzloc L hzL) (hzloc M hzM) (hprim L hPL) (hprim M hPM)
  obtain ⟨γ, hγ, hγg⟩ := gl_of_isom g hg
  refine ⟨γ, hγ, fun a => by rw [hγg, hgs a], by rw [hγg, hgz], loc_iff_of_isom g hm γ hγg⟩

end Formalism.L2.SG.Pf.LatDictZ.Z0.BR
