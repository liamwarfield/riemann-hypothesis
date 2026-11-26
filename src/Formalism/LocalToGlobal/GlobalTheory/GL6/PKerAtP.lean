module

public import Formalism.LocalToGlobal.UnitaryNorms.UnramT
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PRLocV
public import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
public import Formalism.LocalToGlobal.HermitianColumns.ColsHerm

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GlobalTheory.GL4.PFrames
noncomputable section

open NumberField Formalism.BasicNotions Formalism.L2.GlobalTheoryTheory.Comp

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

section Gen

variable {E : Type} [Field E] [NumberField E]

theorem isLattice_between {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (A B : Submodule (𝓞 E) W) (hA : Submodule.IsLattice E A) (hAB : A ≤ B) (T : ℕ) (hT : T ≠ 0)
    (hTB : ∀ x ∈ B, (T : E) • x ∈ A) : Submodule.IsLattice E B := by
  let f : W →ₗ[𝓞 E] W := ((T : ℕ) : 𝓞 E) • LinearMap.id
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : ((T : ℕ) : E) • x = ((T : ℕ) : E) • y := by
      simpa only [f, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul] using hxy
    exact smul_right_injective W (by exact_mod_cast hT : ((T : ℕ) : E) ≠ 0) h1
  have hmap : B.map f ≤ A := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := hTB x hx
    simpa only [f, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul] using h1
  haveI : IsNoetherian (𝓞 E) A := isNoetherian_of_fg_of_noetherian A hA.fg
  have hmfg : (B.map f).FG := by
    have h1 := IsNoetherian.noetherian ((B.map f).comap A.subtype)
    have h2 := h1.map A.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 hmap] at h2
  refine ⟨Submodule.fg_of_fg_map_injective f hf hmfg, ?_⟩
  intro s hs hli
  let g : W →ₗ[E] W := ((T : E) • LinearMap.id)
  have hg : Function.Injective g := smul_right_injective W (by exact_mod_cast hT : (T : E) ≠ 0)
  have hgs : g '' s ⊆ A := by
    rintro _ ⟨x, hx, rfl⟩
    have hxB : x ∈ B := hs hx
    have hmul := hTB x hxB
    simpa [g, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul] using hmul
  have hli' : LinearIndepOn (𝓞 E) id (g '' s) := by
    apply LinearIndepOn.image (f := g.restrictScalars (𝓞 E)) hli
    simp [LinearMap.ker_eq_bot.mpr hg]
  have hli'' : LinearIndepOn E id (g '' s) := hA.linearIndepOn _ hgs hli'
  exact (linearIndepOn_id_imageₛ_iff (f := g) hg.injOn).mp hli''

end Gen

open Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section -- merged from Formalism.LocalToGlobal.GlobalTheory.GL6.PRLocW
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section DualQ

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem rlv_dualQ {n : ℕ} (σ : E →ₐ[F] E) (hσσ : ∀ x, σ (σ x) = x) (J : Matrix (Fin n) (Fin n) E)
    (hH : ∀ u w, hform (σ : E →+* E) J w u = σ (hform (σ : E →+* E) J u w))
    (g : Matrix (Fin n) (Fin n) E) (hg : cT (σ : E →+* E) g * J * g = J)
    (P : Ideal (𝓞 E)) [P.IsPrime] {A B : Submodule (𝓞 E) (Fin n → E)}
    (hBfg : (Formalism.L2.GlobalTheoryTheory.Comp.dl σ J B).FG)
    (hBB : Formalism.L2.GlobalTheoryTheory.Comp.dl σ J (Formalism.L2.GlobalTheoryTheory.Comp.dl σ J B) ≤ B)
    (hP : Formalism.HermitianLatticesTheory.localization₂ P (Formalism.L2.GlobalTheoryTheory.Comp.dl σ J B) ≤ Formalism.HermitianLatticesTheory.localization₂ P (mulLat g (Formalism.L2.GlobalTheoryTheory.Comp.dl σ J A))) :
    Formalism.HermitianLatticesTheory.localization₂ (P.comap (RingOfIntegers.mapRingHom (σ : E →+* E))) (mulLat g A) ≤
      Formalism.HermitianLatticesTheory.localization₂ (P.comap (RingOfIntegers.mapRingHom (σ : E →+* E))) B := by
  classical
  have hP1 : (1 : 𝓞 E) ∉ P := P.ne_top_iff_one.1 (Ideal.IsPrime.ne_top inferInstance)
  intro x hx
  obtain ⟨t0, ht0, hx0⟩ := (rlv_mem_locP _ _ _).1 hx
  obtain ⟨a, ha, hax⟩ := Submodule.mem_map.1 hx0
  simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at hax
  have key : ∀ y ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl σ J B, ∃ s : 𝓞 E, s ∉ P ∧
      (s : E) * hform (σ : E →+* E) J (g *ᵥ a) y ∈ (algebraMap (𝓞 E) E).range := by
    intro y hy
    obtain ⟨s, hs, hsy⟩ := (rlv_mem_locP _ _ _).1 (hP ((rlv_mem_locP _ _ _).2 ⟨1, hP1, by rw [one_smul]; exact hy⟩))
    obtain ⟨w, hw, hwy⟩ := Submodule.mem_map.1 hsy
    simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at hwy
    refine ⟨s, hs, ?_⟩
    have e1 : (s : E) * hform (σ : E →+* E) J (g *ᵥ a) y = hform (σ : E →+* E) J (g *ᵥ a) (s • y) := by
      rw [← algebraMap_smul E s y, Formalism.L2.GlobalTheoryTheory.Comp.hform_smul_right]
    rw [e1, ← hwy, Formalism.UG.P.hform_mulVec, hg]
    exact (Formalism.L2.GlobalTheoryTheory.Comp.mem_dl σ J A w).1 hw a ha
  choose! sf hsfP hsf using key
  obtain ⟨S, hS⟩ := hBfg
  have hSsub : ∀ y ∈ S, y ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl σ J B := fun y hy => hS ▸ Submodule.subset_span hy
  set s : 𝓞 E := ∏ y ∈ S, sf y with hsdef
  have hsP : s ∉ P := by
    rw [hsdef, Ideal.IsPrime.prod_mem_iff]
    rintro ⟨y, hy, hyP⟩
    exact hsfP y (hSsub y hy) hyP
  have hgen : ∀ y ∈ S, (s : E) * hform (σ : E →+* E) J (g *ᵥ a) y ∈ (algebraMap (𝓞 E) E).range := by
    intro y hy
    rw [hsdef, ← Finset.mul_prod_erase S sf hy]
    obtain ⟨r, hr⟩ := hsf y (hSsub y hy)
    refine ⟨(∏ z ∈ S.erase y, sf z) * r, ?_⟩
    rw [map_mul, hr]
    push_cast
    ring
  have hall : ∀ y ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl σ J B, (s : E) * hform (σ : E →+* E) J (g *ᵥ a) y ∈ (algebraMap (𝓞 E) E).range := by
    intro y hy
    rw [← hS] at hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hgen y hy
    | zero => rw [Formalism.L2.GlobalTheoryTheory.Comp.hform_zero_right, mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [Formalism.L2.GlobalTheoryTheory.Comp.hform_add_right, mul_add]; exact add_mem hy hz
    | smul r y _ hy =>
      rw [← algebraMap_smul E r y, Formalism.L2.GlobalTheoryTheory.Comp.hform_smul_right]
      obtain ⟨q, hq⟩ := hy
      exact ⟨r * q, by rw [map_mul, hq]; ring⟩
  set s' : 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E) s with hs'def
  have hs'E : (s' : E) = σ (s : E) := rfl
  have hmem : s' • (g *ᵥ a) ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl σ J (Formalism.L2.GlobalTheoryTheory.Comp.dl σ J B) := by
    apply Submodule.subset_span
    intro y hy
    have e2 : hform (σ : E →+* E) J y (s' • (g *ᵥ a)) = σ ((s : E) * hform (σ : E →+* E) J (g *ᵥ a) y) := by
      rw [← algebraMap_smul E s' (g *ᵥ a), Formalism.L2.GlobalTheoryTheory.Comp.hform_smul_right, hH, map_mul]
      rfl
    rw [e2]
    obtain ⟨q, hq⟩ := hall y hy
    exact ⟨RingOfIntegers.mapRingHom (σ : E →+* E) q, by rw [← hq]; rfl⟩
  refine (rlv_mem_locP _ _ _).2 ⟨s' * t0, ?_, ?_⟩
  · intro hm
    rcases (Ideal.IsPrime.mem_or_mem inferInstance hm) with h1 | h1
    · apply hsP
      have : RingOfIntegers.mapRingHom (σ : E →+* E) s' = s := by
        apply RingOfIntegers.ext
        show σ (σ (s : E)) = (s : E)
        exact hσσ _
      rw [← this]
      exact h1
    · exact ht0 h1
  · rw [mul_smul, ← hax]
    exact hBB hmem

end DualQ

section TiedQ

variable {D : D7} {u : D.what₂.Word}

theorem rlv_sig_sig (x : D.host.E) : sigD D (sigD D x) = x := by
  rw [forms_involution_eq_host_conj, forms_involution_eq_host_conj, host_conj_involutive]


set_option maxHeartbeats 2000000 in
theorem rlv_coordFacts (i : ℕ) (hi : i ≤ D.R.m) :
    (∀ c, Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c)) =
      clsCrd D u i hi c) ∧
    (∀ c, (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c)).FG) ∧
    (∀ a b, hform (sigD D : D.host.E →+* D.host.E) (gramN D i hi) b a =
      sigD D (hform (sigD D : D.host.E →+* D.host.E) (gramN D i hi) a b)) := by
  letI := D.host.cmStar
  set κ : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E) := (D.sp.X i).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm) with hκ
  have hform_eq : ∀ x y, (D.sp.X i).hT x y = hform (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (κ x) (κ y) := by
    intro x y
    have hx : (D.sp.X i).hT x y = ∑ a, ∑ b, star ((D.sp.X i).frame.repr x a) * (D.sp.X i).gram a b *
        (D.sp.X i).frame.repr y b := by
      conv_lhs => rw [← (D.sp.X i).frame.sum_repr x, ← (D.sp.X i).frame.sum_repr y]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        starRingEnd_apply, HSpace.gram, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [RingHom.id_apply]
      ring
    rw [hx]
    unfold hform
    rw [← (finCongr (rankN D i hi)).symm.sum_comp]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← (finCongr (rankN D i hi)).symm.sum_comp]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [gramN, hκ, CMData.sig, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft, starRingEnd_apply]
  let K : Formalism.L2.GlobalTheoryTheory.Comp.Coord D.sp.cm (D.sp.X i) (Fin (D.R.N i)) := ⟨κ, gramN D i hi, hform_eq⟩
  have hdual c := Formalism.HermitianLatticesTheory.dualLattice (𝓞 D.host.E) D.host.E (D.sp.X i).V
    (D.sp.X i).hT (D.sp.X i).herm (D.sp.X i).nondeg
    Formalism.L2.GlobalTheoryTheory.Comp.star_int (D.clsLat u i c) (D.clsLat_lat u i c)
  refine ⟨fun c => ?_, fun c => ?_, fun a b => ?_⟩
  · have e1 := K.lat_dual (Formalism.HermitianLatticesTheory.dual (D.sp.X i).hT (D.clsLat u i c))
    have e2 := K.lat_dual (D.clsLat u i c)
    rw [(hdual c).2.1, e2] at e1
    exact e1.symm
  · have hfg : (K.lat (Formalism.HermitianLatticesTheory.dual (D.sp.X i).hT (D.clsLat u i c))).FG :=
      (hdual c).1.toIsLattice.fg.map _
    rw [K.lat_dual] at hfg
    exact hfg
  · have h := (D.sp.X i).herm.eq (κ.symm a) (κ.symm b)
    rw [hform_eq, hform_eq, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
    exact h.symm


end TiedQ

section TiedW

variable {D : D7} {u : D.what₂.Word}





end TiedW

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

section -- merged from Formalism.LocalToGlobal.GlobalTheory.GL6.PDnDil
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section DdlGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}


end DdlGen

section DdlLoc

variable {E : Type} [Field E] [NumberField E]

theorem ddl_mulLat_one {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) : mulLat (1 : Matrix (Fin n) (Fin n) E) L = L := by
  ext x
  simp only [mulLat, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.one_mulVec]
  exact ⟨fun ⟨y, hy, e⟩ => e ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

theorem localization_inv_smul_eq {n : ℕ} (P : Ideal (𝓞 E)) [P.IsPrime] (g : GL (Fin n) E) {A B : Submodule (𝓞 E) (Fin n → E)}
    (h : Formalism.HermitianLatticesTheory.localization₂ P (mulLat (g : Matrix (Fin n) (Fin n) E) A) = Formalism.HermitianLatticesTheory.localization₂ P B) :
    Formalism.HermitianLatticesTheory.localization₂ P (mulLat ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) B) = Formalism.HermitianLatticesTheory.localization₂ P A := by
  have k1 := rlv_locP_mulLat_le P ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) h.ge
  have k2 := rlv_locP_mulLat_le P ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) h.le
  rw [← rlv_mulLat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, ddl_mulLat_one] at k1 k2
  exact le_antisymm k1 k2

variable {E : Type} [Field E] [NumberField E]

theorem localization_mono₂ (P : Ideal (𝓞 E)) [P.IsPrime] {n : ℕ} {M N : Submodule (𝓞 E) (Fin n → E)} (h : M ≤ N) :
    Formalism.HermitianLatticesTheory.localization₂ P M ≤ Formalism.HermitianLatticesTheory.localization₂ P N := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := (rlv_mem_locP _ _ _).1 hx
  exact (rlv_mem_locP _ _ _).2 ⟨s, hs, h hsx⟩

theorem mem_localization_of_mem₂ (P : Ideal (𝓞 E)) [P.IsPrime] {n : ℕ} {M : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E}
    (h : x ∈ M) : x ∈ Formalism.HermitianLatticesTheory.localization₂ P M :=
  (rlv_mem_locP _ _ _).2 ⟨1, P.ne_top_iff_one.1 (Ideal.IsPrime.ne_top inferInstance), by rw [one_smul]; exact h⟩

theorem localization_smul_cancel {n : ℕ} (P : Ideal (𝓞 E)) [P.IsPrime] (g g' : GL (Fin n) E) {A B : Submodule (𝓞 E) (Fin n → E)}
    (h : Formalism.HermitianLatticesTheory.localization₂ P (mulLat (g' : Matrix (Fin n) (Fin n) E) B) = Formalism.HermitianLatticesTheory.localization₂ P (mulLat (g : Matrix (Fin n) (Fin n) E) A)) :
    Formalism.HermitianLatticesTheory.localization₂ P (mulLat ((g⁻¹ * g' : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) B) = Formalism.HermitianLatticesTheory.localization₂ P A := by
  have k1 := rlv_locP_mulLat_le P ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) h.le
  have k2 := rlv_locP_mulLat_le P ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) h.ge
  have e1 : ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * (g : Matrix (Fin n) (Fin n) E) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [← rlv_mulLat_mul, ← rlv_mulLat_mul, e1, ddl_mulLat_one, ← Units.val_mul] at k1 k2
  exact le_antisymm k1 k2

end DdlLoc

section DdlTied

variable {D : D7} {u : D.what₂.Word}








end DdlTied

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

noncomputable section

open NumberField Ideal IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms

section Unr

variable {D : D7} {u : D.what₂.Word}

theorem unramified_algebraic_weights (A : AtTTied u) (v : (D.mem u).A.vT) :
    ∃ s : 𝓞 D.host.E, s ∉ A.Pv v ∧
      ∀ x ∈ A.Pv v, ∃ z : 𝓞 D.host.E, x * s = z * (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) := by
  have : Fact (D.mem u).A.T.Prime := ⟨(D.mem u).A.T_prime⟩
  have : CharP ((D.mem u).A.Fv v) (D.mem u).A.T := charP_of_card_eq_prime ((D.mem u).A.card_Fv v)
  have hPmax : (A.Pv v).IsMaximal := RingHom.ker_isMaximal_of_surjective (A.res v) (A.res_surj v)
  have hres_nat : ∀ s : ℕ, A.res v (s : 𝓞 D.host.E) = 0 ↔ (D.mem u).A.T ∣ s := by
    intro s; rw [map_natCast]; exact CharP.cast_eq_zero_iff _ (D.mem u).A.T s
  have := Formalism.L2.Host.span_isPrime (D.mem u).A.T
  have hlies : (A.Pv v).LiesOver (span {((D.mem u).A.T : ℤ)}) := by
    refine ⟨?_⟩
    have hle : span {((D.mem u).A.T : ℤ)} ≤ (A.Pv v).comap (algebraMap ℤ (𝓞 D.host.E)) := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show A.res v (algebraMap ℤ (𝓞 D.host.E) ((D.mem u).A.T : ℤ)) = 0
      rw [map_natCast]
      exact (hres_nat _).2 dvd_rfl
    have hmax : (span {((D.mem u).A.T : ℤ)}).IsMaximal := by
      refine this.isMaximal ?_
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast (D.mem u).A.T_prime.ne_zero
    exact hmax.eq_of_le (Ideal.comap_ne_top _ hPmax.ne_top) hle
  obtain ⟨I, hI, hIP⟩ := Formalism.L2.Host.map_eq_mul_coprime D.host (D.mem u).A.T (Formalism.L2.Host.T_ne A v) (A.Pv v)
  obtain ⟨s, hsI, hsP⟩ := Set.not_subset.mp hIP
  refine ⟨s, hsP, fun x hx => ?_⟩
  have hxs : x * s ∈ (span {((D.mem u).A.T : ℤ)}).map (algebraMap ℤ (𝓞 D.host.E)) := by
    rw [hI]; exact Ideal.mul_mem_mul hx hsI
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton', map_natCast] at hxs
  obtain ⟨z, hz⟩ := hxs
  exact ⟨z, hz.symm⟩

theorem unr_smul (A : AtTTied u) (v : (D.mem u).A.vT) :
    ∃ s : 𝓞 D.host.E, s ∉ A.Pv v ∧ ∀ {W : Type} [AddCommGroup W] [Module (𝓞 D.host.E) W]
      (M : Submodule (𝓞 D.host.E) W), ∀ x ∈ A.Pv v • M,
        ∃ y ∈ M, s • x = (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • y := by
  obtain ⟨s, hs, h⟩ := unramified_algebraic_weights A v
  refine ⟨s, hs, fun {W} _ _ M x hx => ?_⟩
  refine Submodule.smul_induction_on (p := fun x => ∃ y ∈ M, s • x = (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • y) hx
    (fun p hp m hm => ?_) (fun x1 x2 h1 h2 => ?_)
  · obtain ⟨z, hz⟩ := h p hp
    exact ⟨z • m, M.smul_mem z hm, by rw [smul_smul, smul_smul, mul_comm s p, hz, mul_comm z]⟩
  · obtain ⟨a, ha, ea⟩ := h1
    obtain ⟨b, hb, eb⟩ := h2
    exact ⟨a + b, M.add_mem ha hb, by rw [smul_add, ea, eb, smul_add]⟩

theorem exists_smul_eq_smul_of_mem_ideal_smul {W : Type} [AddCommGroup W] [Module (𝓞 D.host.E) W] (A : AtTTied u) (v : (D.mem u).A.vT)
    (M : Submodule (𝓞 D.host.E) W) (x : W) (hx : x ∈ A.Pv v • M) :
    ∃ s : 𝓞 D.host.E, s ∉ A.Pv v ∧ ∃ y ∈ M, s • x = (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • y := by
  obtain ⟨s, hs, h⟩ := unr_smul A v
  obtain ⟨y, hy, e⟩ := h M x hx
  exact ⟨s, hs, y, hy, e⟩

end Unr

section TLd

variable {D : D7} {u : D.what₂.Word}

theorem tld_isLat (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    Formalism.L2.GlobalTheoryTheory.Comp.IsLat (clsCrd D u i hi c) := by
  have hLat := bwB_clsCrd_lat D u i hi c
  obtain ⟨hDoubleDual, hDualFG, _⟩ := rlv_coordFacts (D := D) (u := u) i hi
  refine ⟨Module.Finite.iff_fg.2 hLat.fg, ?_⟩
  rw [← hDoubleDual c]
  exact LocB.dual_span (sigD D : D.host.E →+* D.host.E) (gramN D i hi) _
    (Submodule.IsLattice.of_fg _ (hDualFG c))

end TLd

section TLdLoc

open Matrix Formalism.UG

variable {D : D7} {u : D.what₂.Word}

end TLdLoc

section SFGen

open Matrix Formalism.UG IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sf_mulVec_smul {n : ℕ} (v : HeightOneSpectrum (𝓞 F))
    (M : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (s : intV E v)
    (w : Fin n → E ⊗[F] v.adicCompletion F) : M *ᵥ (s • w) = s • (M *ᵥ w) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show _ * ((s : E ⊗[F] v.adicCompletion F) * w j) = (s : E ⊗[F] v.adicCompletion F) * (_ * w j)
  ring


set_option maxHeartbeats 1000000 in
theorem sf_of_gen {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (L2 Lb : Submodule (𝓞 E) (Fin n → E))
    {Mm : Type} [AddCommGroup Mm] [Module (intV E v) Mm]
    (f : latS (F := F) (v.adicCompletion F) (intV E v) Lb →ₗ[intV E v] Mm)
    (y2 : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hy2 : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L2 ↔
      ((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb)
    (g : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hg : g ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) Lb))
    (hgen : ∀ z ∈ L2, ∀ h1 : ((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
        (fun i => inclE (F := F) (v.adicCompletion F) (z i)) ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb,
      f ⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
        (fun i => inclE (F := F) (v.adicCompletion F) (z i))), (hg _).1 h1⟩ = f ⟨_, h1⟩) :
    g ∈ stabFun (latS (F := F) (v.adicCompletion F) (intV E v) Lb) f := by
  refine ⟨hg, fun x => ?_⟩
  have key : ∀ w (hw : w ∈ latS (F := F) (v.adicCompletion F) (intV E v) L2),
      f ⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ w),
        (hg _).1 ((hy2 w).1 hw)⟩ = f ⟨((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ w, (hy2 w).1 hw⟩ := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨z, hz, rfl⟩ := hw
      exact hgen z hz _
    | zero =>
      have e1 : (⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ 0),
          (hg _).1 ((hy2 0).1 (zero_mem _))⟩ : latS (F := F) (v.adicCompletion F) (intV E v) Lb) = 0 :=
        Subtype.ext (by simp)
      have e2 : (⟨((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ 0, (hy2 0).1 (zero_mem _)⟩ :
          latS (F := F) (v.adicCompletion F) (intV E v) Lb) = 0 :=
        Subtype.ext (by simp)
      rw [e1, e2]
    | add a b ha hb iha ihb =>
      have e1 : (⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ (a + b)),
          (hg _).1 ((hy2 _).1 (add_mem ha hb))⟩ : latS (F := F) (v.adicCompletion F) (intV E v) Lb) =
          ⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ a), (hg _).1 ((hy2 a).1 ha)⟩ +
          ⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ b), (hg _).1 ((hy2 b).1 hb)⟩ :=
        Subtype.ext (by simp only [Submodule.coe_add, Matrix.mulVec_add])
      have e2 : (⟨((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ (a + b), (hy2 _).1 (add_mem ha hb)⟩ :
          latS (F := F) (v.adicCompletion F) (intV E v) Lb) =
          ⟨((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ a, (hy2 a).1 ha⟩ +
          ⟨((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ b, (hy2 b).1 hb⟩ :=
        Subtype.ext (by simp only [Submodule.coe_add, Matrix.mulVec_add])
      rw [e1, e2, map_add (f := _), map_add (f := _), iha, ihb]
    | smul s a ha iha =>
      have e1 : (⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ (s • a)),
          (hg _).1 ((hy2 _).1 (Submodule.smul_mem _ s ha))⟩ : latS (F := F) (v.adicCompletion F) (intV E v) Lb) =
          s • ⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ a), (hg _).1 ((hy2 a).1 ha)⟩ :=
        Subtype.ext (by simp only [Submodule.coe_smul]; rw [sf_mulVec_smul, sf_mulVec_smul])
      have e2 : (⟨((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ (s • a), (hy2 _).1 (Submodule.smul_mem _ s ha)⟩ :
          latS (F := F) (v.adicCompletion F) (intV E v) Lb) =
          s • ⟨((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ a, (hy2 a).1 ha⟩ :=
        Subtype.ext (by simp only [Submodule.coe_smul]; rw [sf_mulVec_smul])
      rw [e1, e2, map_smul, map_smul, iha]
  have e : ((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ ((y2 : Matrix (Fin n) (Fin n) _) *ᵥ x.1) = x.1 := by
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have hx : (y2 : Matrix (Fin n) (Fin n) _) *ᵥ x.1 ∈ latS (F := F) (v.adicCompletion F) (intV E v) L2 :=
    (hy2 _).2 (by rw [e]; exact x.2)
  have h := key _ hx
  have e1 : (⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ x.1, (hg x.1).1 x.2⟩ : latS (F := F) (v.adicCompletion F) (intV E v) Lb) =
      ⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
        ((y2 : Matrix (Fin n) (Fin n) _) *ᵥ x.1)), (hg _).1 ((hy2 _).1 hx)⟩ := Subtype.ext (by simp only [e])
  have e2 : x = ⟨((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ ((y2 : Matrix (Fin n) (Fin n) _) *ᵥ x.1),
      (hy2 _).1 hx⟩ := Subtype.ext e.symm
  rw [e1, h, ← e2]

end SFGen

section SFGen2

open Matrix Formalism.UG IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sf_bc_eq {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (y1 y2 : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (g : GL (Fin n) E) :
    ((bc (prV (E := E) v) (y1⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g * y2) : GL (Fin n) _) :
      Matrix (Fin n) (Fin n) _) =
      (((bc (prV (E := E) v) y1)⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *
        ((g : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (v.adicCompletion F))) *
        ((bc (prV (E := E) v) y2 : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := by
  rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul]
  rfl


set_option maxHeartbeats 2000000 in
theorem sf_two {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (L1 L2 Lb : Submodule (𝓞 E) (Fin n → E))
    {Mm : Type} [AddCommGroup Mm] [Module (intV E v) Mm]
    (f : latS (F := F) (v.adicCompletion F) (intV E v) Lb →ₗ[intV E v] Mm)
    (y1 y2 : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hy1 : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L1 ↔
      ((y1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb)
    (hy2 : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L2 ↔
      ((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb)
    (Γ : Matrix (Fin n) (Fin n) E) (g : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hgM : (g : Matrix (Fin n) (Fin n) _) = ((y1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *
      Γ.map (inclE (F := F) (v.adicCompletion F)) * (y2 : Matrix (Fin n) (Fin n) _))
    (hg : g ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) Lb))
    (hF : ∀ z ∈ L2, ∃ a : 𝓞 F, a ∉ v.asIdeal ∧ (algebraMap (𝓞 F) (𝓞 E) a) • (Γ *ᵥ z) ∈ L1 ∧
      ∀ (h1 : ((y1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
          (fun k => inclE (F := F) (v.adicCompletion F) (((algebraMap (𝓞 F) (𝓞 E) a) • (Γ *ᵥ z)) k)) ∈
          latS (F := F) (v.adicCompletion F) (intV E v) Lb)
        (h2 : ((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
          (fun k => inclE (F := F) (v.adicCompletion F) (((algebraMap (𝓞 F) (𝓞 E) a) • z) k)) ∈
          latS (F := F) (v.adicCompletion F) (intV E v) Lb),
        f ⟨_, h1⟩ = f ⟨_, h2⟩) :
    g ∈ stabFun (latS (F := F) (v.adicCompletion F) (intV E v) Lb) f := by
  refine sf_of_gen v L2 Lb f y2 hy2 g hg ?_
  intro z hz h1
  have eG : (g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
        (fun k => inclE (F := F) (v.adicCompletion F) (z k))) =
      ((y1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
        (fun k => inclE (F := F) (v.adicCompletion F) ((Γ *ᵥ z) k)) := by
    rw [hgM, mulVec_mulVec, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one,
      ← mulVec_mulVec]
    congr 1
    funext k
    exact (RingHom.map_mulVec _ _ _ k).symm
  obtain ⟨a, ha, hΓ, hfa⟩ := hF z hz
  let t : intV E v := ⟨(1 : E) ⊗ₜ[F] ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) a : v.adicCompletionIntegers F) :
      v.adicCompletion F), Subring.subset_closure (Or.inr ⟨⟨_, (algebraMap (𝓞 F) (v.adicCompletionIntegers F) a).2⟩, rfl⟩)⟩
  have hι : ∀ y : Fin n → E, (fun k => inclE (F := F) (v.adicCompletion F) (((algebraMap (𝓞 F) (𝓞 E) a) • y) k)) =
      t • (fun k => inclE (F := F) (v.adicCompletion F) (y k)) := by
    intro y; funext k
    show inclE (F := F) (v.adicCompletion F) ((algebraMap (𝓞 F) (𝓞 E) a) • y k) =
      (t : E ⊗[F] v.adicCompletion F) * inclE (F := F) (v.adicCompletion F) (y k)
    rw [rlv_incl_smul, mul_comm]; rfl
  have hA' : ((y1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
      (fun k => inclE (F := F) (v.adicCompletion F) (((algebraMap (𝓞 F) (𝓞 E) a) • (Γ *ᵥ z)) k)) ∈
      latS (F := F) (v.adicCompletion F) (intV E v) Lb := (hy1 _).1 (Submodule.subset_span ⟨_, hΓ, rfl⟩)
  have hB' : ((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
      (fun k => inclE (F := F) (v.adicCompletion F) (((algebraMap (𝓞 F) (𝓞 E) a) • z) k)) ∈
      latS (F := F) (v.adicCompletion F) (intV E v) Lb := (hy2 _).1 (Submodule.subset_span ⟨_, Submodule.smul_mem _ _ hz, rfl⟩)
  have hfT := hfa hA' hB'
  have eA : (⟨_, hA'⟩ : latS (F := F) (v.adicCompletion F) (intV E v) Lb) = t • ⟨_, (hg _).1 h1⟩ := Subtype.ext (by
    simp only [Submodule.coe_smul]
    rw [hι, sf_mulVec_smul, eG])
  have eB : (⟨_, hB'⟩ : latS (F := F) (v.adicCompletion F) (intV E v) Lb) = t • ⟨_, h1⟩ := Subtype.ext (by
    simp only [Submodule.coe_smul]
    rw [hι, sf_mulVec_smul])
  rw [eA, eB, map_smul, map_smul] at hfT
  obtain ⟨s, hs, hsr⟩ := rlv_unit (E := E) v a ha
  have hst1 : (⟨s, hs⟩ : intV E v) * t = 1 := Subtype.ext hsr
  have := congrArg (fun m => (⟨s, hs⟩ : intV E v) • m) hfT
  simp only [smul_smul, hst1, one_smul] at this
  exact this

end SFGen2

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
