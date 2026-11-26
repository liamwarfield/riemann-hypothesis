module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfCharZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullLevelObjectPullbackExistsAndFull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullObjectOfGenericFibreDvr
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarizedCMExtensionDvr

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsLocalizationOfLeClosure
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.JoinRing

def coprimeNat (p : ℕ) (A : Type) [CommRing A] : Submonoid A where
  carrier := {x | ∃ m : ℕ, m.Coprime p ∧ x = m}
  one_mem' := ⟨1, by simp, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, Nat.Coprime.mul_left ha hb, by simp⟩

theorem ne_zero_of_coprime {p m : ℕ} (hp : p.Prime) (hm : m.Coprime p) : m ≠ 0 := by
  rintro rfl
  exact hp.ne_one (by simpa using hm)

theorem coprimeNat_le {p : ℕ} (hp : p.Prime) (A : Type) [CommRing A] [IsDomain A] [CharZero A] :
    coprimeNat p A ≤ nonZeroDivisors A := by
  rintro _ ⟨m, hm, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.mpr (ne_zero_of_coprime hp hm))

theorem isLocalization_of_le_closure {p : ℕ} (hp : p.Prime) (A : Type) [CommRing A] (T : Subring ℂ) [Algebra A T]
    (hinj : Function.Injective (algebraMap A T)) (hinv : ∀ m : ℕ, m.Coprime p → (m : ℂ)⁻¹ ∈ T)
    (hT : T ≤ Subring.closure ({x | ∃ a, x = (algebraMap A T a : ℂ)} ∪ {x | ∃ n : ℕ, n.Coprime p ∧ x = (n : ℂ)⁻¹})) :
    IsLocalization (coprimeNat p A) T := by
  have h0 : ∀ m : ℕ, m.Coprime p → (m : ℂ) ≠ 0 := fun m hm => Nat.cast_ne_zero.mpr (ne_zero_of_coprime hp hm)
  have key : ∀ z ∈ Subring.closure ({x | ∃ a, x = (algebraMap A T a : ℂ)} ∪ {x | ∃ n : ℕ, n.Coprime p ∧ x = (n : ℂ)⁻¹}),
      ∃ m : ℕ, m.Coprime p ∧ ∃ a, z * m = (algebraMap A T a : ℂ) := by
    intro z hz
    induction hz using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨a, rfl⟩ | ⟨m, hm, rfl⟩
      · exact ⟨1, by simp, a, by simp⟩
      · exact ⟨m, hm, 1, by simp [h0 m hm]⟩
    | zero => exact ⟨1, by simp, 0, by simp⟩
    | one => exact ⟨1, by simp, 1, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨m, hm, a, ha⟩ := hx
      obtain ⟨k, hk, b, hb⟩ := hy
      refine ⟨m * k, Nat.Coprime.mul_left hm hk, a * k + b * m, ?_⟩
      simp only [map_add (f := _), map_mul, map_natCast]
      push_cast
      rw [← ha, ← hb]; ring
    | neg x _ hx =>
      obtain ⟨m, hm, a, ha⟩ := hx
      refine ⟨m, hm, -a, ?_⟩
      simp only [map_neg]
      push_cast
      rw [← ha]; ring
    | mul x y _ _ hx hy =>
      obtain ⟨m, hm, a, ha⟩ := hx
      obtain ⟨k, hk, b, hb⟩ := hy
      refine ⟨m * k, Nat.Coprime.mul_left hm hk, a * b, ?_⟩
      simp only [map_mul]
      push_cast
      rw [← ha, ← hb]; ring
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, m, hm, rfl⟩
    simp only [map_natCast]
    refine IsUnit.of_mul_eq_one ⟨_, hinv m hm⟩ (Subtype.ext ?_)
    simp [h0 m hm]
  · intro z
    obtain ⟨m, hm, a, ha⟩ := key z (hT z.2)
    refine ⟨(a, ⟨m, m, hm, rfl⟩), Subtype.ext ?_⟩
    simp only [map_natCast]
    push_cast
    exact ha
  · intro x y h
    exact ⟨1, by rw [hinj h]⟩

theorem inv_mem_ZP {p m : ℕ} (k : ℕ) (hm : m.Coprime p) : (m : ℂ)⁻¹ ∈ ZP p k :=
  Subring.subset_closure (Or.inr ⟨m, hm, rfl⟩)


open CycBase in
theorem isDedekindDomain_ZP {n p : ℕ} (e : ℕ) (hn : n.Prime) (hp : p.Prime) : IsDedekindDomain (ZP p (n ^ e)) := by
  open GlobalTheory.ZM.CycBase in
  haveI := Fact.mk hn
  have hk : n ^ e ≠ 0 := NeZero.ne _
  haveI : IsCyclotomicExtension {n ^ e} ℚ (CF (n ^ e)) := cyc
  haveI : NumberField (CF (n ^ e)) := IsCyclotomicExtension.numberField {n ^ e} ℚ _
  let io : 𝓞 (CF (n ^ e)) →+* ℂ := (CF (n ^ e)).val.toRingHom.comp (algebraMap _ (CF (n ^ e)))
  have hio : Function.Injective io :=
    Subtype.val_injective.comp (RingOfIntegers.coe_injective (K := CF (n ^ e)))
  letI : Algebra (𝓞 (CF (n ^ e))) (ZP p (n ^ e)) := (io.codRestrict _ (mem_ZP p n e hn)).toAlgebra
  have : IsLocalization (coprimeNat p (𝓞 (CF (n ^ e)))) (ZP p (n ^ e)) := by
    refine isLocalization_of_le_closure hp _ _ (fun x y h => hio (congrArg (fun z : ZP p (n ^ e) => (z : ℂ)) h))
      (fun m hm => inv_mem_ZP _ hm) (Subring.closure_mono ?_)
    rintro x (rfl | h)
    · exact Or.inl ⟨(zF_prim hk).toInteger, rfl⟩
    · exact Or.inr h
  exact IsLocalization.isDedekindDomain _ (coprimeNat_le hp (𝓞 (CF (n ^ e)))) _

theorem isDedekindDomain_RZ_of_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {S A e : ℕ}
    (hS : 0 < S) (hA : 0 < A) (h : A ∣ S ^ e) : IsDedekindDomain (RZ H S A) := by
  obtain ⟨l, rfl⟩ : ∃ l : Level H, l.A = A := ⟨GlobalTheory.HostModel.level H A hA, rfl⟩
  exact GlobalTheory.BaseRing.isDedekindDomain_RZ l hS h

theorem flat_inclusion {S T : Subring ℂ} (h : S ≤ T) [IsDedekindDomain S] : Flat (spMap (Subring.inclusion h)) := by
  letI : Algebra S T := (Subring.inclusion h).toAlgebra
  have htf : Module.IsTorsionFree S T := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact fun x y h => Subtype.ext (congrArg (fun z : T => (z : ℂ)) h)
  exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat S T))

theorem noetherian_preimmersion {p : ℕ} (hp : p.Prime) {S T : Subring ℂ} (h : S ≤ T) [IsNoetherianRing S]
    (hinv : ∀ m : ℕ, m.Coprime p → (m : ℂ)⁻¹ ∈ T)
    (hT : T ≤ Subring.closure ((S : Set ℂ) ∪ {x | ∃ n : ℕ, n.Coprime p ∧ x = (n : ℂ)⁻¹})) :
    IsNoetherianRing T ∧ IsPreimmersion (spMap (Subring.inclusion h)) := by
  letI : Algebra S T := (Subring.inclusion h).toAlgebra
  have hL : IsLocalization (coprimeNat p S) T := by
    refine isLocalization_of_le_closure hp _ _ (fun x y h => Subtype.ext (congrArg (fun z : T => (z : ℂ)) h))
      hinv (hT.trans (Subring.closure_mono ?_))
    rintro x (hx | hx)
    · exact Or.inl ⟨⟨x, hx⟩, rfl⟩
    · exact Or.inr hx
  exact ⟨IsLocalization.isNoetherianRing (coprimeNat p S) _ inferInstance,
    IsPreimmersion.of_isLocalization (R := S) (S := T) (coprimeNat p S)⟩

theorem join_rings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (n N p : ℕ), n.Prime → (∃ j, 1 ≤ j ∧ N = n ^ j) → p.Prime → p ≠ n → IsDedekindDomain (RZ H n N) ∧ IsNoetherianRing ↥(RZ H n N ⊔ ZP p N) ∧ Flat (spMap (Subring.inclusion (le_sup_left : RZ H n N ≤ RZ H n N ⊔ ZP p N))) ∧ IsPreimmersion (spMap (Subring.inclusion (le_sup_left : RZ H n N ≤ RZ H n N ⊔ ZP p N))) ∧ Flat (spMap (Subring.inclusion (le_sup_right : ZP p N ≤ RZ H n N ⊔ ZP p N))) := by
  rintro E _ _ _ H n N p hn ⟨j, -, hN⟩ hp -
  have hD : IsDedekindDomain (RZ H n N) :=
    isDedekindDomain_RZ_of_dvd H (e := j) hn.pos (hN ▸ pow_pos hn.pos j) (hN ▸ dvd_rfl)
  have hZ : IsDedekindDomain (ZP p N) := hN ▸ isDedekindDomain_ZP j hn hp
  have h := noetherian_preimmersion hp (le_sup_left : RZ H n N ≤ RZ H n N ⊔ ZP p N)
    (fun m hm => (le_sup_right : ZP p N ≤ _) (inv_mem_ZP _ hm))
    (sup_le (fun x hx => Subring.subset_closure (Or.inl hx)) (Subring.closure_mono (by
      rintro x (rfl | h)
      · exact Or.inl (RZ.ze H n N).2
      · exact Or.inr h)))
  exact ⟨hD, h.1, flat_inclusion _, h.2, flat_inclusion _⟩

end GlobalTheory.JoinRing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.Direct
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.SiegelDirect

open GlobalTheory.SiegelPullComp

private theorem tensor_left_hom_ext' {T : Scheme.{0}} {G : Over T} {X : Scheme.{0}} (a b : X ⟶ (G ⊗ G).left)
    (h1 : a ≫ (fst G G).left = b ≫ (fst G G).left) (h2 : a ≫ (snd G G).left = b ≫ (snd G G).left) : a = b := by
  have hw : b ≫ (G ⊗ G).hom = a ≫ (G ⊗ G).hom := by
    rw [← Over.w (fst G G), reassoc_of% h1]
  have key := CartesianMonoidalCategory.hom_ext
    (Over.homMk a rfl : Over.mk (a ≫ (G ⊗ G).hom) ⟶ G ⊗ G) (Over.homMk b hw)
    (by ext; simpa using h1) (by ext; simpa using h2)
  simpa using congrArg (fun k => k.left) key

theorem exists_inverse {T : Scheme.{0}} {A G : Over T} [GrpObj A] [GrpObj G] {φ : A.left ⟶ G.left}
    {φ₂ : (G2 A).left ⟶ (G2 G).left} (hφ : IsGrpPullback A G (𝟙 T) φ) (hs : Geo.Tor.IsSquare φ φ₂) :
    ∃ (F : G.left ⟶ A.left) (F₂ : (G2 G).left ⟶ (G2 A).left), IsGrpPullback G A (𝟙 T) F ∧ Geo.Tor.IsSquare F F₂ ∧
      φ ≫ F = 𝟙 _ ∧ F₂ ≫ φ₂ = 𝟙 _ := by
  have hw : φ ≫ G.hom = A.hom := by simpa using hφ.1.w
  have : IsIso φ := hφ.1.isIso_fst_of_isIso
  let e : A ≅ G := Over.isoMk (asIso φ) hw
  have heL : e.inv.left = inv φ := rfl
  have hsF : Geo.Tor.IsSquare (inv φ) (e.inv ⊗ₘ e.inv).left := by
    constructor
    · rw [← Over.comp_left, tensorHom_fst, Over.comp_left, heL]
    · rw [← Over.comp_left, tensorHom_snd, Over.comp_left, heL]
  refine ⟨inv φ, (e.inv ⊗ₘ e.inv).left, ⟨?_, ?_⟩, hsF, by simp, ?_⟩
  · refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [← hw]
    simp
  · intro U x y x₀ y₀ hx hy
    have key := hφ.2 (Over.mk (U.hom ≫ 𝟙 T)) x₀ y₀ (Over.homMk x.left (by simp))
      (Over.homMk y.left (by simp)) (by simp [hx]) (by simp [hy])
    have hxy := mul_left_congr (a := (U.hom ≫ 𝟙 T) ≫ 𝟙 T) (b := U.hom) (by simp)
      (Over.homMk x.left (by simp)) (Over.homMk y.left (by simp)) x y (by simp) (by simp)
    rw [hxy.symm.trans key]
    simp
  · apply tensor_left_hom_ext'
    · rw [Category.assoc, hs.1, ← Category.assoc, hsF.1]
      simp
    · rw [Category.assoc, hs.2, ← Category.assoc, hsF.2]
      simp

theorem direct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (O : Type) [CommRing O] (T : Scheme.{0}) (sT : T ⟶ Sp O) (t : SAB H T) (lev : D.La → (𝟙_ (Over T) ⟶ t.G)) (g p N : ℕ) (Ag : SiegelFamily g p N) (z : ZP p N →+* O) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (w : T ⟶ pullback Ag.s (spMap z)), SiegData sT t lev Ag z bas w → ∃ (θ : t.G.left ⟶ Ag.univ.A.left) (θ₂ : (G2 t.G).left ⟶ (G2 Ag.univ.A).left), IsGrpPullback t.G Ag.univ.A (w ≫ pullback.fst _ _) θ ∧ IsSquare θ θ₂ ∧ LBIso (abelian₂ t.G t.PP.L) (Ag.univ.P.pull θ₂) ∧ ∀ u, (lev (bas u)).left ≫ θ = (w ≫ pullback.fst _ _) ≫ (Ag.univ.lev u).left := by
  intro E _ _ _ H D O _ T sT t lev g p N Ag z bas w hd
  obtain ⟨o, φ, φ₂, hφ, hs, hL, hlev, hcl, ψ, ψ₂, hψ, hs', hP, hlev'⟩ := hd
  obtain ⟨F, F₂, hF, hsF, hφF, hF₂⟩ := exists_inverse hφ hs
  have h0 : t.PP.L.IsLB := t.PP.isLB
  have hΛ : (abelian₂ t.G t.PP.L).IsLB := by
    unfold abelian₂
    exact ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ h0 _ _
  refine ⟨F ≫ ψ, F₂ ≫ ψ₂, (hF.comp hψ).congr (Category.id_comp _) rfl, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Category.assoc, hs'.1, ← Category.assoc, hsF.1, Category.assoc]
  · rw [Category.assoc, hs'.2, ← Category.assoc, hsF.2, Category.assoc]
  · have hΛ₁ := pull_isLB hΛ (𝟙 (G2 t.G).left)
    have hΛ₂ := pull_isLB (pull_isLB hΛ φ₂) F₂
    have hO := pull_isLB o.isLB F₂
    have hU₁ := pull_isLB (pull_isLB Ag.univ.isLB ψ₂) F₂
    have hU₂ := pull_isLB Ag.univ.isLB (F₂ ≫ ψ₂)
    have s1 : LBIso (abelian₂ t.G t.PP.L) ((abelian₂ t.G t.PP.L).pull (𝟙 _)) := iso_pull_id hΛ
    have s2 : LBIso ((abelian₂ t.G t.PP.L).pull (𝟙 _)) (((abelian₂ t.G t.PP.L).pull φ₂).pull F₂) := by
      have k := iso_pull_pull hΛ φ₂ F₂
      rw [hF₂] at k
      exact k.symm
    have s3 : LBIso (((abelian₂ t.G t.PP.L).pull φ₂).pull F₂) (o.P.pull F₂) := (iso_pull F₂ hL).symm
    have s4 : LBIso (o.P.pull F₂) ((Ag.univ.P.pull ψ₂).pull F₂) := iso_pull F₂ hP
    have s5 : LBIso ((Ag.univ.P.pull ψ₂).pull F₂) (Ag.univ.P.pull (F₂ ≫ ψ₂)) := iso_pull_pull Ag.univ.isLB ψ₂ F₂
    exact LBIso.trans hΛ hΛ₁ hU₂ s1 (LBIso.trans hΛ₁ hΛ₂ hU₂ s2
      (LBIso.trans hΛ₂ hO hU₂ s3 (LBIso.trans hO hU₁ hU₂ s4 s5)))
  · intro u
    rw [← hlev u]
    simp only [Category.assoc, reassoc_of% hφF]
    exact hlev' u

end GlobalTheory.SiegelDirect

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.Rigidity
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.EpsAct

theorem subsingleton_sp_dualNumber (k : Type) [Field k] : Subsingleton (Sp (DualNumber k)) := by
  change Subsingleton (PrimeSpectrum (DualNumber k))
  have key : ∀ (p : PrimeSpectrum (DualNumber k)) (x : DualNumber k), x ∈ p.asIdeal ↔ x.fst = 0 := by
    intro p x
    constructor
    · intro hx
      by_contra h
      exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
        (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 h)))
    · intro h
      apply p.isPrime.mem_of_pow_mem 2
      have hx : x = TrivSqZeroExt.inr x.snd := TrivSqZeroExt.ext (by simp [h]) (by simp)
      rw [hx, pow_two]
      simp
  exact ⟨fun p q => PrimeSpectrum.ext (Ideal.ext fun x => (key p x).trans (key q x).symm)⟩

theorem rigidity (hL : Out.Laws) (k : Type) [Field k] {Z : Scheme.{0}} (c₀ : Z ⟶ Sp k)
    (A' G' : Over (Sp (DualNumber k))) [GrpObj A'] [GrpObj G'] (j : Z ⟶ A'.left) (a b : A' ⟶ G')
    (hA : IsAbelianScheme A')
    (hj : IsPullback j c₀ A'.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom))
    (hab : j ≫ a.left = j ≫ b.left) (hη : η[A'] ≫ a = η[A'] ≫ b) : a = b := by
  classical
  have hsurj : Function.Surjective A'.hom.appTop.hom := (hL.globalFns _ A' hA).2
  set d : A' ⟶ G' := a * b⁻¹ with hd
  have hsub : Subsingleton (Sp (DualNumber k)) := subsingleton_sp_dualNumber k
  have hjs : Function.Surjective j.base := by
    have hs0 : Surjective (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) := by
      constructor
      intro y
      obtain ⟨q⟩ : Nonempty (Sp k) := by
        change Nonempty (PrimeSpectrum k)
        infer_instance
      exact ⟨q, Subsingleton.elim _ _⟩
    exact (MorphismProperty.of_isPullback (P := @Surjective) hj.flip hs0).surj
  have key : ∀ {W : Over (Sp (DualNumber k))} (u : W ⟶ A'), u ≫ a = u ≫ b → u ≫ d = 1 := by
    intro W u h
    rw [MonObj.comp_mul, GrpObj.comp_inv, h, mul_inv_cancel]
  have hjd : j ≫ d.left = (toUnit (Over.mk (j ≫ A'.hom))).left ≫ η[G'].left := by
    have h1 := congrArg (fun f => Over.Hom.left f)
      (key (Over.homMk j rfl : Over.mk (j ≫ A'.hom) ⟶ A') (by ext; exact hab))
    simpa [Hom.one_def] using h1
  obtain ⟨pt⟩ : Nonempty ((𝟙_ (Over (Sp (DualNumber k)))).left) := by
    obtain ⟨q⟩ : Nonempty (Sp k) := by
      change Nonempty (PrimeSpectrum k)
      infer_instance
    exact ⟨(spMap (TrivSqZeroExt.fstHom k k k).toRingHom).base q⟩
  have hsub1 : Subsingleton ((𝟙_ (Over (Sp (DualNumber k)))).left) := hsub
  have hy : ∀ x, d.left x = η[G'].left pt := by
    intro x
    obtain ⟨z, rfl⟩ := hjs x
    have h2 := congrArg (fun f : Z ⟶ G'.left => f z) hjd
    simp only [Scheme.Hom.comp_apply] at h2
    rw [h2]
    exact congrArg _ (Subsingleton.elim _ _)
  have hfac := GlobalTheory.DualRigidity.eq_comp_section_of_const A'.hom η[A'].left d.left
    (by simp) hsurj _ hy
  have hη' : η[A'] ≫ d = 1 := key _ hη
  have hd2 : d = toUnit A' ≫ η[A'] ≫ d := by
    ext
    exact hfac
  have hd1 : d = 1 := by
    rw [hd2, hη']
    simp
  exact mul_inv_eq_one.1 hd1

theorem main : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] (T : Scheme.{0}) (t : SAB H T) (x : Sp (DualNumber k) ⟶ T) (t' : SAB H (Sp (DualNumber k))) (ν : SABMap t' t x) (φ : t'.G.left ⟶ t.G.left), IsProper t.G.hom → IsGrpPullback t'.G t.G (constPt x) φ → (∀ (Z : Scheme.{0}) (j : Z ⟶ t'.G.left) (c : Z ⟶ Sp k), j ≫ t'.G.hom = c ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → j ≫ φ = j ≫ ν.φ) → ∀ a, (t'.act.act a).left ≫ φ = φ ≫ (t.act.act a).left := by
  intro hL E _ _ _ H k _ T t x t' ν φ hP hpb hag a
  have hsq := hpb.1
  have hprop : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) hsq hP
  have hs := t'.semi
  have hA : IsAbelianScheme t'.G :=
    { comm := hs.comm, smooth := hs.smooth, proper := hprop, geomConnected := hs.geomConnected }
  have hα : ((t'.act.act a).left ≫ φ) ≫ t.G.hom = t'.G.hom ≫ constPt x := by
    rw [Category.assoc, hsq.w, ← Category.assoc, Over.w]
  have hβ : (φ ≫ (t.act.act a).left) ≫ t.G.hom = t'.G.hom ≫ constPt x := by
    rw [Category.assoc, Over.w, hsq.w]
  let A : t'.G ⟶ t'.G := Over.homMk (hsq.lift _ _ hα) (hsq.lift_snd _ _ _)
  let B : t'.G ⟶ t'.G := Over.homMk (hsq.lift _ _ hβ) (hsq.lift_snd _ _ _)
  have e3 : (t'.act.act a).left ≫ ν.φ = ν.φ ≫ (t.act.act a).left := ν.act a
  have hj := IsPullback.of_hasPullback t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)
  have hab : pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ A.left = pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ B.left := by
    apply hsq.hom_ext
    · simp only [A, B, Over.homMk_left, Category.assoc, IsPullback.lift_fst]
      have e1 := hag _ (pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (pullback.snd t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) hj.w
      have e2 := hag _ (pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ (t'.act.act a).left) (pullback.snd t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom))
        (by rw [Category.assoc, Over.w]; exact hj.w)
      rw [← Category.assoc, e2, Category.assoc, e3, ← Category.assoc, ← e1, Category.assoc]
    · simp only [A, B, Over.homMk_left, Category.assoc, IsPullback.lift_snd]
  let e : Over.mk ((𝟙_ (Over (Sp (DualNumber k)))).hom ≫ constPt x) ⟶ t.G :=
    Over.homMk (η[t'.G].left ≫ φ) (by rw [Category.assoc, hsq.w, ← Category.assoc, Over.w]; rfl)
  have hη1 : (η[t'.G] : 𝟙_ _ ⟶ t'.G) = 1 := by simp [Hom.one_def]
  have he1 : e = 1 := by
    have hm := hpb.2 _ η[t'.G] η[t'.G] e e rfl rfl
    rw [hη1, _root_.mul_one] at hm
    have hee : e * e = e := by
      ext
      rw [hm, ← hη1]
      rfl
    exact _root_.mul_eq_left.1 hee
  have he2 : e ≫ t.act.act a = e := by
    have := t.act.hom a
    rw [he1, Hom.one_def, Category.assoc, IsMonHom.one_hom]
  have he3 := congrArg Over.Hom.left he2
  have hm1 : η[t'.G] ≫ t'.act.act a = η[t'.G] := by
    have := t'.act.hom a
    exact IsMonHom.one_hom _
  have hm2 := congrArg Over.Hom.left hm1
  have hη : η[t'.G] ≫ A = η[t'.G] ≫ B := by
    ext
    simp only [Over.comp_left]
    apply hsq.hom_ext
    · simp only [A, B, Over.homMk_left, Category.assoc, IsPullback.lift_fst]
      simp only [e, Over.comp_left, Over.homMk_left, Category.assoc] at he3 hm2
      rw [← Category.assoc, hm2, he3]
    · simp only [A, B, Over.homMk_left, Category.assoc, IsPullback.lift_snd]
  have hAB := rigidity hL k (pullback.snd t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) t'.G t'.G (pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) A B hA hj hab hη
  have hL' := congrArg Over.Hom.left hAB
  simp only [A, B, Over.homMk_left] at hL'
  calc (t'.act.act a).left ≫ φ = hsq.lift _ _ hα ≫ φ := (hsq.lift_fst _ _ _).symm
    _ = hsq.lift _ _ hβ ≫ φ := by rw [hL']
    _ = φ ≫ (t.act.act a).left := hsq.lift_fst _ _ _

end GlobalTheory.EpsAct
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfIsProperOfLbIsoLam
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory

theorem lbIso_lam_pull_id_w0 {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}
    (t : SAB H S) :
    LBIso t.PP.L ((abelian₂ t.G t.PP.L).pull (Y := t.G.left) (lift (𝟙 t.G) (t.act.act H.w0)).left) := by
  have hΛ : (abelian₂ t.G t.PP.L).IsLB := LB.isLB_linComb t.PP.isLB _ _
  refine t.prim.trans t.PP.isLB (LB.isLB_linComb t.PP.isLB _ _) (LB.isLB_pull hΛ _) ?_
  refine LBIso.chartPull (A := abelian₂ t.G t.PP.L) (B := abelian₂ t.G t.PP.L) (h := (lift (𝟙 t.G) (t.act.act H.w0)).left)
    (chartPullSame t.PP.L _ _ _ _ fun I => ?_) (Geo.Tor.chartPullPull _ _ _ rfl) (Pdiv.PullbackComparison.gen_refl _ hΛ)
  have e : psum t.G ![𝟙 t.G, t.act.act H.w0] I.down =
      lift (𝟙 t.G) (t.act.act H.w0) ≫ psum t.G (x2 t.G) I.down := by
    refine Eq.trans (congrArg (fun z => psum t.G z I.down) (funext fun i => ?_))
      (psum_hom (preHom (lift (𝟙 t.G) (t.act.act H.w0))) (x2 t.G) I.down).symm
    fin_cases i
    · exact (lift_fst _ _).symm
    · exact (lift_snd _ _).symm
  exact congrArg (fun z => z.left) e

theorem exists_sabMap_of_isProper_of_lbIso_lam : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (φ : t'.G.left ⟶ t.G.left) (φ₂ : (G2 t'.G).left ⟶ (G2 t.G).left), IsProper t.G.hom → IsGrpPullback t'.G t.G f φ → IsSquare φ φ₂ → LBIso (abelian₂ t'.G t'.PP.L) ((abelian₂ t.G t.PP.L).pull φ₂) → (∀ a, (t'.act.act a).left ≫ φ = φ ≫ (t.act.act a).left) → ∃ m : SABMap t' t f, m.φ = φ := by
  intro hL E _ _ _ H S S' t t' f φ φ₂ hp gp sq hΛ hact
  refine exists_sabMap_of_isProper_of_lbIso hL.globalFns E H S S' t t' f φ hp gp ?_ hact
  have l : (abelian₂ t.G t.PP.L).IsLB := LB.isLB_linComb t.PP.isLB _ _
  have l' : (abelian₂ t'.G t'.PP.L).IsLB := LB.isLB_linComb t'.PP.isLB _ _
  let δ : t.G.left ⟶ (G2 t.G).left := (lift (𝟙 t.G) (t.act.act H.w0)).left
  let δ' : t'.G.left ⟶ (G2 t'.G).left := (lift (𝟙 t'.G) (t'.act.act H.w0)).left
  have a₁ : δ ≫ (fst t.G t.G).left = 𝟙 _ := congrArg (fun z => z.left) (lift_fst (𝟙 t.G) (t.act.act H.w0))
  have a₂ : δ ≫ (snd t.G t.G).left = (t.act.act H.w0).left :=
    congrArg (fun z => z.left) (lift_snd (𝟙 t.G) (t.act.act H.w0))
  have b₁ : δ' ≫ (fst t'.G t'.G).left = 𝟙 _ := congrArg (fun z => z.left) (lift_fst (𝟙 t'.G) (t'.act.act H.w0))
  have b₂ : δ' ≫ (snd t'.G t'.G).left = (t'.act.act H.w0).left :=
    congrArg (fun z => z.left) (lift_snd (𝟙 t'.G) (t'.act.act H.w0))
  have e : δ' ≫ φ₂ = φ ≫ δ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst t.G t.G).left = (_ ≫ _) ≫ (fst t.G t.G).left
      rw [Category.assoc, sq.1, ← Category.assoc, b₁, Category.assoc, a₁, Category.id_comp, Category.comp_id]
    · show (_ ≫ _) ≫ (snd t.G t.G).left = (_ ≫ _) ≫ (snd t.G t.G).left
      rw [Category.assoc, sq.2, ← Category.assoc, b₂, Category.assoc, a₂, hact]
  have s₁ : LBIso t'.PP.L (((abelian₂ t.G t.PP.L).pull φ₂).pull δ') :=
    (lbIso_lam_pull_id_w0 t').trans t'.PP.isLB (LB.isLB_pull l' _) (LB.isLB_pull (LB.isLB_pull l _) _)
      (SiegelPullComp.iso_pull δ' hΛ)
  have s₂ : LBIso t'.PP.L ((abelian₂ t.G t.PP.L).pull (δ' ≫ φ₂)) :=
    s₁.trans t'.PP.isLB (LB.isLB_pull (LB.isLB_pull l _) _) (LB.isLB_pull l _) (SiegelPullComp.iso_pull_pull l φ₂ δ')
  rw [e] at s₂
  have s₃ : LBIso t'.PP.L (((abelian₂ t.G t.PP.L).pull δ).pull φ) :=
    s₂.trans t'.PP.isLB (LB.isLB_pull l _) (LB.isLB_pull (LB.isLB_pull l _) _) (SiegelPullComp.iso_pull_pull l δ φ).symm
  exact s₃.trans t'.PP.isLB (LB.isLB_pull (LB.isLB_pull l _) _) (LB.isLB_pull t.PP.isLB _)
    (SiegelPullComp.iso_pull φ (lbIso_lam_pull_id_w0 t)).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmFamilyFiniteUnramifiedOverSiegelFamily
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.FamSiegel

theorem exists_sabMap_constPt : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] (T Y : Scheme.{0}) (t : SAB H T) (A : Over Y) (_ : GrpObj A) (P : LB (G2 A).left) (y : T ⟶ Y) (θ : t.G.left ⟶ A.left) (θ₂ : (G2 t.G).left ⟶ (G2 A).left) (x : Sp (DualNumber k) ⟶ T) (t' : SAB H (Sp (DualNumber k))) (ν : SABMap t' t x), IsProper t.G.hom → P.IsLB → IsGrpPullback t.G A y θ → IsSquare θ θ₂ → LBIso (abelian₂ t.G t.PP.L) (P.pull θ₂) → x ≫ y = constPt x ≫ y → ∃ ν' : SABMap t' t (constPt x), ν'.φ ≫ θ = ν.φ ≫ θ := by
  intro hL E _ _ _ H k _ T Y t A _ P y θ θ₂ x t' ν hp hP hθ hsq hiso hx
  obtain ⟨φ, hφ₁, hφ₂⟩ : ∃ φ : t'.G.left ⟶ t.G.left, φ ≫ θ = ν.φ ≫ θ ∧ φ ≫ t.G.hom = t'.G.hom ≫ constPt x :=
    ⟨hθ.1.lift (ν.φ ≫ θ) (t'.G.hom ≫ constPt x) (by
      rw [Category.assoc, hθ.1.w, ← Category.assoc, ν.cart.1.w, Category.assoc, hx, Category.assoc]),
      hθ.1.lift_fst _ _ _, hθ.1.lift_snd _ _ _⟩
  have hφ : IsGrpPullback t'.G t.G (constPt x) φ :=
    hθ.cancel (by rw [hφ₁, ← hx]; exact ν.cart.comp hθ) hφ₂
  obtain ⟨φ₂, hφs⟩ := (GlobalTheory.LamPull.lam_pull E H _ _ t t' (constPt x)).1 φ hφ₂
  obtain ⟨ν₂, hνs⟩ := (GlobalTheory.LamPull.lam_pull E H _ _ t t' x).1 ν.φ ν.cart.1.w
  have hν := (GlobalTheory.LamPull.lam_pull E H _ _ t t' x).2 ν ν₂ hνs
  have e : φ₂ ≫ θ₂ = ν₂ ≫ θ₂ := by
    apply pullback.hom_ext
    · change (φ₂ ≫ θ₂) ≫ (fst A A).left = (ν₂ ≫ θ₂) ≫ (fst A A).left
      rw [Category.assoc, Category.assoc, hsq.1, ← Category.assoc, ← Category.assoc, hφs.1, hνs.1, Category.assoc,
        Category.assoc, hφ₁]
    · change (φ₂ ≫ θ₂) ≫ (snd A A).left = (ν₂ ≫ θ₂) ≫ (snd A A).left
      rw [Category.assoc, Category.assoc, hsq.2, ← Category.assoc, ← Category.assoc, hφs.2, hνs.2, Category.assoc,
        Category.assoc, hφ₁]
  have l : (abelian₂ t.G t.PP.L).IsLB := LB.isLB_linComb t.PP.isLB _ _
  have l' : (abelian₂ t'.G t'.PP.L).IsLB := LB.isLB_linComb t'.PP.isLB _ _
  have key : ∀ a : (G2 t'.G).left ⟶ (G2 t.G).left, LBIso ((abelian₂ t.G t.PP.L).pull a) (P.pull (a ≫ θ₂)) := fun a =>
    (SiegelPullComp.iso_pull a hiso).trans (LB.isLB_pull l _) (LB.isLB_pull (LB.isLB_pull hP _) _) (LB.isLB_pull hP _)
      (SiegelPullComp.iso_pull_pull hP θ₂ a)
  have hlam : LBIso (abelian₂ t'.G t'.PP.L) ((abelian₂ t.G t.PP.L).pull φ₂) :=
    (hν.trans l' (LB.isLB_pull l _) (LB.isLB_pull hP _) (key ν₂)).trans l' (LB.isLB_pull hP _) (LB.isLB_pull l _)
      (e ▸ (key φ₂).symm)
  have hc : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ constPt x =
      spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x := by
    rw [constPt, ← Category.assoc]
    exact (congrArg (· ≫ _) (TangentCrit.dualPt_dualBase k)).trans (Category.id_comp _)
  obtain ⟨m, hm⟩ := GlobalTheory.exists_sabMap_of_isProper_of_lbIso_lam hL E H _ _ t t' (constPt x) φ φ₂ hp hφ hφs hlam
    (GlobalTheory.EpsAct.main hL E H k T t x t' ν φ hp hφ fun Z j c hj => hθ.1.hom_ext
      (by rw [Category.assoc, Category.assoc, hφ₁])
      (by rw [Category.assoc, Category.assoc, hφ₂, ν.cart.1.w, ← Category.assoc, ← Category.assoc, hj, Category.assoc,
        Category.assoc, hc]))
  exact ⟨m, by rw [hm, hφ₁]⟩

theorem exists_extension : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (MM : Scheme.{0}) (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM) (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)) (g : ℕ) (B : Type) [CommRing B] (ζ : B) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (c : SiegPre g N ζ sY) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (sV : Sp V ⟶ Sp (RZ H n N)) (y : Sp V ⟶ Y) (x : Sp K ⟶ MM) (tK : SAB H (Sp K)) (ν : SABMap tK tM x) (lvK : D.La → (𝟙_ (Over (Sp K)) ⟶ tK.G)) (θ : tK.G.left ⟶ c.A.left), 0 < N → FamCore D sM tM lev → Flat sV → x ≫ sM = spMap (algebraMap V K) ≫ sV → (∀ a, (lvK a).left ≫ ν.φ = x ≫ (lev a).left) → IsGrpPullback tK.G c.A (spMap (algebraMap V K) ≫ y) θ → (∀ u, (lvK (bas u)).left ≫ θ = (spMap (algebraMap V K) ≫ y) ≫ (c.lev u).left) → ∃ x' : Sp V ⟶ MM, spMap (algebraMap V K) ≫ x' = x ∧ x' ≫ sM = sV := by
  intro hX hL hL₂ E _ _ _ H D n N MM sM tM lev g B _ ζ Y sY c bas V K _ _ _ _ _ _ sV y x tK ν lvK θ hN F hfl hx hlv hθ hl
  have hK := (GlobalTheory.fullObj_pull E H D n N _ _ sM tM lev x).2 tK ν lvK hlv F.obj
  rw [hx] at hK
  have hA := isGrpPullback_pullback c.A y
  have := c.ab.smooth
  have := c.ab.proper
  have := c.ab.geomConnected
  have hab : IsAbelianScheme ((Over.pullback y).obj c.A) :=
    ⟨inferInstance, MorphismProperty.of_isPullback (P := @Smooth) hA.1 ‹_›,
      MorphismProperty.of_isPullback (P := @IsProper) hA.1 ‹_›,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hA.1 ‹_›⟩
  obtain ⟨φ, hφ₁, hφ₂⟩ : ∃ φ : tK.G.left ⟶ ((Over.pullback y).obj c.A).left, φ ≫ pullback.fst _ _ = θ ∧
      φ ≫ ((Over.pullback y).obj c.A).hom = tK.G.hom ≫ spMap (algebraMap V K) :=
    ⟨hA.1.lift θ _ (hθ.1.w.trans (Category.assoc _ _ _).symm), hA.1.lift_fst _ _ _, hA.1.lift_snd _ _ _⟩
  obtain ⟨t, m, e, he, hmon, hamp, hkt⟩ := GlobalTheory.T.exists_principallyPolarizedCM_extension_dvr hX hL hL₂ E H V K _ tK φ hab
    (hA.cancel (by rw [hφ₁]; exact hθ) hφ₂) hK.ample hK.ktriv
  have hψ : IsGrpPullback t.G c.A y (e.hom.left ≫ pullback.fst _ _) :=
    ((isGrpPullback_of_iso e).comp hA).congr (Category.id_comp _) rfl
  have hθ' : m.φ ≫ e.hom.left ≫ pullback.fst _ _ = θ := by rw [← Category.assoc, he, hφ₁]
  generalize e.hom.left ≫ pullback.fst c.A.hom y = ψ at hψ hθ'
  have hex : ∀ a : D.La, ∃ s : 𝟙_ (Over (Sp V)) ⟶ t.G, s.left ≫ ψ = y ≫ (c.lev (bas.symm a)).left := fun a =>
    ⟨Over.homMk (hψ.1.lift (y ≫ (c.lev (bas.symm a)).left) (𝟙 _) (by
      rw [Category.assoc, Over.w]; exact (Category.comp_id _).trans (Category.id_comp _).symm))
      (hψ.1.lift_snd _ _ _), hψ.1.lift_fst _ _ _⟩
  choose lv hlv' using hex
  let U : Over.mk ((𝟙_ (Over (Sp V))).hom ≫ y) ⟶ 𝟙_ (Over Y) := toUnit _
  have hU : U.left = y := (Category.comp_id _).symm.trans ((Over.w U).trans (Category.id_comp _))
  have hpush : ∀ a, pushHom hψ _ (lv a) = U ≫ c.lev (bas.symm a) := fun a =>
    Over.OverMorphism.ext ((hlv' a).trans (by rw [Over.comp_left, hU]))
  have hinj : Function.Injective (pushHom hψ (𝟙_ (Over (Sp V)))) := fun a b h =>
    Over.OverMorphism.ext (hψ.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  have hadd : ∀ a b, lv (a + b) = lv a * lv b := fun a b => hinj (by
    rw [map_mul, hpush, hpush, hpush, map_add (f := _), c.lev_add, MonObj.comp_mul])
  have hker : ∀ a, lv (N • a) = 1 := fun a => by
    have h0 : lv 0 = 1 := by simpa using hadd 0 0
    have hk : ∀ k : ℕ, lv (k • a) = lv a ^ k := fun k => by
      induction k with
      | zero => simpa using h0
      | succ k ih => rw [succ_nsmul, hadd, ih, pow_succ]
    apply hinj
    rw [hk, map_pow, map_one, hpush, ← MonObj.comp_pow, c.lev_tors, MonObj.comp_one]
  have hm : ∀ a, (lvK a).left ≫ m.φ = spMap (algebraMap V K) ≫ (lv a).left := fun a =>
    ObjComp.sec_cancel hψ.1 m.cart.1.w (Over.w (lv a)) (Over.w (lvK a)) (hlv' a) (by
      rw [hθ']; simpa using hl (bas.symm a))
  have hV := GlobalTheory.FullSpread.fullObj_of_genericFibre hL hL₂ E H D n N V K sV t lv tK m lvK hN
    (MorphismProperty.of_isPullback (P := @IsProper) hψ.1 ‹_›) hamp hkt hadd hker hm hK
  obtain ⟨x', ⟨hx', m', hm'⟩, -⟩ := F.rep _ sV t lv inferInstance inferInstance hfl hV
  have : Flat (spMap (algebraMap V K)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat K (nonZeroDivisors V))
  obtain ⟨m'', hm''⟩ := ObjMaps.exists_sab_comp m' m
  refine ⟨x', (F.rep _ _ tK lvK inferInstance inferInstance inferInstance hK).unique
    ⟨by rw [Category.assoc, hx'], m'', fun a => ?_⟩ ⟨hx, ν, hlv⟩, hx'⟩
  rw [hm'']
  exact ObjComp.sec_comp (hm' a) (hm a)

end GlobalTheory.FamSiegel

namespace GlobalTheory.FamSiegel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {n N : ℕ}

theorem locallyOfFiniteType_of_qproj {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (h : IsQProjOver s) :
    LocallyOfFiniteType s := by
  obtain ⟨N, i, hi, -, hs⟩ := h
  have := isProper_str R N
  rw [← hs]
  infer_instance

theorem isSeparated_of_qproj {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (h : IsQProjOver s) :
    IsSeparated s := by
  obtain ⟨N, i, hi, -, hs⟩ := h
  have := isProper_str R N
  rw [← hs]
  infer_instance

theorem isReduced_of_flat_preimmersion {X Y : Scheme.{0}} (f : X ⟶ Y) [Flat f] [IsPreimmersion f] [IsReduced Y] :
    IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have hs : Function.Surjective (f.stalkMap x).hom := f.stalkMap_surjective x
    have hi : Function.Injective (f.stalkMap x).hom := by
      have hf := Flat.stalkMap f x
      algebraize [(f.stalkMap x).hom]
      have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
        inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
      have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (f x)) (B := X.presheaf.stalk x)
      exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
    exact isReduced_of_injective (RingEquiv.ofBijective _ ⟨hi, hs⟩).symm (RingEquiv.injective _)
  exact isReduced_of_isReduced_stalk X

variable {MM : Scheme.{0}} {sM : MM ⟶ Sp (RZ H n N)} {tM : SAB H MM} {lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)}
  {g p : ℕ} {Ag : SiegelFamily g p N} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La}
  {O : Type} [CommRing O] {b : RZ H n N →+* O} {z : ZP p N →+* O}

theorem unramified (hL : Out.Laws) (F : FamCore D sM tM lev) {t : SAB H (pullback sM (spMap b))}
    (ν : SABMap t tM (pullback.fst _ _)) {lv : D.La → (𝟙_ (Over (pullback sM (spMap b))) ⟶ t.G)}
    (hlv : ∀ a, (lv a).left ≫ ν.φ = pullback.fst _ _ ≫ (lev a).left)
    {w : pullback sM (spMap b) ⟶ pullback Ag.s (spMap z)} [LocallyOfFiniteType w]
    (hw : SiegData (pullback.snd _ _) t lv Ag z bas w) : FormallyUnramified w := by
  obtain ⟨θ, θ₂, hθ, hsq, hiso, hl⟩ := GlobalTheory.SiegelDirect.direct E H D O _ _ t lv g p N Ag z bas w hw
  have hs : w ≫ pullback.snd _ _ = pullback.snd sM (spMap b) := by
    obtain ⟨_, _, _, -, -, -, -, h, -⟩ := hw
    exact h
  have hp : IsProper t.G.hom := MorphismProperty.of_isPullback (P := @IsProper) ν.cart.1 F.obj.proper
  refine TangentCrit.formallyUnramified_of_tangent w fun k _ _ x hx => ?_
  have hx' : x ≫ w = constPt x ≫ w := hx.trans (by simp only [constPt, Category.assoc])
  have hy : x ≫ w ≫ pullback.fst _ _ = constPt x ≫ w ≫ pullback.fst _ _ := by
    rw [← Category.assoc, hx', Category.assoc]
  have h₂ : x ≫ pullback.snd sM (spMap b) = constPt x ≫ pullback.snd sM (spMap b) := by
    rw [← hs, ← Category.assoc, hx', Category.assoc]
  obtain ⟨t', κ, lv', hlv'⟩ := (GlobalTheory.fullObj_pull E H D n N _ _ (pullback.fst _ _ ≫ sM) t lv x).1
  obtain ⟨κ', hκ'⟩ := exists_sabMap_constPt hL E H k _ _ t Ag.univ.A inferInstance Ag.univ.P _ θ θ₂ x t' κ hp Ag.univ.isLB hθ hsq
    hiso hy
  have hlv'' : ∀ a, (lv' a).left ≫ κ'.φ = constPt x ≫ (lv a).left := fun a => by
    obtain ⟨u, rfl⟩ := bas.surjective a
    refine ObjComp.sec_cancel hθ.1 κ'.cart.1.w (Over.w (lv (bas u))) (Over.w (lv' (bas u))) (hl u) ?_
    rw [hκ', ← hy]
    exact ObjComp.sec_comp (hl u) (hlv' (bas u))
  obtain ⟨m, hm⟩ := ObjMaps.exists_sab_comp ν κ
  have e' : constPt x ≫ pullback.fst sM (spMap b) = constPt (x ≫ pullback.fst _ _) := by
    simp only [constPt, Category.assoc]
  obtain ⟨m', hm'⟩ : ∃ m' : SABMap t' tM (constPt (x ≫ pullback.fst _ _)), m'.φ = κ'.φ ≫ ν.φ := by
    rw [← e']; exact ObjMaps.exists_sab_comp ν κ'
  refine pullback.hom_ext ?_ h₂
  refine (F.unram k _ t' lv' m m' ?_ (fun a => ?_) fun a => ?_).trans e'.symm
  · rw [← e', Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, h₂, Category.assoc]
  · rw [hm]; exact ObjComp.sec_comp (hlv a) (hlv' a)
  · rw [hm', ← e']; exact ObjComp.sec_comp (hlv a) (hlv'' a)

theorem proper (hX : GlobalTheory.LN.HomExtSt) (hL : Out.Laws) (hL₂ : Out.Laws2) (hN : 0 < N) (F : FamCore D sM tM lev)
    [IsDedekindDomain (RZ H n N)] [IsDomain O] [IsNoetherianRing O] (hb : Function.Injective b)
    (hq : IsQProjOver Ag.s) {t : SAB H (pullback sM (spMap b))}
    (ν : SABMap t tM (pullback.fst _ _)) {lv : D.La → (𝟙_ (Over (pullback sM (spMap b))) ⟶ t.G)}
    (hlv : ∀ a, (lv a).left ≫ ν.φ = pullback.fst _ _ ≫ (lev a).left)
    {w : pullback sM (spMap b) ⟶ pullback Ag.s (spMap z)}
    (hw : SiegData (pullback.snd _ _) t lv Ag z bas w) : IsProper w := by
  obtain ⟨θ, θ₂, hθ, -, -, hl⟩ := GlobalTheory.SiegelDirect.direct E H D O _ _ t lv g p N Ag z bas w hw
  have hs : w ≫ pullback.snd _ _ = pullback.snd sM (spMap b) := by
    obtain ⟨_, _, _, -, -, -, -, h, -⟩ := hw
    exact h
  have := isSeparated_of_qproj hq
  have := locallyOfFiniteType_of_qproj hq
  have := F.flat
  have : IsLocallyNoetherian (pullback Ag.s (spMap z)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Ag.s (spMap z))
  refine GlobalTheory.ValuativeGeneric.isProper_of_lift_generic O _ _ w (pullback.snd _ _) inferInstance ?_ ?_
  · rw [hs]
    exact (GlobalTheory.isQProjOver_finite_and_baseChange _ _ sM F.qproj).2 O b
  intro V K _ _ _ _ _ _ _ x y hx hxy
  have h₂ : x ≫ pullback.snd sM (spMap b) = spMap (algebraMap V K) ≫ y ≫ pullback.snd _ _ := by
    rw [← hs, ← Category.assoc, hxy, Category.assoc]
  have hfl : Flat ((y ≫ pullback.snd _ _) ≫ spMap b) :=
    GlobalTheory.GenericFlat.generic_charZero_and_flat.2 _ O b _ (pullback.snd sM (spMap b)) V K x _ hb inferInstance hx h₂
  obtain ⟨t', κ, lv', hlv'⟩ := (GlobalTheory.fullObj_pull E H D n N _ _ (pullback.fst _ _ ≫ sM) t lv x).1
  obtain ⟨m, hm⟩ := ObjMaps.exists_sab_comp ν κ
  have hy : x ≫ w ≫ pullback.fst _ _ = spMap (algebraMap V K) ≫ y ≫ pullback.fst _ _ := by
    rw [← Category.assoc, hxy, Category.assoc]
  obtain ⟨x', hx₁, hx₂⟩ := exists_extension hX hL hL₂ E H D n N MM sM tM lev g _ _ _ _ Ag.univ bas V K _ (y ≫ pullback.fst _ _) _ t' m
    lv' (κ.φ ≫ θ) hN F hfl
    (by rw [Category.assoc, pullback.condition, ← Category.assoc, h₂]; simp only [Category.assoc])
    (fun a => by rw [hm]; exact ObjComp.sec_comp (hlv a) (hlv' a))
    (hy ▸ κ.cart.comp hθ) (fun u => hy ▸ ObjComp.sec_comp (hl u) (hlv' (bas u)))
  refine ⟨pullback.lift x' (y ≫ pullback.snd _ _) hx₂, pullback.hom_ext ?_ ?_⟩
  · rw [Category.assoc, pullback.lift_fst, hx₁]
  · rw [Category.assoc, pullback.lift_snd, h₂]

theorem core (hX : GlobalTheory.LN.HomExtSt) (hL : Out.Laws) (hL₂ : Out.Laws2) (hN : 0 < N) (hodd : Odd N)
    (F : FamCore D sM tM lev) [IsDedekindDomain (RZ H n N)] [IsDomain O] [CharZero O] [IsNoetherianRing O]
    (hb : Function.Injective b) [Flat (spMap b)] [IsPreimmersion (spMap b)] [Flat (spMap z)] (hu : IsUnit (N : O))
    (hz : z (zetaZP p N) = b (RZ.ze H n N)) (hbas : ∀ x y, D.EF (bas x) (bas y) = omegaStd x y) (hA : SiegRep Ag)
    {t : SAB H (pullback sM (spMap b))}
    (ν : SABMap t tM (pullback.fst _ _)) {lv : D.La → (𝟙_ (Over (pullback sM (spMap b))) ⟶ t.G)}
    (hlv : ∀ a, (lv a).left ≫ ν.φ = pullback.fst _ _ ≫ (lev a).left) :
    ∃ w : pullback sM (spMap b) ⟶ pullback Ag.s (spMap z),
      SiegData (pullback.snd _ _) t lv Ag z bas w ∧ IsFinite w ∧ FormallyUnramified w := by
  have := F.flat
  have := F.red
  have := locallyOfFiniteType_of_qproj F.qproj
  have hn : IsLocallyNoetherian (pullback sM (spMap b)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd sM (spMap b))
  have hr : IsReduced (pullback sM (spMap b)) := isReduced_of_flat_preimmersion (pullback.fst _ _)
  have ho := (GlobalTheory.fullObj_pull E H D n N _ _ sM tM lev _).2 t ν lv hlv F.obj
  rw [pullback.condition] at ho
  obtain ⟨o, φ, φ₂, hpr, h₁, h₂, h₃, h₄⟩ := GlobalTheory.exists_siegPre_of_fullObj hL hL₂ E H D n N p O b z _ (pullback.snd _ _) t lv g bas hodd hu hz hn
    (GlobalTheory.GenericFlat.generic_charZero_and_flat.1 O _ (pullback.snd sM (spMap b)) inferInstance) hbas ho
  obtain ⟨f, ⟨hf, hf'⟩, -⟩ := hA.2 _ _ o hr hn inferInstance hpr
  have hw : SiegData (pullback.snd _ _) t lv Ag z bas (pullback.lift f _ hf) :=
    ⟨o, φ, φ₂, h₁, h₂, h₃, h₄, pullback.lift_snd _ _ _, by rw [pullback.lift_fst]; exact hf'⟩
  have := proper hX hL hL₂ hN F hb hA.1 ν hlv hw
  have := unramified hL F ν hlv hw
  have := TangentCrit.locallyQuasiFinite_of_formallyUnramified (pullback.lift f _ hf)
  exact ⟨_, hw, .of_isProper_of_locallyQuasiFinite _, ‹_›⟩

theorem baseChange {O' : Type} [CommRing O'] (c : O →+* O') {b' : RZ H n N →+* O'} {z' : ZP p N →+* O'}
    (hb : c.comp b = b') (hz : c.comp z = z') {t : SAB H (pullback sM (spMap b))}
    (ν : SABMap t tM (pullback.fst _ _)) {lv : D.La → (𝟙_ (Over (pullback sM (spMap b))) ⟶ t.G)}
    (hlv : ∀ a, (lv a).left ≫ ν.φ = pullback.fst _ _ ≫ (lev a).left)
    {w : pullback sM (spMap b) ⟶ pullback Ag.s (spMap z)} (hw : SiegData (pullback.snd _ _) t lv Ag z bas w)
    [IsFinite w] [FormallyUnramified w] {T : Scheme.{0}} {sT : T ⟶ Sp O'} {f : T ⟶ MM} {tT : SAB H T}
    (κ : SABMap tT tM f) {lvT : D.La → (𝟙_ (Over T) ⟶ tT.G)} (hT : IsPullback f sT sM (spMap b'))
    (hlvT : ∀ a, (lvT a).left ≫ κ.φ = f ≫ (lev a).left) :
    ∃ w' : T ⟶ pullback Ag.s (spMap z'), SiegData sT tT lvT Ag z' bas w' ∧ IsFinite w' ∧ FormallyUnramified w' := by
  have eb : spMap c ≫ spMap b = spMap b' := by rw [← hb, ← Spec.map_comp]; rfl
  have ez : spMap c ≫ spMap z = spMap z' := by rw [← hz, ← Spec.map_comp]; rfl
  have hs : w ≫ pullback.snd _ _ = pullback.snd sM (spMap b) := by
    obtain ⟨_, _, _, -, -, -, -, h, -⟩ := hw
    exact h
  obtain ⟨r, hr₁, hr₂⟩ : ∃ r : T ⟶ pullback sM (spMap b), r ≫ pullback.fst _ _ = f ∧ r ≫ pullback.snd _ _ = sT ≫ spMap c :=
    ⟨pullback.lift f (sT ≫ spMap c) (by rw [Category.assoc, eb, hT.w]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hr : IsPullback r sT (pullback.snd sM (spMap b)) (spMap c) :=
    IsPullback.of_right (by rw [hr₁, eb]; exact hT) hr₂ (IsPullback.of_hasPullback _ _)
  subst hr₁
  obtain ⟨κ', hκ'⟩ := ObjMaps.exists_sab_cancel ν κ
  have hl : ∀ a, (lvT a).left ≫ κ'.φ = r ≫ (lv a).left := fun a =>
    ObjComp.sec_cancel ν.cart.1 κ'.cart.1.w (Over.w (lv a)) (Over.w (lvT a)) (hlv a) (by rw [← hκ']; exact hlvT a)
  have e : (r ≫ pullback.snd sM (spMap b)) ≫ spMap z = sT ≫ spMap z' := by rw [hr₂, Category.assoc, ez]
  obtain ⟨w', hw₁, hw₂⟩ : ∃ w' : T ⟶ pullback Ag.s (spMap z'),
      w' ≫ pullback.fst _ _ = (r ≫ w) ≫ pullback.fst _ _ ∧ w' ≫ pullback.snd _ _ = sT :=
    ⟨pullback.lift ((r ≫ w) ≫ pullback.fst _ _) sT (by
      rw [← e, ← hs]; simp only [Category.assoc, pullback.condition]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨q, hq₁, hq₂⟩ : ∃ q : pullback Ag.s (spMap z') ⟶ pullback Ag.s (spMap z),
      q ≫ pullback.fst _ _ = pullback.fst _ _ ∧ q ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap c :=
    ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap c) (by rw [Category.assoc, ez, pullback.condition]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hq : IsPullback q (pullback.snd _ _) (pullback.snd Ag.s (spMap z)) (spMap c) :=
    IsPullback.of_right (by rw [hq₁, ez]; exact IsPullback.of_hasPullback _ _) hq₂ (IsPullback.of_hasPullback _ _)
  have hsq : IsPullback r w' w q := by
    refine IsPullback.of_bot (by rw [hw₂, hs]; exact hr) (pullback.hom_ext ?_ ?_) hq
    · rw [Category.assoc w', hq₁, hw₁]
    · rw [Category.assoc, hs, hr₂, Category.assoc, hq₂, ← Category.assoc, hw₂]
  refine ⟨w', ?_, MorphismProperty.of_isPullback (P := @IsFinite) hsq ‹_›,
    MorphismProperty.of_isPullback (P := @FormallyUnramified) hsq ‹_›⟩
  obtain ⟨o, φ, φ₂, h₁, h₂, h₃, h₄, -, h₅⟩ := GlobalTheory.T.siegelData_pullback_of_levelMap E H D O _ T _ r t tT κ' lv lvT g p N Ag z bas w hl hw
  rw [← hw₁] at h₅
  unfold SiegData
  generalize (r ≫ pullback.snd sM (spMap b)) ≫ spMap z = s at e o φ φ₂ h₁ h₂ h₃ h₄ h₅
  subst e
  exact ⟨o, φ, φ₂, h₁, h₂, h₃, h₄, hw₂, h₅⟩

theorem exists_lift_subring {O : Type} [CommRing O] {i : O →+* ℂ} (hi : Function.Injective i) {S : Subring ℂ}
    (h : S ≤ i.range) : ∃ c : S →+* O, ∀ x, i (c x) = x := by
  let e : O ≃+* i.range :=
    RingEquiv.ofBijective i.rangeRestrict ⟨fun _ _ h => hi (congrArg Subtype.val h), i.rangeRestrict_surjective⟩
  exact ⟨e.symm.toRingHom.comp (Subring.inclusion h), fun x => congrArg Subtype.val (e.apply_symm_apply ⟨x, h x.2⟩)⟩

theorem isUnit_natCast_of_inv_mem {S : Subring ℂ} {m : ℕ} (hm : m ≠ 0) (h : (m : ℂ)⁻¹ ∈ S) : IsUnit (m : S) := by
  refine IsUnit.of_mul_eq_one ⟨_, h⟩ (Subtype.ext ?_)
  simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hm : (m : ℂ) ≠ 0)

end GlobalTheory.FamSiegel


open GlobalTheory.FamSiegel in
theorem GlobalTheory.siegClause_of_famCore : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (MM : Scheme.{0}) (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM) (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)), 1 ≤ D.p + D.q → n.Prime → Odd n → (∃ j, 1 ≤ j ∧ N = n ^ j) → FamCore D sM tM lev → (∀ p : ℕ, p.Prime → p ≠ n → ∃ Ag : SiegelFamily (Module.finrank ℚ E / 2 * (D.p + D.q)) p N, SiegRep Ag) → SiegClause D sM tM lev := by
  intro hX hL hL₂ E _ _ _ H D n N MM sM tM lev _ hn hodd hj F hAg p hp hpn
  obtain ⟨Ag, hA⟩ := hAg p hp hpn
  obtain ⟨bas₀, hbas₀⟩ := GlobalTheory.ZM.exists_isSympBasis E H D
  obtain ⟨-, bas, hbas⟩ := GlobalTheory.ZM.sympBasis_std E H D _ bas₀ hbas₀
  obtain ⟨hD, hO, h₁, h₂, h₃⟩ := GlobalTheory.JoinRing.join_rings E H n N p hn hj hp hpn
  obtain ⟨j, -, hj⟩ := hj
  have hN : 0 < N := by rw [hj]; exact pow_pos hn.pos j
  have hNo : Odd N := by rw [hj]; exact hodd.pow
  refine ⟨Ag, bas, hbas, fun O _ i z b hi hz hb T sT f tT κ lvT hT hlvT => ?_⟩
  have hle : RZ H n N ⊔ ZP p N ≤ i.range :=
    sup_le (fun x hx => ⟨b ⟨x, hx⟩, hb _⟩) fun x hx => ⟨z ⟨x, hx⟩, hz _⟩
  obtain ⟨S, l₁, l₂, hO, h₁, h₂, h₃, hle⟩ : ∃ (S : Subring ℂ) (l₁ : RZ H n N ≤ S) (l₂ : ZP p N ≤ S),
      IsNoetherianRing S ∧ Flat (spMap (Subring.inclusion l₁)) ∧ IsPreimmersion (spMap (Subring.inclusion l₁)) ∧
        Flat (spMap (Subring.inclusion l₂)) ∧ S ≤ i.range := ⟨_, le_sup_left, le_sup_right, hO, h₁, h₂, h₃, hle⟩
  have hu : IsUnit (N : S) := by
    have := (GlobalTheory.FamSiegel.isUnit_natCast_of_inv_mem hn.ne_zero (l₁ (Subring.subset_closure (Or.inr (Or.inl rfl))))).pow j
    rwa [← Nat.cast_pow, ← hj] at this
  obtain ⟨t, ν, lv, hlv⟩ := (GlobalTheory.fullObj_pull E H D n N _ _ sM tM lev (pullback.fst sM (spMap (Subring.inclusion l₁)))).1
  obtain ⟨w, hw, _, _⟩ := GlobalTheory.FamSiegel.core (z := Subring.inclusion l₂) hX hL hL₂ hN hNo F (Subring.inclusion_injective l₁) hu
    (Subtype.ext rfl) hbas hA ν hlv
  obtain ⟨c, hc⟩ := GlobalTheory.FamSiegel.exists_lift_subring hi hle
  exact GlobalTheory.FamSiegel.baseChange c (RingHom.ext fun x => hi ((hc ⟨x, l₁ x.2⟩).trans (hb x).symm))
    (RingHom.ext fun x => hi ((hc ⟨x, l₂ x.2⟩).trans (hz x).symm)) ν hlv hw κ hT hlvT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmFamilyFiniteUnramifiedOverSiegelFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmFamily_finite_unramified_over_siegelFamily : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (MM : Scheme.{0}) (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM) (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)), 1 ≤ D.p + D.q → n.Prime → Odd n → (∃ j, 1 ≤ j ∧ N = n ^ j) → FamCore D sM tM lev → (∀ p : ℕ, p.Prime → p ≠ n → ∃ Ag : SiegelFamily (Module.finrank ℚ E / 2 * (D.p + D.q)) p N, SiegRep Ag) → SiegClause D sM tM lev := by
  first | exact @GlobalTheory.siegClause_of_famCore | exact GlobalTheory.siegClause_of_famCore | (intros; apply GlobalTheory.siegClause_of_famCore <;> assumption)
end
