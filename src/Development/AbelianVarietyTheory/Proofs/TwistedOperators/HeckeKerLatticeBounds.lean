module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFormEigenMemSinglePart

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKerLatticeBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLiftKer
set_option autoImplicit false

noncomputable section

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HeckeKerLat

theorem ex_nsmul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P) (n : ℕ) (w : Fin g → ℂ) :
    F.ex i P (n • w) = F.ex i P w ^ n := by
  induction n with
  | zero =>
    rw [zero_smul, pow_zero]
    have := (F.ex_ker i P hP 0).2 (zero_mem _)
    exact this
  | succ n ih => rw [succ_nsmul, F.ex_add i P hP, ih, pow_succ]

theorem exists_lift_ker : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty) (i j : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (P' : (F.Di j).La →+ (Fin g → ℂ)) (p : ℕ) (C : Subgroup (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) (ψ : pullback Xo.univ.t.G.hom (F.u i P) ⟶ pullback Xo.univ.t.G.hom (F.u j P')) (ψp : (Over.mk (F.u i P) ⟶ Xo.univ.t.G) →* (Over.mk (F.u j P') ⟶ Xo.univ.t.G)), IsPeriod (F.Di i) ty P → IsPeriod (F.Di j) ty P' → p.Prime → (∀ a ∈ C, a ^ p ^ 2 = 1) → Formalism.L2.Pj.IsHkIsog p (F.u i P) (F.u j P') C ψ ψp →
  ∃ (gam : (F.Di i).La →ₗ[𝓞 E] (F.Di j).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
    (∀ a b, (F.Di j).EF (gam a) (gam b) = (p : ℤ) ^ 2 * (F.Di i).EF a b) ∧ (∀ a, P' (gam a) = h (P a)) ∧
    (∀ b, ∃ a, gam a = (p ^ 2) • b) ∧ (∀ z, F.ex j P' (h z) = ψp (F.ex i P z)) ∧
    (∀ a, F.ex i P (((p : ℂ) ^ 2)⁻¹ • P a) ∈ C ↔ ∃ b, gam a = (p ^ 2) • b) ∧
    ∀ c ∈ C, ∃ a, c = F.ex i P (((p : ℂ) ^ 2)⁻¹ • P a) := by
  intro E _ _ _ H Dw l Xo σ g ty F i j P P' p C ψ ψp hP hP' hp hC hI
  obtain ⟨gam, h, h1, h2, h3, h4⟩ := GlobalTheory.T.heckeIsogeny_lifts_to_lattice_map_scaling_forms E H Dw l Xo σ g ty F i j P P' p C ψ ψp hP hP' hp hC hI
  have hker : ψp.ker = C := hI.2.2.2.2.2.1
  have hp0 : ((p : ℂ) ^ 2) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)
  refine ⟨gam, h, h1, h2, h3, h4, fun a => ?_, fun c hc => ?_⟩
  · rw [← hker, MonoidHom.mem_ker, ← h4, map_smul, ← h2, F.ex_ker j P' hP']
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨b, hP'.2.1 ?_⟩
      rw [map_nsmul, hb, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      push_cast
      rw [mul_inv_cancel₀ hp0, one_smul]
    · rintro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      rw [hb, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      push_cast
      rw [inv_mul_cancel₀ hp0, one_smul]
  · obtain ⟨w, rfl⟩ := F.ex_onto i P hP c
    have e1 : F.ex i P ((p ^ 2) • w) = 1 := by rw [ex_nsmul F i P hP, hC _ hc]
    obtain ⟨a, ha⟩ := (F.ex_ker i P hP _).1 e1
    refine ⟨a, congrArg _ ?_⟩
    rw [ha, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    push_cast
    rw [inv_mul_cancel₀ hp0, one_smul]

end GlobalTheory.HeckeKerLat
end
end

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section

set_option autoImplicit false

namespace GlobalTheory.HeckeKerIdx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem ex_smul_act (F : FamilyUnif Xo σ ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) (c : ℂ) (r : 𝓞 E) (v : (F.Di i).La) :
    F.ex i P (c • P (r • v)) = F.ex i P (c • P v) ≫ Xo.univ.t.act.act r := by
  rw [← F.ex_lin i P hP]
  congr 1
  ext k
  rw [Pi.smul_apply, hP.1, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]

theorem inv_smul_natCast {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (P : La →+ (Fin g → ℂ)) {n : ℕ}
    (hn : n ≠ 0) (w : La) : ((n : ℂ))⁻¹ • P ((n : 𝓞 E) • w) = P w := by
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn), one_smul]

theorem sq_inv_smul_natCast {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (P : La →+ (Fin g → ℂ)) {n : ℕ}
    (hn : n ≠ 0) (w : La) : ((n : ℂ) ^ 2)⁻¹ • P ((n : 𝓞 E) • w) = (n : ℂ)⁻¹ • P w := by
  rw [pow_two, mul_inv, mul_smul, inv_smul_natCast P hn]

theorem mem_span_smul_top {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (n : ℕ) (x : La) :
    x ∈ Ideal.span {(n : 𝓞 E)} • (⊤ : Submodule (𝓞 E) La) ↔ ∃ b, (n : 𝓞 E) • b = x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp

end GlobalTheory.HeckeKerIdx


open GlobalTheory.HeckeKerIdx in
theorem GlobalTheory.heckeKer_lattice_bounds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (𝔓 : Ideal (𝓞 E)) (p k : ℕ) (C : Subgroup (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) (M : Submodule (𝓞 E) (F.Di i).La), IsPeriod (F.Di i) ty P → GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime l 𝔓 p → Xo.univ.t.HeckeKer (Over.mk (F.u i P)) Dw 𝔓 p k C → (∀ a, F.ex i P (((p : ℂ) ^ 2)⁻¹ • P a) ∈ C ↔ a ∈ M) → (Ideal.span {(p : 𝓞 E)} * 𝔓) • (⊤ : Submodule (𝓞 E) (F.Di i).La) ≤ M ∧ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) • M ≤ Ideal.span {(p : 𝓞 E)} • (⊤ : Submodule (𝓞 E) (F.Di i).La) ∧ Nat.card (↥(Ideal.span {(p : 𝓞 E)} • (⊤ : Submodule (𝓞 E) (F.Di i).La)) ⧸ M.comap (Ideal.span {(p : 𝓞 E)} • (⊤ : Submodule (𝓞 E) (F.Di i).La)).subtype) = Ideal.absNorm 𝔓 ^ k := by
  intro E _ _ _ H Dw l Xo σ g ty F i P 𝔓 p k C M hP hH hK hM
  obtain ⟨-, -, -, hp, hp𝔓⟩ := hH
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp0
  refine ⟨?_, ?_, ?_⟩
  · rw [Submodule.smul_le]
    intro x hx a _
    obtain ⟨π, hπ, rfl⟩ := Ideal.mem_span_singleton_mul.1 hx
    obtain ⟨J, hJ⟩ : 𝔓 ∣ Ideal.span {(p : 𝓞 E)} :=
      Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hp𝔓)
    rw [← hM, mul_smul, sq_inv_smul_natCast P hp0]
    refine hK.2.1 J (by rw [hJ, mul_comm]) fun j hj => ?_
    rw [← ex_smul_act F i P hP, smul_smul]
    have hjπ : j * π ∈ Ideal.span {(p : 𝓞 E)} := by
      rw [hJ, mul_comm j]
      exact Ideal.mul_mem_mul hπ hj
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hjπ
    rw [hc, mul_smul, inv_smul_natCast P hp0]
    exact (F.ex_ker i P hP _).2 ⟨_, rfl⟩
  · rw [Submodule.smul_le]
    intro r hr a ha
    have h1 := hK.2.2.1 ((hM a).2 ha) ((p : 𝓞 E) * r)
      (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hr)
    rw [← ex_smul_act F i P hP, mul_smul, sq_inv_smul_natCast P hp0, F.ex_ker i P hP] at h1
    obtain ⟨b, hb⟩ := h1
    rw [mem_span_smul_top]
    refine ⟨b, hP.2.1 ?_⟩
    rw [Nat.cast_smul_eq_nsmul, map_nsmul, hb, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hpC, one_smul]
  · set N : Submodule (𝓞 E) (F.Di i).La := Ideal.span {(p : 𝓞 E)} • (⊤ : Submodule (𝓞 E) (F.Di i).La) with hN
    set Tp := GlobalTheory.HeckeKerModel.torsSub Xo.univ.t (Over.mk (F.u i P)) p with hTp
    have hmemTp : ∀ y, y ∈ Tp ↔ y ^ p = 1 := fun y => GlobalTheory.HeckeKerModel.mem_tors_span Xo.univ.t y p
    have hpow : ∀ w, F.ex i P w ^ p = F.ex i P (p • w) := fun w => (GlobalTheory.HeckeKerLat.ex_nsmul F i P hP p w).symm
    have hinvmem : ∀ b, F.ex i P ((p : ℂ)⁻¹ • P b) ∈ Tp := fun b => by
      rw [hmemTp, hpow, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hpC, one_smul]
      exact (F.ex_ker i P hP _).2 ⟨b, rfl⟩
    have hmemN : ∀ x ∈ N, F.ex i P (((p : ℂ) ^ 2)⁻¹ • P x) ∈ Tp := fun x hx => by
      obtain ⟨b, rfl⟩ := (mem_span_smul_top p x).1 hx
      rw [sq_inv_smul_natCast P hp0]
      exact hinvmem b
    let fA : ↥N →+ Additive ↥Tp :=
      { toFun := fun x => Additive.ofMul ⟨F.ex i P (((p : ℂ) ^ 2)⁻¹ • P x), hmemN x.1 x.2⟩
        map_zero' := by
          apply Additive.toMul.injective
          apply Subtype.ext
          show F.ex i P (((p : ℂ) ^ 2)⁻¹ • P 0) = 1
          rw [map_zero, smul_zero]
          exact (F.ex_ker i P hP 0).2 (zero_mem _)
        map_add' := fun x y => by
          apply Additive.toMul.injective
          apply Subtype.ext
          show F.ex i P (((p : ℂ) ^ 2)⁻¹ • P (x.1 + y.1)) = F.ex i P (((p : ℂ) ^ 2)⁻¹ • P x.1) * F.ex i P (((p : ℂ) ^ 2)⁻¹ • P y.1)
          rw [map_add (f := _), smul_add, F.ex_add i P hP] }
    let h0 : (F.Di i).La →+ ↥N :=
      { toFun := fun a => ⟨(p : 𝓞 E) • a, (mem_span_smul_top p _).2 ⟨a, rfl⟩⟩
        map_zero' := by ext; simp
        map_add' := fun a b => by ext; simp [smul_add] }
    have hgsurj : Function.Surjective (fA.comp h0) := by
      intro y
      obtain ⟨w, hw⟩ := F.ex_onto i P hP (Additive.toMul y).1
      have h1 : F.ex i P (p • w) = 1 := by rw [← hpow, hw]; exact (hmemTp _).1 (Additive.toMul y).2
      obtain ⟨a, ha⟩ := (F.ex_ker i P hP _).1 h1
      refine ⟨a, ?_⟩
      apply Additive.toMul.injective
      apply Subtype.ext
      show F.ex i P (((p : ℂ) ^ 2)⁻¹ • P ((p : 𝓞 E) • a)) = (Additive.toMul y).1
      rw [sq_inv_smul_natCast P hp0, ha, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hpC, one_smul, hw]
    have hsurj : Function.Surjective fA := fun y => by
      obtain ⟨a, ha⟩ := hgsurj y
      exact ⟨h0 a, ha⟩
    set H' : AddSubgroup (Additive ↥Tp) := Subgroup.toAddSubgroup (C.subgroupOf Tp) with hH'
    have hker : (M.comap N.subtype).toAddSubgroup = H'.comap fA := by
      ext x
      rw [AddSubgroup.mem_comap]
      show x.1 ∈ M ↔ _
      rw [← hM]
      rfl
    have hidx : Nat.card (↥N ⧸ M.comap N.subtype) = H'.index := by
      rw [← AddSubgroup.index_comap_of_surjective H' hsurj, ← hker]
      rfl
    have hcardTp : Nat.card (Additive ↥Tp) = Nat.card (Xo.univ.t.tors (Over.mk (F.u i P)) (Ideal.span {(p : 𝓞 E)})) := rfl
    have hcardH : Nat.card H' = Nat.card ((C : Set (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) ∩ Xo.univ.t.tors (Over.mk (F.u i P)) (Ideal.span {(p : 𝓞 E)}) : Set (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) :=
      Nat.card_congr
        { toFun := fun z => ⟨(Additive.toMul z.1).1, z.2, (Additive.toMul z.1).2⟩
          invFun := fun z => ⟨Additive.ofMul ⟨z.1, z.2.2⟩, z.2.1⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have hfin : Nat.card (Additive ↥Tp) ≠ 0 := by
      have := (F.Di i).fin
      have := GlobalTheory.datum_free_int (F.Di i)
      have : Module.Finite ℤ (F.Di i).La := Module.Finite.trans (𝓞 E) (F.Di i).La
      have hle : (nsmulAddMonoidHom (α := (F.Di i).La) p).range ≤ (fA.comp h0).ker := by
        rintro _ ⟨b, rfl⟩
        rw [AddMonoidHom.mem_ker]
        apply Additive.toMul.injective
        apply Subtype.ext
        show F.ex i P (((p : ℂ) ^ 2)⁻¹ • P ((p : 𝓞 E) • (p • b))) = 1
        rw [sq_inv_smul_natCast P hp0, ← Nat.cast_smul_eq_nsmul (𝓞 E), inv_smul_natCast P hp0]
        exact (F.ex_ker i P hP _).2 ⟨b, rfl⟩
      have hd := AddSubgroup.index_dvd_of_le hle
      rw [AddSubgroup.index_range_nsmul, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hgsurj,
        AddSubgroup.card_top] at hd
      intro h0'
      rw [h0', zero_dvd_iff] at hd
      exact pow_ne_zero _ hp0 hd
    have key := H'.index_mul_card
    rw [hcardTp, hK.2.2.2.2.2, hcardH] at key
    rw [hidx]
    have hc : Nat.card ((C : Set (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) ∩ Xo.univ.t.tors (Over.mk (F.u i P)) (Ideal.span {(p : 𝓞 E)}) : Set (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) ≠ 0 := by
      intro hc0
      apply hfin
      rw [hcardTp, hK.2.2.2.2.2, hc0, zero_mul]
    rw [mul_comm (Nat.card _) (Ideal.absNorm 𝔓 ^ k)] at key
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hc) key
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatioLocalFunctionsGeometricFibreDescendsBase
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatioLocalFunctionsGeometricFibreDescendsBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

namespace GlobalTheory.GlobalSectionsBijection

theorem toΓ_bij (S : Type) [CommRing S] : Function.Bijective (toΓ S) :=
  (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv)

theorem appLE_top_top {X Y : Scheme.{0}} (f : X ⟶ Y) : f.appLE ⊤ ⊤ le_top = f.appTop :=
  (Scheme.Hom.app_eq_appLE _).symm

theorem spMap_appLE_toΓ {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) (a : T) :
    ((spMap χ).appLE ⊤ ⊤ le_top).hom (toΓ T a) = toΓ Ω (χ a) := by
  rw [appLE_top_top]
  exact (congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom χ))).symm

theorem compat {T Ω : Type} [CommRing T] [CommRing Ω] {Y : Scheme.{0}} (q : Y ⟶ Sp T) (χ : T →+* Ω)
    (w : Sp Ω ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) (hw : w ≫ q = spMap χ) (a : T) :
    (w.appLE U ⊤ h).hom ((q.appLE ⊤ U le_top).hom (toΓ T a)) = toΓ Ω (χ a) := by
  have key : (q.appLE ⊤ U le_top ≫ w.appLE U ⊤ h) = (w ≫ q).appLE ⊤ ⊤ le_top :=
    Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  rw [← CommRingCat.comp_apply, key]
  have : ∀ g : Sp Ω ⟶ Sp T, g = spMap χ → (g.appLE ⊤ ⊤ le_top).hom (toΓ T a) = toΓ Ω (χ a) := by
    rintro _ rfl; exact spMap_appLE_toΓ χ a
  exact this _ hw

end GlobalTheory.GlobalSectionsBijection

namespace GlobalTheory.GlobalSectionsBijection

theorem ne_zero_of_mem {Ω : Type} [CommRing Ω] {Y : Scheme.{0}} (w : Sp Ω ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U)
    (s : Γ(Y, U)) (x : Sp Ω) (hx : w x ∈ Y.basicOpen s) : (w.appLE U ⊤ h).hom s ≠ 0 := by
  intro h0
  have e := Scheme.basicOpen_appLE w ⊤ U h s
  rw [h0, Scheme.basicOpen_zero] at e
  have : x ∈ (⊤ ⊓ w ⁻¹ᵁ Y.basicOpen s : (Sp Ω).Opens) := ⟨trivial, hx⟩
  rw [← e] at this
  exact this

theorem mem_of_ne_zero {Ω : Type} [Field Ω] {Y : Scheme.{0}} (w : Sp Ω ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U)
    (s : Γ(Y, U)) (hs : (w.appLE U ⊤ h).hom s ≠ 0) (x : Sp Ω) : w x ∈ Y.basicOpen s := by
  set g := (w.appLE U ⊤ h).hom s
  have hu : IsUnit g := by
    have e0 : (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom g ≠ 0 := by
      intro e0
      apply hs
      have := congrArg (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom e0
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id, map_zero] at this
      exact this
    have := (IsUnit.mk0 _ e0).map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id] at this
    exact this
  have e := Scheme.basicOpen_appLE w ⊤ U h s
  rw [Scheme.basicOpen_of_isUnit _ hu] at e
  have : x ∈ (⊤ : (Sp Ω).Opens) := trivial
  rw [e] at this
  exact this.2

theorem exists_geom (Y : Scheme.{0}) (y : Y) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (w : Sp Ω ⟶ Y), ∀ x, w x = y := by
  refine ⟨AlgebraicClosure (Y.residueField y), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
      Y.fromSpecResidueField y, fun x => ?_⟩
  have : (Y.fromSpecResidueField y) ((Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
      (AlgebraicClosure (Y.residueField y))))) x) ∈ Set.range (Y.fromSpecResidueField y) := ⟨_, rfl⟩
  rw [Scheme.range_fromSpecResidueField] at this
  exact this

end GlobalTheory.GlobalSectionsBijection

namespace GlobalTheory.GlobalSectionsBijection

theorem fromSpec_appLE_top {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W) (e : ⊤ ≤ hW.fromSpec ⁻¹ᵁ W) :
    hW.fromSpec.appLE W ⊤ e = (Scheme.ΓSpecIso Γ(Y, W)).inv := by
  rw [Scheme.Hom.appLE, hW.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  rw [show (eqToHom hW.fromSpec_preimage_self).op ≫ (homOfLE e).op = 𝟙 _ from Subsingleton.elim _ _,
    CategoryTheory.Functor.map_id, Category.comp_id]

theorem chart_top {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {R : Type} [CommRing R]
    (c : Γ(Y, V) →+* R) : ⊤ ≤ (spMap c ≫ hV.fromSpec) ⁻¹ᵁ V := by
  intro x _
  show hV.fromSpec (spMap c x) ∈ (V : Set Y)
  rw [← hV.range_fromSpec]
  exact ⟨_, rfl⟩

theorem chart_eval {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {R : Type} [CommRing R]
    (c : Γ(Y, V) →+* R) (U' : Y.Opens) (hle : V ≤ U') (h : ⊤ ≤ (spMap c ≫ hV.fromSpec) ⁻¹ᵁ U')
    (s : Γ(Y, U')) :
    ((spMap c ≫ hV.fromSpec).appLE U' ⊤ h).hom s = toΓ R (c ((Y.presheaf.map (homOfLE hle).op).hom s)) := by
  have h' := chart_top hV c
  have e1 : (spMap c ≫ hV.fromSpec).appLE U' ⊤ h =
      Y.presheaf.map (homOfLE hle).op ≫ (spMap c ≫ hV.fromSpec).appLE V ⊤ h' :=
    (Scheme.Hom.map_appLE _ _ _).symm
  have e0 : (⊤ : (Spec Γ(Y, V)).Opens) ≤ hV.fromSpec ⁻¹ᵁ V := by simp
  have e2 : (spMap c ≫ hV.fromSpec).appLE V ⊤ h' =
      hV.fromSpec.appLE V ⊤ e0 ≫ (spMap c).appLE ⊤ ⊤ le_top :=
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [e1, e2, fromSpec_appLE_top]
  simp only [CommRingCat.comp_apply]
  exact spMap_appLE_toΓ c _

end GlobalTheory.GlobalSectionsBijection

namespace GlobalTheory.GlobalSectionsBijection

theorem chart_comp {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {R T : Type} [CommRing R] [CommRing T]
    (q : Y ⟶ Sp T) (c : Γ(Y, V) →+* R) :
    (spMap c ≫ hV.fromSpec) ≫ q = spMap (c.comp ((q.appLE ⊤ V le_top).hom.comp (toΓ T))) := by
  apply ext_of_isAffine
  rw [← appLE_top_top, ← appLE_top_top]
  ext x
  obtain ⟨a, rfl⟩ := (toΓ_bij T).2 x
  have key : ((spMap c ≫ hV.fromSpec) ≫ q).appLE ⊤ ⊤ le_top =
      q.appLE ⊤ V le_top ≫ (spMap c ≫ hV.fromSpec).appLE V ⊤ (chart_top hV c) :=
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [key, CommRingCat.comp_apply, chart_eval hV c V le_rfl, spMap_appLE_toΓ]
  simp

end GlobalTheory.GlobalSectionsBijection


open GlobalTheory.GlobalSectionsBijection in
theorem GlobalTheory.ratio_descends : ∀ (T : Type) [CommRing T] [IsReduced T] (Y : Scheme.{0}) (q : Y ⟶ Sp T) (I₀ : Type) (U : I₀ → Y.Opens) (t t₀ : ∀ j, Γ(Y, U j)), Smooth q → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T →+* Ω), ∃ α : Ω, (∀ (j : I₀) (w : Sp Ω ⟶ Y) (h : ⊤ ≤ w ⁻¹ᵁ U j), w ≫ q = spMap χ → (w.appLE (U j) ⊤ h).hom (t j) = toΓ Ω α * (w.appLE (U j) ⊤ h).hom (t₀ j)) ∧ ∃ (j : I₀) (w : Sp Ω ⟶ Y) (h : ⊤ ≤ w ⁻¹ᵁ U j), w ≫ q = spMap χ ∧ (w.appLE (U j) ⊤ h).hom (t₀ j) ≠ 0) → ∃ a : T, ∀ j, t j = (q.appLE ⊤ (U j) le_top).hom (toΓ T a) * t₀ j := by
  intro T _ _ Y q I₀ U t t₀ hq H
  haveI := hq
  haveI : IsReduced Y := GlobalTheory.isReduced_of_smooth_of_isReduced q
  let F : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℤ Ω], (T →ₐ[ℤ] Ω) → Ω :=
    fun Ω _ _ _ χ => Classical.choose (H Ω χ.toRingHom)
  have hF : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℤ Ω] (χ : T →ₐ[ℤ] Ω) (j : I₀) (w : Sp Ω ⟶ Y)
      (h : ⊤ ≤ w ⁻¹ᵁ U j), w ≫ q = spMap χ.toRingHom →
      (w.appLE (U j) ⊤ h).hom (t j) = toΓ Ω (F Ω χ) * (w.appLE (U j) ⊤ h).hom (t₀ j) :=
    fun Ω _ _ _ χ => (Classical.choose_spec (H Ω χ.toRingHom)).1
  refine (GlobalTheory.T.exists_function_of_smooth_local_descent_reduced ℤ T F ?_).elim ?_
  · intro p
    let κ := p.asIdeal.ResidueField
    let Ω := AlgebraicClosure κ
    let χ : T →+* Ω := (algebraMap κ Ω).comp (algebraMap T κ)
    obtain ⟨α, hα, j, w, h, hwq, hne⟩ := H Ω χ
    have hyD : w default ∈ Y.basicOpen (t₀ j) := mem_of_ne_zero w (U j) h (t₀ j) hne default
    obtain ⟨V, hV, hyV, hVD⟩ := exists_isAffineOpen_mem_and_subset hyD
    have hVU : V ≤ U j := hVD.trans (Y.basicOpen_le _)
    let φ : T →+* Γ(Y, V) := (q.appLE ⊤ V le_top).hom.comp (toΓ T)
    letI := φ.toAlgebra
    have hu : IsUnit ((Y.presheaf.map (homOfLE hVU).op).hom (t₀ j)) := by
      have h0 := Y.toRingedSpace.isUnit_res_basicOpen (t₀ j)
      have h1 := h0.map (Y.presheaf.map (homOfLE hVD).op).hom
      convert h1 using 1
      exact congrArg (fun f => (CommRingCat.Hom.hom f) (t₀ j))
        (Y.presheaf.map_comp (homOfLE (Y.basicOpen_le (t₀ j))).op (homOfLE hVD).op)
    let b' : Γ(Y, V) := (Y.presheaf.map (homOfLE hVU).op).hom (t j) * ↑hu.unit⁻¹
    refine ⟨Γ(Y, V), inferInstance, inferInstance, inferInstance, inferInstance, b', ?_, ?_, ?_⟩
    · show φ.Smooth
      exact (RingHom.Smooth.of_bijective (toΓ_bij T)).comp (q.smooth_appLE (isAffineOpen_top _) hV le_top)
    · have hwV : ⊤ ≤ w ⁻¹ᵁ V := fun x _ => by
        show w x ∈ V
        rw [Subsingleton.elim x default]; exact hyV
      let ψ : Γ(Y, V) →+* Ω := (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom.comp (w.appLE V ⊤ hwV).hom
      have hψφ : ψ.comp φ = χ := by
        ext a
        show (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ((w.appLE V ⊤ hwV).hom ((q.appLE ⊤ V le_top).hom (toΓ T a))) = χ a
        rw [compat q χ w V hwV hwq a, toΓ, ← CommRingCat.comp_apply, Iso.inv_hom_id]
        rfl
      refine ⟨⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩, PrimeSpectrum.ext ?_⟩
      show Ideal.comap φ (RingHom.ker ψ) = p.asIdeal
      rw [RingHom.comap_ker, hψφ]
      ext a
      simp only [RingHom.mem_ker, χ, RingHom.comp_apply, map_eq_zero_iff _ (algebraMap κ Ω).injective]
      rw [← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]
    · intro Ω' _ _ _ χ'
      let c : Γ(Y, V) →+* Ω' := χ'.toRingHom
      have hw'U : ⊤ ≤ (spMap c ≫ hV.fromSpec) ⁻¹ᵁ U j := fun x hx => hVU (chart_top hV c hx)
      have hcomp : (spMap c ≫ hV.fromSpec) ≫ q =
          spMap (χ'.comp (IsScalarTower.toAlgHom ℤ T Γ(Y, V))).toRingHom := chart_comp hV q c
      have e := hF Ω' _ j _ hw'U hcomp
      rw [chart_eval hV c (U j) hVU, chart_eval hV c (U j) hVU, ← map_mul] at e
      have e2 := (toΓ_bij Ω').1 e
      show c (_ * _) = _
      rw [map_mul, e2, _root_.mul_assoc, ← map_mul, hu.mul_val_inv, map_one, _root_.mul_one]
  · intro a ha
    refine ⟨a, fun j => ?_⟩
    rw [← sub_eq_zero]
    apply eq_zero_of_basicOpen_eq_bot
    rw [eq_bot_iff]
    intro y hy
    exfalso
    obtain ⟨Ω, _, _, w, hw⟩ := exists_geom Y y
    have hyU : y ∈ U j := Y.basicOpen_le _ hy
    have h : ⊤ ≤ w ⁻¹ᵁ U j := fun x _ => by
      show w x ∈ U j
      rw [hw]; exact hyU
    let χ : T →+* Ω := (Spec.preimage (w ≫ q)).hom
    have hχ : w ≫ q = spMap χ := (Spec.map_preimage (w ≫ q)).symm
    have e1 := hF Ω χ.toIntAlgHom j w h hχ
    have e2 := ha Ω χ.toIntAlgHom
    apply ne_zero_of_mem w (U j) h _ default (by rw [hw]; exact hy)
    rw [map_sub, map_mul, compat q χ w (U j) h hχ a, e1]
    rw [← e2]
    simp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatioLocalFunctionsGeometricFibreDescendsBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratio_localFunctions_geometricFibre_descends_base : ∀ (T : Type) [CommRing T] [IsReduced T] (Y : Scheme.{0}) (q : Y ⟶ Sp T) (I₀ : Type) (U : I₀ → Y.Opens) (t t₀ : ∀ j, Γ(Y, U j)), Smooth q → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T →+* Ω), ∃ α : Ω, (∀ (j : I₀) (w : Sp Ω ⟶ Y) (h : ⊤ ≤ w ⁻¹ᵁ U j), w ≫ q = spMap χ → (w.appLE (U j) ⊤ h).hom (t j) = toΓ Ω α * (w.appLE (U j) ⊤ h).hom (t₀ j)) ∧ ∃ (j : I₀) (w : Sp Ω ⟶ Y) (h : ⊤ ≤ w ⁻¹ᵁ U j), w ≫ q = spMap χ ∧ (w.appLE (U j) ⊤ h).hom (t₀ j) ≠ 0) → ∃ a : T, ∀ j, t j = (q.appLE ⊤ (U j) le_top).hom (toΓ T a) * t₀ j := by
  first | exact @GlobalTheory.ratio_descends | exact GlobalTheory.ratio_descends | (intros; apply GlobalTheory.ratio_descends <;> assumption)
end
end
