module

public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaExponentIdentities
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLocalHomOfAlgebraic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesUniqueInvertible
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteAdeleFieldIdentificationEqBaseChangeRingEq
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegerExponentSectionEqZeroOfIncreasingFlag

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionDualNumberPointEqConstantCharZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionDualNumberPointEqConstantCharZero
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsConst

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem ext_of_two {B C : Type} [CommRing B] [CommRing C] [IsLocalRing B] [IsLocalRing C]
    (d e : B →+* C) [IsLocalHom d] [IsLocalHom e] (hde : ∀ x y, d x = d y → e x = e y → x = y)
    {X : Scheme.{0}} (a b : Sp B ⟶ X) (h1 : spMap d ≫ a = spMap d ≫ b) (h2 : spMap e ≫ a = spMap e ≫ b) :
    a = b := by
  obtain ⟨⟨x, f, hf⟩, rfl⟩ := (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm.surjective a
  obtain ⟨⟨y, g, hg⟩, rfl⟩ := (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm.surjective b
  have l1 : ∀ (k : B →+* C) [IsLocalHom k] (φ : X.presheaf.stalk x ⟶ CommRingCat.of B),
      IsLocalHom φ.hom → IsLocalHom (φ ≫ CommRingCat.ofHom k).hom := by
    intro k _ φ _
    rw [CommRingCat.hom_comp]; exact RingHom.isLocalHom_comp k φ.hom
  have l2 : ∀ (k : B →+* C) [IsLocalHom k] (φ : X.presheaf.stalk y ⟶ CommRingCat.of B),
      IsLocalHom φ.hom → IsLocalHom (φ ≫ CommRingCat.ofHom k).hom := by
    intro k _ φ _
    rw [CommRingCat.hom_comp]; exact RingHom.isLocalHom_comp k φ.hom
  have key : ∀ (k : B →+* C) [IsLocalHom k], spMap k ≫ (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm ⟨x, f, hf⟩ =
      spMap k ≫ (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm ⟨y, g, hg⟩ →
      (⟨x, f ≫ CommRingCat.ofHom k, l1 k f hf⟩ : Σ z : X, {φ : X.presheaf.stalk z ⟶ CommRingCat.of C // IsLocalHom φ.hom}) =
        ⟨y, g ≫ CommRingCat.ofHom k, l2 k g hg⟩ := by
    intro k _ h
    apply (SpecToEquivOfLocalRing X (CommRingCat.of C)).symm.injective
    simpa [SpecToEquivOfLocalRing] using h
  have k1 := key d h1
  have k2 := key e h2
  obtain rfl : x = y := congrArg Sigma.fst k1
  have h5 : f ≫ CommRingCat.ofHom d = g ≫ CommRingCat.ofHom d :=
    congrArg Subtype.val (eq_of_heq (Sigma.mk.inj k1).2)
  have h6 : f ≫ CommRingCat.ofHom e = g ≫ CommRingCat.ofHom e :=
    congrArg Subtype.val (eq_of_heq (Sigma.mk.inj k2).2)
  obtain rfl : f = g := by
    ext s
    exact hde _ _ (congrArg (fun k => k.hom s) h5) (congrArg (fun k => k.hom s) h6)
  rfl

variable {K : Type} [Field K]

theorem isLocalRing_tsze (M : Type) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M] :
    IsLocalRing (TrivSqZeroExt K M) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact IsLocalRing.isUnit_or_isUnit_one_sub_self _

attribute [local instance] isLocalRing_tsze

theorem isLocalHom_map {M N : Type} [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M]
    [AddCommGroup N] [Module K N] [Module Kᵐᵒᵖ N] [IsCentralScalar K N] (l : M →ₗ[K] N) :
    IsLocalHom (TrivSqZeroExt.map l).toRingHom :=
  ⟨fun a ha => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst] at ha ⊢
    simpa using ha⟩

abbrev ovO (B : Type) [CommRing B] [Algebra K B] : Over (Sp K) := Over.mk (spMap (algebraMap K B))

def ovH {B C : Type} [CommRing B] [Algebra K B] [CommRing C] [Algebra K C] (φ : B →ₐ[K] C) :
    ovO (K := K) C ⟶ ovO B :=
  Over.homMk (spMap φ.toRingHom) (by
    simp only [ovO, Over.mk_hom]
    rw [sp_comp]
    congr 2
    exact φ.comp_algebraMap)

theorem ovH_left {B C : Type} [CommRing B] [Algebra K B] [CommRing C] [Algebra K C] (φ : B →ₐ[K] C) :
    (ovH φ).left = spMap φ.toRingHom := rfl

theorem ovH_comp {B C E : Type} [CommRing B] [Algebra K B] [CommRing C] [Algebra K C] [CommRing E] [Algebra K E]
    (φ : B →ₐ[K] C) (ψ : C →ₐ[K] E) : ovH (ψ.comp φ) = ovH ψ ≫ ovH φ := by
  ext1
  simp only [Over.comp_left, ovH_left, sp_comp]
  rfl

theorem ovH_id {B : Type} [CommRing B] [Algebra K B] : ovH (AlgHom.id K B) = 𝟙 (ovO B) := by
  ext1
  simp only [ovH_left, Over.id_left]
  exact Spec.map_id _

abbrev sc (t : K) : DualNumber K →ₐ[K] DualNumber K := TrivSqZeroExt.map (t • LinearMap.id)

abbrev jj (s t : K) : DualNumber K →ₐ[K] TrivSqZeroExt K (K × K) :=
  TrivSqZeroExt.map (LinearMap.prod (s • LinearMap.id) (t • LinearMap.id))

abbrev r1 : TrivSqZeroExt K (K × K) →ₐ[K] DualNumber K := TrivSqZeroExt.map (LinearMap.fst K K K)
abbrev r2 : TrivSqZeroExt K (K × K) →ₐ[K] DualNumber K := TrivSqZeroExt.map (LinearMap.snd K K K)
abbrev dd : TrivSqZeroExt K (K × K) →ₐ[K] DualNumber K := TrivSqZeroExt.map (LinearMap.fst K K K + LinearMap.snd K K K)

theorem dualNumberFirstProj_comp_twoEpsLinearComb (s t : K) : (r1 (K := K)).comp (jj s t) = sc s := by
  apply AlgHom.ext; intro x; ext <;> simp
theorem dualNumberSecondProj_comp_twoEpsLinearComb (s t : K) : (r2 (K := K)).comp (jj s t) = sc t := by
  apply AlgHom.ext; intro x; ext <;> simp
theorem dd_jj (s t : K) : (dd (K := K)).comp (jj s t) = sc (s + t) := by
  apply AlgHom.ext; intro x; ext <;> simp [add_mul]
theorem sc_sc (a b : K) : (sc a).comp (sc b) = sc (a * b) := by
  apply AlgHom.ext; intro x; ext <;> simp <;> ring
theorem sc_one : sc (1 : K) = AlgHom.id K _ := by
  apply AlgHom.ext; intro x; ext <;> simp

section Pts
variable {A : Over (Sp K)} [GrpObj A]

theorem ext2 (a b : ovO (K := K) (TrivSqZeroExt K (K × K)) ⟶ A) (h1 : ovH r1 ≫ a = ovH r1 ≫ b)
    (h2 : ovH r2 ≫ a = ovH r2 ≫ b) : a = b := by
  haveI := isLocalHom_map (K := K) (LinearMap.fst K K K)
  haveI := isLocalHom_map (K := K) (LinearMap.snd K K K)
  ext1
  refine ext_of_two (r1 (K := K)).toRingHom (r2 (K := K)).toRingHom ?_ a.left b.left
    (by simpa only [Over.comp_left, ovH_left] using congrArg CommaMorphism.left h1)
    (by simpa only [Over.comp_left, ovH_left] using congrArg CommaMorphism.left h2)
  intro x y hx hy
  have a1 := congrArg TrivSqZeroExt.fst hx
  have a2 := congrArg TrivSqZeroExt.snd hx
  have a3 := congrArg TrivSqZeroExt.snd hy
  simp at a1 a2 a3
  ext
  · exact a1
  · exact a2
  · exact a3

theorem hadd (hc : ∀ x y : ovO (K := K) (DualNumber K) ⟶ A, x * y = y * x) (x : ovO (DualNumber K) ⟶ A) (s t : K) :
    ovH (sc (s + t)) ≫ x * ovH (sc 0) ≫ x = ovH (sc s) ≫ x * ovH (sc t) ≫ x := by
  have e : ovH (jj s t) ≫ x * ovH (jj 0 0) ≫ x = ovH (jj s 0) ≫ x * ovH (jj 0 t) ≫ x := by
    apply ext2
    · simp only [MonObj.comp_mul, ← Category.assoc, ← ovH_comp, dualNumberFirstProj_comp_twoEpsLinearComb]
    · simp only [MonObj.comp_mul, ← Category.assoc, ← ovH_comp, dualNumberSecondProj_comp_twoEpsLinearComb]
      exact hc _ _
  have e2 := congrArg (fun z => ovH dd ≫ z) e
  simp only [MonObj.comp_mul, ← Category.assoc, ← ovH_comp, dd_jj, add_zero, zero_add] at e2
  exact e2

end Pts

theorem eq_zeroScale_of_pow_eq_one_of_affine_fieldAction {G : Type} [CharZero K] [Group G] (hc : ∀ x y : G, x * y = y * x) (P : K → G → G)
    (hmul : ∀ t x y, P t (x * y) = P t x * P t y) (hcomp : ∀ a b x, P a (P b x) = P (a * b) x)
    (h1 : ∀ x, P 1 x = x) (hadd : ∀ s t x, P (s + t) x * P 0 x = P s x * P t x)
    (u : G) (n : ℕ) (hn : 0 < n) (hu : u ^ n = 1) : u = P 0 u := by
  letI : CommGroup G := { ‹Group G› with mul_comm := hc }
  have hone : ∀ t, P t 1 = 1 := fun t => mul_left_cancel (a := P t 1) (by rw [_root_.mul_one, ← hmul, _root_.one_mul])
  have hpow : ∀ t x (m : ℕ), P t (x ^ m) = P t x ^ m := by
    intro t x m
    induction m with
    | zero => simp [hone]
    | succ m ih => rw [pow_succ, hmul, ih, pow_succ]
  have step : ∀ m : ℕ, P m u * P 0 u ^ m = u ^ m * P 0 u := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h := hadd m 1 u
      rw [h1] at h
      rw [Nat.cast_succ, pow_succ', ← _root_.mul_assoc, h, mul_right_comm, ih, pow_succ]
      exact mul_right_comm _ _ _
  have e := step n
  rw [← hpow, hu, hone, _root_.mul_one, _root_.one_mul] at e
  calc u = P 1 u := (h1 u).symm
    _ = P ((n : K)⁻¹ * n) u := by rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn.ne')]
    _ = P (n : K)⁻¹ (P n u) := (hcomp _ _ _).symm
    _ = P (n : K)⁻¹ (P 0 u) := by rw [e]
    _ = P 0 u := by rw [hcomp, mul_zero]

end GlobalTheory.TorsConst

theorem GlobalTheory.TorsConst.torsion_eq_const : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] (f : Sp (DualNumber K) ⟶ Sp K), f = spMap (algebraMap K (DualNumber K)) → (∀ x y : Over.mk f ⟶ A, x * y = y * x) → ∀ (u : Over.mk f ⟶ A) (n : ℕ), 0 < n → u ^ n = 1 → u.left = spMap (algebraMap K (DualNumber K)) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ u.left := by
  intro K _ _ A _ f hf hc u n hn hu
  subst hf
  open GlobalTheory.TorsConst in
  have key : u = ovH (sc 0) ≫ u :=
    eq_zeroScale_of_pow_eq_one_of_affine_fieldAction hc (fun t x => ovH (sc t) ≫ x) (fun t x y => MonObj.comp_mul _ _ _)
      (fun a b x => by simp only [← Category.assoc, ← ovH_comp, sc_sc])
      (fun x => by simp only [sc_one, ovH_id, Category.id_comp]) (fun s t x => hadd hc x s t) u n hn hu
  have e : (algebraMap K (DualNumber K)).comp (TrivSqZeroExt.fstHom K K K).toRingHom = (GlobalTheory.TorsConst.sc (0 : K)).toRingHom := by
    ext x <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  conv_lhs => rw [key]
  rw [Over.comp_left, GlobalTheory.TorsConst.ovH_left, ← e, ← Category.assoc, GlobalTheory.TorsConst.sp_comp]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionDualNumberPointEqConstantCharZeroStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_dualNumber_point_eq_constant_charZero : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] (f : Sp (DualNumber K) ⟶ Sp K), f = spMap (algebraMap K (DualNumber K)) → (∀ x y : Over.mk f ⟶ A, x * y = y * x) → ∀ (u : Over.mk f ⟶ A) (n : ℕ), 0 < n → u ^ n = 1 → u.left = spMap (algebraMap K (DualNumber K)) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ u.left := by
  first | exact @GlobalTheory.TorsConst.torsion_eq_const | exact GlobalTheory.TorsConst.torsion_eq_const | (intros; apply GlobalTheory.TorsConst.torsion_eq_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumericalPointOfSize
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.RefSum

namespace GlobalTheory.RefSum.NumSizes

theorem r_log_div_le (r t q : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hq : 4 * t * r + 1 < q) :
    (r : ℝ) * Real.log q / ((q : ℝ) - 1) ≤ 2 * Real.log 6 + 4 * Real.log ((r : ℝ) + t) := by
  have hr' : (1:ℝ) ≤ r := by exact_mod_cast hr
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  set Q : ℝ := 4 * t * r + 2 with hQ
  have hqQ : Q ≤ q := by rw [hQ]; exact_mod_cast (by omega : 4 * t * r + 2 ≤ q)
  have hQ6 : (6:ℝ) ≤ Q := by rw [hQ]; nlinarith
  have he : Real.exp 1 ≤ Q := by have := Real.exp_one_lt_d9; linarith
  have hant : Real.log q / q ≤ Real.log Q / Q :=
    Real.log_div_self_antitoneOn (Set.mem_Ici.2 he) (Set.mem_Ici.2 (he.trans hqQ)) hqQ
  have hq0 : (0:ℝ) < q := by linarith
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
  have s1 : (r : ℝ) * Real.log q / ((q : ℝ) - 1) ≤ (r : ℝ) * Real.log q / ((q : ℝ) / 2) :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  have s2 : (r : ℝ) * Real.log q / ((q : ℝ) / 2) = 2 * r * (Real.log q / q) := by
    field_simp
  have s3 : 2 * (r : ℝ) * (Real.log Q / Q) ≤ 2 * Real.log Q := by
    have hrQ : (r : ℝ) ≤ Q := by rw [hQ]; nlinarith
    have hQ0 : (0:ℝ) < Q := by linarith
    rw [mul_div_assoc', div_le_iff₀ hQ0]
    nlinarith
  have s4 : Real.log Q ≤ Real.log 6 + 2 * Real.log ((r : ℝ) + t) := by
    have h6 : Q ≤ 6 * ((r : ℝ) + t) ^ 2 := by rw [hQ]; nlinarith
    calc Real.log Q ≤ Real.log (6 * ((r : ℝ) + t) ^ 2) := Real.log_le_log (by linarith) h6
      _ = Real.log 6 + 2 * Real.log ((r : ℝ) + t) := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  calc (r : ℝ) * Real.log q / ((q : ℝ) - 1) ≤ 2 * r * (Real.log q / q) := s1.trans s2.le
    _ ≤ 2 * r * (Real.log Q / Q) := mul_le_mul_of_nonneg_left hant (by positivity)
    _ ≤ 2 * Real.log Q := s3
    _ ≤ 2 * Real.log 6 + 4 * Real.log ((r : ℝ) + t) := by linarith

theorem sq_le_dim (f r m : ℕ) (hf : 2 ≤ f) (hr : 2 ≤ r) (hm : 2 ≤ m) : r ^ 2 ≤ m * (f * r.choose 2) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  have h : (s + 2).choose 2 * 2 = (s + 2) * (s + 1) := by
    have := Nat.add_one_mul_choose_eq (s + 1) 1
    rw [Nat.choose_one_right] at this
    exact this.symm
  have h4 : 2 * (2 * (s + 2).choose 2) ≤ m * (f * (s + 2).choose 2) :=
    Nat.mul_le_mul hm (Nat.mul_le_mul hf le_rfl)
  nlinarith

variable {D : D7} {L : SizeData₂ D}

theorem one_le_L (s : Scale) : 1 ≤ s.L := Real.one_le_rpow s.one_lt_alt.le s.eps_pos.le

theorem ranks_le {P : ParameterChoice' D L} (T : ParamsT D L P) :
    1 ≤ T.PP ∧ (D.R.f : ℝ) * D.R.r ≤ L.sc.b ∧ (D.R.r : ℝ) + D.R.t ≤ 2 * L.sc.b := by
  have hn : 0 < D.R.n := D.R.ord_pos
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ D.R.f)
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)
  have hL := one_le_L L.sc
  have hfr : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := one_le_mul_of_one_le_of_one_le hf hr
  have hZ : (D.R.f : ℝ) * D.R.r ≤ zBase L := le_mul_of_one_le_right (by positivity) hL
  have hZ1 : 1 ≤ zBase L := hfr.trans hZ
  have hZP : zBase L ≤ T.PP := by
    rw [T.PP_eq]
    have a : zBase L ≤ zBase L ^ T.eP := Real.self_le_rpow_of_one_le hZ1 (by linarith [T.eP_ge])
    exact a.trans (le_mul_of_one_le_left (by linarith) T.one_le_CP)
  have hPP : 1 ≤ T.PP := hZ1.trans hZP
  have hTO : (1 : ℝ) ≤ T.TO := by exact_mod_cast (by have := T.TO_40; omega : 1 ≤ T.TO)
  have hb : 1 ≤ L.sc.b := Real.one_le_exp (by linarith)
  have hs : (T.TO : ℝ) * T.PP ≤ L.sc.b := T.TO_PP'.trans (Real.rpow_le_self_of_one_le hb (by norm_num))
  have hP2 : T.PP ≤ (T.TO : ℝ) * T.PP := le_mul_of_one_le_left (by linarith) hTO
  refine ⟨hPP, by linarith, ?_⟩
  have e1 : (D.R.r : ℝ) + D.R.t = T.nP + T.TO * T.nWn := by exact_mod_cast T.split
  have e2 : (T.nP : ℝ) ≤ T.nWn := by exact_mod_cast T.nW_lo.2.2
  have e3 : (T.TO : ℝ) * T.nWn ≤ T.TO * T.PP := mul_le_mul_of_nonneg_left T.nW_le (by linarith)
  linarith [T.nW_le]

variable {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem unitE_eq : unitE p = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) := rfl

theorem dim_eq : GlobalTheory.CompHt.dimFlag (dat p i) = D.R.f * D.R.r.choose 2 := by
  exact GlobalTheory.SlopeRec.dimFlag_eq p.fw.laws.pins ⟨Nat.le_add_left 1 i, i.2⟩

theorem lenT_mul_le {P : ParameterChoice' D L} (T : ParamsT D L P) :
    (lenT p i T.PP : ℝ) * (D.R.r : ℝ) ^ 3 ≤ 2 * L.sc.b := by
  have hn : 0 < D.R.n := D.R.ord_pos
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  have hr2 : 2 ≤ D.R.r := by unfold Ranks.r; omega
  have hsq := sq_le_dim D.R.f D.R.r D.R.m (by unfold Ranks.f; omega) hr2 h1
  rw [← T.Dp_eq] at hsq
  have hD1 : 1 ≤ T.Dp := by
    rcases Nat.eq_zero_or_pos T.Dp with h | h
    · rw [h] at hsq; nlinarith
    · exact h
  have hsq' : (D.R.r : ℝ) ^ 2 ≤ D.R.m * T.Dp := by exact_mod_cast hsq
  have hD : (1 : ℝ) ≤ T.Dp := by exact_mod_cast hD1
  have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hPP := (ranks_le T).1
  have hW : (1 : ℝ) ≤ T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hPP) (one_le_pow₀ hD)) hk
  have hlen : (lenT p i T.PP : ℝ) ≤ 2 * (T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k) := by
    unfold lenT
    rw [dim_eq, ← T.Dp_eq]
    have a := (Nat.ceil_lt_add_one (a := T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k / D.R.m) (by positivity)).le
    have b : T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k / D.R.m ≤ T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k := div_le_self (by linarith) hm
    linarith
  have hr3 : (D.R.r : ℝ) ^ 3 ≤ D.R.r * (D.R.m * T.Dp) := by
    rw [pow_succ']; exact mul_le_mul_of_nonneg_left hsq' (by positivity)
  have hb : (D.R.r : ℝ) * D.R.m * D.R.k * T.PP ^ 2 * (T.Dp : ℝ) ^ 3 ≤ L.sc.b := by
    refine le_trans ?_ T.b_ge
    have : T.CbN * (D.R.r : ℝ) * D.R.m * D.R.k * T.PP ^ 2 * (T.Dp : ℝ) ^ 3 =
      T.CbN * ((D.R.r : ℝ) * D.R.m * D.R.k * T.PP ^ 2 * (T.Dp : ℝ) ^ 3) := by ring
    rw [this]
    exact le_mul_of_one_le_left (by positivity) T.CbN_ge
  calc (lenT p i T.PP : ℝ) * (D.R.r : ℝ) ^ 3
      ≤ 2 * (T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k) * (D.R.r * (D.R.m * T.Dp)) :=
        mul_le_mul hlen hr3 (by positivity) (by linarith)
    _ = 2 * ((D.R.r : ℝ) * D.R.m * D.R.k * T.PP ^ 2 * (T.Dp : ℝ) ^ 3) := by ring
    _ ≤ 2 * L.sc.b := by linarith

theorem numAt {P : ParameterChoice' D L} (T : ParamsT D L P) (hll : 1 ≤ Real.log (Real.log L.sc.x)) :
    NumAt p i T.PP (|L.Ct| + 20) := by
  have hn : 0 < D.R.n := D.R.ord_pos
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  have h3 := D.R.rank_add_five_le
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; omega
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ D.R.f)
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr1
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hL := one_le_L L.sc
  have hb : 1 ≤ L.sc.b := Real.one_le_exp (by linarith)
  have hlb : Real.log L.sc.b = L.sc.L := Real.log_exp _
  have hC := abs_nonneg L.Ct
  obtain ⟨-, hfr, hrt⟩ := ranks_le T
  have hCL : 20 * L.sc.L ≤ (|L.Ct| + 20) * L.sc.L := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hlr : Real.log D.R.r ≤ L.sc.L :=
    hlb ▸ Real.log_le_log (by linarith) ((le_mul_of_one_le_left (by linarith) hf).trans hfr)
  have hlf : Real.log D.R.f ≤ L.sc.L :=
    hlb ▸ Real.log_le_log (by linarith) ((le_mul_of_one_le_right (by linarith) hr).trans hfr)
  refine ⟨hL, hb, by linarith, hll, ?_, ?_, by linarith, ?_, ?_, ?_⟩
  · rw [unitE_eq]
    refine le_mul_of_one_le_left ?_ (by linarith)
    have : 0 ≤ L.sc.L := by linarith
    have : 0 ≤ Real.log (Real.log L.sc.x) := by linarith
    positivity
  · have hx := L.sc.one_lt_alt
    have hlx : 0 < Real.log L.sc.x := Real.log_pos hx
    have hk : (2 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 2 ≤ D.R.k)
    have hkt : (D.R.k : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.k ≤ D.R.t)
    have a : Real.log D.R.k ≤ L.Ct * Real.log L.sc.x := by
      rw [← Real.log_rpow (by linarith)]
      exact Real.log_le_log (by linarith) (hkt.trans L.t_win.2)
    have b : Real.log D.R.k ≤ (|L.Ct| + 1) * Real.log L.sc.x :=
      a.trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self L.Ct]) hlx.le)
    have c := Real.log_le_log (Real.log_pos (by linarith)) b
    rw [Real.log_mul (by linarith) hlx.ne'] at c
    have d := Real.log_le_sub_one_of_pos (by linarith : 0 < |L.Ct| + 1)
    nlinarith
  · have hQ : (D.host.QS : ℝ) ≤ (D.R.f : ℝ) ^ 2 := by
      have := D.host.QS_le
      exact_mod_cast this.trans (Nat.pow_le_pow_left (by unfold Ranks.f; omega) 2)
    have hQ0 : (0 : ℝ) < D.host.QS := by exact_mod_cast D.host.QS_pos
    have a := Real.log_le_log hQ0 hQ
    rw [Real.log_pow] at a
    push_cast at a
    have h2' := Real.log_two_gt_d9
    unfold Formalism.MainNotions.DIV.Cons.vd2
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  · exact (lenT_mul_le p i T).trans (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
  · intro q hq
    have hq' : 4 * D.R.t * D.R.r + 1 < q := by
      rcases Finset.mem_insert.1 hq with h | h
      · exact h ▸ D.host.qd_big.1
      · exact (Finset.mem_singleton.1 h) ▸ D.host.qd_big.2
    have a := r_log_div_le D.R.r D.R.t q hr1 (by omega) hq'
    have b : Real.log ((D.R.r : ℝ) + D.R.t) ≤ Real.log 2 + L.sc.L := by
      rw [← hlb, ← Real.log_mul (by norm_num) (by linarith)]
      exact Real.log_le_log (by positivity) hrt
    have c := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)
    have d := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have e : (|L.Ct| + 20) * L.sc.L ≤ (|L.Ct| + 20) * D.R.m * L.sc.L :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by linarith) hm) (by linarith)
    linarith

end GlobalTheory.RefSum.NumSizes

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartRationalTensorZeroAtPrimeIffPlaceIdem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartRationalTensorZeroAtPrimeIffPlaceIdem
open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ZeroAtPlaces

section Generic

variable {K : Type} [Field K] [NumberField K]

theorem ev_mul (a b : FiniteAdeleRing (𝓞 K) K) (Q : HeightOneSpectrum (𝓞 K)) : (a * b) Q = a Q * b Q := rfl

theorem val_nat (Q : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Valued.v ((n : FiniteAdeleRing (𝓞 K) K) Q) = Q.valuation K ((n : 𝓞 K) : K) := by
  rw [← Formalism.UG.P.levelaf_valued_algebraMap, ← map_natCast (algebraMap K (FiniteAdeleRing (𝓞 K) K)) n]
  rfl

theorem val_nat_eq_one (Q : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : (n : 𝓞 K) ∉ Q.asIdeal) :
    Valued.v ((n : FiniteAdeleRing (𝓞 K) K) Q) = 1 := by
  rw [val_nat]
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K), not_lt] at hn
  exact le_antisymm (Q.valuation_le_one (K := K) _) hn

theorem val_nat_lt_one (Q : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : (n : 𝓞 K) ∈ Q.asIdeal) :
    Valued.v ((n : FiniteAdeleRing (𝓞 K) K) Q) < 1 := by
  rw [val_nat]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) Q _).2 hn

theorem divisible_iff {q : ℕ} (hq : q.Prime) (y : FiniteAdeleRing (𝓞 K) K)
    (hy : ∃ n : ℕ, 0 < n ∧ ∀ Q, ((n : FiniteAdeleRing (𝓞 K) K) * y) Q ∈ Q.adicCompletionIntegers K) :
    (∀ k : ℕ, ∃ m : ℕ, 0 < m ∧ Nat.Coprime m q ∧ ∃ s : FiniteAdeleRing (𝓞 K) K,
      (∀ Q, s Q ∈ Q.adicCompletionIntegers K) ∧
        (m : FiniteAdeleRing (𝓞 K) K) * y = (q : FiniteAdeleRing (𝓞 K) K) ^ k * s) ↔
    ∀ Q : HeightOneSpectrum (𝓞 K), (q : 𝓞 K) ∈ Q.asIdeal → y Q = 0 := by
  constructor
  · intro h Q hQ
    by_contra h0
    have h1 : Valued.v (y Q) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    obtain ⟨k, hk⟩ := exists_pow_lt₀ (val_nat_lt_one Q hQ) (Units.mk0 _ h1)
    obtain ⟨m, -, hm, s, hs, e⟩ := h k
    have hm' : (m : 𝓞 K) ∉ Q.asIdeal := by
      intro hmem
      obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hm).map (Int.castRingHom (𝓞 K))
      simp only [eq_intCast, Int.cast_natCast] at hab
      refine Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
      rw [← hab]
      exact add_mem (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ hQ)
    have e1 : (m : FiniteAdeleRing (𝓞 K) K) Q * y Q = ((q : FiniteAdeleRing (𝓞 K) K) Q) ^ k * s Q :=
      congrArg (fun z : FiniteAdeleRing (𝓞 K) K => z Q) e
    have e2 := congrArg Valued.v e1
    rw [map_mul, map_mul, map_pow, val_nat_eq_one Q hm', one_mul] at e2
    have hs1 : Valued.v (s Q) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hs Q)
    rw [Units.val_mk0, e2] at hk
    exact absurd hk (not_lt.2 (mul_le_of_le_one_right' hs1))
  · intro h k
    obtain ⟨n, hn, hint⟩ := hy
    obtain ⟨j, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' q hq.ne_one
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero _))
    have hq0 : (q : K) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
    have hu : (q : FiniteAdeleRing (𝓞 K) K) ^ k * algebraMap K _ ((q : K) ^ k)⁻¹ = 1 := by
      rw [← map_natCast (algebraMap K (FiniteAdeleRing (𝓞 K) K)) q, ← map_pow, ← map_mul,
        mul_inv_cancel₀ (pow_ne_zero k hq0), map_one]
    refine ⟨m, hm0, ((Nat.Prime.coprime_iff_not_dvd hq).2 hm).symm,
      algebraMap K _ ((q : K) ^ k)⁻¹ * ((m : FiniteAdeleRing (𝓞 K) K) * y), fun Q => ?_,
      by rw [← mul_assoc, hu, one_mul]⟩
    by_cases hQ : (q : 𝓞 K) ∈ Q.asIdeal
    · rw [ev_mul, ev_mul, h Q hQ, mul_zero, mul_zero]
      exact zero_mem _
    · have h1 := val_nat_eq_one Q hQ
      have h2 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hint Q)
      have e1 : ((q : FiniteAdeleRing (𝓞 K) K) Q) ^ k *
          (algebraMap K (FiniteAdeleRing (𝓞 K) K) ((q : K) ^ k)⁻¹) Q = 1 :=
        congrArg (fun z : FiniteAdeleRing (𝓞 K) K => z Q) hu
      have e2 := congrArg Valued.v e1
      rw [map_mul, map_pow, h1, one_pow, one_mul, map_one] at e2
      have e3 : (((q ^ j * m : ℕ) : FiniteAdeleRing (𝓞 K) K) * y) Q =
          ((q : FiniteAdeleRing (𝓞 K) K) Q) ^ j * ((m : FiniteAdeleRing (𝓞 K) K) * y) Q := by
        rw [Nat.cast_mul, Nat.cast_pow, mul_assoc]
        rfl
      rw [e3, map_mul, map_pow, h1, one_pow, one_mul] at h2
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, ev_mul, map_mul, e2, one_mul]
      exact h2

end Generic

open GlobalTheory.BotFormula GlobalTheory.BotClassDict

theorem mem_OhE_iff {D : D7} (y : Formalism.MainNotions.StandardLatticesGL3.AE D) :
    y ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D ↔ ∀ Q, toFinE D y Q ∈ Q.adicCompletionIntegers D.host.E :=
  ⟨fun hy => GlobalTheory.AdeleBaseChange.map_mem_int (ι := (toFinE D).toRingHom) toFinE_tmul hy,
    fun hy => GlobalTheory.AdeleBaseChange.mem_int_of_map (ι := (toFinE D).toRingHom) toFinE_tmul hy⟩

theorem zeroAt_iff_comp {D : D7} {q : ℕ} (hq : q.Prime) (y : Formalism.MainNotions.StandardLatticesGL3.AE D) :
    Formalism.MainNotions.StandardLatticesGL3.ZeroAt D q y ↔
      ∀ Q : HeightOneSpectrum (𝓞 D.host.E), (q : 𝓞 D.host.E) ∈ Q.asIdeal → toFinE D y Q = 0 := by
  obtain ⟨n, hn, hint⟩ := (GlobalTheory.AdelicApprox.approx_mod_ideal D ⊤ top_ne_bot).2.1 y
  rw [mem_OhE_iff, map_mul, map_natCast] at hint
  rw [← divisible_iff hq (toFinE D y) ⟨n, hn, hint⟩]
  refine forall_congr' fun k => exists_congr fun m => and_congr_right' (and_congr_right' ⟨?_, ?_⟩)
  · rintro ⟨s, hs, e⟩
    refine ⟨toFinE D s, (mem_OhE_iff s).1 hs, ?_⟩
    have := congrArg (toFinE D) e
    rwa [map_mul, map_mul, map_pow, map_natCast, map_natCast] at this
  · rintro ⟨s, hs, e⟩
    obtain ⟨s, rfl⟩ := (toFinE D).surjective s
    refine ⟨s, (mem_OhE_iff s).2 hs, (toFinE D).injective ?_⟩
    rw [map_mul, map_mul, map_pow, map_natCast, map_natCast]
    exact e

theorem toFinE_finQ {D : D7} (a : AE D) :
    toFinE D (finQ D a) = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D a) := by
  rw [← finAdEquiv_toAfE, toAfE_finQ]
  rfl

theorem comp_base {D : D7} (η : AF D.host.F) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    toFinE D (finQ D (algebraMap (AF D.host.F) (AE D) η)) Q =
      GlobalTheory.AdeleBaseChange.locMap D.host.F Q (η.2 (Q.under (𝓞 D.host.F))) := by
  have h : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (algebraMap (AF D.host.F) (AE D) η)) =
      GlobalTheory.AdeleBaseChange.adMap D.host.F D.host.E η.2 * algebraMap D.host.E _ 1 := GlobalTheory.LFun.toFinAd_tmul η.2 1
  rw [toFinE_finQ, h, map_one, mul_one]
  rfl

theorem idem_mul_eq_zero_iff {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {η : AF D.host.F} (h : IsPlaceIdem D v η)
    (a : AE D) : algebraMap (AF D.host.F) (AE D) η * a = 0 ↔
      ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q.under (𝓞 D.host.F) = v → toFinE D (finQ D a) Q = 0 := by
  have hev : ∀ Q, toFinE D (finQ D (algebraMap (AF D.host.F) (AE D) η * a)) Q =
      GlobalTheory.AdeleBaseChange.locMap D.host.F Q (η.2 (Q.under (𝓞 D.host.F))) * toFinE D (finQ D a) Q := by
    intro Q
    rw [RingHom.map_mul, map_mul, ev_mul, comp_base]
  obtain ⟨α, rfl, h1, h0⟩ := h
  have hinf : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := TensorProduct.zero_tmul _ _
  have k1 : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q.under (𝓞 D.host.F) = v →
      GlobalTheory.AdeleBaseChange.locMap D.host.F Q ((pairA D.host.F 0 α).2 (Q.under (𝓞 D.host.F))) = 1 := by
    intro Q hQ
    subst hQ
    exact (congrArg _ h1).trans (map_one _)
  have k0 : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q.under (𝓞 D.host.F) ≠ v →
      GlobalTheory.AdeleBaseChange.locMap D.host.F Q ((pairA D.host.F 0 α).2 (Q.under (𝓞 D.host.F))) = 0 :=
    fun Q hQ => (congrArg _ (h0 _ hQ)).trans (map_zero _)
  constructor
  · intro e Q hQ
    have := hev Q
    rw [e, k1 Q hQ, one_mul, RingHom.map_zero, map_zero] at this
    exact this.symm
  · intro e
    refine GlobalTheory.SplitScalar.adele_ext (by rw [RingHom.map_mul, hinf, zero_mul, RingHom.map_zero]) ?_
    apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
    rw [← toFinE_finQ, RingHom.map_zero, map_zero]
    refine FiniteAdeleRing.ext _ fun Q => (hev Q).trans ?_
    by_cases hQ : Q.under (𝓞 D.host.F) = v
    · rw [e Q hQ, mul_zero]
      rfl
    · rw [k0 Q hQ, zero_mul]
      rfl

theorem zeroAt_finQ_iff : ∀ (D : D7) (q : ℕ), q.Prime → ∀ a : AE D, (Formalism.MainNotions.StandardLatticesGL3.ZeroAt D q (finQ D a) ↔
  ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (η : AF D.host.F), IsPlaceIdem D v η → (q : 𝓞 D.host.F) ∈ v.asIdeal →
    algebraMap (AF D.host.F) (AE D) η * a = 0) := by
  intro D q hq a
  have hmem : ∀ Q : HeightOneSpectrum (𝓞 D.host.E),
      (q : 𝓞 D.host.F) ∈ (Q.under (𝓞 D.host.F)).asIdeal ↔ (q : 𝓞 D.host.E) ∈ Q.asIdeal := by
    intro Q
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ Q.asIdeal ↔ _
    rw [map_natCast]
  rw [zeroAt_iff_comp hq]
  constructor
  · intro h v η hη hv
    refine (idem_mul_eq_zero_iff hη a).2 fun Q hQ => h Q ((hmem Q).1 ?_)
    rw [hQ]
    exact hv
  · intro h Q hQ
    obtain ⟨η, hη⟩ := GlobalTheory.IdemSupport.exists_placeIdem (D := D) (Q.under (𝓞 D.host.F))
    exact (idem_mul_eq_zero_iff hη a).1 (h _ η hη ((hmem Q).2 hQ)) Q rfl

end GlobalTheory.ZeroAtPlaces
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartRationalTensorZeroAtPrimeIffPlaceIdemStatement
open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePartRationalTensor_zeroAtPrime_iff_placeIdem : ∀ (D : D7) (q : ℕ), q.Prime → ∀ a : AE D, (Formalism.MainNotions.StandardLatticesGL3.ZeroAt D q (finQ D a) ↔
  ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (η : AF D.host.F), IsPlaceIdem D v η → (q : 𝓞 D.host.F) ∈ v.asIdeal →
    algebraMap (AF D.host.F) (AE D) η * a = 0) := by
  first | exact @GlobalTheory.ZeroAtPlaces.zeroAt_finQ_iff | exact GlobalTheory.ZeroAtPlaces.zeroAt_finQ_iff | (intros; apply GlobalTheory.ZeroAtPlaces.zeroAt_finQ_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnReadingIntegerExponentSection
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOnRdUFlat
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TrueCx.FlatConst

section Hol

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD _root_.Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT
open GlobalTheory.Reg GlobalTheory.KeyFourth GlobalTheory.AllWt GlobalTheory.FlatLine

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_generic_units (hpq : 1 ≤ Dw.p + Dw.q) (h : GenFrEx Xo c) :
    ∃ v : ∀ Z : Comp Xo c, (Om Z)ˣ, ∀ C : FChart h,
      ∃ u : (C.R)ˣ, ((u : C.R) : Om C.Z) = ((kch C.t ^ 4 * v C.Z : (Om C.Z)ˣ) : Om C.Z) := by
  obtain ⟨κ, h₁, h₂, -, -, -, h₃, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (Dw.mult τ))).symm
  have hc : ∀ Z : Comp Xo c, CharZero (Om Z) := fun Z =>
    charZero_of_injective_algebraMap (algebraMap c.F (Om Z)).injective
  choose Ψ hΨ using fun Z : Comp Xo c => exists_tied E H Dw l Xo c _ e (Om Z) (genFr h Z) hpq
  refine ⟨fun Z => κ (Om Z) (Ψ Z).key, fun C => ?_⟩
  letI : Algebra c.F C.R := Subalgebra.algebra C.R
  haveI := C.sm
  haveI : IsIntegrallyClosed C.R := isIntegrallyClosed_of_smooth c.F C.R
  haveI : IsNoetherianRing C.R := Algebra.FiniteType.isNoetherianRing c.F C.R
  haveI : CharZero C.R := charZero_of_injective_algebraMap (algebraMap c.F C.R).injective
  obtain ⟨Φ, hΦ⟩ := exists_tied E H Dw l Xo c _ e C.R C.y hpq
  obtain ⟨Φ', hΦ'⟩ := exists_tied E H Dw l Xo c _ e (Om C.Z) C.yg hpq
  obtain ⟨u, hu⟩ := h₃ C.R Φ.key
  refine ⟨u, ?_⟩
  rw [← rule_frBor κ h₁ h₂ E H Dw l Xo c _ e (Om C.Z) C.t _ _ (Ψ C.Z) Φ' C.bor (hΨ _) hΦ']
  exact (hu (Om C.Z) _ _ (tied_keyPB E H Dw l Xo c _ e _ _ C.R.val C.y C.yg Φ Φ' C.gen hΦ hΦ')).symm

theorem exists_key_four (hpq : 1 ≤ Dw.p + Dw.q) (σ : c.F →+* ℂ) :
    ∃ ρ ∈ secZ Xo c (fun i => keyEx Dw i * 4), ∀ y : FrPt Xo c (CAt σ), toC (evR Xo c ρ y) ≠ 0 := by
  obtain ⟨-, -, h, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨v, hv⟩ := exists_generic_units hpq h
  have hk : ∀ C : FChart h, (∏ i, C.t i ^ (keyEx Dw i * 4) : (Om C.Z)ˣ) = kch C.t ^ 4 := fun C => by
    rw [kch, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => by rw [zpow_mul]; rfl
  obtain ⟨ρ, hρ, hρv⟩ := GlobalTheory.SecGlueInt.exists_secZ_of_regular E H Dw l Xo c h (fun i => keyEx Dw i * 4)
    (fun Z => v Z) fun C => by
      obtain ⟨u, hu⟩ := hv C
      rw [hk, ← Units.val_mul, ← hu]
      exact u.1.2
  refine ⟨ρ, hρ, fun y => ?_⟩
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  obtain ⟨C, ψ, z, t, hz, hb⟩ := hA h (CAt σ) y
  obtain ⟨u, hu⟩ := hv C
  obtain ⟨b, hb₁, hb₂⟩ := GlobalTheory.DegCmp.fChart_exists_val C hρ
  have hbu : b = u := Subtype.ext (by
    rw [hb₁, hu, hk, GlobalTheory.CompHt.genVal_apply h, hρv, Units.val_mul])
  show evR Xo c ρ y ≠ 0
  rw [GlobalTheory.FlagTan.evR_frBor hρ hb, hb₂ _ ψ z hz, hbu]
  exact mul_ne_zero (Units.ne_zero _) (u.isUnit.map ψ).ne_zero

theorem exists_sec_four (hpq : 1 ≤ Dw.p + Dw.q) {σ : c.F →+* ℂ} (y : FrPt Xo c (CAt σ)) :
    ∃ n, Even n ∧ ∃ g ∈ sec Xo c (fun _ => 4) n, toC (evR Xo c g y) ≠ 0 := by
  obtain ⟨ρ, hρ, h0⟩ := exists_key_four (Xo := Xo) hpq σ
  obtain ⟨n, hn, ⟨m, rfl⟩, η, hη, hη0⟩ := exists_even_sec_evR_ne_zero E H Dw l Xo c σ y
  rw [← secZ_nat] at hη
  have h2 := mul_mem_secZ hη hη
  have h3 := mul_mem_secZ (mul_mem_secZ h2 h2) hρ
  refine ⟨2 * (4 * m - 4), even_two_mul _, η * η * (η * η) * ρ, ?_, ?_⟩
  · rw [← secZ_nat]
    convert h3 using 2
    funext i
    cases i with
    | none => simp only [ex, keyEx, Pi.add_apply]; omega
    | some i => simp [ex, keyEx]
  · have h1 : toC (evR Xo c η y) ≠ 0 := hη0
    simp only [CompSplitPfB.cspB_evR_mul]
    exact mul_ne_zero (M₀ := ℂ) (mul_ne_zero (M₀ := ℂ) (mul_ne_zero (M₀ := ℂ) h1 h1) (mul_ne_zero (M₀ := ℂ) h1 h1)) (h0 y)


variable {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r}

end Hol

section Main

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open Formalism.DegreeFormula Formalism.MJ Formalism.UG _root_.Formalism.L2.Geo _root_.Formalism.L2.PjFree
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory GlobalTheory.HodgeDomain GlobalTheory.LieMet GlobalTheory.CxPts GlobalTheory.TrueCx
open GlobalTheory.AllWt (Psi)
attribute [local instance] Over.cartesianMonoidalCategory

end Main

end GlobalTheory.TrueCx.FlatConst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnReadingIntegerExponentSection
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ReadCont

open NumberField IsDedekindDomain Module Formalism.BasicNotions _root_.Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem pow_succ_mem_secZ {e : Ix Dw → ℤ} {g : Rul Xo c} (hg : g ∈ secZ Xo c e) (m : ℕ) :
    g ^ (m + 1) ∈ secZ Xo c ((m + 1) • e) := by
  induction m with
  | zero => simpa using hg
  | succ m ih =>
    rw [pow_succ, succ_nsmul]
    exact mul_mem_secZ ih hg

theorem differentiableOn_rdU_of_antitone {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} (hU : IsUnf U)
    (hpq : 1 ≤ Dw.p + Dw.q) {e : Ix Dw → ℤ} (he0 : e none = 0)
    (hanti : ∀ τ (i j : Fin (Dw.mult τ)), i ≤ j → e (some ⟨τ, j⟩) ≤ e (some ⟨τ, i⟩))
    {f : Rul Xo c} (hf : f ∈ secZ Xo c e) (k : U.Comp) : DifferentiableOn ℂ (rdU U f k) (U.X k).dom := by
  intro x hx
  have ho : IsOpen (U.X k).dom := FourierCoefficientDomain.isOpen_dom _
  obtain ⟨n, hn, g, hg, hg0⟩ := GlobalTheory.TrueCx.FlatConst.exists_sec_four hpq (U.un k ⟨x, hx⟩)
  set M : ℕ := ∑ i : Ix Dw, (e i).natAbs with hMdef
  have hM : ∀ i, -(4 * ((M + 1 : ℕ) : ℤ)) ≤ e i := fun i => by
    have h1 : (e i).natAbs ≤ M := Finset.single_le_sum (f := fun i => (e i).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
    have h2 : -((e i).natAbs : ℤ) ≤ e i := by
      have := Int.natAbs_abs (e i); rw [← Int.abs_eq_natAbs]; exact neg_abs_le _
    have h3 : ((e i).natAbs : ℤ) ≤ M := by exact_mod_cast h1
    push_cast; linarith
  let a : (E →+* ℂ) × ℕ → ℕ := fun p =>
    if h : p.2 < Dw.mult p.1 then (4 * ((M + 1 : ℕ) : ℤ) + e (some ⟨p.1, ⟨p.2, h⟩⟩)).toNat else 0
  have hdom : Dom a ((M + 1) * n) := by
    refine ⟨fun τ i j hij => ?_, hn.mul_left _⟩
    show a (τ, j) ≤ a (τ, i)
    simp only [a]
    by_cases hj : j < Dw.mult τ
    · have hi : i < Dw.mult τ := lt_of_le_of_lt hij hj
      rw [dif_pos hj, dif_pos hi]
      exact Int.toNat_le_toNat (by linarith [hanti τ ⟨i, hi⟩ ⟨j, hj⟩ hij])
    · rw [dite_eq_right hj]; exact Nat.zero_le _
  have hgp := pow_succ_mem_secZ (Xo := Xo) (c := c) (by rw [secZ_nat]; exact hg) M
  have hgf : g ^ (M + 1) * f ∈ sec Xo c a ((M + 1) * n) := by
    rw [← secZ_nat]
    convert mul_mem_secZ hgp hf using 2
    funext i
    rcases i with _ | ⟨τ, i⟩
    · simp [ex, he0]
    · have hi := i.2
      rw [Pi.add_apply, Pi.smul_apply]
      simp only [ex, a, dif_pos hi, nsmul_eq_mul]
      rw [Int.toNat_of_nonneg (by linarith [hM (some ⟨τ, i⟩)])]
      push_cast
      ring
  have d1 := (hU.2.2.2.2.1 _ n ⟨fun _ _ _ _ => le_rfl, hn⟩ g hg k).1
  have d2 := (hU.2.2.2.2.1 _ _ hdom _ hgf k).1
  have hx0 : rdU U g k x ≠ 0 := by
    have : rdU U g k x = toC (evR Xo c g (U.un k ⟨x, hx⟩)) := dif_pos hx
    rwa [this]
  have a1 := d1.differentiableAt (ho.mem_nhds hx)
  have a2 := d2.differentiableAt (ho.mem_nhds hx)
  refine ((a2.mul ((a1.pow (M + 1)).inv (pow_ne_zero _ hx0))).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [a1.continuousAt.eventually_ne hx0] with y hy0
  have e1 : rdU U (g ^ (M + 1) * f) k y = rdU U g k y ^ (M + 1) * rdU U f k y := by
    rw [Formalism.L2.Pj.rdU_mul]
    have : ∀ m : ℕ, rdU U (g ^ (m + 1)) = rdU U g ^ (m + 1) := fun m => by
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ g (m + 1), Formalism.L2.Pj.rdU_mul, ih, ← pow_succ]
    rw [this]; rfl
  rw [Pi.mul_apply, Pi.inv_apply, e1, Pi.pow_apply, mul_right_comm, mul_inv_cancel₀ (pow_ne_zero _ hy0), one_mul]

end GlobalTheory.ReadCont

namespace GlobalTheory.ReadCont

open NumberField IsDedekindDomain Module Formalism.BasicNotions _root_.Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem continuousOn_rdU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (e : Ix Dw → ℤ), e none = 0 → ∀ s ∈ secZ Xo c e, ∀ σ, GoodEmb c σ → ∀ k, ContinuousOn (rdU (U σ) s k) ((U σ).X k).dom := by
  intro E _ _ _ H Dw l Xo c r U x hL e he0 s hs σ hσ k
  by_cases hanti : ∀ τ (i j : Fin (Dw.mult τ)), i ≤ j → e (some ⟨τ, j⟩) ≤ e (some ⟨τ, i⟩)
  · exact (differentiableOn_rdU_of_antitone (hL.unf σ hσ) hL.pos he0 hanti hs k).continuousOn
  · push_neg at hanti
    obtain ⟨τ, i, j, hij, hlt⟩ := hanti
    have hij' : i < j := lt_of_le_of_ne hij (by rintro rfl; exact lt_irrefl _ hlt)
    rw [GlobalTheory.T.integerExponentSection_eq_zero_of_increasing_flag E H Dw l Xo c e τ i j hij' hlt s hs, map_zero]
    exact continuousOn_const

end GlobalTheory.ReadCont
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnReadingIntegerExponentSectionStatement
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousOn_reading_integerExponent_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (e : Ix Dw → ℤ), e none = 0 → ∀ s ∈ secZ Xo c e, ∀ σ, GoodEmb c σ → ∀ k, ContinuousOn (rdU (U σ) s k) ((U σ).X k).dom := by
  first | exact @GlobalTheory.ReadCont.continuousOn_rdU | exact GlobalTheory.ReadCont.continuousOn_rdU | (intros; apply GlobalTheory.ReadCont.continuousOn_rdU <;> assumption)
end
end
