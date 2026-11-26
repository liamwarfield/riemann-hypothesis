module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.InverseWeylLiftEqPair
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.TrLatRange

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.DefUTest
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.TrBndDen
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem trBnd_den {K : Type} [Field K] (Q : Submodule (PowerSeries K) (FractionRing (PowerSeries K)))
    (hQ : Q.FG) : ∃ s : ℕ, ∀ z ∈ Q, ∃ a : PowerSeries K,
      algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) a =
        algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) PowerSeries.X ^ s * z := by
  obtain ⟨T, rfl⟩ := hQ
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors (PowerSeries K)) T
  have hb0 : (b : PowerSeries K) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  obtain ⟨s, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 PowerSeries.X_irreducible
  refine ⟨s, fun z hz => ?_⟩
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, ha⟩ := hb z hz
    refine ⟨(u⁻¹ : (PowerSeries K)ˣ) * a, ?_⟩
    rw [map_mul, ha, Algebra.smul_def, hu, ← mul_assoc, ← map_mul, ← mul_assoc, Units.inv_mul, one_mul, map_pow]
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨c, hc⟩ := hz
    exact ⟨a + c, by rw [map_add (f := _), ha, hc, mul_add]⟩
  | smul c z _ hz =>
    obtain ⟨a, ha⟩ := hz
    exact ⟨c * a, by rw [map_mul, ha, Algebra.smul_def]; ring⟩

theorem UpperTheory.V.Pa.trBnd :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ (R : Type) [CommRing R] [Algebra S.F R] (e : R →ₐ[S.F] S.F) (θ : S.U.AA →+* R), S.Test R e θ → ∀ (lam : R →ₗ[S.F] S.F) (i j : Fin S.n), BndF S.x.t fun g : S.G.G₀ => lam (θ (S.U.vr g i j)) := by
  intro l _ S R _ _ e θ hT lam i j
  letI : Algebra S.x.A R := ((algebraMap S.F R).comp (algebraMap S.x.A S.F)).toAlgebra
  haveI : IsScalarTower S.x.A S.F R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨M, -, -, -, hM, P, hP, hPm, hMP⟩ := trLat l S R e θ hT
  obtain ⟨s, hs⟩ := trBnd_den (P.map (lam.restrictScalars S.x.A)) (hP.map _)
  have hs' : ∀ z ∈ P, ∃ a : S.x.A, algebraMap S.x.A S.F a = algebraMap S.x.A S.F S.x.t ^ s * lam z :=
    fun z hz => hs _ (Submodule.mem_map_of_mem hz)
  choose φ hφ using fun g : S.G.G₀ => hs' _ (hPm _ (S.U.vr_mem g) i j)
  refine ⟨s, φ, fun N => ?_, hφ⟩
  obtain ⟨j', hj'⟩ := hM N
  obtain ⟨V, hV⟩ := S.U.cont j'
  have key : ∀ q ∈ maximalIdeal S.B ^ j' • S.U.P, ∃ z ∈ P, θ (q i j) = S.x.t ^ N • z := by
    intro q hq
    refine Submodule.smul_induction_on hq ?_ ?_
    · intro b hb p hp
      obtain ⟨y, hy, hby⟩ := hj' b hb
      refine ⟨y * θ (p i j), hMP y hy _ (hPm p hp i j), ?_⟩
      rw [Matrix.smul_apply, Algebra.smul_def, map_mul, hby, smul_mul_assoc]
    · rintro a b ⟨z, hz, ha⟩ ⟨w, hw, hb⟩
      exact ⟨z + w, P.add_mem hz hw, by rw [Matrix.add_apply, map_add (f := _), ha, hb, smul_add]⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨{y | g⁻¹ * y ∈ V}, V.toOpenSubgroup.isOpen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp only [Set.mem_setOf_eq, inv_mul_cancel]
    exact one_mem V
  · intro y hy
    obtain ⟨z, hz, hq⟩ := key _ (hV g _ hy)
    rw [mul_inv_cancel_left, Matrix.sub_apply, map_sub] at hq
    obtain ⟨a, ha⟩ := hs' z hz
    rw [Ideal.Quotient.eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    refine ⟨a, IsFractionRing.injective S.x.A S.F ?_⟩
    rw [map_sub, hφ, hφ, ← mul_sub, ← map_sub, hq, LinearMap.map_smul_of_tower, map_mul, ha, Algebra.smul_def]
    ring
end

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem UpperTheory.V.Pa.defUTest_smul {F : Type} [CommRing F] {e : ℕ} (c : F) (x : DD F e) :
    c • x = DD.C c * x := rfl

private def UpperTheory.V.Pa.defUTest_a (F : Type) [CommRing F] (e : ℕ) : DD F e →ₗ[F] F where
  toFun x := x.a
  map_add' _ _ := rfl
  map_smul' c x := by simp [defUTest_smul]

private def UpperTheory.V.Pa.defUTest_ep (F : Type) [CommRing F] {e : ℕ} (k : Fin e) : DD F e →ₗ[F] F where
  toFun x := x.ep k
  map_add' _ _ := rfl
  map_smul' c x := by simp [defUTest_smul]

private def UpperTheory.V.Pa.defUTest_ep' (F : Type) [CommRing F] {e : ℕ} (k : Fin e) : DD F e →ₗ[F] F where
  toFun x := x.ep' k
  map_add' _ _ := rfl
  map_smul' c x := by simp [defUTest_smul]

private def UpperTheory.V.Pa.defUTest_eta (F : Type) [CommRing F] (e : ℕ) : DD F e →ₗ[F] F where
  toFun x := x.eta
  map_add' _ _ := rfl
  map_smul' c x := by simp [defUTest_smul]

theorem UpperTheory.V.Pa.defUTest :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ (e : ℕ) (α : Fin e → S.Bh →+ S.F) (μ : Fin e → S.U.N →+ S.F) (Φ : S.U.N →+ S.F), (∀ k, α k ∈ S.Tp) → (∀ k, μ k ∈ S.La) → (∀ (b : S.Bh) y, Φ (b • y) = S.rF b * Φ y + ∑ k, α k b * μ k y) → ∃ (u : S.G.G₀ → Matrix (Fin S.n) (Fin S.n) (DD S.F e)) (ψ : ∀ v, Fin S.n → S.L.Gv v →* (DD S.F e)ˣ), DefU S.h S.x u ψ ∧ (∀ k, epC S.h S.x u k = S.laC (μ k)) ∧ ∀ k, epC' S.h S.x u k = S.alC (α k) := by
  intro l _ S e α μ Φ hα hμ hΦ
  obtain ⟨θ, hT, hθ⟩ := testEx l S e α μ Φ hα hμ hΦ
  obtain ⟨_, hE, _, hψ, hm⟩ := testVal l S (DD S.F e) (DD.aug S.F e) θ hT
  obtain ⟨hord, hine, _, _, _⟩ := vrRel l S
  have hp := prAdd l S
  have hB : ∀ b : S.B, S.pr1 (algebraMap S.B S.U.AA b) = 0 := by
    intro b
    have h1 := (hp.2.1 (algebraMap S.B S.Bh b) 0).2
    simpa [← IsScalarTower.algebraMap_apply] using h1
  let u : S.G.G₀ → Matrix (Fin S.n) (Fin S.n) (DD S.F e) := fun g => (S.U.vr g).map θ
  let ψ : ∀ v, Fin S.n → S.L.Gv v →* (DD S.F e)ˣ := fun v i =>
    (Units.map (θ.comp (algebraMap S.B S.U.AA)).toMonoidHom).comp (S.u.ψ v i)
  refine ⟨u, ψ, ?_, ?_, ?_⟩
  · refine
      { one := by simp [u]
        mul := by intro g g'; simp [u, Matrix.map_mul]
        red := ?_
        even := ?_
        form := ?_
        ine := ?_
        ψ_red := ?_
        ψ_even := ?_
        ψ_mu := ?_
        ord := ?_
        bnd := ?_ }
    · intro g
      ext i j
      simp only [u, Matrix.map_apply, hθ]
      exact (prVr l S g i j).1
    · intro g i j
      obtain ⟨_, h1, h2⟩ := prVr l S g i j
      constructor
      · intro hij
        simp only [u, Matrix.map_apply, hθ]
        refine ⟨?_, ?_, ?_, ?_⟩ <;>
          first
          | (intro h; exact absurd h (by decide))
          | (intro _; funext k; simp [h1 hij])
          | (intro _; simp [h1 hij])
      · intro hij
        simp only [u, Matrix.map_apply, hθ]
        refine ⟨?_, ?_, ?_, ?_⟩ <;>
          first
          | (intro h; exact absurd h (by decide))
          | (intro _; funext k; simp [h2 hij])
          | (intro _; simp [h2 hij])
    · intro g
      have h := congrArg θ.mapMatrix (S.U.form g)
      simp only [map_mul, RingHom.mapMatrix_apply, Matrix.transpose_map] at h
      rw [show ((S.U.vr g).map θ)ᵀ = ((S.U.vr g)ᵀ).map θ from (Matrix.transpose_map).symm]
      refine h.trans (Matrix.ext fun i j => ?_)
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.one_apply_eq, map_one, mul_one]
        exact (hE g _).trans rfl
      · simp only [Matrix.one_apply_ne hij, map_zero, mul_zero]
    · intro w g hg
      simp [u, hine w g hg]
    · intro v i g
      exact hψ v i g
    · intro v i g
      simp only [ψ, MonoidHom.comp_apply, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
        RingHom.coe_comp, Function.comp_apply, hθ, hB]
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        first
        | (intro h; exact absurd h (by decide))
        | (intro _; funext k; simp)
        | (intro _; simp)
    · intro v i g hg
      exact Units.ext (hm v i g hg)
    · intro v g
      have h := congrArg θ.mapMatrix (hord v g)
      rw [map_list_prod, map_zero, List.map_ofFn] at h
      refine Eq.trans ?_ h
      refine congrArg List.prod (congrArg List.ofFn (funext fun i => Matrix.ext fun a b => ?_))
      by_cases hab : a = b
      · subst hab
        simp [u, ψ, Matrix.algebraMap_matrix_apply, Matrix.sub_apply]
      · simp [u, ψ, Matrix.algebraMap_matrix_apply, Matrix.sub_apply, hab]
    · intro i j
      exact ⟨trBnd l S _ _ θ hT (defUTest_a S.F e) i j,
        fun k => trBnd l S _ _ θ hT (defUTest_ep S.F k) i j,
        fun k => trBnd l S _ _ θ hT (defUTest_ep' S.F k) i j,
        trBnd l S _ _ θ hT (defUTest_eta S.F e) i j⟩
  · intro k
    funext γ
    simp only [epC, Ctx.laC, u, Matrix.map_map]
    congr 1
    ext i j
    simp [hθ]
  · intro k
    funext γ
    simp only [epC', Ctx.alC, u, Matrix.map_map]
    congr 1
    ext i j
    simp [hθ]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.SelmerSpannedByKappaLaurentAlt
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.k3F :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), K3 h k → SelmerSpannedByKappaLaurent h k := by
  intro l _ L G G0 h n x k hK z hz hb
  obtain ⟨s₀, hs⟩ := selScale l L G G0 h n x false z hz hb
  obtain ⟨z', hz', hzz⟩ := hs s₀ le_rfl
  obtain ⟨s', c, Y, hY, hYt, hYe⟩ := hK z' hz'
  set f := algebraMap x.A x.Fr with hf
  have ht : f x.t ≠ 0 := by
    intro h0
    apply PowerSeries.X_ne_zero (R := x.K)
    exact IsFractionRing.injective x.A x.Fr (h0.trans (map_zero f).symm)
  have hsm : ∀ (a : x.A) (M : Matrix (Fin n) (Fin n) x.A), f.mapMatrix (a • M) = f a • M.map f := by
    intro a M
    ext i j
    simp
  have key : ∀ g, x.t ^ s' • z' g - ∑ j, c j • k.κ j (h.p₀ g) =
      x.ρX x.A (h.p₀ g) * Y * x.ρX x.A (h.p₀ g⁻¹) - Y := by
    intro g
    have e := congrFun hYe g
    simpa [dY, Finset.sum_apply] using e
  have key2 : ∀ g, f x.t ^ s' • (z' g).map f - ∑ j, f (c j) • kapF h k j g =
      x.ρX x.Fr (h.p₀ g) * Y.map f * x.ρX x.Fr (h.p₀ g⁻¹) - Y.map f := by
    intro g
    have e := congrArg f.mapMatrix (key g)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sub, map_mul, map_sum, hsm, kapF, NP.ρX, Matrix.map_map, RingHom.mapMatrix_apply] using e
  set u := (f x.t ^ (s' + s₀))⁻¹ with hu
  refine ⟨fun j => u * f (c j), u • Y.map f, ?_, ?_, ?_⟩
  · intro i j
    obtain ⟨h1, h2⟩ := hY i j
    refine ⟨fun hij => ?_, fun _ => Submodule.mem_top⟩
    have h3 := h1 hij
    rw [Submodule.mem_bot] at h3 ⊢
    simp [h3]
  · ext i j
    have h3 := congrFun (congrFun hYt i) j
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h3
    simp [Matrix.transpose_apply, h3]
  · funext g
    have e := key2 g
    rw [hzz g, smul_smul, ← pow_add] at e
    simp only [dY, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply]
    rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, ← e, smul_sub, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero _ ht), one_smul, Finset.smul_sum]
    simp [smul_smul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EvenCocyclesLiftLaurent
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.AlgebraMapMemSecondOrder
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

namespace UpperTheory.V.Pa.SelmerFractionFieldBaseChange

variable {l : ℕ} [Fact l.Prime] {Fm : GFrame l} {n : ℕ} {x : NP Fm n} (k : Kap x) (F : Type) [CommRing F] [Algebra x.A F]

end UpperTheory.V.Pa.SelmerFractionFieldBaseChange

private theorem selMap2_lemma {R S Γ : Type} [CommRing R] [CommRing S] [TopologicalSpace Γ] (I : Ideal R) (J : Ideal S)
    (π : R →+ S) (hπ : ∀ N u, u ∈ I ^ N → π u ∈ J ^ N) (f : Γ → R) (hf : AdicCont I f) :
    AdicCont J (fun g => π (f g)) := by
  intro N
  have hs := Ideal.Quotient.mk_surjective (I := I ^ N)
  have e : (fun g => Ideal.Quotient.mk (J ^ N) (π (f g))) =
      (fun q => Ideal.Quotient.mk (J ^ N) (π (Function.surjInv hs q))) ∘
        (fun g => Ideal.Quotient.mk (I ^ N) (f g)) := by
    funext g
    simp only [Function.comp]
    rw [Ideal.Quotient.eq, ← map_sub]
    apply hπ
    rw [← Ideal.Quotient.eq]
    exact (Function.surjInv_eq hs _).symm
  rw [e]
  exact (hf N).comp _

private theorem dd_components_mem_span_pow_of_mem_span_algebraMap_pow {A : Type} [CommRing A] (g : ℕ) (t : A) (N : ℕ) (u : DD A g)
    (hu : u ∈ Ideal.span {algebraMap A (DD A g) t} ^ N) :
    u.a ∈ Ideal.span {t} ^ N ∧ (∀ j, u.ep j ∈ Ideal.span {t} ^ N) ∧ (∀ j, u.ep' j ∈ Ideal.span {t} ^ N) ∧
      u.eta ∈ Ideal.span {t} ^ N := by
  rw [Ideal.span_singleton_pow, ← map_pow, Ideal.mem_span_singleton'] at hu
  obtain ⟨r, rfl⟩ := hu
  rw [Ideal.span_singleton_pow]
  have ha : (algebraMap A (DD A g) (t ^ N)).a = t ^ N := rfl
  have he : (algebraMap A (DD A g) (t ^ N)).ep = 0 := rfl
  have he' : (algebraMap A (DD A g) (t ^ N)).ep' = 0 := rfl
  have hη : (algebraMap A (DD A g) (t ^ N)).eta = 0 := rfl
  refine ⟨?_, fun j => ?_, fun j => ?_, ?_⟩
  · rw [DD.mul_a, ha]
    exact Ideal.mem_span_singleton'.mpr ⟨r.a, rfl⟩
  · rw [DD.mul_ep, ha, he]
    exact Ideal.mem_span_singleton'.mpr ⟨r.ep j, by simp⟩
  · rw [DD.mul_ep', ha, he']
    exact Ideal.mem_span_singleton'.mpr ⟨r.ep' j, by simp⟩
  · rw [DD.mul_eta, ha, he, he', hη]
    exact Ideal.mem_span_singleton'.mpr ⟨r.eta, by simp⟩

private theorem dd_map_algebraMap_algebraMap {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (g : ℕ) (c : A) :
    DD.map (algebraMap A B) (algebraMap A (DD A g) c) = algebraMap A (DD B g) c :=
  DD.ext rfl (funext fun _ => map_zero _) (funext fun _ => map_zero _) (map_zero _)

private theorem dd_map_mem_span_algebraMap_pow {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (g : ℕ) (t : A) (N : ℕ) (u : DD A g)
    (hu : u ∈ Ideal.span {algebraMap A (DD A g) t} ^ N) :
    DD.map (algebraMap A B) u ∈ Ideal.span {algebraMap A (DD B g) t} ^ N := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hu ⊢
  obtain ⟨r, rfl⟩ := hu
  exact ⟨DD.map (algebraMap A B) r, by rw [map_mul, map_pow, dd_map_algebraMap_algebraMap]⟩

private theorem ddMap_algebraMap_mem_ddPart {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (g : ℕ) (b1 b2 b3 b4 : Bool)
    (u : DD A g) (hu : u ∈ ddPart A A g b1 b2 b3 b4) : DD.map (algebraMap A B) u ∈ ddPart A B g b1 b2 b3 b4 := by
  obtain ⟨h1, h2, h3, h4⟩ := hu
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · show algebraMap A B u.a = 0
    rw [h1 h, map_zero]
  · show (fun j => algebraMap A B (u.ep j)) = 0
    rw [h2 h]
    funext j
    exact map_zero _
  · show (fun j => algebraMap A B (u.ep' j)) = 0
    rw [h3 h]
    funext j
    exact map_zero _
  · show algebraMap A B u.eta = 0
    rw [h4 h, map_zero]

private theorem map_ddMap_algebraMap_mem_W2 {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (n g a : ℕ)
    (Z : Matrix (Fin n) (Fin n) (DD A g)) (hZ : Z ∈ W2 n A A g a) :
    Z.map (DD.map (algebraMap A B)) ∈ W2 n A B g a := by
  intro i j
  exact ⟨fun hc => ddMap_algebraMap_mem_ddPart g _ _ _ _ _ ((hZ i j).1 hc), fun hc => ddMap_algebraMap_mem_ddPart g _ _ _ _ _ ((hZ i j).2 hc)⟩

private theorem map_algebraMap_map_ddMap_algebraMap {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (n g : ℕ)
    (M : Matrix (Fin n) (Fin n) A) :
    (M.map (algebraMap A (DD A g))).map (DD.map (algebraMap A B)) = M.map (algebraMap A (DD B g)) := by
  exact Matrix.ext fun i j => dd_map_algebraMap_algebraMap (A := A) (B := B) g (M i j)

private theorem epM_map_ddMap_algebraMap {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (n g : ℕ)
    (Z : Fin g → Matrix (Fin n) (Fin n) A) :
    (DD.epM Z).map (DD.map (algebraMap A B)) = DD.epM (fun j => (Z j).map (algebraMap A B)) := by
  refine Matrix.ext fun i j => DD.ext ?_ ?_ ?_ ?_
  · exact map_zero (algebraMap A B)
  · rfl
  · funext m
    exact map_zero (algebraMap A B)
  · exact map_zero (algebraMap A B)

private theorem kap_rho1_map_ddMap_algebraMap {l : ℕ} [Fact l.Prime] {Fm : GFrame l} {n : ℕ} {x : NP Fm n} (k : Kap x) (B : Type)
    [CommRing B] [Algebra x.A B] (g : Fm.G₀) :
    (k.ρ1 x.A g).map (DD.map (algebraMap x.A B)) = k.ρ1 B g := by
  have e : ∀ M : Matrix (Fin n) (Fin n) (DD x.A k.g),
      M.map (DD.map (algebraMap x.A B)) = (DD.map (algebraMap x.A B)).mapMatrix M := fun _ => rfl
  unfold Kap.ρ1 NP.ρX
  rw [e, map_mul, map_add (f := _), map_one, ← e, ← e, epM_map_ddMap_algebraMap, map_algebraMap_map_ddMap_algebraMap]
  rfl

private theorem w1_map_dd_map_algebraMap {l : ℕ} [Fact l.Prime] {Fm : GFrame l} {n : ℕ} {x : NP Fm n} (k : Kap x) (B : Type)
    [CommRing B] [Algebra x.A B] (v : Fm.Vl) :
    (k.w1 x.A v).map (DD.map (algebraMap x.A B)) = k.w1 B v := by
  have e : ∀ M : Matrix (Fin n) (Fin n) (DD x.A k.g),
      M.map (DD.map (algebraMap x.A B)) = (DD.map (algebraMap x.A B)).mapMatrix M := fun _ => rfl
  unfold Kap.w1 NP.wX
  rw [e, map_mul, map_sub, map_one, ← e, ← e, epM_map_ddMap_algebraMap, map_algebraMap_map_ddMap_algebraMap]
  rfl

private theorem wi1_map_dd_map_algebraMap {l : ℕ} [Fact l.Prime] {Fm : GFrame l} {n : ℕ} {x : NP Fm n} (k : Kap x) (B : Type)
    [CommRing B] [Algebra x.A B] (v : Fm.Vl) :
    (k.wi1 x.A v).map (DD.map (algebraMap x.A B)) = k.wi1 B v := by
  have e : ∀ M : Matrix (Fin n) (Fin n) (DD x.A k.g),
      M.map (DD.map (algebraMap x.A B)) = (DD.map (algebraMap x.A B)).mapMatrix M := fun _ => rfl
  unfold Kap.wi1 NP.wiX
  rw [e, map_mul, map_add (f := _), map_one, ← e, ← e, epM_map_ddMap_algebraMap, map_algebraMap_map_ddMap_algebraMap]
  rfl

private theorem selMap2_lemma_12 {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) {R S : Type} [CommRing R] [CommRing S]
    (Φ : R →+* S) (ρ z : F.G₀ → Matrix (Fin n) (Fin n) R) (w wi : F.Vl → Matrix (Fin n) (Fin n) R)
    (ρ' z' : F.G₀ → Matrix (Fin n) (Fin n) S) (w' wi' : F.Vl → Matrix (Fin n) (Fin n) S)
    (hρ : ∀ g, ρ' g = (ρ g).map Φ) (hz : ∀ g, z' g = (z g).map Φ) (hw : ∀ v, w' v = (w v).map Φ)
    (hwi : ∀ v, wi' v = (wi v).map Φ) (v : F.Vl) (Y : Matrix (Fin n) (Fin n) R)
    (hL : LocAt F ρ w wi z v Y) : LocAt F ρ' w' wi' z' v (Y.map Φ) := by
  have eM : ∀ M : Matrix (Fin n) (Fin n) R, M.map Φ = Φ.mapMatrix M := fun _ => rfl
  intro g
  obtain ⟨h1, h2⟩ := hL g
  have e : wi' v * (z' (F.φ v g) - dY F ρ' (Y.map Φ) (F.φ v g)) * w' v =
      (wi v * (z (F.φ v g) - dY F ρ Y (F.φ v g)) * w v).map Φ := by
    simp only [dY, hρ, hz, hw, hwi, eM, map_mul, map_sub]
  refine ⟨fun i j hij => ?_, fun hg i => ?_⟩
  · rw [e, Matrix.map_apply, h1 i j hij, map_zero]
  · rw [e, Matrix.map_apply, h2 hg i, map_zero]

open UpperTheory.V.Pa.SelmerFractionFieldBaseChange in
theorem UpperTheory.V.Pa.selMap2 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), ∀ z ∈ Sel2 h x.A k, (fun g => (z g).map (DD.map (algebraMap x.A x.Fr))) ∈ Sel2 h x.Fr k ∧ BndD x.t fun g => (z g).map (DD.map (algebraMap x.A x.Fr)) := by
  intro l _ L G G0 h n x k z hz
  obtain ⟨hV, hC, hco, hcj, hIu, hloc⟩ := hz
  have eM : ∀ M : Matrix (Fin n) (Fin n) (DD x.A k.g),
      M.map (DD.map (algebraMap x.A x.Fr)) = (DD.map (algebraMap x.A x.Fr)).mapMatrix M := fun _ => rfl
  refine ⟨⟨fun g => map_ddMap_algebraMap_mem_W2 n k.g x.a _ (hV g), fun i j => ?_, fun g1 g2 => ?_, fun g => ?_,
    fun u g hg => ?_, fun v => ?_⟩, fun i j => ⟨?_, fun m => ?_, fun m => ?_, ?_⟩⟩
  · exact selMap2_lemma _ _ (DD.map (algebraMap x.A x.Fr)).toAddMonoidHom
      (fun N u hu => dd_map_mem_span_algebraMap_pow k.g x.t N u hu) (fun g => z g i j) (hC i j)
  · beta_reduce
    beta_reduce at hco
    rw [hco g1 g2, ← kap_rho1_map_ddMap_algebraMap k x.Fr, ← kap_rho1_map_ddMap_algebraMap k x.Fr]
    simp only [eM, map_add (f := _), map_mul]
  · beta_reduce
    rw [hcj g]
    exact Matrix.ext fun i j => map_neg (DD.map (algebraMap x.A x.Fr)) (z g j i)
  · beta_reduce
    rw [hIu u g hg]
    exact Matrix.map_zero _ (map_zero _)
  · obtain ⟨Y, hY, hL⟩ := hloc v
    exact ⟨Y.map (DD.map (algebraMap x.A x.Fr)), map_ddMap_algebraMap_mem_W2 n k.g x.a _ hY,
      selMap2_lemma_12 G.frame (DD.map (algebraMap x.A x.Fr)) _ z _ _ _ _ _ _
        (fun g => (kap_rho1_map_ddMap_algebraMap k x.Fr _).symm) (fun g => rfl) (fun v => (w1_map_dd_map_algebraMap k x.Fr v).symm)
        (fun v => (wi1_map_dd_map_algebraMap k x.Fr v).symm) v Y hL⟩
  · refine ⟨0, fun g => (z g i j).a, ?_, fun g => by rw [pow_zero, one_mul]; rfl⟩
    exact selMap2_lemma _ _ { toFun := fun u : DD x.A k.g => u.a, map_zero' := rfl, map_add' := fun _ _ => rfl }
      (fun N u hu => (dd_components_mem_span_pow_of_mem_span_algebraMap_pow k.g x.t N u hu).1) (fun g => z g i j) (hC i j)
  · refine ⟨0, fun g => (z g i j).ep m, ?_, fun g => by rw [pow_zero, one_mul]; rfl⟩
    exact selMap2_lemma _ _ { toFun := fun u : DD x.A k.g => u.ep m, map_zero' := rfl, map_add' := fun _ _ => rfl }
      (fun N u hu => (dd_components_mem_span_pow_of_mem_span_algebraMap_pow k.g x.t N u hu).2.1 m) (fun g => z g i j) (hC i j)
  · refine ⟨0, fun g => (z g i j).ep' m, ?_, fun g => by rw [pow_zero, one_mul]; rfl⟩
    exact selMap2_lemma _ _ { toFun := fun u : DD x.A k.g => u.ep' m, map_zero' := rfl, map_add' := fun _ _ => rfl }
      (fun N u hu => (dd_components_mem_span_pow_of_mem_span_algebraMap_pow k.g x.t N u hu).2.2.1 m) (fun g => z g i j) (hC i j)
  · refine ⟨0, fun g => (z g i j).eta, ?_, fun g => by rw [pow_zero, one_mul]; rfl⟩
    exact selMap2_lemma _ _ { toFun := fun u : DD x.A k.g => u.eta, map_zero' := rfl, map_add' := fun _ _ => rfl }
      (fun N u hu => (dd_components_mem_span_pow_of_mem_span_algebraMap_pow k.g x.t N u hu).2.2.2) (fun g => z g i j) (hC i j)
end

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.k2F :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), K2 h k → EvenCocyclesLiftLaurent h k := by
  intro l _ L G G0 h n x k hK z hz
  set f := algebraMap x.A x.Fr with hf
  have ht : f x.t ≠ 0 := by
    intro h0
    apply PowerSeries.X_ne_zero (R := x.K)
    exact IsFractionRing.injective x.A x.Fr (h0.trans (map_zero f).symm)
  choose s₀ hs using fun i j => selScale l L G G0 h n x true (z i j) (hz i j).1 (hz i j).2
  set S := Finset.univ.sup (fun p : Fin (k.g + 1) × Fin k.g => s₀ p.1 p.2) with hSdef
  have hS : ∀ i j, s₀ i j ≤ S := fun i j =>
    Finset.le_sup (f := fun p : Fin (k.g + 1) × Fin k.g => s₀ p.1 p.2) (Finset.mem_univ (i, j))
  choose z' hz' hzz using fun i j => hs i j S (hS i j)
  obtain ⟨c, hc, Ψ, hΨ, hΨe⟩ := hK z' (fun i j => hz' i j)
  obtain ⟨hΨ1, hΨ2⟩ := selMap2 l L G G0 h n x k Ψ hΨ
  refine ⟨fun i => f (c i) * f x.t ^ S, ?_, _, hΨ1, hΨ2, ?_⟩
  · intro h0
    apply hc
    funext i
    have e := congrFun h0 i
    rcases mul_eq_zero.1 e with e | e
    · exact IsFractionRing.injective x.A x.Fr (e.trans (map_zero f).symm)
    · exact absurd e (pow_ne_zero S ht)
  · intro j γ a b
    have hz2 : ∀ i, f (z' i j γ a b) = f x.t ^ S * z i j γ a b := fun i => by
      have e := congrArg (fun M => M a b) (hzz i j γ)
      simpa using e
    show f ((Ψ γ a b).ep' j) = _
    rw [hΨe j γ a b]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.sum_apply, Finset.sum_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
      map_sum, map_mul, hz2]
    refine Finset.sum_congr rfl fun i _ => by ring
end
