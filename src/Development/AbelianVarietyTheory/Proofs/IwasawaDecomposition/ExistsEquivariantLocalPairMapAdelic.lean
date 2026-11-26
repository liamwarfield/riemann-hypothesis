module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductMeasureBasicProperties

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalUnitaryPairToPairComponentMemLocalLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalUnitaryPairToPairComponentMemLocalLevel
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.LevelHecke.PairToLevel

theorem span_fun {A R M n : Type} [CommRing A] [CommRing R] [Algebra R A] [AddCommGroup M] [Module R M] [Fintype n]
    (Λ : Submodule R (n → A)) (f : Λ →ₗ[R] M) (B1 B2 : Matrix n n A) (S : Set (n → A))
    (h : ∀ w ∈ S, ∃ h1 h2, f ⟨B1 *ᵥ w, h1⟩ = f ⟨B2 *ᵥ w, h2⟩) :
    ∀ w ∈ Submodule.span R S, ∃ h1 h2, f ⟨B1 *ᵥ w, h1⟩ = f ⟨B2 *ᵥ w, h2⟩ := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem y hy => exact h y hy
  | zero =>
    simp only [Matrix.mulVec_zero]
    exact ⟨zero_mem _, zero_mem _, trivial⟩
  | add a b _ _ ha hb =>
    obtain ⟨a1, a2, ha⟩ := ha
    obtain ⟨b1, b2, hb⟩ := hb
    simp only [Matrix.mulVec_add]
    refine ⟨add_mem a1 b1, add_mem a2 b2, ?_⟩
    have := congrArg₂ (· + ·) ha hb
    simp only [← map_add (f := _)] at this
    exact this
  | smul a b _ hb =>
    obtain ⟨b1, b2, hb⟩ := hb
    simp only [Matrix.mulVec_smul]
    refine ⟨Λ.smul_mem a b1, Λ.smul_mem a b2, ?_⟩
    have := congrArg (a • ·) hb
    simp only [← map_smul] at this
    exact this

theorem unit_fun {A R M n : Type} [CommRing A] [CommRing R] [Algebra R A] [AddCommGroup M] [Module R M] [Fintype n]
    (Λ : Submodule R (n → A)) (f : Λ →ₗ[R] M) (B1 B2 : Matrix n n A) (w w' : n → A) (s : R) (e : w = s • w')
    (h : ∃ h1 h2, f ⟨B1 *ᵥ w', h1⟩ = f ⟨B2 *ᵥ w', h2⟩) :
    ∃ h1 h2, f ⟨B1 *ᵥ w, h1⟩ = f ⟨B2 *ᵥ w, h2⟩ :=
  span_fun Λ f B1 B2 {w'} (by rintro _ rfl; exact h) w (e ▸ Submodule.smul_mem _ s (Submodule.subset_span rfl))

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem stabFun_gen {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) {L1 L2 : Submodule (𝓞 E) (Fin n → E)}
    {M : Type} [AddCommGroup M] [Module (intV E v) M]
    (Λ : Submodule (intV E v) (Fin n → E ⊗[F] v.adicCompletion F)) (f : Λ →ₗ[intV E v] M)
    (y1 y2 : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hy1 : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L1 ↔ (y1⁻¹).1 *ᵥ x ∈ Λ)
    (hy2 : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L2 ↔ (y2⁻¹).1 *ᵥ x ∈ Λ)
    (g : GL (Fin n) E)
    (hle : latS (F := F) (v.adicCompletion F) (intV E v) (mulLat g.1 L2) ≤
      latS (F := F) (v.adicCompletion F) (intV E v) L1)
    (hge : latS (F := F) (v.adicCompletion F) (intV E v) L1 ≤
      latS (F := F) (v.adicCompletion F) (intV E v) (mulLat g.1 L2))
    (hf : ∀ z ∈ L2, ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ ∃ h1 h2,
      f ⟨(y1⁻¹).1 *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) ((g.1 *ᵥ (algebraMap (𝓞 F) (𝓞 E) r • z)) a)), h1⟩ =
      f ⟨(y2⁻¹).1 *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) ((algebraMap (𝓞 F) (𝓞 E) r • z) a)), h2⟩) :
    y1⁻¹ * bc (inclE (F := F) (v.adicCompletion F)) g * y2 ∈ stabFun Λ f := by
  have hG : ∀ x, (y1⁻¹ * bc (inclE (F := F) (v.adicCompletion F)) g * y2).1 *ᵥ x =
      (y1⁻¹).1 *ᵥ ((g.1.map (inclE (F := F) (v.adicCompletion F))) *ᵥ (y2.1 *ᵥ x)) := by
    intro x
    rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec]
    rfl
  have hc : ∀ w, (y2⁻¹).1 *ᵥ (y2.1 *ᵥ w) = w := by
    intro w
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have hY2 : ∀ w, w ∈ Λ ↔ y2.1 *ᵥ w ∈ latS (F := F) (v.adicCompletion F) (intV E v) L2 := by
    intro w
    rw [hy2, hc]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [hG]
    constructor
    · intro hx
      exact (hy1 _).1 (hle (rlv_latS_mulLat v _ L2 _ ((hY2 x).1 hx)))
    · intro hx
      have h1 := (hy1 _).2 hx
      have h2 := rlv_latS_mulLat v (g⁻¹).1 _ _ (hge h1)
      rw [rlv_mulLat_inv, rlv_map_inv_mul] at h2
      exact (hY2 x).2 h2
  · have hx2 : y2.1 *ᵥ x.1 ∈ Submodule.span (intV E v)
        ((fun x i => inclE (F := F) (v.adicCompletion F) (x i)) '' (L2 : Set (Fin n → E))) := by
      have := (hY2 x.1).1 x.2
      unfold latS at this
      exact this
    have key := span_fun Λ f ((y1⁻¹).1 * g.1.map (inclE (F := F) (v.adicCompletion F))) (y2⁻¹).1
      ((fun (x : Fin n → E) (i : Fin n) => inclE (F := F) (v.adicCompletion F) (x i)) '' (L2 : Set (Fin n → E))) ?_ (y2.1 *ᵥ x.1) hx2
    · obtain ⟨h1, h2, key⟩ := key
      convert key using 2
      · apply Subtype.ext
        show (y1⁻¹ * bc (inclE (F := F) (v.adicCompletion F)) g * y2).1 *ᵥ x.1 = _
        rw [hG, mulVec_mulVec]
      · exact Subtype.ext (hc _).symm
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨r, hr, h1, h2, hf⟩ := hf z hz
      obtain ⟨s, hs, hsr⟩ := rlv_unit (E := E) v r hr
      refine unit_fun Λ f _ _ _
        (fun a => inclE (F := F) (v.adicCompletion F) ((algebraMap (𝓞 F) (𝓞 E) r • z) a)) ⟨s, hs⟩ ?_ ?_
      · funext i
        show inclE (F := F) (v.adicCompletion F) (z i) = s * inclE (F := F) (v.adicCompletion F) (((algebraMap (𝓞 F) (𝓞 E) r) • z) i)
        rw [Pi.smul_apply, rlv_incl_smul]
        calc inclE (F := F) (v.adicCompletion F) (z i) = inclE (F := F) (v.adicCompletion F) (z i) * 1 := (mul_one _).symm
          _ = _ := by rw [← hsr]; ring
      · have e : ((y1⁻¹).1 * g.1.map (inclE (F := F) (v.adicCompletion F))) *ᵥ
            (fun a => inclE (F := F) (v.adicCompletion F) ((algebraMap (𝓞 F) (𝓞 E) r • z) a)) =
            (y1⁻¹).1 *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) ((g.1 *ᵥ (algebraMap (𝓞 F) (𝓞 E) r • z)) a)) := by
          rw [← mulVec_mulVec]
          congr 1
          funext i
          exact (RingHom.map_mulVec _ _ _ _).symm
        refine ⟨e ▸ h1, h2, ?_⟩
        rw [← hf]
        congr 1
        exact Subtype.ext e

theorem loc_map {R V k : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k] (res : R →+* k)
    (g : V ≃ₗ[R] V) (M : Submodule R V) (x : V) :
    x ∈ loc res (M.map (g : V →ₗ[R] V)) ↔ g.symm x ∈ loc res M := by
  simp only [mem_loc, Submodule.mem_map_equiv, map_smul]

theorem mem_mulLat {E : Type} [Field E] {n : ℕ} (g : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (z : Fin n → E) (hz : z ∈ L) : g *ᵥ z ∈ mulLat g L := ⟨z, hz, rfl⟩

theorem exists_mul {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (P Q : Ideal (𝓞 E)) [P.IsPrime] [Q.IsPrime]
    (hN : ∀ a : 𝓞 E, a ∉ P → a ∉ Q → ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ ∃ b : 𝓞 E, algebraMap (𝓞 F) (𝓞 E) r = b * a)
    (g : Matrix (Fin n) (Fin n) E) (L M : Submodule (𝓞 E) (Fin n → E))
    (hP : Formalism.HermitianLatticesTheory.localization₂ P (mulLat g L) ≤ Formalism.HermitianLatticesTheory.localization₂ P M)
    (hQ : Formalism.HermitianLatticesTheory.localization₂ Q (mulLat g L) ≤ Formalism.HermitianLatticesTheory.localization₂ Q M) (z : Fin n → E) (hz : z ∈ L) :
    ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ g *ᵥ (algebraMap (𝓞 F) (𝓞 E) r • z) ∈ M := by
  obtain ⟨a, haP, haQ, hax⟩ := rlv_two P Q hP hQ (mem_mulLat g L z hz)
  obtain ⟨r, hr, b, hb⟩ := hN a haP haQ
  refine ⟨r, hr, ?_⟩
  rw [Matrix.mulVec_smul, hb, mul_smul]
  exact Submodule.smul_mem _ b hax

set_option synthInstance.maxHeartbeats 400000 in
theorem comp_eq {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (y y' : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E) :
    bc (prV (E := E) v) (y⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y') =
      (bc (prV (E := E) v) y)⁻¹ * bc (inclE (F := F) (v.adicCompletion F)) γ * bc (prV (E := E) v) y' := by
  rw [map_mul, map_mul, map_inv]
  rfl

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem stabFun_loc {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) {L1 L2 : Submodule (𝓞 E) (Fin n → E)}
    {M : Type} [AddCommGroup M] [Module (intV E v) M]
    (Λ : Submodule (intV E v) (Fin n → E ⊗[F] v.adicCompletion F)) (f : Λ →ₗ[intV E v] M)
    (y1 y2 : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hy1 : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L1 ↔ (y1⁻¹).1 *ᵥ x ∈ Λ)
    (hy2 : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L2 ↔ (y2⁻¹).1 *ᵥ x ∈ Λ)
    (g : GL (Fin n) E) (P Q : Ideal (𝓞 E)) [P.IsPrime] [Q.IsPrime]
    (hN : ∀ a : 𝓞 E, a ∉ P → a ∉ Q → ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ ∃ b : 𝓞 E, algebraMap (𝓞 F) (𝓞 E) r = b * a)
    (hP : Formalism.HermitianLatticesTheory.localization₂ P (mulLat g.1 L2) = Formalism.HermitianLatticesTheory.localization₂ P L1)
    (hQ : Formalism.HermitianLatticesTheory.localization₂ Q (mulLat g.1 L2) = Formalism.HermitianLatticesTheory.localization₂ Q L1)
    (hf : ∀ w ∈ L2, g.1 *ᵥ w ∈ L1 → ∀ h1 h2,
      f ⟨(y1⁻¹).1 *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) ((g.1 *ᵥ w) a)), h1⟩ =
      f ⟨(y2⁻¹).1 *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) (w a)), h2⟩) :
    y1⁻¹ * bc (inclE (F := F) (v.adicCompletion F)) g * y2 ∈ stabFun Λ f := by
  refine stabFun_gen v Λ f y1 y2 hy1 hy2 g (rlv_locV v P Q hN hP.le hQ.le) (rlv_locV v P Q hN hP.ge hQ.ge) ?_
  intro z hz
  obtain ⟨r, hr, m1⟩ := exists_mul v P Q hN g.1 L2 L1 hP.le hQ.le z hz
  have m2 : algebraMap (𝓞 F) (𝓞 E) r • z ∈ L2 := Submodule.smul_mem _ _ hz
  have n1 := (hy1 _).1 (Submodule.subset_span ⟨_, m1, rfl⟩)
  have n2 := (hy2 _).1 (Submodule.subset_span ⟨_, m2, rfl⟩)
  exact ⟨r, hr, n1, n2, hf _ m2 m1 n1 n2⟩


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem main : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v), FvTie P K fMe → cT (sigD D : D.host.E →+* D.host.E) (gramN D i hi) = gramN D i hi → ∀ (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (γ : GL (Fin (D.R.N i)) D.host.E), γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → (pc P v c').act (glE γ) = pc P v c → mov K (A.eV v).1 c γ c' ∈ K.lev.Uloc (A.eV v).1 := by
  intro D u A i hi P K fMe hT hJ v c c' γ hγ hpc
  have : (A.Pv v).IsPrime := RingHom.ker_isPrime _
  have hσσ : ∀ x, (sigD D : D.host.E →+* D.host.E) ((sigD D : D.host.E →+* D.host.E) x) = x := fun x => by
    show sigD D (sigD D x) = x
    rw [forms_involution_eq_host_conj, forms_involution_eq_host_conj, host_conj_involutive]
  have hL : ∀ x, (glE γ).symm x ∈ (pc P v c').L ↔ x ∈ (pc P v c).L := fun x => by
    rw [← hpc, Pr.mem_act]
  have hF : ∀ x, (pc P v c').f ((glE γ).symm x) = (pc P v c).f x := fun x => by
    rw [← hpc]; rfl
  have hfv : ∀ w (m2 : w ∈ Ld D u i hi c') (m1 : γ.1 *ᵥ w ∈ Ld D u i hi c),
      (D.fm u).fv i v c (P.pr v c ⟨_, m1⟩) = (D.fm u).fv i v c' (P.pr v c' ⟨_, m2⟩) := by
    intro w m2 m1
    rw [← locExt_coe (A.res v) _ (P.pr v c) (P.pr_smul v c), ← locExt_coe (A.res v) _ (P.pr v c') (P.pr_smul v c')]
    have h3 := hF (glE γ w)
    rw [LinearEquiv.symm_apply_apply] at h3
    exact h3.symm
  have hdP : Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat γ.1 (Ld D u i hi c')) = Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Ld D u i hi c) := by
    ext x
    exact (loc_map (A.res v) (glE γ) (Ld D u i hi c') x).trans (hL x)
  have hP : Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat γ.1 (clsCrd D u i hi c')) = Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (clsCrd D u i hi c) := by
    ext x
    refine (loc_map (A.res v) (glE γ) (clsCrd D u i hi c') x).trans ?_
    show _ ↔ x ∈ loc (A.res v) (clsCrd D u i hi c)
    rw [← GlobalTheory.LevelHecke.loc_lk_eq_loc_cls D u A i hi K v c, ← GlobalTheory.LevelHecke.loc_lk_eq_loc_cls D u A i hi K v c', pc_isKer P K v c, pc_isKer P K v c', hL, hF]
  have hPQ : ∀ a b : 𝓞 D.host.E, (b : D.host.E) = (sigD D : D.host.E →+* D.host.E) (a : D.host.E) →
      (a ∈ rlvQ A v ↔ b ∈ A.Pv v) := by
    intro a b hb
    have : b = RingOfIntegers.mapRingHom (sigD D : D.host.E →+* D.host.E) a := RingOfIntegers.ext hb
    rw [this]; rfl
  have hlat := bwB_clsCrd_lat D u i hi
  have hlatFull : ∀ c, Submodule.IsFullLattice D.host.E (clsCrd D u i hi c) := by
    intro c
    letI := D.host.cmStar
    let φ := (D.sp.X i).frame.equivFun.trans
      (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm)
    letI : Submodule.IsLattice D.host.E (clsCrd D u i hi c) := hlat c
    let hbase : Submodule.IsFullLattice D.host.E (D.clsLat u i c) := D.clsLat_lat u i c
    constructor
    change Submodule.span D.host.E (((D.clsLat u i c).map
      (φ.toLinearMap.restrictScalars (𝓞 D.host.E)) : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Set (Fin (D.R.N i) → D.host.E)) = ⊤
    rw [show Submodule.span D.host.E (((D.clsLat u i c).map
        (φ.toLinearMap.restrictScalars (𝓞 D.host.E)) : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Set (Fin (D.R.N i) → D.host.E)) =
        (Submodule.span D.host.E (D.clsLat u i c : Set _)).map φ.toLinearMap by
          rw [Submodule.map_span]; rfl,
      hbase.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact φ.surjective
  obtain ⟨hγL, hγd⟩ := (GlobalTheory.LevelHecke.DualConj.dual_conj_primes _ _ _ _ (A.Pv v) (rlvQ A v) hσσ (bwB_gramN_det D i hi) hJ hPQ _ _
    (hlatFull c') (hlatFull c)).2.2 γ hγ
  obtain ⟨k1, k2, -⟩ := GlobalTheory.LevelHecke.DualConj.dual_conj_primes _ _ _ _ (A.Pv v) (rlvQ A v) hσσ (bwB_gramN_det D i hi) hJ hPQ _ _ hγL (hlatFull c)
  have hdQ := k1 hP
  rw [hγd] at hdQ k2
  have hQ := k2 hdP
  have hN := rlv_norm A v
  have hU : (K.y c).1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * (K.y c').1 ∈
      UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    mul_mem (mul_mem (inv_mem (K.y c).2) (Formalism.UG.P.rational_points_le_holds _ _ _ _ _ _ ⟨γ, hγ, rfl⟩)) (K.y c').2
  have hLb : Submodule.IsFullLattice D.host.E K.lev.Lb :=
    { toIsLattice := Submodule.IsLattice.of_fg D.host.E ((Submodule.fg_top _).1 K.lev.Lb_fin.fg_top)
      span_eq_top := K.lev.Lb_span }
  have hy : ∀ c, ∀ x, x ∈ latS (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (intV D.host.E (A.eV v).1) (Ld D u i hi c) ↔
      ((bc (prV (E := D.host.E) (A.eV v).1) (K.y c).1)⁻¹).1 *ᵥ x ∈ dualV K (A.eV v).1 := fun c =>
    GlobalTheory.DualCompletion.dual_move _ _ (sigD D) _ (gramN D i hi) (A.eV v).1 _ K.lev.Lb _ (bwB_gramN_det D i hi) (hlatFull c) hLb
      (Formalism.UG.P.afsplit_bc_mem _ _ _ _ (K.y c).2) (fun x => by
        rw [← map_inv]; exact rlv_yloc (A.eV v).1 (K.y c).1 (K.y_lat c) x)
  rw [K.lev.UlocAlt _ (A.eV v).2]
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Formalism.UG.P.afsplit_bc_mem _ _ _ _ hU, ?_⟩, ?_⟩
  · exact rlv_stab (A.eV v).1 (K.y c).1 (K.y c').1 (K.y_lat c) (K.y_lat c') γ
      (rlv_locV (A.eV v).1 (A.Pv v) (rlvQ A v) hN hP.le hQ.le)
      (rlv_locV (A.eV v).1 (A.Pv v) (rlvQ A v) hN hP.ge hQ.ge)
  · have e : mov K (A.eV v).1 c γ c' = (bc (prV (E := D.host.E) (A.eV v).1) (K.y c).1)⁻¹ *
        bc (inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F)) γ * bc (prV (E := D.host.E) (A.eV v).1) (K.y c').1 :=
      comp_eq _ _ _ _
    rw [e]
    refine stabFun_loc (A.eV v).1 _ _ _ _ (hy c) (hy c') γ (A.Pv v) (rlvQ A v) hN hdP hdQ ?_
    intro w m2 m1 n1 n2
    exact (fMe v).injective ((hT v c ⟨_, m1⟩ n1).symm.trans ((hfv w m2 m1).trans (hT v c' ⟨_, m2⟩ n2)))

end GlobalTheory.LevelHecke.PairToLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalUnitaryPairToPairComponentMemLocalLevelStatement
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalUnitary_pairToPair_component_mem_localLevel : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v), FvTie P K fMe → cT (sigD D : D.host.E →+* D.host.E) (gramN D i hi) = gramN D i hi → ∀ (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (γ : GL (Fin (D.R.N i)) D.host.E), γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → (pc P v c').act (glE γ) = pc P v c → mov K (A.eV v).1 c γ c' ∈ K.lev.Uloc (A.eV v).1 := by
  first | exact @GlobalTheory.LevelHecke.PairToLevel.main | exact GlobalTheory.LevelHecke.PairToLevel.main | (intros; apply GlobalTheory.LevelHecke.PairToLevel.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivariantLocalPairMapAdelic
noncomputable section

namespace GlobalTheory.LevelHecke

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem pm_mulsF_of_mem (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    (h : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hh : h ∈ S.Uloc v) : MulsF S v hv 1 h := by
  rw [S.UlocAlt v hv] at hh
  obtain ⟨hg, h2⟩ := (Subgroup.mem_inf.1 hh).2
  exact ⟨hg, fun x => by rw [one_smul]; exact h2 x⟩

theorem pm_mulsF_mul (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    {a b : ℤ} {g h : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (hg : MulsF S v hv a g) (hh : MulsF S v hv b h) :
    MulsF S v hv (b * a) (g * h) := by
  obtain ⟨ha, ha'⟩ := hg
  obtain ⟨hb, hb'⟩ := hh
  refine ⟨Subgroup.mul_mem _ ha hb, fun x => ?_⟩
  have h1 := ha' ⟨h.1 *ᵥ x.1, (hb x.1).1 x.2⟩
  have h2 := hb' x
  rw [← h2, ← h1, mul_smul]
  congr 3
  apply Subtype.ext
  simp [Matrix.mulVec_mulVec]

theorem pm_gen (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    {k : Type} [Field k] {C : Type} (y : C → GA σ J)
    (hy : Function.Surjective (fun c => (Quotient.mk'' (y c) : Cls S)))
    (q : C → Pr (𝓞 E) (Fin n → E) k)
    (h1 : ∀ (c c' : C) (γ : GL (Fin n) E) (a : ℤ), MulsF S v hv a (bc (prV (E := E) v)
      ((y c).1⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c').1)) →
      (q c').act (glE γ) = (q c).dil (a : k))
    (h2 : ∀ (c c' : C) (γ : GL (Fin n) E), γ ∈ UJ (σ : E →+* E) J → (q c').act (glE γ) = q c →
      bc (prV (E := E) v) ((y c).1⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c').1) ∈ S.Uloc v) :
    ∃ p : GA σ J → Pr (𝓞 E) (Fin n → E) k, PMap S v hv p ∧ (∀ c, p (y c) = q c) ∧
      ∀ x, ∃ c γ, p x = (q c).act (glE γ) := by
  have hpres : ∀ x : GA σ J, ∃ (c : C) (γ : GL (Fin n) E) (κ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
      γ ∈ UJ (σ : E →+* E) J ∧ κ ∈ S.U ∧
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c).1 * κ := by
    intro x
    obtain ⟨c, hc⟩ := hy (Quotient.mk'' x)
    obtain ⟨hh', hhm, kk, hkm, heq⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 hc
    obtain ⟨γ, hγ, hγe⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhm)
    refine ⟨c, γ, kk.1, hγ, Subgroup.mem_subgroupOf.1 hkm, ?_⟩
    rw [heq, Subgroup.coe_mul, Subgroup.coe_mul, ← hγe]
  choose cc gg kk hgg hkk hx using hpres
  have hloc : ∀ κ ∈ S.U, bc (prV (E := E) v) κ ∈ S.Uloc v := fun κ hκ => ((S.U_eq κ).1 hκ).2 v
  have hmov : ∀ (c c' : C) (γ γ' : GL (Fin n) E) (κ κ' δ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ' * (y c').1 * κ' =
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c).1 * κ * δ →
      bc (prV (E := E) v) ((y c).1⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ⁻¹ * γ') * (y c').1) =
        bc (prV (E := E) v) κ * bc (prV (E := E) v) δ * (bc (prV (E := E) v) κ')⁻¹ := by
    intro c c' γ γ' κ κ' δ h
    rw [← map_inv, ← map_mul, ← map_mul, map_mul (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))), map_inv]
    congr 1
    have h' := eq_mul_inv_of_mul_eq h
    rw [mul_assoc, mul_assoc, h']
    group
  have hact : ∀ (c' : C) (γ γ' : GL (Fin n) E),
      ((q c').act (glE (γ⁻¹ * γ'))).act (glE γ) = (q c').act (glE γ') := by
    intro c' γ γ'
    rw [Pr.act_act, ← glE_mul, mul_inv_cancel_left]
  have key : ∀ (c c' : C) (γ γ' : GL (Fin n) E) (κ κ' δ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (a : ℤ),
      κ ∈ S.U → κ' ∈ S.U →
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ' * (y c').1 * κ' =
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c).1 * κ * δ →
      MulsF S v hv a (bc (prV (E := E) v) δ) →
      (q c').act (glE γ') = ((q c).act (glE γ)).dil (a : k) := by
    intro c c' γ γ' κ κ' δ a hκ hκ' h hδ
    have hm := pm_mulsF_mul S v hv (pm_mulsF_mul S v hv (pm_mulsF_of_mem S v hv _ (hloc κ hκ)) hδ)
      (pm_mulsF_of_mem S v hv _ (inv_mem (hloc κ' hκ')))
    rw [one_mul, mul_one, ← hmov c c' γ γ' κ κ' δ h] at hm
    rw [← hact c' γ γ', h1 c c' _ a hm, Pr.act_dil]
  have key1 : ∀ (c c' : C) (γ γ' : GL (Fin n) E) (κ κ' : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
      κ ∈ S.U → κ' ∈ S.U →
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ' * (y c').1 * κ' =
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c).1 * κ →
      (q c').act (glE γ') = (q c).act (glE γ) := by
    intro c c' γ γ' κ κ' hκ hκ' h
    have := key c c' γ γ' κ κ' 1 1 hκ hκ' (by rw [h, mul_one])
      (pm_mulsF_of_mem S v hv _ (by rw [map_one]; exact one_mem _))
    rwa [Int.cast_one, Pr.dil_one] at this
  refine ⟨fun x => (q (cc x)).act (glE (gg x)), ⟨fun γ _ x x' h => ?_, fun x δ => ⟨fun h => ?_, fun h => ?_⟩,
    fun x δ a h => ?_⟩, fun c => ?_, fun x => ⟨_, _, rfl⟩⟩
  · show (q (cc x')).act _ = ((q (cc x)).act _).act _
    rw [Pr.act_act, ← glE_mul]
    refine key1 _ _ _ _ (kk x) (kk x') (hkk x) (hkk x') ?_
    rw [← hx x', h, map_mul]
    conv_lhs => rw [hx x]
    simp only [mul_assoc]
  · have h' : (q (cc (x * δ))).act (glE (gg (x * δ))) = (q (cc x)).act (glE (gg x)) := h
    rw [← hact _ (gg x)] at h'
    have h3 := h2 _ _ _ (mul_mem (inv_mem (hgg x)) (hgg (x * δ))) (Pr.act_injective _ h')
    rw [hmov _ _ _ _ (kk x) (kk (x * δ)) δ.1 (by rw [← hx x, ← hx (x * δ)]; rfl)] at h3
    have h4 := mul_mem (mul_mem (inv_mem (hloc _ (hkk x))) h3) (hloc _ (hkk (x * δ)))
    rwa [← mul_assoc, inv_mul_cancel_right, inv_mul_cancel_left] at h4
  · have := key _ _ _ _ (kk x) (kk (x * δ)) δ.1 1 (hkk x) (hkk (x * δ)) (by rw [← hx x, ← hx (x * δ)]; rfl)
      (pm_mulsF_of_mem S v hv _ h)
    rwa [Int.cast_one, Pr.dil_one] at this
  · exact key _ _ _ _ (kk x) (kk (x * δ)) δ.1 a (hkk x) (hkk (x * δ)) (by rw [← hx x, ← hx (x * δ)]; rfl) h.2.2
  · have := key1 c (cc (y c)) 1 (gg (y c)) 1 (kk (y c)) (one_mem _) (hkk _)
      (by rw [← hx (y c), map_one, one_mul, mul_one])
    rwa [glE_one, Pr.act_refl] at this

end Gen


set_option maxHeartbeats 1000000 in
theorem exists_pmap : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v), FvTie P K fMe → cT (sigD D : D.host.E →+* D.host.E) (gramN D i hi) = gramN D i hi → ∀ v : (D.mem u).A.vT, ∃ p : GA (sigD D) (gramN D i hi) → Pr (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) ((D.mem u).A.Fv v), PMap K.lev (A.eV v).1 (A.eV v).2 p ∧ (∀ c, p (K.y c) = pc P v c) ∧ ∀ x, (p x).Ok (A.res v) := by
  intro D u A i hi P K fMe hF hJ v
  obtain ⟨p, h1, h2, h3⟩ := pm_gen K.lev (A.eV v).1 (A.eV v).2 K.y K.y_bij.2 (pc P v)
    (GlobalTheory.T.classPair_moved_of_multipliesLocalFunctional D u A i hi P K fMe hF v) (GlobalTheory.T.rationalUnitary_pairToPair_component_mem_localLevel D u A i hi P K fMe hF hJ v)
  refine ⟨p, h1, h2, fun x => ?_⟩
  obtain ⟨c, γ, h⟩ := h3 x
  rw [h]
  exact (pc_ok P v c).act _

end GlobalTheory.LevelHecke

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivariantLocalPairMapAdelicStatement
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equivariant_local_pair_map_adelic : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v), FvTie P K fMe → cT (sigD D : D.host.E →+* D.host.E) (gramN D i hi) = gramN D i hi → ∀ v : (D.mem u).A.vT, ∃ p : GA (sigD D) (gramN D i hi) → Pr (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) ((D.mem u).A.Fv v), PMap K.lev (A.eV v).1 (A.eV v).2 p ∧ (∀ c, p (K.y c) = pc P v c) ∧ ∀ x, (p x).Ok (A.res v) := by
  first | exact @GlobalTheory.LevelHecke.exists_pmap | exact GlobalTheory.LevelHecke.exists_pmap | (intros; apply GlobalTheory.LevelHecke.exists_pmap <;> assumption)
end
