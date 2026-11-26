module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullLevelObjectPullbackExistsAndFull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVR
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIdealOfLocally

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardTorsionAbelianVariety
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardTorsionAbelianVariety
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem card_torsion_abelianVariety : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g N : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (N : k) ≠ 0 → Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ B // x ^ N = 1} = N ^ (2 * g) :=
  fun k _ _ B _ g N hB hg hN => GlobalTheory.abMulN_holds k B g N hB hg hN

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardTorsionAbelianVarietyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_torsion_eq_pow_two_mul_dim : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g N : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (N : k) ≠ 0 → Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ B // x ^ N = 1} = N ^ (2 * g) := by
  first | exact @GlobalTheory.card_torsion_abelianVariety | exact GlobalTheory.card_torsion_abelianVariety | (intros; apply GlobalTheory.card_torsion_abelianVariety <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELTripleOfDenseFibres
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELTripleOfDenseFibres
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PELFamily

section Pairing

variable {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) {T : Over S}

theorem weilIs_pow_left (hW : Out.WeilSt) {n : ℕ} {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ}
    (h : Out.WeilIs P.A P.L n x y c) (m : ℕ) : Out.WeilIs P.A P.L n (x ^ (m + 1)) y (c ^ (m + 1)) := by
  induction m with
  | zero => rwa [zero_add, pow_one, pow_one]
  | succ m ih =>
    rw [pow_succ x, pow_succ c]
    exact (hW S P n T).2.1 _ _ _ _ _ ih h

theorem weilIs_lower (hW : Out.WeilSt) {n m : ℕ} (hm : 0 < m) (hu : IsUnit ((n * m : ℕ) : Γ(T.left, ⊤)))
    {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ} (hx : x ^ (n * m) = 1) (hy : y ^ (n * m) = 1)
    (h : Out.WeilIs P.A P.L ((n * m : ℕ) : ℤ) x y c) : Out.WeilIs P.A P.L n (x ^ m) (y ^ m) (c ^ m) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have h₁ := CommPairing.weilIs_symm P.isLB (weilIs_pow_left P hW (CommPairing.weilIs_symm P.isLB h) m)
  rw [inv_pow, inv_inv, Nat.cast_mul] at h₁
  exact ((hW S P n T).2.2.2 _ x _ _ hu hx (by rw [← pow_mul, mul_comm, hy])).1 h₁

theorem eq_one_of_weilIs_one {K : Type} [Field K] (hW : Out.WeilSt) {x : Sp K ⟶ S} {n : ℕ}
    {y : Over.mk x ⟶ P.A} {c : Kˣ} (h : Out.WeilIs P.A P.L n 1 y (unitOn c)) : c = 1 := by
  have h₁ := (hW S P n _).2.1 _ _ _ _ _ h h
  rw [_root_.mul_one] at h₁
  have e : unitOn (c * c) = unitOn c * unitOn c := map_mul _ _ _
  exact mul_eq_left.1 (weilIs_unique_fieldPoint S P.A P.L P.isLB K x n 1 y _ _ (e ▸ h₁) h)

end Pairing

theorem weilIs_of_lbIso (hG : Out.GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L M : LB A.left} (hL : L.IsLB) (hM : M.IsLB) (h : LBIso L (M.pull (𝟙 A : A ⟶ A).left)) {n : ℤ} {T : Over S}
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (hw : Out.WeilIs A M n x y c) : Out.WeilIs A L n x y c := by
  have h₁ : LBIso (lbPow L 1) (M.pull (𝟙 A : A ⟶ A).left) :=
    LBIso.trans (DVR.linComb_isLB _ hL _ _) hL (pull_isLB hM _) (lbIso_lbPow_one hL) h
  have := (weilIs_along_hom hG S A A (𝟙 A) L M 1 n T x y c c hA hA hL hM inferInstance h₁
    (by rwa [Category.comp_id, Category.comp_id])).1
  rwa [Nat.cast_one, _root_.mul_one] at this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {g k : ℕ} {J : Type}
  {a : J → 𝓞 E} {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La} {o : Type} [CommRing o] {b : TBase o k} {em : o →+* ℂ} {ρ : o}
  {S : Scheme.{0}} {s : S ⟶ Sp o}

theorem exists_fibre (hL : Out.Laws) (hcl : Subring.closure (Set.range a) = ⊤) {t : TObj g k J b s} {p : S}
    (hp : p ∈ fromSet em (PELClass (b := b) D a bas ρ em) t) :
    ∃ (K : Type) (_ : Field K) (_ : CharZero K) (x : Sp K ⟶ S) (tx : TObj g k J b (x ≫ s)) (τ : SAB H (Sp K)),
      p ∈ Set.range x ∧ TMap tx t x ∧ IsPEL D a bas ρ tx τ := by
  obtain ⟨K, _, x, hx, K₀, _, β, i, j, t₀, tx, tc, hj, hs, m₁, m₂, m₃, τ, hτ⟩ := hp
  obtain ⟨τ₀, h₀⟩ := GlobalTheory.T.pelStructure_descends_field_extension hL E H D g k J a bas o b ρ K₀ ℂ j β _ t₀ tc τ hcl
    (by rw [← hj]; exact Spec.map_comp _ _) m₃ hτ
  obtain ⟨τ', h'⟩ := PELPull.isPEL_pull E H D g k J a bas o b ρ _ _ _ _ _ t₀ tx τ₀ hs.symm m₂ h₀
  have : CharZero K₀ := j.charZero
  exact ⟨K, inferInstance, (i.charZero_iff i.injective).1 inferInstance, x, tx, τ', hx, m₁, h'⟩

theorem exists_fibre_map (hL : Out.Laws) (hcl : Subring.closure (Set.range a) = ⊤) {t : TObj g k J b s} {p : S}
    (hp : p ∈ fromSet em (PELClass (b := b) D a bas ρ em) t) :
    ∃ (K : Type) (_ : Field K) (_ : CharZero K) (x : Sp K ⟶ S) (τ : SAB H (Sp K)) (ψ : τ.G.left ⟶ t.A.left),
      p ∈ Set.range x ∧ IsGrpPullback τ.G t.A x ψ ∧ LBIso τ.PP.L (t.L.pull ψ) ∧
      (∀ j, (τ.act.act (a j)).left ≫ ψ = ψ ≫ (t.act j).left) ∧
      ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (y : Sp Ω ⟶ Sp K) (β : o →+* Ω), y ≫ x ≫ s = spMap β →
        DetCond D τ.act y (β ρ) ∧ ∃ I : TateIso D Ω (Over.mk y ⟶ τ.G) (fun c z => z ≫ τ.act.act c)
            (fun n z z' c => Out.WeilIs τ.G τ.PP.L n z z' (unitOn c)),
          (I.ζ k : Ω) = β b.ζ ∧ ∀ i, (I.ev k (bas (Pi.single i 1))).left ≫ ψ = (y ≫ x) ≫ (t.pt i).left := by
  obtain ⟨K, _, _, x, tx, τ, hx, ⟨ψ, hψ, hψL, hpt, hact⟩, φ, hφ, hφL, hφa, hgeom⟩ := exists_fibre hL hcl hp
  refine ⟨K, inferInstance, inferInstance, x, τ, φ.hom.left ≫ ψ, hx,
    ((isGrpPullback_of_iso φ).comp hψ).congr (Category.id_comp x) rfl,
    hφL.trans τ.PP.isLB (pull_isLB tx.isLB _) (pull_isLB t.isLB _) (PELPull.lbIso_pull hψL _ rfl),
    fun j => ?_, fun Ω _ _ _ y β hy => ?_⟩
  · have h₁ : (τ.act.act (a j)).left ≫ φ.hom.left = φ.hom.left ≫ (tx.act j).left :=
      congrArg (fun z => z.left) (hφa j)
    rw [← Category.assoc, h₁, Category.assoc, hact, Category.assoc]
  · obtain ⟨hdet, I, hI, hA⟩ := hgeom Ω y β hy
    refine ⟨hdet, I, hI, fun i => ?_⟩
    have h₁ : (I.ev k (bas (Pi.single i 1))).left ≫ φ.hom.left = y ≫ (tx.pt i).left :=
      congrArg (fun z => z.left) (hA i)
    rw [← Category.assoc, h₁, Category.assoc, hpt, Category.assoc]

theorem exists_geom (hL : Out.Laws) (hcl : Subring.closure (Set.range a) = ⊤) {t : TObj g k J b s}
    (r : OAct (𝓞 E) t.A)
    (hr : ∀ (T : Scheme.{0}) (x : T ⟶ S) (G : Over T) [GrpObj G] (φ : G.left ⟶ t.A.left) (act : OAct (𝓞 E) G),
      IsGrpPullback G t.A x φ → (∀ j, (act.act (a j)).left ≫ φ = φ ≫ (t.act j).left) →
      ∀ c, (act.act c).left ≫ φ = φ ≫ (r.act c).left) {p : S}
    (hp : p ∈ fromSet em (PELClass (b := b) D a bas ρ em) t) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ S) (β : o →+* K),
      p ∈ Set.range x ∧ x ≫ s = spMap β ∧ DetCond D r x (β ρ) ∧
      ∃ I : TateIso D K (Over.mk x ⟶ t.A) (fun c z => z ≫ r.act c)
          (fun n z z' c => Out.WeilIs t.A t.L n z z' (unitOn c)),
        (I.ζ k : K) = β b.ζ ∧ ∀ i, I.ev k (bas (Pi.single i 1)) =
          (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ t.pt i := by
  have := t.ab.comm
  obtain ⟨K, _, _, x, τ, ψ, ⟨q, hq⟩, hψ, hψL, hact, hgeom⟩ := exists_fibre_map hL hcl hp
  have hc := hr _ x τ.G ψ τ.act hψ hact
  let y : Sp (AlgebraicClosure K) ⟶ Sp K := spMap (algebraMap K (AlgebraicClosure K))
  obtain ⟨β, hβ⟩ : ∃ β : o →+* AlgebraicClosure K, y ≫ x ≫ s = spMap β :=
    ⟨(Spec.preimage (y ≫ x ≫ s)).hom, (Spec.map_preimage _).symm⟩
  obtain ⟨hdet, I, hI, hA⟩ := hgeom _ y β hβ
  refine ⟨AlgebraicClosure K, inferInstance, inferInstance, inferInstance, y ≫ x, β,
    ⟨(default : PrimeSpectrum (AlgebraicClosure K)), ?_⟩, (Category.assoc _ _ _).trans hβ, fun σ => ?_,
    ObjPull.tateMove (ObjPull.pushEquiv hψ (Over.mk y)).symm (fun c z => ?_) (fun n z z' c hz => ?_) I, hI,
    fun i => Over.OverMorphism.ext (hA i)⟩
  · exact (Scheme.Hom.comp_apply y x _).trans ((congrArg x (Subsingleton.elim (α := PrimeSpectrum K) _ _)).trans hq)
  · rw [← LiePull.lieMult_pull _ _ _ t.A τ.G x ψ r τ.act hψ hc _ y σ,
      ← LiePull.lieMult_pull _ _ _ t.A τ.G x ψ r τ.act hψ hc _ y σ]
    exact hdet σ
  · obtain ⟨z, rfl⟩ := (ObjPull.pushEquiv hψ (Over.mk y)).surjective z
    rw [MulEquiv.symm_apply_eq, MulEquiv.symm_apply_apply]
    apply Over.OverMorphism.ext
    show (z.left ≫ _) ≫ _ = (z.left ≫ _) ≫ _
    rw [Category.assoc, ← hc, Category.assoc]
  · exact (weilIs_iff_of_isGrpPullback_comm _ _ t.A τ.G x ψ t.L τ.PP.L t.isLB τ.PP.isLB hψ hψL (Over.mk y) n _ _ z z' _
      (ObjPull.pushEquiv_symm_left hψ (Over.mk y) z).symm
      (ObjPull.pushEquiv_symm_left hψ (Over.mk y) z').symm).1 hz

theorem exists_isPEL_of_dense : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (w w' : J), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (ρ : o) (S : Scheme.{0}) [IsLocallyNoetherian S] [IsReduced S] (s : S ⟶ Sp o) (t : TObj g k J b s), em ρ = H.rt0 → Function.Injective em → Dense (fromSet em (PELClass (b := b) D a bas ρ em) t) → ∃ τ : SAB H S, IsPEL D a bas ρ t τ := by
  intro hL _ hcube E _ _ _ H D g J a bas w w' _ _ hw _ hcl k o _ b em ρ S _ _ s t hρ hem hd
  have := t.ab.comm
  obtain ⟨r, hra, hr⟩ := GlobalTheory.T.oAct_spread_from_dense_fibres_abelianScheme (𝓞 E) J a S t.A t.act hcl t.ab t.hom (hd.mono fun p hp => by
    obtain ⟨K, _, _, x, τ, ψ, hx, hψ, -, hact, -⟩ := exists_fibre_map hL hcl hp
    exact ⟨K, inferInstance, x, τ.G, inferInstance, ψ, τ.act, hx, hψ, hact⟩)
  have hadj := fun c => GlobalTheory.T.adjoint_endomorphisms_cubeLB_of_dense_fibres hL.globalFns S t.A t.L (r.act c) (r.act (H.bar c)) t.ab t.isLB t.ample (r.hom _)
    (r.hom _) (hd.mono fun p hp => by
      obtain ⟨K, _, _, x, τ, ψ, hx, hψ, hψL, hact, -⟩ := exists_fibre_map hL hcl hp
      have hc := hr _ x τ.G ψ τ.act hψ hact
      exact ⟨K, inferInstance, x, τ.G, inferInstance, inferInstance, ψ, τ.PP.L, _, _, hx, hψ, τ.PP.isLB, hψL, hc _, hc _,
        τ.adj c⟩)
  have hprim := GlobalTheory.T.lbIso_cube_graph_of_dense_fibres hL.globalFns S t.A t.L (r.act H.w0) t.ab t.isLB t.ample t.rigid (r.hom _)
    (hd.mono fun p hp => by
      obtain ⟨K, _, _, x, τ, ψ, hx, hψ, hψL, hact, -⟩ := exists_fibre_map hL hcl hp
      have hc := hr _ x τ.G ψ τ.act hψ hact
      exact ⟨K, inferInstance, x, τ.G, inferInstance, inferInstance, ψ, τ.PP.L, _, hx, hψ, τ.PP.isLB, hψL, hc _, τ.prim⟩)
  obtain ⟨PP, cub, sym, iso, -, prim, adj⟩ := PrimNorm.exists_primitive_normalisation hL.globalFns E H _ t.A r t.L t.ab
    t.isLB (hcube _ t.pol t.L t.isLB) hadj
  have iso' : LBIso PP.L (t.L.pull (𝟙 t.A : t.A ⟶ t.A).left) := by
    refine LBIso.trans PP.isLB t.isLB (pull_isLB t.isLB _)
      (LBIso.trans PP.isLB (DVR.linComb_isLB _ t.isLB _ _) t.isLB iso hprim.symm) ?_
    exact (LBIso.chartPull (Geo.Tor.chartPullPull t.L (𝟙 _) (𝟙 _) rfl) (chartPullId t.L) (lbIso_refl t.isLB)).symm
  refine ⟨⟨t.A, isSemiAbelian_of_isAbelianScheme _ t.ab, r, PP, cub, sym, adj, prim⟩, Iso.refl _,
    inferInstanceAs (IsMonHom (𝟙 t.A)), iso', fun j => ?_, fun K _ _ _ x β hx => ⟨?_, ?_⟩⟩
  · show r.act (a j) ≫ 𝟙 _ = 𝟙 _ ≫ t.act j
    rw [hra, Category.comp_id, Category.id_comp]
  · refine GlobalTheory.T.determinantCondition_spreads_of_dense_points E H D S t.A g r o s ρ t.dim (hem ?_) (hd.mono fun p hp => ?_) K x β hx
    · rw [map_pow, hρ, H.sqrt_neg_disc_sq, map_neg, map_natCast]
    · obtain ⟨K, _, _, _, x, β, h₁, h₂, h₃, -⟩ := exists_geom hL hcl r hr hp
      exact ⟨K, inferInstance, inferInstance, inferInstance, x, β, h₁, h₂, h₃⟩
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => by
    have := b.unit.map em
    simp [h] at this
  have hcard : ∀ n, 0 < n → Nat.card {z : Over.mk x ⟶ t.A // z ^ n = 1} = n ^ Module.finrank ℤ D.La := fun n hn => by
    rw [← bas.finrank_eq, Module.finrank_fin_fun]
    exact (hL.mulN S t.pol n hn).2.2.2.2 K x (Nat.cast_ne_zero.2 hn.ne')
  obtain ⟨I, hI, hA⟩ := GlobalTheory.T.tateIsometry_of_finiteLevel_isometries E H D K (Over.mk x ⟶ t.A) (fun c z => z ≫ r.act c)
    (fun n z z' c => Out.WeilIs t.A t.L n z z' (unitOn c)) k (β b.ζ) _ (fun i => bas (Pi.single i 1))
    (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ t.pt i) hk
    (fun n hn => Nat.finite_of_card_ne_zero (by rw [hcard n hn]; positivity))
    (fun n m z z' c hn hm hz hz' h => by
      have e : unitOn (c ^ m) = unitOn c ^ m := map_pow _ _ _
      have u : IsUnit ((n * m : ℕ) : K) := (Nat.cast_ne_zero.2 (Nat.mul_pos hn hm).ne').isUnit
      have u' := u.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      rw [map_natCast] at u'
      rw [e]
      exact weilIs_lower t.pol hL.weil hm u' hz hz' h)
    (fun m hm => by
      have hn := Nat.mul_pos hk hm
      obtain ⟨ζ, ev, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := GlobalTheory.T.exists_level_isometry_of_dense_geometric_points hL E H D S t.pol r.act o s b.ζ _
        (fun i => bas (Pi.single i 1)) t.pt (k * m) m hn (hd.mono fun p hp => by
          obtain ⟨K, _, _, _, x, β, h₁, h₂, -, I, h₃, h₄⟩ := exists_geom hL hcl r hr hp
          exact ⟨K, inferInstance, x, β, I.ζ (k * m), I.ev (k * m), Nat.cast_ne_zero.2 hn.ne', h₁, h₂, I.ζ_prim _ hn,
            I.add _, fun v => (I.onto _ hn _).2 ⟨v, rfl⟩, I.lin _, I.isom _ hn,
            by rw [← h₃, ← I.ζ_pow k m hk hm, Units.val_pow_eq_pow_val],
            fun i => (I.tower k m hk hm _).trans (h₄ i)⟩) K x β (Nat.cast_ne_zero.2 hn.ne') hx
      obtain ⟨h₈, h₉⟩ := GlobalTheory.T.torsionIsometry_primitiveRoot_bijective_mod_n E H D K (Over.mk x ⟶ t.A)
        (fun z z' c => Out.WeilIs t.A t.L (k * m : ℕ) z z' (unitOn c)) (k * m) ζ ev hn (hcard _ hn)
        (fun _ _ _ h => eq_one_of_weilIs_one t.pol hL.weil h) h₁ h₂ h₃ h₅
      exact ⟨ζ, ev, h₁, h₂, h₄, h₈, h₉, h₅, h₆, h₇⟩)
  exact ⟨{ I with isom := fun n hn z z' => weilIs_of_lbIso hL.globalFns t.ab PP.isLB t.isLB iso' (I.isom n hn z z') },
    hI, fun i => (Category.comp_id _).trans (hA i)⟩

end GlobalTheory.PELFamily
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELTripleOfDenseFibresStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isPELTriple_of_dense_fibres : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (w w' : J), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (ρ : o) (S : Scheme.{0}) [IsLocallyNoetherian S] [IsReduced S] (s : S ⟶ Sp o) (t : TObj g k J b s), em ρ = H.rt0 → Function.Injective em → Dense (fromSet em (PELClass (b := b) D a bas ρ em) t) → ∃ τ : SAB H S, IsPEL D a bas ρ t τ := by
  first | exact @GlobalTheory.PELFamily.exists_isPEL_of_dense | exact GlobalTheory.PELFamily.exists_isPEL_of_dense | (intros; apply GlobalTheory.PELFamily.exists_isPEL_of_dense <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecNeZeroOfLbIso
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.AmpleSpecialisation

theorem exists_sec_ne_zero_of_lbIso {Y : Scheme.{0}} {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (h : LBIso A B)
    (hs : ∃ s : LB.Sec B, ∃ j, s.f j ≠ 0) : ∃ s : LB.Sec A, ∃ j, s.f j ≠ 0 := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨t, b, hb⟩ := hs
  refine ⟨DVR.secOfIso t hu hA hB, ?_⟩
  by_contra hn
  push Not at hn
  refine hb (fn_ext fun y hy => ?_)
  obtain ⟨a, ha⟩ := exists_chart hA y
  have e := (DVR.secOfIso_spec t hu hA hB a b).symm
  rw [hn a] at e
  have e' := (DVR.isoCand_rs u t a b le_rfl).symm.trans ((congrArg (DVR.rs le_rfl) (e.trans (map_zero _))).trans
    (map_zero _))
  have e'' := (Units.mul_right_eq_zero _).1 e'
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ A.U a ⊓ B.U b := ⟨ha, hy⟩
  refine (gs_res (𝟙 Y) y inf_le_right hm _).symm.trans ((congrArg (gs (𝟙 Y) y _) e'').trans ?_)
  rw [gs_eq _ y _ hm, gs_eq _ y _ hy, map_zero, map_zero, map_zero, map_zero]

theorem lbIso_pull_div_lbPow {X Y : Scheme.{0}} {L M : LB X} (hL : L.IsLB) (hM : M.IsLB) (f : Y ⟶ X) (a : ℕ) :
    LBIso ((LB.div (lbPow M a) L).pull f) (LB.div (lbPow (M.pull f) a) (L.pull f)) := by
  have hp : (lbPow M a).IsLB := LB.isLB_linComb hM _ _
  have hp' : (lbPow (M.pull f) a).IsLB := LB.isLB_linComb (pull_isLB hM f) _ _
  refine (CechPic.cls_eq_iff (pull_isLB (LB.isLB_div hp hL) f) (LB.isLB_div hp' (pull_isLB hL f))).1 ?_
  rw [CechPic.cls_pull (LB.isLB_div hp hL), CechPic.cls_div hp hL, CechPic.cls_div hp' (pull_isLB hL f),
    CechPic.cls_lbPow hM, CechPic.cls_lbPow (pull_isLB hM f), CechPic.cls_pull hM, CechPic.cls_pull hL,
    map_sub, map_nsmul]

def baseChange {S S' : Scheme.{0}} (P : Out.PolAV S) (f : S' ⟶ S) : Out.PolAV S' where
  A := (Over.pullback f).obj P.A
  isAb := Out.TLinPf.isAb_pullback f P.A P.isAb
  g := P.g
  smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
    (isGrpPullback_pullback P.A f).1 P.smoothDim
  L := P.L.pull (pullback.fst P.A.hom f)
  isLB := pull_isLB P.isLB _
  rigid := PolBaseChange.rigidified_pull (isGrpPullback_pullback P.A f) P.rigid
  sym := PolBaseChange.sym_pull (isGrpPullback_pullback P.A f) P.sym
  ample :=
    haveI := P.isAb.proper
    AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample (IsPullback.of_hasPullback P.A.hom f)
  ktriv := by
    obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl (pull_isLB P.isLB (pullback.fst P.A.hom f))
    exact kTriv_pull (isGrpPullback_pullback P.A f) P.isLB (pull_isLB P.isLB _) ((isGen_iff w).1 hw) P.ktriv

theorem relAmple_of_genericFibre : Out.Laws → Out.Laws2 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] [IsIntegral S] (P : Out.PolAV S) (M : LB P.A.left) (K : Type) [Field K] (x : Sp K ⟶ S), M.IsLB → Set.range x = {genericPoint S} → Out.RelAmple ((Over.pullback x).obj P.A) (M.pull (pullback.fst P.A.hom x)) → Out.RelAmple P.A M := by
  intro hL _ S _ _ P M K _ x hM hx hamp
  have hne : Nonempty (baseChange P x).A.left :=
    ⟨eSec (baseChange P x).A (Classical.arbitrary (Sp K))⟩
  obtain ⟨a, s, ha, hs⟩ := GlobalTheory.T.exists_sec_relAmplePow_div_ne_zero K (baseChange P x).A (baseChange P x).L (M.pull (pullback.fst P.A.hom x))
    (baseChange P x).isAb.proper hne (baseChange P x).isLB (pull_isLB hM _) hamp
  have hp : (lbPow M a).IsLB := LB.isLB_linComb hM _ _
  have hN := LB.isLB_div hp P.isLB
  have hN' : ∀ {Y : Scheme.{0}} (f : Y ⟶ P.A.left), (LB.div (lbPow (M.pull f) a) (P.L.pull f)).IsLB := fun f =>
    LB.isLB_div (LB.isLB_linComb (pull_isLB hM f) _ _) (pull_isLB P.isLB f)
  obtain ⟨t, ht⟩ := exists_sec_ne_zero_of_lbIso (pull_isLB hN _) (hN' _)
    (lbIso_pull_div_lbPow P.isLB hM (pullback.fst P.A.hom x) a) ⟨s, hs⟩
  refine GlobalTheory.T.relAmple_of_ample_geometricFibres_abelianScheme hL S P M hM fun K' _ _ y => ?_
  obtain ⟨t', ht'⟩ := exists_sec_ne_zero_of_lbIso (hN' _) (pull_isLB hN _)
    (lbIso_pull_div_lbPow P.isLB hM (pullback.fst P.A.hom y) a).symm
    (GlobalTheory.T.exists_section_ne_zero_fibre_of_generic_section hL S P _ K K' x y t hN hx ht)
  obtain ⟨r, u, hu⟩ := GlobalTheory.T.exists_sections_cover_cube_effective_abelianVariety GlobalTheory.T.cube_theorem_and_sections_finite_growth_abelianVariety.1 K' (baseChange P y) _ t' (hN' _) ht'
  exact GlobalTheory.T.relAmple_of_cube_div_generated_field K' (baseChange P y).A (baseChange P y).L (M.pull (pullback.fst P.A.hom y)) a r u
    (baseChange P y).isAb.proper (baseChange P y).isLB (pull_isLB hM _) ha (baseChange P y).ample hu

end GlobalTheory.AmpleSpecialisation
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelQuotientRepresentsReduced
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelQuotientRepresentsReduced
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.LevelCover

noncomputable section

namespace GlobalTheory.LevelQuotRep

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem isSeparated_of_qproj {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsQProjOver f) :
    IsSeparated f := by
  obtain ⟨N, i, hi, -, rfl⟩ := h
  unfold PSpace.str
  infer_instance

theorem exists_lift_geom {W Z : Scheme.{0}} (q : W ⟶ Z) [LocallyOfFiniteType q] [Surjective q] {K : Type} [Field K]
    [IsAlgClosed K] (x : Sp K ⟶ Z) : ∃ h : Sp K ⟶ W, h ≫ q = x := by
  obtain ⟨y, -⟩ := (pullback.snd q x).surjective (IsLocalRing.closedPoint K)
  have : JacobsonSpace ↥(pullback q x) := LocallyOfFiniteType.jacobsonSpace (pullback.snd q x)
  obtain ⟨y', -, hy'⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback q x)))
    ⟨y, trivial⟩ isOpen_univ.isLocallyClosed
  have hc : IsClosed {y'} := hy'
  refine ⟨pointOfClosedPoint (pullback.snd q x) y' hc ≫ pullback.fst q x, ?_⟩
  rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

theorem finite_etale_onto_spMap {K L : Type} [Field K] [Field L] [CharZero K] [CharZero L] [FiniteDimensional ℚ L]
    (k : K →+* L) : IsFinite (spMap k) ∧ Etale (spMap k) ∧ Surjective (spMap k) := by
  algebraize [k]
  have : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun x => by simp
  have hf : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  refine ⟨?_, ?_, ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩⟩
  · rw [IsFinite.SpecMap_iff]
    exact hf
  · rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
    have : Algebra.FinitePresentation K L := Algebra.FinitePresentation.of_finiteType.mp inferInstance
    exact (⟨inferInstance, inferInstance⟩ : Algebra.Etale K L)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l₂ : Level H}

theorem finiteDimensional_KA (l : Level H) : FiniteDimensional ℚ (KA l) := by
  refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
  rcases hx with rfl | rfl
  · refine IsIntegral.of_pow two_pos ?_
    rw [H.sqrt_neg_disc_sq]
    exact (isIntegral_algebraMap (x := (H.d : ℚ))).neg
  · refine IsIntegral.of_pow l.A_pos ?_
    rw [show zeta l.A ^ l.A = 1 from (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]
    exact isIntegral_one

section Obj

variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {b : Base l B} {b' : Base l B'} {b'' : Base l B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}
  {o : Obj D l b s} {o' : Obj D l b' s'} {o'' : Obj D l b'' s''}

theorem obj_comp {f : S' ⟶ S} {f' : S'' ⟶ S'} (m' : ObjMap o'' o' f') (m : ObjMap o' o f) :
    Nonempty (ObjMap o'' o (f' ≫ f)) :=
  ⟨(((ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o o' o'').2 f f' m).1 m').choose⟩

theorem obj_cancel {f : S' ⟶ S} {e : S'' ⟶ S} (m : ObjMap o' o f) (n : ObjMap o'' o e) (g : S'' ⟶ S')
    (he : g ≫ f = e) : Nonempty (ObjMap o'' o' g) := by
  subst he
  exact ⟨(((ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o o' o'').2 f g m).2 n).choose⟩

theorem obj_pull_same (o : Obj D l b s) (f : S' ⟶ S) : ∃ o' : Obj D l b (f ≫ s), Nonempty (ObjMap o' o f) :=
  obj_pull E H D l _ _ b b (RingHom.id _) _ _ s _ f rfl rfl (by rw [spMap_id', Category.comp_id]) o

end Obj

variable {Xo₂ : Moduli D l₂} (Q : LevelQuot l Xo₂)

theorem exists_lowers {B : Type} [CommRing B] {b : Base l B} {T : Scheme.{0}} {t : T ⟶ Sp B} {o : Obj D l b t}
    {z : T ⟶ Q.X} (n : ObjMap o Q.univ z) (y : T ⟶ Xo₂.X) (hy : y ≫ Q.π = z) :
    ∃ mu : SABMap o.t Xo₂.univ.t y, Lowers l Xo₂.univ o.eta o.etaA y mu.φ := by
  obtain ⟨mu, hmu⟩ := sab_cancel Q.m n.toSABMap y hy
  refine ⟨mu, fun a => sec_cancel mu Q.m _ _ ?_, fun a => sec_cancel mu Q.m _ _ ?_⟩
  · rw [hmu, Q.eta, ← Category.assoc, hy]; exact n.eta a
  · rw [hmu, Q.etaA, ← Category.assoc, hy]; exact n.etaA a

theorem hom_unique {B : Type} [CommRing B] {b : Base l B} {T : Scheme.{0}} [IsReduced T] {t : T ⟶ Sp B}
    {o : Obj D l b t} {f f' : T ⟶ Q.X} (h : f ≫ Q.s = f' ≫ Q.s) (m : ObjMap o Q.univ f) (m' : ObjMap o Q.univ f') :
    f = f' := by
  have := isSeparated_of_qproj Q.qproj
  have := Q.fin
  have := Q.onto
  refine (hom_eq_iff_forall_isAlgClosed Q.s h).mpr fun K _ _ x => ?_
  obtain ⟨ox, ⟨n⟩⟩ := obj_pull_same o x
  obtain ⟨u⟩ := obj_comp n m
  obtain ⟨u'⟩ := obj_comp n m'
  obtain ⟨y, hy⟩ := exists_lift_geom Q.π (x ≫ f)
  obtain ⟨y', hy'⟩ := exists_lift_geom Q.π (x ≫ f')
  obtain ⟨mu, hmu⟩ := exists_lowers Q u y hy
  obtain ⟨mu', hmu'⟩ := exists_lowers Q u' y' hy'
  rw [← hy, ← hy']
  refine Q.fibre K y y' ox.t mu mu' ox.eta ox.etaA ?_ hmu hmu'
  rw [← Q.overK, ← Category.assoc, ← Category.assoc, hy, hy', Category.assoc, Category.assoc, h]

def baseUp : Base l (KA l₂) where
  unit := (baseKA l₂).unit
  ρ := Q.jK (baseKA l).ρ
  ρ_sq := by rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  ζ := Q.jK (baseKA l).ζ
  ζ_prim := (baseKA l).ζ_prim.map_of_injective Q.jK.injective

theorem baseKA_rho_coe (l : Level H) : (((baseKA l).ρ : KA l) : ℂ) = H.rt0 := rfl

theorem baseUp_rho_coe : (((baseUp Q).ρ : KA l₂) : ℂ) = (((baseKA l).ρ : KA l) : ℂ) := Q.jK_val (baseKA l).ρ

theorem baseUp_rho : (baseUp Q).ρ = (baseKA l₂).ρ :=
  Subtype.ext ((baseUp_rho_coe Q).trans ((baseKA_rho_coe l).trans (baseKA_rho_coe l₂).symm))

theorem baseUp_zeta (hd : l.A ∣ l₂.A) : (baseUp Q).ζ = (baseKA l₂).ζ ^ (l₂.A / l.A) := Subtype.ext (by
  rw [IntermediateField.coe_pow]
  exact (Q.jK_val _).trans (zeta_dvd l₂.A_pos hd))

theorem exists_cover (hL : Out.Laws) (hpq : 1 ≤ D.p + D.q) (hd : l.Dvd l₂) {S : Scheme.{0}} [IsReduced S]
    {s' : S ⟶ Sp (KA l)} (ob : Obj D l (baseKA l) s') :
    ∃ (S₂ : Scheme.{0}) (q : S₂ ⟶ S) (g : S₂ ⟶ Q.X) (s₂ : S₂ ⟶ Sp (KA l₂)) (o : Obj D l (baseUp Q) s₂),
      IsFinite q ∧ Etale q ∧ Surjective q ∧ g ≫ Q.s = q ≫ s' ∧ Nonempty (ObjMap o ob q) ∧
        Nonempty (ObjMap o Q.univ g) := by
  have := finiteDimensional_KA l₂
  obtain ⟨k1, k2, k3⟩ := finite_etale_onto_spMap Q.jK
  obtain ⟨o₁, ⟨n₁⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseUp Q) Q.jK _ _ s' (pullback.snd s' (spMap Q.jK))
    (pullback.fst _ _) rfl rfl pullback.condition ob
  obtain ⟨S₂, p, o₂, m, hf, he, hs, ⟨hm₁, hm₂⟩, -⟩ := GlobalTheory.T.exists_finiteEtale_deeper_level_cover hL E H D l l₂ _ (baseUp Q) (baseKA l₂) _ _ o₁ hpq hd
    (baseUp_rho Q) (baseUp_zeta Q hd.2.2)
  have hr : IsReduced S₂ := isReduced_of_smooth_of_isReduced (p ≫ pullback.fst s' (spMap Q.jK))
  obtain ⟨f₂, ⟨hf₂, ⟨u⟩⟩, -⟩ := Xo₂.rep S₂ _ hr o₂
  let o := ObjLower.lower o₂ hd (baseUp_rho Q) (baseUp_zeta Q hd.2.2)
  let mo : ObjMap o o₁ p := ⟨m, hm₁, hm₂⟩
  obtain ⟨z, hz⟩ := sab_comp u.toSABMap Q.m rfl
  refine ⟨S₂, p ≫ pullback.fst _ _, f₂ ≫ Q.π, _, o, inferInstance, inferInstance, inferInstance, ?_,
    obj_comp mo n₁, ⟨⟨z, fun a => ?_, fun a => ?_⟩⟩⟩
  · rw [Category.assoc, Q.overK, ← Category.assoc, hf₂, Category.assoc, Category.assoc, pullback.condition]
  · show (o₂.eta a ^ (l₂.M / l.M)).left ≫ z.φ = _
    rw [hz, ← Category.assoc, sec_pow u.toSABMap _ _ (u.eta a), Category.assoc, Q.eta, Category.assoc]
  · show (o₂.etaA a ^ (l₂.A / l.A)).left ≫ z.φ = _
    rw [hz, ← Category.assoc, sec_pow u.toSABMap _ _ (u.etaA a), Category.assoc, Q.etaA, Category.assoc]

end GlobalTheory.LevelQuotRep

namespace GlobalTheory


open LevelQuotRep in
theorem levelQuot_represents : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo₂ : Moduli D l₂) (Q : LevelQuot l Xo₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (KA l)), IsReduced S → ∀ ob : Obj D l (baseKA l) s', ∃! f : S ⟶ Q.X, f ≫ Q.s = s' ∧ Nonempty (ObjMap ob Q.univ f) := by
  intro hL hL2 E _ _ _ H D l l₂ Xo₂ Q hpq hd S s' hS ob
  refine existsUnique_of_exists_of_unique ?_
    fun f f' ⟨h, ⟨m⟩⟩ ⟨h', ⟨m'⟩⟩ => hom_unique Q (h.trans h'.symm) m m'
  obtain ⟨S₂, q, g, s₂, o, hf, he, hs, hg, ⟨mq⟩, ⟨mg⟩⟩ := exists_cover Q hL hpq hd ob
  have key : pullback.fst q q ≫ g = pullback.snd q q ≫ g := by
    have : IsReduced (pullback q q) := isReduced_of_smooth_of_isReduced (pullback.fst q q ≫ q)
    obtain ⟨oR, ⟨n⟩⟩ := obj_pull_same o (pullback.fst q q)
    obtain ⟨n₁⟩ := obj_comp n mq
    obtain ⟨n'⟩ := obj_cancel mq n₁ (pullback.snd q q) pullback.condition.symm
    obtain ⟨u⟩ := obj_comp n mg
    obtain ⟨u'⟩ := obj_comp n' mg
    exact hom_unique Q (by rw [Category.assoc, Category.assoc, hg, pullback.condition_assoc]) u u'
  have hcoeq : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ S₂), g₁ ≫ q = g₂ ≫ q → g₁ ≫ g = g₂ ≫ g := fun g₁ g₂ h => by
    have := pullback.lift g₁ g₂ h ≫= key
    rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc] at this
  have hfac : q ≫ EffectiveEpi.desc q g hcoeq = g := EffectiveEpi.fac q g hcoeq
  refine ⟨EffectiveEpi.desc q g hcoeq, ?_, ?_⟩
  · rw [← cancel_epi q, ← Category.assoc, hfac, hg]
  · exact GlobalTheory.T.nonempty_objMap_of_finite_etale_surjective_cover hL hL2 E H D l _ _ _ _ _ _ _ _ _ _ _ _ Q.univ ob o q _ (Or.inl hS) hf he hs ⟨mq⟩
      (hfac.symm ▸ ⟨mg⟩)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelQuotientRepresentsReducedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelQuotient_represents_reduced : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo₂ : Moduli D l₂) (Q : LevelQuot l Xo₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (KA l)), IsReduced S → ∀ ob : Obj D l (baseKA l) s', ∃! f : S ⟶ Q.X, f ≫ Q.s = s' ∧ Nonempty (ObjMap ob Q.univ f) := by
  first | exact @GlobalTheory.levelQuot_represents | exact GlobalTheory.levelQuot_represents | (intros; apply GlobalTheory.levelQuot_represents <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelFamilyLocalisedCyclotomicIntegers
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelFamilyLocalisedCyclotomicIntegers
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.SiegelRingChange

noncomputable section
namespace GlobalTheory.SiegelFamilyBaseChange

theorem pb_iff {h k : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
    {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''} {c : SiegPre h k ζ s}
    {c' : SiegPre h k ζ' s'} {f : S' ⟶ S} (H : SiegPB c' c f) (c'' : SiegPre h k ζ'' s'') (f' : S'' ⟶ S') :
    SiegPB c'' c' f' ↔ SiegPB c'' c (f' ≫ f) :=
  (GlobalTheory.SiegelPullComp.id_comp_cancel h k B B' B'' ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f').2 H

theorem quasiCompact_of_isQProjOver {o : Type} [CommRing o] {X : Scheme.{0}} {f : X ⟶ Sp o} (h : IsQProjOver f) :
    QuasiCompact f := by
  obtain ⟨N, i, -, hi, rfl⟩ := h
  have : IsProper (PSpace.str o N) := isProper_str o N
  infer_instance

theorem injective_of_isAlgebraic {o O : Type} [CommRing o] [IsDomain o] [CommRing O] [CharZero O]
    (ha : Algebra.IsAlgebraic ℤ o) (ψ : o →+* O) : Function.Injective ψ := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  refine Ideal.comap_ne_bot_of_algebraic_mem (I := RingHom.ker ψ) hx0 hx (ha.1 x) ?_
  rw [eq_bot_iff]
  intro n hn
  simpa [Ideal.mem_comap, RingHom.mem_ker] using hn

theorem dense_generic {o O : Type} [CommRing o] [CommRing O] [IsDomain O] (ψ : o →+* O)
    (hψ : Function.Injective ψ) : Dense {x : Sp O | (spMap ψ x).asIdeal = ⊥} := by
  let x₀ : PrimeSpectrum O := ⟨⊥, Ideal.isPrime_bot⟩
  have hx₀ : Dense ({x₀} : Set (PrimeSpectrum O)) := by
    rw [dense_iff_closure_eq, PrimeSpectrum.closure_singleton]
    simp [x₀]
  refine Dense.mono (s₁ := ({x₀} : Set (Sp O))) ?_ hx₀
  rintro x rfl
  exact Ideal.comap_bot_of_injective ψ hψ

variable {h k : ℕ} {o B : Type} [CommRing o] [CommRing B] {ζ : o} {ζ' : B}

theorem rep_baseChange (F : SFam h k ζ) (j : o →+* B) (hj : j ζ = ζ')
    (U : SiegPre h k ζ' (pullback.snd F.s (spMap j))) (hU : SiegPB U F.univ (pullback.fst F.s (spMap j)))
    {S : Scheme.{0}} (s' : S ⟶ Sp B) (c : SiegPre h k ζ' s') (hr : IsReduced S)
    (hd : Dense {x : S | ((s' ≫ spMap j) x).asIdeal = ⊥}) (hp : c.Principal) :
    ∃ f : S ⟶ pullback F.s (spMap j), f ≫ pullback.snd F.s (spMap j) = s' ∧ SiegPB c U f := by
  obtain ⟨g, hg, H⟩ := F.rep S _ (down j hj c) hr hd hp
  refine ⟨pullback.lift g s' hg, pullback.lift_snd _ _ _, (pb_iff hU c _).2 ?_⟩
  rw [pullback.lift_fst]
  exact H

theorem inj_baseChange (F : SFam h k ζ) (j : o →+* B) (hj : j ζ = ζ')
    (U : SiegPre h k ζ' (pullback.snd F.s (spMap j))) (hU : SiegPB U F.univ (pullback.fst F.s (spMap j)))
    {R : Type} [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ pullback F.s (spMap j)) (s' : Sp R ⟶ Sp B)
    (c : SiegPre h k ζ' s') (e : x ≫ pullback.snd F.s (spMap j) = y ≫ pullback.snd F.s (spMap j))
    (hx : SiegPB c U x) (hy : SiegPB c U y) : x = y := by
  refine pullback.hom_ext ?_ e
  refine F.inj R _ _ _ (down j hj c) ?_ ((pb_iff hU c _).1 hx) ((pb_iff hU c _).1 hy)
  simp only [Category.assoc, pullback.condition]
  rw [reassoc_of% e]

theorem exists_siegelFamily : Out.Laws → Out.Laws2 → ∀ (h k p : ℕ) (o : Type) [CommRing o] (ζ : o) (j : o →+* ZP p k), Odd k → 3 ≤ k → p.Prime → Function.Injective j → j ζ = zetaZP p k → (∀ (K : Type) [Field K] (y : Sp (DualNumber K) ⟶ Sp (ZP p k)), y = constPt y) → Algebra.IsAlgebraic ℤ o → SFam h k ζ → ∃ Ag : SiegelFamily h p k, SRep Ag := by
  intro L₁ L₂ h k p o _ ζ j hodd hk hpp hinj hj hc ha F
  have hpull := siegPre_pull_ringChange h k o (ZP p k) ζ (zetaZP p k) j F.X (pullback F.s (spMap j)) F.s
    (pullback.snd F.s (spMap j)) (pullback.fst F.s (spMap j)) hj pullback.condition
  obtain ⟨U, hU⟩ := hpull.1 F.univ
  have hUp : U.Principal := hpull.2.1 _ _ hU F.princ
  have := F.smooth
  have := F.isSeparated
  have := quasiCompact_of_isQProjOver F.qproj
  have : IsDomain o := hinj.isDomain j
  have hsm : SmoothOfRelativeDimension (h * (h + 1) / 2) (pullback.snd F.s (spMap j)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) F.smooth
  refine ⟨⟨pullback F.s (spMap j), pullback.snd F.s (spMap j), hsm, inferInstance, U, hUp, ?_, ?_⟩,
    (inferInstance : IsSeparated (pullback.snd F.s (spMap j))), ?_⟩
  · intro C O _ _ _ _ _ _ _ _ hO hpn β c hgen hsp
    have hp : c.Principal := GlobalTheory.T.principal_siegel_of_generic_principal_special_ample L₁ L₂ h k hodd hk _ _ C O hO p hpp hpn β c hgen hsp
    have : IsDomain O := hO.1.isDomain (algebraMap O C)
    have : CharZero O := RingHom.charZero (algebraMap O C)
    refine rep_baseChange F j hj U hU _ c inferInstance ?_ hp
    rw [← spMap_comp']
    exact dense_generic _ (injective_of_isAlgebraic ha _)
  · intro K _ x c h₁ h₂
    refine inj_baseChange F j hj U hU x _ _ c ?_ h₁ h₂
    rw [hc K (x ≫ _)]
    simp only [constPt, Category.assoc]
  · intro S s' c hr hd hp
    refine rep_baseChange F j hj U hU s' c hr (hd.mono fun x hx => ?_) hp
    have hx' : (s' x).asIdeal = ⊥ := hx
    change ((s' x).asIdeal).comap j = ⊥
    rw [hx']
    exact Ideal.comap_bot_of_injective j hinj

end GlobalTheory.SiegelFamilyBaseChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelFamilyLocalisedCyclotomicIntegersStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegelFamily_localised_cyclotomic_integers : Out.Laws → Out.Laws2 → ∀ (h k p : ℕ) (o : Type) [CommRing o] (ζ : o) (j : o →+* ZP p k), Odd k → 3 ≤ k → p.Prime → Function.Injective j → j ζ = zetaZP p k → (∀ (K : Type) [Field K] (y : Sp (DualNumber K) ⟶ Sp (ZP p k)), y = constPt y) → Algebra.IsAlgebraic ℤ o → SFam h k ζ → ∃ Ag : SiegelFamily h p k, SRep Ag := by
  first | exact @GlobalTheory.SiegelFamilyBaseChange.exists_siegelFamily | exact GlobalTheory.SiegelFamilyBaseChange.exists_siegelFamily | (intros; apply GlobalTheory.SiegelFamilyBaseChange.exists_siegelFamily <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaGroupKTrivialOfPrincipalGenericFibreDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaGroupKTrivialOfPrincipalGenericFibreDvr
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.KTrivSpread

theorem kTriv_of_finite_flat {V K : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K]
    {A : Over (Sp V)} [GrpObj A] (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) {Z : Over (Sp V)} (i : Z ⟶ A)
    [IsFinite Z.hom] [Flat Z.hom]
    (hZ : ∀ (T : Over (Sp V)) (x : T ⟶ A), MemKL A L x ↔ ∃ z : T ⟶ Z, z ≫ i = x)
    {A' : Over (Sp K)} [GrpObj A'] {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A (spMap (algebraMap V K)) φ)
    {L' : LB A'.left} (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hk : KTriv A' L') : KTriv A L := by
  have := hA.proper
  have := schemeTheoreticallyDominant_fractionField V K
  let Y := pullback Z.hom (spMap (algebraMap V K))
  have : IsAffine Y := isAffine_of_isAffineHom (pullback.snd Z.hom (spMap (algebraMap V K)))
  have : IsSchemeTheoreticallyDominant (pullback.fst Z.hom (spMap (algebraMap V K))) :=
    .of_isPullback (IsPullback.of_hasPullback Z.hom (spMap (algebraMap V K))).flip
  let d : Sp Γ(Y, ⊤) ⟶ Z.left := Y.isoSpec.inv ≫ pullback.fst Z.hom (spMap (algebraMap V K))
  let t : Sp Γ(Y, ⊤) ⟶ Sp K := Y.isoSpec.inv ≫ pullback.snd Z.hom (spMap (algebraMap V K))
  have hd : d ≫ Z.hom = t ≫ spMap (algebraMap V K) := by
    simp only [d, t, Category.assoc, pullback.condition]
  have hdi : (d ≫ i.left) ≫ A.hom = t ≫ spMap (algebraMap V K) := by
    rw [Category.assoc, Over.w i, hd]
  let x : Over.mk t ⟶ A' := Over.homMk (h.1.lift _ _ hdi) (h.1.lift_snd _ _ _)
  let z : Over.mk (t ≫ spMap (algebraMap V K)) ⟶ Z := Over.homMk d hd
  have hz : z ≫ i = pushPt h.1.w x := Over.OverMorphism.ext (h.1.lift_fst _ _ hdi).symm
  have hx : x = 1 := hk _ t x (memKL_of_push h hL hL' hw x ((hZ _ _).2 ⟨z, hz⟩))
  have hx' : pushPt h.1.w x = 1 := (congrArg (pushHom h (Over.mk t)) hx).trans (map_one _)
  have hi : i = toUnit Z ≫ η[A] := by
    have : IsSchemeTheoreticallyDominant d := by
      dsimp only [d]; infer_instance
    refine over_ext_of_schemeTheoreticallyDominant d (congrArg (fun q => q.left)
      (show z ≫ i = z ≫ toUnit Z ≫ η[A] from ?_))
    rw [hz, hx', ← Category.assoc, comp_toUnit]
    rfl
  intro R _ s y hy
  obtain ⟨u, rfl⟩ := (hZ _ y).1 hy
  rw [hi, ← Category.assoc, comp_toUnit]

theorem kTriv_of_generic_fibre : Laws → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → RelAmple B M.L.L → KTriv B M.L.L := by
  intro hL V K _ _ _ _ _ _ P B _ _ M φ hB h hw ha
  have hM := M.L.isLB
  have hP : AbLaw.IsProjBy B.hom :=
    (AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ B M.L.L hB hM ha V (𝟙 _) B.left (𝟙 _) B.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)).1
  obtain ⟨hO, hu, hK⟩ := UU.TrivTwist.inK_iff_trivial_twist _ B M.L.L hM
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.T.exists_closed_subscheme_translation_kernel hL.globalFns V B hB hP M.L.L _ hM hO
  have hfin : IsFinite H.hom :=
    AmpleStabFinite.isFinite_of_relAmple hL.globalFns V B hB M.L.L _ hM hO ha H j hj hH
  have hflat : Flat H.hom := GlobalTheory.T.flat_kernelPolarisation_cosets_over_DVR hL.globalFns V B hB hP M.L M.c _ hO hu H j hj hH hfin
  exact kTriv_of_finite_flat hB hM j (fun T x => (hK _ rfl T x).trans (hH T x)) h P.isLB hw P.ktriv

end GlobalTheory.KTrivSpread
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaGroupKTrivialOfPrincipalGenericFibreDvrStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGroupK_trivial_of_principal_genericFibre_dvr : Laws → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → RelAmple B M.L.L → KTriv B M.L.L := by
  first | exact @GlobalTheory.KTrivSpread.kTriv_of_generic_fibre | exact GlobalTheory.KTrivSpread.kTriv_of_generic_fibre | (intros; apply GlobalTheory.KTrivSpread.kTriv_of_generic_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGenSecIffFibres
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.GenSecFibre

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.VVRank GlobalTheory.EmbPull TopologicalSpace

variable {S : Scheme.{0}} (P : PolAV S) {T T' : Over S}

theorem mem_nonzeroLocus_pullS (a : ℤ) (h : T' ⟶ T) (th : LB.Sec (LPow P.A P.L a T)) (z : (T' ⊗ P.A).left) :
    z ∈ nonzeroLocus (pullS P.A a h th) ↔ (h ▷ P.A).left z ∈ nonzeroLocus th := by
  have e : ∀ j, z ∈ (LPow P.A P.L a T').U j → (IsUnit (gs (𝟙 _) z _ ((pullS P.A a h th).f j)) ↔
      IsUnit (gs (𝟙 _) ((h ▷ P.A).left z) _ (th.f j))) := fun j hj => by
    have q := gs_pullTo (φ := fun _ : Fin 1 => (snd T P.A).left) (ε := fun _ => a) th (h ▷ P.A).left
      (fun _ => whisker_snd_left P.A h) (𝟙 _) z j hj
    rw [Category.id_comp] at q
    have q' := q.trans (gs_stalkMap (h ▷ P.A).left z _ (wchart_le_of_eq _ (fun _ => whisker_snd_left P.A h) j hj) _)
    exact (iff_of_eq (congrArg IsUnit q')).trans (isUnit_map_iff _ _)
  rw [mem_nonzeroLocus, mem_nonzeroLocus]
  refine exists_congr fun j => ⟨fun ⟨hj, u⟩ => ⟨?_, (e j hj).1 u⟩, fun ⟨hj, u⟩ => ?_⟩
  · exact wchart_le_of_eq (φ := fun _ : Fin 1 => (snd T P.A).left) _ (fun _ => whisker_snd_left P.A h) j hj
  · have hj' := mem_wchart_of_eq (φ := fun _ : Fin 1 => (snd T P.A).left) _ (fun _ => whisker_snd_left P.A h) z j hj
    exact ⟨hj', (e j hj').2 u⟩

theorem exists_mem_nonzeroLocus (hS : SecBaseChangeAnySt) [IsAffine T.left] {th : LB.Sec (LPow P.A P.L 1 T)}
    (H : IsGenSec P.A P.L 1 th) (p : T.left) :
    ∃ q : (T ⊗ P.A).left, (fst T P.A).left q = p ∧ q ∈ nonzeroLocus th := by
  let w : Spec (CommRingCat.of (T.left.residueField p)) ⟶ T.left := T.left.fromSpecResidueField p
  let h : Over.mk (w ≫ T.hom) ⟶ T := Over.homMk w rfl
  have : IsAffine (Over.mk (w ≫ T.hom)).left := inferInstanceAs (IsAffine (Spec _))
  have h₀ := ThetaCoset.ne_zero_of_isGenSec hS P (w ≫ T.hom) (isGenSec_pullS P hS h H)
  have := P.isAb.smooth
  have : Smooth (fst (Over.mk (w ≫ T.hom)) P.A).left :=
    inferInstanceAs (Smooth (pullback.fst (w ≫ T.hom) P.A.hom))
  have : IsReduced (Over.mk (w ≫ T.hom) ⊗ P.A).left :=
    isReduced_scheme_of_smooth_of_isIntegrallyClosed (T.left.residueField p) (fst (Over.mk (w ≫ T.hom)) P.A).left
  obtain ⟨z, hz⟩ : ∃ z, z ∈ nonzeroLocus (pullS P.A 1 h th) := by
    by_contra hn
    refine h₀ (Subtype.ext (funext fun j => ?_))
    exact eq_zero_of_basicOpen_eq_bot _ (le_bot_iff.1 fun z hz => hn ⟨z, Opens.mem_iSup.2 ⟨j, hz⟩⟩)
  refine ⟨(h ▷ P.A).left z, ?_, (mem_nonzeroLocus_pullS P 1 h th z).1 hz⟩
  rw [← Scheme.Hom.comp_apply, (isPullback_whisker P.A h).w, Scheme.Hom.comp_apply]
  exact (T.left.range_fromSpecResidueField p).le ⟨_, rfl⟩

theorem map_sub_eq_zero' {R R' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup M] [AddCommGroup M'] [Module R M]
    [Module R' M'] (σ : R →+* R') (φ : M →ₛₗ[σ] M') (s t : M) (b : M') (a c d₀ e₀ : R) (d e : R')
    (ht : φ t = d • b) (hs : φ s = e • b) (hd : σ d₀ = σ a * d) (he : σ e₀ = σ c * e) :
    φ ((d₀ * c) • s - (e₀ * a) • t) = 0 := by
  rw [map_sub, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, map_mul, map_mul, ht, hs, hd, he, smul_smul, smul_smul,
    sub_eq_zero]
  congr 1
  ring

theorem isGenSec_of_fibres (hS : SecBaseChangeAnySt) [IsAffine T.left] {th : LB.Sec (LPow P.A P.L 1 T)}
    (H : ∀ p : T.left, ∃ q : (T ⊗ P.A).left, (fst T P.A).left q = p ∧ q ∈ nonzeroLocus th) :
    IsGenSec P.A P.L 1 th := by
  intro s
  let I : Ideal Γ(T.left, ⊤) := (Submodule.span Γ(T.left, ⊤)
    {SecM.ofSec P.A th}).comap (LinearMap.toSpanSingleton _ _ (SecM.ofSec P.A s))
  have key : ∀ p : T.left, ∃ f ∈ I, p ∈ T.left.basicOpen f := fun p => by
    obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl (T.hom p)
    have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
    obtain ⟨f, hf, hp⟩ := (isAffineOpen_top T.left).exists_basicOpen_le (V := T.hom ⁻¹ᵁ V) ⟨p, hV⟩ trivial
    let W := T.left.basicOpen f
    let l : overRes W ⟶ overRes (T := baseOver S) V := Over.homMk
      (IsOpenImmersion.lift V.ι (W.ι ≫ T.hom) (by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨y, rfl⟩
        exact hf y.2)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
    have hW : IsAffineOpen W := (isAffineOpen_top _).basicOpen f
    have : IsAffine (overRes W).left := hW
    obtain ⟨c, -⟩ := exists_basis P 1 b hb (overRes W) l
    have rep : ∀ x : SecM P.A P.L 1 (overRes W), ∃ d : Γ((overRes W).left, ⊤), x = d • (c hq.default :) := fun x => by
      have := c.sum_repr x
      rw [Fintype.sum_unique] at this
      exact ⟨_, this.symm⟩
    obtain ⟨d, hd⟩ := rep (pullM P.A P.L 1 (overResι W) (SecM.ofSec P.A th))
    obtain ⟨e, he⟩ := rep (pullM P.A P.L 1 (overResι W) (SecM.ofSec P.A s))
    obtain ⟨m, d₀, hd₀⟩ : ∃ (m : ℕ) (d₀ : Γ(T.left, ⊤)), (overResι W).left.appTop.hom d₀ =
        (overResι W).left.appTop.hom (f ^ m) * d := exists_pow_mul_extend f d
    obtain ⟨n, e₀, he₀⟩ : ∃ (m : ℕ) (d₀ : Γ(T.left, ⊤)), (overResι W).left.appTop.hom d₀ =
        (overResι W).left.appTop.hom (f ^ m) * e := exists_pow_mul_extend f e
    obtain ⟨N, hN⟩ := exists_pow_kill_secM P 1 f ((d₀ * f ^ n) • SecM.ofSec P.A s - (e₀ * f ^ m) • SecM.ofSec P.A th)
      (map_sub_eq_zero' _ _ _ _ _ _ _ _ _ d e hd he hd₀ he₀)
    have hu : p ∈ T.left.basicOpen d₀ := by
      obtain ⟨q, hqp, hq0⟩ := H p
      obtain ⟨z, hz, hz'⟩ := Scheme.exists_preimage_of_isPullback (isPullback_whisker P.A (overResι W)) q
        ⟨p, hp⟩ hqp
      subst hz
      obtain ⟨j, hj, u⟩ := (mem_nonzeroLocus _ _).1 ((mem_nonzeroLocus_pullS P 1 (overResι W) th z).2 hq0)
      have k := (congrArg (fun x => gs (𝟙 _) z _ (x.1 j)) hd).trans (PushInv.gs_smul P.A P.L _ 1 d _ j z hj)
      have u₁ : IsUnit (gs (fst (overRes W) P.A).left z ⊤ d) := isUnit_of_mul_isUnit_left (k ▸ u)
      rw [gs_stalkMap _ z ⊤ trivial, isUnit_map_iff, gs_eq _ _ ⊤ trivial] at u₁
      have u₂ : (fst (overRes W) P.A).left z ∈ (overRes W).left.basicOpen d := (Scheme.mem_basicOpen_top _ _ _).2 u₁
      have u₃ : (⟨p, hp⟩ : (overRes W).left) ∈ (overResι W).left ⁻¹ᵁ T.left.basicOpen d₀ := by
        rw [Scheme.preimage_basicOpen_top, hd₀, Scheme.basicOpen_mul, ← Scheme.preimage_basicOpen_top]
        refine ⟨?_, hz' ▸ u₂⟩
        change p ∈ T.left.basicOpen (f ^ m)
        rw [Scheme.mem_basicOpen_top] at hp ⊢
        rw [map_pow]
        exact hp.pow _
      exact u₃
    refine ⟨f ^ N * (d₀ * f ^ n), Submodule.mem_span_singleton.2 ⟨f ^ N * (e₀ * f ^ m), ?_⟩, ?_⟩
    · rw [smul_sub, sub_eq_zero, ← mul_smul, ← mul_smul] at hN
      exact hN.symm
    · rw [Scheme.mem_basicOpen_top] at hp hu ⊢
      simp only [map_mul, map_pow]
      exact (hp.pow _).mul (hu.mul (hp.pow _))
  have hI : Ideal.span (I : Set Γ(T.left, ⊤)) = ⊤ :=
    (isAffineOpen_top T.left).self_le_iSup_basicOpen_iff.1 fun p _ => by
      obtain ⟨f, hf, hp⟩ := key p
      exact Opens.mem_iSup.2 ⟨⟨f, hf⟩, hp⟩
  rw [Ideal.span_eq, Ideal.eq_top_iff_one] at hI
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hI
  rw [LinearMap.toSpanSingleton_apply, one_smul] at hr
  exact ⟨r, fun j => (congrArg (fun q => q.1 j) hr).symm⟩

theorem isGenSec_iff_fibres : Out.Laws2 → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (R : Type) [CommRing R] (y : Sp R ⟶ S) (th : LB.Sec (Out.LPow P.A P.L 1 (Over.mk y))), Out.IsGenSec P.A P.L 1 th ↔ ∀ p : Sp R, ∃ q : (Over.mk y ⊗ P.A).left, (fst (Over.mk y) P.A).left q = p ∧ q ∈ Out.nonzeroLocus th := by
  intro h S P R _ y th
  have : IsAffine (Over.mk y).left := inferInstanceAs (IsAffine (Spec _))
  exact ⟨exists_mem_nonzeroLocus P h.secBaseChangeAny,
    isGenSec_of_fibres P (T := Over.mk y) h.secBaseChangeAny⟩

end GlobalTheory.GenSecFibre
end
end
