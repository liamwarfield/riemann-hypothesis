module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OriginLineBundlePolarisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymmOfKsCoc
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MatrixIntertwinesAdjoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsE8IsSharpBasis
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsConstKOfLocDerK
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDerivationExtendOfFormallySmoothStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsKsMatrixOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KSField

section Linear
variable {K : Type} [Field K] {Y : Scheme.{0}} {I : Type} {U : I → Y.Opens} {g : ℕ}

theorem isCob_const_mul (q : Y ⟶ Sp K) (a : K) {c : C1 U} (h : IsCob U c) :
    IsCob U (fun i j => constFn q (U i ⊓ U j) a * c i j) := by
  have := isCob_lc q (g := 1) (fun _ => a) (fun _ => c) fun _ => h
  convert this using 1
  funext i j
  simp [lc]

theorem matrix_comb (q : Y ⟶ Sp K) {φ θ θ' θ'' : Fin g → C1 U} (hφ : ∀ c, IsCob U (lc q c φ) → c = 0)
    {Θ Θ' Θ'' : Matrix (Fin g) (Fin g) K} (c : K) (h : ∀ b, IsCob U (θ b - lc q (Θ b) φ))
    (h' : ∀ b, IsCob U (θ' b - lc q (Θ' b) φ)) (h'' : ∀ b, IsCob U (θ'' b - lc q (Θ'' b) φ))
    (e : ∀ a, IsCob U (fun i j => θ'' a i j - constFn q _ c * θ a i j - θ' a i j)) : Θ'' = c • Θ + Θ' := by
  rw [← sub_eq_zero]
  funext b
  refine hφ _ ?_
  convert (((e b).sub (h'' b)).add (isCob_const_mul q c (h b))).add (h' b) using 1
  funext i j
  have : ∀ a, constFn q (U i ⊓ U j) ((Θ'' - (c • Θ + Θ')) b a) = constFn q (U i ⊓ U j) (Θ'' b a) -
      (constFn q (U i ⊓ U j) c * constFn q (U i ⊓ U j) (Θ b a) + constFn q (U i ⊓ U j) (Θ' b a)) := fun a => by
    simp [constFn]
  simp only [lc, Pi.add_apply, Pi.sub_apply, this, sub_mul, add_mul, mul_sub, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.mul_sum, _root_.mul_assoc]
  ring

end Linear

def linearOfComb {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] (f : V → W)
    (h : ∀ (c : K) x y, f (c • x + y) = c • f x + f y) : V →ₗ[K] W where
  toFun := f
  map_add' x y := by simpa using h 1 x y
  map_smul' c x := by
    have h0 : f 0 = 0 := by simpa using h 1 0 0
    simpa [h0] using h c x 0

theorem lbIso_cube_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {s : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G s φ) {L : LB G.left} {L' : LB G'.left}
    (hL : L.IsLB) (hL' : L'.IsLB) (e : LBIso L' (L.pull φ)) {f f' : G ⟶ G} {f₀ f₀' : G' ⟶ G'}
    (hf : f₀.left ≫ φ = φ ≫ f.left) (hf' : f₀'.left ≫ φ = φ ≫ f'.left)
    (H : LBIso (cubeLB G ![fst G G ≫ f, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ f'] L)) :
    LBIso (cubeLB G' ![fst G' G' ≫ f₀, snd G' G'] L') (cubeLB G' ![fst G' G', snd G' G' ≫ f₀'] L') := by
  obtain ⟨w, hw⟩ := e
  have pa : ∀ {a : G ⟶ G} {a₀ : G' ⟶ G'}, a₀.left ≫ φ = φ ≫ a.left → ∀ {T : Over S'} (x : T ⟶ G'),
      pushPt h.1.w (x ≫ a₀) = pushPt h.1.w x ≫ a := fun ha _ x => Over.OverMorphism.ext (by
    show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
    rw [Category.assoc, ha, Category.assoc])
  let U := lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))
  have M : LBIso (L.LinComb (fun I : ULift (Finset (Fin 2)) => (psum G' ![fst G' G' ≫ f₀, snd G' G'] I.down).left ≫ φ)
        fun I => (-1) ^ (2 - I.down.card))
      (L.LinComb (fun I : ULift (Finset (Fin 2)) => (psum G' ![fst G' G', snd G' G' ≫ f₀'] I.down).left ≫ φ)
        fun I => (-1) ^ (2 - I.down.card)) := by
    refine LBIso.chartPull (chartPullSame L _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
      (chartPullSame L _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) H
    · fin_cases i
      · exact (pa hf _).trans (by simp [U])
      · simp [U]
    · fin_cases i
      · simp [U]
      · exact (pa hf' _).trans (by simp [U])
  exact LBIso.trans (DVR.linComb_isLB _ hL' _ _) (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _)
    (iso_linComb ((isGen_iff w).1 hw) _ _)
    (LBIso.trans (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _) M
      (iso_linComb ((isGen_iff w).1 hw) _ _).symm)

theorem isDerK_snd {K : Type} [Field K] {r : ℕ} (lam : (Fin r → K) →ₗ[K] K) :
    IsDerK (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom (fun x => lam x.snd) := by
  refine ⟨fun a b => by simp, fun a b => ?_⟩
  simp [TrivSqZeroExt.snd_mul]

theorem spMap_fst_dirMap {K : Type} [Field K] {r : ℕ} (lam : (Fin r → K) →ₗ[K] K) :
    spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (dirMap lam) =
      spMap (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x <;> simp [dirMap]

theorem exists_ksMatrix_of
    (href : ∀ (X : Scheme.{0}) (L : LB X), CompactSpace X → L.IsLB → ∃ L' : LB X, Finite L'.ι ∧ L'.IsLB ∧ (∀ i, IsAffineOpen (L'.U i)) ∧ LBIso L L')
    (hinv : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (v : epsR K ⟶ A₀), IsTangent v → (∃ dd, IsInvDer v dd) ∧ ∀ dd, IsInvDer v dd → (∀ W f f', dd W (f + f') = dd W f + dd W f') ∧ (∀ W f f', dd W (f * f') = f * dd W f' + f' * dd W f) ∧ (∀ W W' (f : Γ(A₀.left, W)), W' ≤ W → dd W' (rsT f W') = rsT (dd W f) W') ∧ (∀ W a, dd W (constFn A₀.hom W a) = 0) ∧ ∀ dd', IsInvDer v dd' → dd' = dd)
    (hphi : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (X : Scheme.{0}) (m : P₀.A.left ⟶ X) (L : LB X), L.IsLB → LBIso P₀.L (L.pull m) → (∃ φ, IsDlog m L dd φ) ∧ ∀ φ, IsDlog m L dd φ → (∀ a, IsCoc _ (φ a)) ∧ ∀ c, IsCob _ (lc P₀.A.hom c φ) → c = 0)
    (hcoc : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → Smooth p → ∀ (D : R → K) (I : Type) (W : I → X.Opens), IsDerK x₀ D → (∀ i, IsAffineOpen (W i)) → ∃ d θ, KSCoc A₀.hom p m D W dd d θ ∧ ∀ a, IsCoc _ (θ a))
    (hlin : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → ∀ (I : Type) (W : I → X.Opens) (D D' : R → K) (c : K) d d' d'' θ θ' θ'', KSCoc A₀.hom p m D W dd d θ → KSCoc A₀.hom p m D' W dd d' θ' → KSCoc A₀.hom p m (fun r => c * D r + D' r) W dd d'' θ'' → ∀ a, IsCob _ (fun i j => θ'' a i j - constFn A₀.hom _ c * θ a i j - θ' a i j))
    (hsym : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (P : Out.PolAV (Sp R)) (m : P₀.A.left ⟶ P.A.left) (L : LB P.A.left) [Finite L.ι] (D : R → K) (d : L.ι → ∀ O : P.A.left.Opens, Γ(P.A.left, O) → Γ(P₀.A.left, m ⁻¹ᵁ O)) (θ φ : Fin g → C1 (fun i => m ⁻¹ᵁ L.U i)), IsGrpPullback P₀.A P.A (spMap x₀) m → L.IsLB → (∀ i, IsAffineOpen (L.U i)) → LBIso P₀.L (L.pull m) → KSCoc P₀.A.hom P.A.hom m D L.U dd d θ → IsDlog m L dd φ → ∃ Θ : Matrix (Fin g) (Fin g) K, Θ.IsSymm ∧ ∀ b, IsCob (fun i => m ⁻¹ᵁ L.U i) (θ b - lc P₀.A.hom (Θ b) φ))
    (hend : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (P : Out.PolAV (Sp R)) (m : P₀.A.left ⟶ P.A.left) (L : LB P.A.left) [Finite L.ι] (D : R → K) (d : L.ι → ∀ O : P.A.left.Opens, Γ(P.A.left, O) → Γ(P₀.A.left, m ⁻¹ᵁ O)) (θ φ : Fin g → C1 (fun i => m ⁻¹ᵁ L.U i)), IsGrpPullback P₀.A P.A (spMap x₀) m → L.IsLB → (∀ i, IsAffineOpen (L.U i)) → LBIso P₀.L (L.pull m) → KSCoc P₀.A.hom P.A.hom m D L.U dd d θ → IsDlog m L dd φ → ∀ (Θ : Matrix (Fin g) (Fin g) K) (f : P.A ⟶ P.A) (f₀ f₀' : P₀.A ⟶ P₀.A) (F F' : Matrix (Fin g) (Fin g) K), (∀ b, IsCob (fun i => m ⁻¹ᵁ L.U i) (θ b - lc P₀.A.hom (Θ b) φ)) → IsMonHom f₀ → IsMonHom f₀' → f₀.left ≫ m = m ≫ f.left → LBIso (cubeLB P₀.A ![fst P₀.A P₀.A ≫ f₀, snd P₀.A P₀.A] P₀.L) (cubeLB P₀.A ![fst P₀.A P₀.A, snd P₀.A P₀.A ≫ f₀'] P₀.L) → (∀ j, IsLieComb (fun i => F i j) v (v j ≫ f₀)) → (∀ j, IsLieComb (fun i => F' i j) v (v j ≫ f₀')) → F * Θ = Θ * F'.transpose)
    (hzero : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → ∀ (I : Type) (W : I → X.Opens) (D : R → K) d θ, ⨆ i, W i = ⊤ → KSCoc A₀.hom p m D W dd d θ → (∀ a, IsCob _ (θ a)) → ∃ d₁, LocDerK A₀.hom p m D ⊤ d₁)
    (htriv : Out.Laws → ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (R : Type) [CommRing R] (xD : R →+* DualNumber K) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (ψ : A'.left ⟶ A.left) (j : A₀.left ⟶ A'.left) (d : ∀ W : A.left.Opens, Γ(A.left, W) → Γ(A₀.left, (j ≫ ψ) ⁻¹ᵁ W)), IsAbelianScheme A₀ → IsAbelianScheme A' → IsGrpPullback A' A (spMap xD) ψ → IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) j → LocDerK A₀.hom A.hom (j ≫ ψ) (fun r => (xD r).snd) ⊤ d → ∃ ρ, IsConstK A' A₀ ρ j) :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (P : Out.PolAV (Sp (TrivSqZeroExt K (Fin r → K)))) (P₀ : Out.PolAV (Sp K)) (φ₀ : P₀.A.left ⟶ P.A.left) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)), IsGrpPullback P₀.A P.A (spMap (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom) φ₀ → LBIso P₀.L (P.L.pull φ₀) → IsLieBasis v → ∃ Θ : ((Fin r → K) →ₗ[K] K) →ₗ[K] Matrix (Fin g) (Fin g) K, (∀ lam, (Θ lam).IsSymm) ∧ (∀ (f f' : P.A ⟶ P.A) (f₀ f₀' : P₀.A ⟶ P₀.A) (F F' : Matrix (Fin g) (Fin g) K), IsMonHom f → IsMonHom f' → f₀.left ≫ φ₀ = φ₀ ≫ f.left → f₀'.left ≫ φ₀ = φ₀ ≫ f'.left → LBIso (cubeLB P.A ![fst P.A P.A ≫ f, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ f'] P.L) → (∀ j, IsLieComb (fun i => F i j) v (v j ≫ f₀)) → (∀ j, IsLieComb (fun i => F' i j) v (v j ≫ f₀')) → ∀ lam, F * Θ lam = Θ lam * F'.transpose) ∧ ∀ lam, Θ lam = 0 → ∀ (G : Over (Sp (DualNumber K))) [GrpObj G] (ψ : G.left ⟶ P.A.left), IsGrpPullback G P.A (spMap (dirMap lam)) ψ → ∃ ψ₀ : G.left ⟶ P₀.A.left, IsGrpPullback G P₀.A (spMap (algebraMap K (DualNumber K))) ψ₀ ∧ ∀ io : P₀.A.left ⟶ G.left, io ≫ ψ = φ₀ → io ≫ G.hom = P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom → io ≫ ψ₀ = 𝟙 _ := by
  intro hL hL2 hC K _ _ r P P₀ φ₀ g v hp hI hv
  have hc : CompactSpace P.A.left := by
    have := P.isAb.proper
    exact QuasiCompact.compactSpace_of_compactSpace P.A.hom
  obtain ⟨L, hfin, hLB, haff, hiso⟩ := href _ P.L hc P.isLB
  have hI' : LBIso P₀.L (L.pull φ₀) := LBIso.trans P₀.isLB (pull_isLB P.isLB _) (pull_isLB hLB _) hI
    (hiso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (Geo.Tor.chartPullPull _ _ _ rfl))
  choose dd hdd using fun a => (hinv K P₀.A (v a) (hv.1 a)).1
  obtain ⟨⟨φ, hφ⟩, hφ'⟩ := hphi K P₀ g v dd hv hdd _ φ₀ L hLB hI'
  have hind := (hφ' φ hφ).2
  choose d θ hks _ using fun lam : (Fin r → K) →ₗ[K] K =>
    hcoc K P₀.A g v dd P₀.isAb.smooth hv hdd _ _ _ P.A.hom φ₀ hp.1 P.isAb.smooth _ L.ι L.U (isDerK_snd lam) haff
  choose Θ hΘ hΘ' using fun lam : (Fin r → K) →ₗ[K] K =>
    hsym hL hL2 hC K P₀ g v dd hv hdd _ _ P φ₀ L _ (d lam) (θ lam) φ hp hLB haff hI' (hks lam) hφ
  refine ⟨linearOfComb Θ fun c x y => matrix_comb P₀.A.hom hind c (hΘ' x) (hΘ' y) (hΘ' _)
    (hlin K P₀.A g v dd P₀.isAb.smooth hv hdd _ _ _ P.A.hom φ₀ hp.1 L.ι L.U _ _ c _ _ _ _ _ _ (hks x) (hks y)
      (hks (c • x + y))), hΘ, fun f f' f₀ f₀' F F' hf hf' e e' H hF hF' lam => ?_, fun lam h0 G _ ψ hψ => ?_⟩
  · exact hend K P₀ g v dd hv hdd _ _ P φ₀ L _ (d lam) (θ lam) φ hp hLB haff hI' (hks lam) hφ (Θ lam) f f₀ f₀' F F'
      (hΘ' lam) (PureType.isMonHom_over hp hp e) (PureType.isMonHom_over hp hp e') e
      (lbIso_cube_pull hp P.isLB P₀.isLB hI e e' H) hF hF'
  · have h0' : Θ lam = 0 := h0
    have hcob : ∀ a, IsCob _ (θ lam a) := fun a => by
      convert hΘ' lam a using 1
      funext i j
      simp [h0', lc, constFn]
    obtain ⟨d₁, hd₁⟩ := hzero K P₀.A g v dd P₀.isAb.smooth hv hdd _ _ _ P.A.hom φ₀ hp.1 L.ι L.U _ _ _ hLB.cover
      (hks lam) hcob
    have w : φ₀ ≫ P.A.hom = (P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ spMap (dirMap lam) := by
      rw [Category.assoc, spMap_fst_dirMap, hp.1.w]
    obtain ⟨j, hj, hj'⟩ : ∃ j : P₀.A.left ⟶ G.left, j ≫ ψ = φ₀ ∧
        j ≫ G.hom = P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom :=
      ⟨hψ.1.lift _ _ w, hψ.1.lift_fst _ _ w, hψ.1.lift_snd _ _ w⟩
    have hD : (fun x : TrivSqZeroExt K (Fin r → K) => (dirMap lam x).snd) = fun x => lam x.snd :=
      funext fun x => TrivSqZeroExt.snd_map lam x
    obtain ⟨d₂, hd₂⟩ : ∃ d₂, LocDerK P₀.A.hom P.A.hom (j ≫ ψ) (fun x => (dirMap lam x).snd) ⊤ d₂ := by
      rw [hj, hD]
      exact ⟨d₁, hd₁⟩
    obtain ⟨ρ, hρ, -, hρ'⟩ := htriv hL K P₀.A _ (dirMap lam) P.A G ψ j d₂ P₀.isAb
      (PolPull.isAbelianScheme_of_isGrpPullback P.isAb hψ) hψ
      (hψ.cancel (hp.congr (spMap_fst_dirMap lam).symm hj.symm) hj') hd₂
    refine ⟨ρ, hρ, fun io h₁ h₂ => ?_⟩
    rw [hψ.1.hom_ext (h₁.trans hj.symm) (h₂.trans hj'.symm), hρ']

end GlobalTheory.KSField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KsCocLinear
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.LinDir

theorem pbT_id {Y : Scheme.{0}} {O : Y.Opens} (s : Γ(Y, O)) : pbT (𝟙 Y) s O = s := by
  unfold pbT
  rw [dite_eq_left (show O ≤ (𝟙 Y) ⁻¹ᵁ O from le_rfl)]
  have : (𝟙 Y : Y ⟶ Y).appLE O O (show O ≤ (𝟙 Y) ⁻¹ᵁ O from le_rfl) = 𝟙 _ := by
    change 𝟙 _ ≫ Y.presheaf.map (𝟙 (Opposite.op O)) = _
    simp
  rw [this]; rfl

theorem constFn_lin {K : Type} [Field K] {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) (c x y : K) :
    constFn q O (c * x + y) - constFn q O c * constFn q O x - constFn q O y = constFn q O 0 := by
  simp [constFn]

theorem locDerK_comb {K : Type} [Field K] {Y X : Scheme.{0}} {R : Type} [CommRing R] {q : Y ⟶ Sp K} {p : X ⟶ Sp R}
    {m : Y ⟶ X} {D D' : R → K} {c : K} {W₀ : X.Opens} {d d' d'' : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)}
    (h : LocDerK q p m D W₀ d) (h' : LocDerK q p m D' W₀ d')
    (h'' : LocDerK q p m (fun r => c * D r + D' r) W₀ d'') :
    LocDerK q p m (fun _ => 0) W₀ (fun W f => d'' W f - constFn q (m ⁻¹ᵁ W) c * d W f - d' W f) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro W hW f f'
    rw [h.add W hW, h'.add W hW, h''.add W hW]; ring
  · intro W hW f f'
    rw [h.mul W hW, h'.mul W hW, h''.mul W hW]; ring
  · intro W W' l hW f
    rw [h.res W W' l hW, h'.res W W' l hW, h''.res W W' l hW, rsT_sub, rsT_sub, rsT_mul,
      rsT_constFn q (m.preimage_mono l)]
  · intro W hW r
    rw [h.base W hW, h'.base W hW, h''.base W hW, constFn_lin]

theorem locDerK_zero {K : Type} [Field K] {Y X : Scheme.{0}} {R : Type} [CommRing R] (q : Y ⟶ Sp K) (p : X ⟶ Sp R)
    (m : Y ⟶ X) (W₀ : X.Opens) : LocDerK q p m (fun _ => 0) W₀ (fun _ _ => 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro W hW f f'
    simp
  · intro W hW f f'
    simp
  · intro W W' l hW f
    rw [rsT_zero]
  · intro W hW r
    simp [constFn]

theorem basis_id (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀))
    (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)) (hs : Smooth A₀.hom) (hv : IsLieBasis v)
    (hd : ∀ a, IsInvDer (v a) (dd a)) (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R)
    (m : A₀.left ⟶ X) (hp : IsPullback m A₀.hom p (spMap x₀)) (W₀ : X.Opens)
    (d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m ⁻¹ᵁ W)) (h : LocDerK A₀.hom p m (fun _ => 0) W₀ d) :
    ∃! c : Fin g → Γ(A₀.left, m ⁻¹ᵁ W₀), ∀ W, W ≤ W₀ → ∀ f,
      d W f = ∑ a, rsT (c a) _ * dd a (m ⁻¹ᵁ W) ((m.app W).hom f) := by
  have key : ∀ (y : A₀.left ⟶ A₀.left) (m' : A₀.left ⟶ X) (q' : A₀.left ⟶ Sp K), y ≫ m = m' → y ≫ A₀.hom = q' →
      ∀ (d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m' ⁻¹ᵁ W)), LocDerK q' p m' (fun _ => 0) W₀ d →
      ∃! c : Fin g → Γ(A₀.left, m' ⁻¹ᵁ W₀), ∀ W, W ≤ W₀ → ∀ f,
        d W f = ∑ a, rsT (c a) _ * pbT y (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) _ := by
    intro y m' q' e₁ e₂ d h
    subst e₁ e₂
    exact GlobalTheory.T.invariantVectorFields_basis_verticalDerivations K A₀ g v dd hs hv hd R x₀ X p m hp _ y W₀ d h
  have := key (𝟙 _) m A₀.hom (Category.id_comp _) (Category.id_comp _) d h
  simpa only [pbT_id] using this

theorem ksCoc_linear : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → ∀ (I : Type) (W : I → X.Opens) (D D' : R → K) (c : K) d d' d'' θ θ' θ'', KSCoc A₀.hom p m D W dd d θ → KSCoc A₀.hom p m D' W dd d' θ' → KSCoc A₀.hom p m (fun r => c * D r + D' r) W dd d'' θ'' → ∀ a, IsCob _ (fun i j => θ'' a i j - constFn A₀.hom _ c * θ a i j - θ' a i j) := by
  intro K _ A₀ _ g v dd hs hv hd R _ x₀ X p m hp I W D D' c d d' d'' θ θ' θ'' h h' h'' a
  have hb := basis_id K A₀ g v dd hs hv hd R x₀ X p m hp
  choose b hbb using fun i => (hb (W i) _ (locDerK_comb (h.der i) (h'.der i) (h''.der i))).exists
  refine ⟨fun i => b i a, fun i j => ?_⟩
  have e : m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j = m ⁻¹ᵁ (W i ⊓ W j) := rfl
  have hu := (hb (W i ⊓ W j) _ (locDerK_zero A₀.hom p m _)).unique
    (y₁ := fun a => rsT (θ'' a i j - constFn A₀.hom _ c * θ a i j - θ' a i j -
      (rsT (b j a) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j) - rsT (b i a) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j))) _) (y₂ := fun _ => 0)
    (by
      intro O hO f
      have l : m ⁻¹ᵁ O ≤ m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j := (m.preimage_mono hO).trans e.ge
      have h1 := h.diff i j O hO f
      have h2 := h'.diff i j O hO f
      have h3 := h''.diff i j O hO f
      have h4 := hbb i O (hO.trans inf_le_left) f
      have h5 := hbb j O (hO.trans inf_le_right) f
      have : ∀ a, rsT (rsT (θ'' a i j - constFn A₀.hom _ c * θ a i j - θ' a i j -
          (rsT (b j a) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j) - rsT (b i a) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j))) (m ⁻¹ᵁ (W i ⊓ W j)))
          (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f) =
          rsT (θ'' a i j) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f)
          - constFn A₀.hom (m ⁻¹ᵁ O) c * (rsT (θ a i j) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f))
          - rsT (θ' a i j) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f)
          - (rsT (b j a) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f)
            - rsT (b i a) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f)) := by
        intro a
        rw [rsT_rsT e.ge (m.preimage_mono hO), rsT_sub, rsT_sub, rsT_sub, rsT_sub, rsT_mul,
          rsT_constFn _ l, rsT_rsT inf_le_left l, rsT_rsT inf_le_right l]
        ring
      simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [← h1, ← h2, ← h3, ← h4, ← h5]
      ring)
    (by
      intro O hO f
      simp only [rsT_zero, zero_mul, Finset.sum_const_zero])
  have h0 := congrArg (fun s => rsT s (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j)) (congrFun hu a)
  simp only [] at h0
  rw [rsT_rsT e.ge e.le, rsT_self, rsT_zero] at h0
  exact sub_eq_zero.1 h0

end GlobalTheory.KS.LinDir
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstFnZero
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalDerivationLiftSmoothOverField
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalDerivationLiftSmoothOverField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

noncomputable def liftConstHomK {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) :
    R →+* Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem liftConstHomK_smooth {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens)
    (hp : Smooth p) (hU : IsAffineOpen U) : (liftConstHomK p U).Smooth := by
  have h1 : (p.appLE ⊤ U (fun _ _ => trivial)).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth p hp ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (fun _ _ => trivial)
  exact RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv)) h1

theorem app_constFn_of_commK {R S : Type} [CommRing R] [CommRing S] (x₀ : R →+* S) {Y X : Scheme.{0}}
    (q : Y ⟶ Sp S) (p : X ⟶ Sp R) (m : Y ⟶ X) (h : m ≫ p = q ≫ spMap x₀) (W : X.Opens) (a : R) :
    (m.app W).hom (constFn p W a) = constFn q (m ⁻¹ᵁ W) (x₀ a) := by
  have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ W (fun _ _ => trivial) ≫ m.app W =
      CommRingCat.ofHom x₀ ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ q.appLE ⊤ (m ⁻¹ᵁ W) (fun _ _ => trivial) := by
    rw [← Category.assoc (CommRingCat.ofHom x₀), Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    congr 1
    have e1 : p.appLE ⊤ W (fun _ _ => trivial) ≫ m.app W = (m ≫ p).appLE ⊤ (m ⁻¹ᵁ W) (fun _ _ => trivial) := by
      rw [Scheme.Hom.app_eq_appLE]
      exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    have e2 : (q ≫ spMap x₀).appLE ⊤ (m ⁻¹ᵁ W) (fun _ _ => trivial) =
        (Spec.map (CommRingCat.ofHom x₀)).appTop ≫ q.appLE ⊤ (m ⁻¹ᵁ W) (fun _ _ => trivial) :=
      Scheme.Hom.comp_appLE _ _ _ _ _
    rw [e1, ← e2]
    simp only [h]
  exact congrArg (fun φ => φ.hom a) key

theorem exists_locDerK_of_smooth : ∀ (K : Type) [Field K] (R : Type) [CommRing R] (x₀ : R →+* K) (Y X : Scheme.{0}) (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → K) (W₀ : X.Opens), Smooth p → m ≫ p = q ≫ spMap x₀ → IsDerK x₀ D → IsAffineOpen W₀ → ∃ d, LocDerK q p m D W₀ d := by
  intro K _ R _ x₀ Y X q p m D W₀ hp hm hD hW
  letI : Algebra R Γ(X, W₀) := (liftConstHomK p W₀).toAlgebra
  haveI : Algebra.Smooth R Γ(X, W₀) := liftConstHomK_smooth p W₀ hp hW
  have hc : ∀ a, (m.app W₀).hom (algebraMap R Γ(X, W₀) a) = liftConstHomK q (m ⁻¹ᵁ W₀) (x₀ a) :=
    fun a => app_constFn_of_commK x₀ q p m hm W₀ a
  obtain ⟨d₀, h1, h2, h3⟩ := GlobalTheory.T.exists_derivation_extend' R Γ(X, W₀) Γ(Y, m ⁻¹ᵁ W₀) (m.app W₀).hom
    (fun r => liftConstHomK q (m ⁻¹ᵁ W₀) (D r)) (fun a b => by rw [hD.1, map_add (f := _)])
    (fun a b => by rw [hD.2, hc, hc, map_add (f := _), map_mul, map_mul])
  obtain ⟨d, hd, -⟩ := (GlobalTheory.T.existsUnique_localDerivationAlongFibreField_of_affine K R Y X q p m D W₀ hW).1 d₀ h1 h2 h3
  exact ⟨d, hd⟩

end GlobalTheory.KS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalDerivationLiftSmoothOverFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_derivation_lift_smooth_over_field : ∀ (K : Type) [Field K] (R : Type) [CommRing R] (x₀ : R →+* K) (Y X : Scheme.{0}) (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → K) (W₀ : X.Opens), Smooth p → m ≫ p = q ≫ spMap x₀ → IsDerK x₀ D → IsAffineOpen W₀ → ∃ d, LocDerK q p m D W₀ d := by
  first | exact @GlobalTheory.KS.exists_locDerK_of_smooth | exact GlobalTheory.KS.exists_locDerK_of_smooth | (intros; apply GlobalTheory.KS.exists_locDerK_of_smooth <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.Cocycle

theorem rsT_of_le {Y : Scheme.{0}} {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) :
    rsT s O = (Y.presheaf.map (homOfLE h).op).hom s := by
  unfold rsT; rw [dite_eq_left h]

theorem rsT_rsT {Y : Scheme.{0}} {O₀ O₁ O₂ : Y.Opens} (h : O₁ ≤ O₀) (h' : O₂ ≤ O₁) (s : Γ(Y, O₀)) :
    rsT (rsT s O₁) O₂ = rsT s O₂ := by
  rw [rsT_of_le h', rsT_of_le h, rsT_of_le (h'.trans h), ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem rsT_add {Y : Scheme.{0}} {O₀ O : Y.Opens} (h : O ≤ O₀) (s t : Γ(Y, O₀)) :
    rsT (s + t) O = rsT s O + rsT t O := by
  simp only [rsT_of_le h, map_add (f := _)]

theorem rsT_sub {Y : Scheme.{0}} {O₀ O : Y.Opens} (h : O ≤ O₀) (s t : Γ(Y, O₀)) :
    rsT (s - t) O = rsT s O - rsT t O := by
  simp only [rsT_of_le h, map_sub]

theorem pbT_id {Y : Scheme.{0}} {O : Y.Opens} (s : Γ(Y, O)) : pbT (𝟙 Y) s O = s := by
  unfold pbT
  rw [dite_eq_left (show O ≤ (𝟙 Y) ⁻¹ᵁ O from le_rfl)]
  have : (𝟙 Y : Y ⟶ Y).appLE O O (show O ≤ (𝟙 Y) ⁻¹ᵁ O from le_rfl) = 𝟙 _ := by
    change 𝟙 _ ≫ Y.presheaf.map (𝟙 (Opposite.op O)) = _
    simp
  rw [this]; rfl

theorem constFn_zero' {K : Type} [Field K] {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) :
    constFn q O (0 : K) = 0 := by
  simp [constFn]

theorem locDerK_sub {K : Type} [Field K] {Y X : Scheme.{0}} {R : Type} [CommRing R] {q : Y ⟶ Sp K} {p : X ⟶ Sp R}
    {m : Y ⟶ X} {D : R → K} {W₁ W₂ W₀ : X.Opens} {d₁ d₂ : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)}
    (h₁ : LocDerK q p m D W₁ d₁) (h₂ : LocDerK q p m D W₂ d₂) (l₁ : W₀ ≤ W₁) (l₂ : W₀ ≤ W₂) :
    LocDerK q p m (fun _ => 0) W₀ (fun W f => d₂ W f - d₁ W f) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro W hW f f'
    rw [h₁.add W (hW.trans l₁), h₂.add W (hW.trans l₂)]; ring
  · intro W hW f f'
    rw [h₁.mul W (hW.trans l₁), h₂.mul W (hW.trans l₂)]; ring
  · intro W W' h hW f
    rw [h₁.res W W' h (hW.trans l₁), h₂.res W W' h (hW.trans l₂), rsT_sub (m.preimage_mono h)]
  · intro W hW r
    rw [h₁.base W (hW.trans l₁), h₂.base W (hW.trans l₂), sub_self, constFn_zero']

theorem basis_id (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀))
    (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)) (hs : Smooth A₀.hom) (hv : IsLieBasis v)
    (hd : ∀ a, IsInvDer (v a) (dd a)) (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R)
    (m : A₀.left ⟶ X) (hp : IsPullback m A₀.hom p (spMap x₀)) (W₀ : X.Opens)
    (d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m ⁻¹ᵁ W)) (h : LocDerK A₀.hom p m (fun _ => 0) W₀ d) :
    ∃! c : Fin g → Γ(A₀.left, m ⁻¹ᵁ W₀), ∀ W, W ≤ W₀ → ∀ f,
      d W f = ∑ a, rsT (c a) _ * dd a (m ⁻¹ᵁ W) ((m.app W).hom f) := by
  have key : ∀ (y : A₀.left ⟶ A₀.left) (m' : A₀.left ⟶ X) (q' : A₀.left ⟶ Sp K), y ≫ m = m' → y ≫ A₀.hom = q' →
      ∀ (d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m' ⁻¹ᵁ W)), LocDerK q' p m' (fun _ => 0) W₀ d →
      ∃! c : Fin g → Γ(A₀.left, m' ⁻¹ᵁ W₀), ∀ W, W ≤ W₀ → ∀ f,
        d W f = ∑ a, rsT (c a) _ * pbT y (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) _ := by
    intro y m' q' e₁ e₂ d h
    subst e₁ e₂
    exact GlobalTheory.T.invariantVectorFields_basis_verticalDerivations K A₀ g v dd hs hv hd R x₀ X p m hp _ y W₀ d h
  have := key (𝟙 _) m A₀.hom (Category.id_comp _) (Category.id_comp _) d h
  simpa only [pbT_id] using this

theorem exists_ksCoc : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → Smooth p → ∀ (D : R → K) (I : Type) (W : I → X.Opens), IsDerK x₀ D → (∀ i, IsAffineOpen (W i)) → ∃ d θ, KSCoc A₀.hom p m D W dd d θ ∧ ∀ a, IsCoc _ (θ a) := by
  intro K _ A₀ _ g v dd hs hv hd R _ x₀ X p m hp hsp D I W hD hW
  choose d hder using fun i => GlobalTheory.T.exists_local_derivation_lift_smooth_over_field K R x₀ A₀.left X A₀.hom p m D (W i) hsp hp.w hD (hW i)
  have hb := basis_id K A₀ g v dd hs hv hd R x₀ X p m hp
  choose c hc using fun i j => (hb (W i ⊓ W j) _ (locDerK_sub (hder i) (hder j) inf_le_left inf_le_right)).exists
  have e : ∀ i j, m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j = m ⁻¹ᵁ (W i ⊓ W j) := fun i j => rfl
  have e3 : ∀ i j k, m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j ⊓ m ⁻¹ᵁ W k = m ⁻¹ᵁ (W i ⊓ W j ⊓ W k) := fun i j k => rfl
  refine ⟨d, fun a i j => rsT (c i j a) _, ⟨hder, ?_⟩, ?_⟩
  · intro i j O hO f
    rw [hc i j O hO f]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [rsT_rsT (e i j).le ((m.preimage_mono hO).trans (e i j).ge)]
  · intro a i j k
    have lij : W i ⊓ W j ⊓ W k ≤ W i ⊓ W j := inf_le_left
    have ljk : W i ⊓ W j ⊓ W k ≤ W j ⊓ W k := inf_le_inf_right _ inf_le_right
    have lik : W i ⊓ W j ⊓ W k ≤ W i ⊓ W k := inf_le_inf_right _ inf_le_left
    have hu := (hb (W i ⊓ W j ⊓ W k) _
      (locDerK_sub (hder i) (hder k) (lik.trans inf_le_left) inf_le_right)).unique
      (y₁ := fun a => rsT (c i j a) _ + rsT (c j k a) _) (y₂ := fun a => rsT (c i k a) _)
      (by
        intro O hO f
        have h1 := hc i j O (hO.trans lij) f
        have h2 := hc j k O (hO.trans ljk) f
        have : d k O f - d i O f = (d j O f - d i O f) + (d k O f - d j O f) := by ring
        rw [this, h1, h2, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [rsT_add (m.preimage_mono hO), rsT_rsT (m.preimage_mono lij) (m.preimage_mono hO),
          rsT_rsT (m.preimage_mono ljk) (m.preimage_mono hO), add_mul])
      (by
        intro O hO f
        rw [hc i k O (hO.trans lik) f]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [rsT_rsT (m.preimage_mono lik) (m.preimage_mono hO)])
    rw [rsT_rsT (e i j).le inf_le_left, rsT_rsT (e j k).le (inf_le_inf_right _ inf_le_right),
      rsT_rsT (e i k).le (inf_le_inf_right _ inf_le_left)]
    exact congrFun hu a

end GlobalTheory.KS.Cocycle
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsKsMatrix
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem GlobalTheory.KSField.exists_ksMatrix : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (P : Out.PolAV (Sp (TrivSqZeroExt K (Fin r → K)))) (P₀ : Out.PolAV (Sp K)) (φ₀ : P₀.A.left ⟶ P.A.left) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)), IsGrpPullback P₀.A P.A (spMap (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom) φ₀ → LBIso P₀.L (P.L.pull φ₀) → IsLieBasis v → ∃ Θ : ((Fin r → K) →ₗ[K] K) →ₗ[K] Matrix (Fin g) (Fin g) K, (∀ lam, (Θ lam).IsSymm) ∧ (∀ (f f' : P.A ⟶ P.A) (f₀ f₀' : P₀.A ⟶ P₀.A) (F F' : Matrix (Fin g) (Fin g) K), IsMonHom f → IsMonHom f' → f₀.left ≫ φ₀ = φ₀ ≫ f.left → f₀'.left ≫ φ₀ = φ₀ ≫ f'.left → LBIso (cubeLB P.A ![fst P.A P.A ≫ f, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ f'] P.L) → (∀ j, IsLieComb (fun i => F i j) v (v j ≫ f₀)) → (∀ j, IsLieComb (fun i => F' i j) v (v j ≫ f₀')) → ∀ lam, F * Θ lam = Θ lam * F'.transpose) ∧ ∀ lam, Θ lam = 0 → ∀ (G : Over (Sp (DualNumber K))) [GrpObj G] (ψ : G.left ⟶ P.A.left), IsGrpPullback G P.A (spMap (dirMap lam)) ψ → ∃ ψ₀ : G.left ⟶ P₀.A.left, IsGrpPullback G P₀.A (spMap (algebraMap K (DualNumber K))) ψ₀ ∧ ∀ io : P₀.A.left ⟶ G.left, io ≫ ψ = φ₀ → io ≫ G.hom = P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom → io ≫ ψ₀ = 𝟙 _ :=
  GlobalTheory.KSField.exists_ksMatrix_of GlobalTheory.FinAffineCharts.exists_finite_affine_charts GlobalTheory.KS.InvField.main GlobalTheory.KS.DlogPol.dlog_independent GlobalTheory.KS.Cocycle.exists_ksCoc GlobalTheory.KS.LinDir.ksCoc_linear GlobalTheory.KS.Sym.exists_symm_of_ksCoc GlobalTheory.KS.matrix_intertwines_adjoint GlobalTheory.KS.exists_global_locDer_of_isCob GlobalTheory.KS.exists_isConstK_of_locDerK
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsKsMatrixStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ksMatrix_alt : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (P : Out.PolAV (Sp (TrivSqZeroExt K (Fin r → K)))) (P₀ : Out.PolAV (Sp K)) (φ₀ : P₀.A.left ⟶ P.A.left) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)), IsGrpPullback P₀.A P.A (spMap (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom) φ₀ → LBIso P₀.L (P.L.pull φ₀) → IsLieBasis v → ∃ Θ : ((Fin r → K) →ₗ[K] K) →ₗ[K] Matrix (Fin g) (Fin g) K, (∀ lam, (Θ lam).IsSymm) ∧ (∀ (f f' : P.A ⟶ P.A) (f₀ f₀' : P₀.A ⟶ P₀.A) (F F' : Matrix (Fin g) (Fin g) K), IsMonHom f → IsMonHom f' → f₀.left ≫ φ₀ = φ₀ ≫ f.left → f₀'.left ≫ φ₀ = φ₀ ≫ f'.left → LBIso (cubeLB P.A ![fst P.A P.A ≫ f, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ f'] P.L) → (∀ j, IsLieComb (fun i => F i j) v (v j ≫ f₀)) → (∀ j, IsLieComb (fun i => F' i j) v (v j ≫ f₀')) → ∀ lam, F * Θ lam = Θ lam * F'.transpose) ∧ ∀ lam, Θ lam = 0 → ∀ (G : Over (Sp (DualNumber K))) [GrpObj G] (ψ : G.left ⟶ P.A.left), IsGrpPullback G P.A (spMap (dirMap lam)) ψ → ∃ ψ₀ : G.left ⟶ P₀.A.left, IsGrpPullback G P₀.A (spMap (algebraMap K (DualNumber K))) ψ₀ ∧ ∀ io : P₀.A.left ⟶ G.left, io ≫ ψ = φ₀ → io ≫ G.hom = P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom → io ≫ ψ₀ = 𝟙 _ := by
  first | exact @GlobalTheory.KSField.exists_ksMatrix | exact GlobalTheory.KSField.exists_ksMatrix | (intros; apply GlobalTheory.KSField.exists_ksMatrix <;> assumption)
end
