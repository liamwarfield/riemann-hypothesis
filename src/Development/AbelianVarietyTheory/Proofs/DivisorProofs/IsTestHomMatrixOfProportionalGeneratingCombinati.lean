module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantSecond

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGeneratorIsoBundleOfMatrixRelation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGeneratorIsoBundleOfMatrixRelation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv.CondGen

theorem gs_appLE_self {X Y : Scheme.{0}} (q : Y ⟶ X) (U : X.Opens) (W : Y.Opens) (e : W ≤ q ⁻¹ᵁ U) (z : Y)
    (hz : z ∈ W) (f : Γ(X, U)) : gs (𝟙 Y) z W ((q.appLE U W e).hom f) = gs q z U f := by
  have h1 := gs_res (𝟙 Y) z e hz ((q.app U).hom f)
  have h2 := gs_pull (𝟙 Y) q z U (e hz) f
  rw [Category.id_comp] at h2
  exact h1.trans h2

theorem gs_fsum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {n : ℕ} (a : Fin n → Γ(X, U)) :
    gs f y U (∑ i, a i) = ∑ i, gs f y U (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eq f y U h, map_sum]

end GlobalTheory.HomFixUniv.CondGen


open GlobalTheory.HomFixUniv.CondGen in
theorem GlobalTheory.HomFixUniv.isGen_of_matRel : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (R : Type) [CommRing R] (A' B' : Over (Sp R)) (Φ' : A' ⟶ B') (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) (c : Fin mA → Fin mB → Γ(Sp R, ⊤)) (u : ∀ p, Γ(A'.left, (isoLB (L := L) (M := M) k Φ' ψA ψB).U p)ˣ), GlobalTheory.HomFixUniv.Generates bA ψA A'.hom c → (∀ (j : Fin mB) (p : (Fin 1 → M.ι) × (Fin 1 → L.ι)),
      ((Φ'.left ≫ ψB).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        (u p).val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (by simp)).hom (c i j) *
          (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)) → (⟨u⟩ : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)).IsGen := by
  intro Rg _ A B _ _ L M k mA mB bA bB R _ A' B' Φ' ψA ψB c u hG hR p p'
  apply unit_ext
  intro z hz
  have hzp : z ∈ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p := hz.1
  have hzp' : z ∈ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p' := hz.2
  have hmB : (Φ'.left ≫ ψB) z ∈ LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1 :=
    GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1 hzp.1
  have hmB' : (Φ'.left ≫ ψB) z ∈ LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p'.1 :=
    GlobalTheory.HomFixMat.wchart_comp_le M _ _ p'.1 hzp'.1
  have hmA : ψA z ∈ LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2 :=
    GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2 hzp.2
  have hmA' : ψA z ∈ LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p'.2 :=
    GlobalTheory.HomFixMat.wchart_comp_le L _ _ p'.2 hzp'.2
  have key : ∀ (q : (Fin 1 → M.ι) × (Fin 1 → L.ι)), z ∈ (isoLB (L := L) (M := M) k Φ' ψA ψB).U q → ∀ j : Fin mB,
      gs (Φ'.left ≫ ψB) z (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) q.1) ((bB j).f q.1) =
        (gm (𝟙 _) z _ (u q)).val * GlobalTheory.HomFixUniv.comb bA ψA A'.hom c z q.2 j := by
    intro q hq j
    have e := congrArg (gs (𝟙 A'.left) z ((isoLB (L := L) (M := M) k Φ' ψA ψB).U q)) (hR j q)
    refine (gs_appLE_self _ _ _ _ z hq _).symm.trans (e.trans ?_)
    rw [gs_mul _ z _ hq, gs_unit _ z _ hq, gs_fsum _ z _ hq]
    unfold GlobalTheory.HomFixUniv.comb
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gs_mul _ z _ hq]
    exact congrArg₂ (· * ·) (gs_appLE_self _ _ _ _ z hq _) (gs_appLE_self _ _ _ _ z hq _)
  have tB : ∀ j : Fin mB, gs (Φ'.left ≫ ψB) z (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1) ((bB j).f p.1) =
      (trF (L := M) (fun _ : Fin 1 => (snd (topS Rg) B).left) (fun _ => (k : ℤ)) (Φ'.left ≫ ψB) z p.1 p'.1).val *
        gs (Φ'.left ≫ ψB) z (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p'.1) ((bB j).f p'.1) :=
    fun j => sec_trans (bB j) (Φ'.left ≫ ψB) z hmB hmB'
  have tA : ∀ i : Fin mA, gs ψA z (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2) ((bA i).f p.2) =
      (trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2).val *
        gs ψA z (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p'.2) ((bA i).f p'.2) :=
    fun i => sec_trans (bA i) ψA z hmA hmA'
  have tC : ∀ j : Fin mB, GlobalTheory.HomFixUniv.comb bA ψA A'.hom c z p.2 j =
      (trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2).val *
        GlobalTheory.HomFixUniv.comb bA ψA A'.hom c z p'.2 j := by
    intro j
    unfold GlobalTheory.HomFixUniv.comb
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (congrArg (_ * ·) (tA i)).trans (mul_left_comm _ _ _)
  have hg : gm (𝟙 A'.left) z _ ((isoLB (L := L) (M := M) k Φ' ψA ψB).g p p') =
      trF (L := M) (fun _ : Fin 1 => (snd (topS Rg) B).left) (fun _ => (k : ℤ)) (Φ'.left ≫ ψB) z p.1 p'.1 *
        (trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2)⁻¹ := by
    show gm (𝟙 A'.left) z _ (res _ _ * (res _ _)⁻¹) = _
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ z _ hz _).trans ?_)
      ((map_inv _ _).trans (congrArg _ ((gm_res _ z _ hz _).trans ?_))))
    · exact (gm_linComb M _ _ (𝟙 A'.left) z p.1 p'.1 hzp.1 hzp'.1).trans (by simp only [trF, Category.id_comp])
    · exact (gm_linComb L _ _ (𝟙 A'.left) z p.2 p'.2 hzp.2 hzp'.2).trans (by simp only [trF, Category.id_comp])
  obtain ⟨j, hj⟩ := hG z p.2 hmA
  refine (gm_res _ z _ hz _).trans (Eq.trans ?_ (map_mul _ _ _).symm)
  rw [hg, gm_res _ z _ hz]
  apply Units.ext
  apply hj.mul_right_cancel
  have e1 := key p hzp j
  have e2 := key p' hzp' j
  have e3 := tB j
  have e4 := tC j
  have hinv := Units.inv_mul (trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2)
  rw [e1, e2, e4] at e3
  simp only [Units.val_mul]
  rw [e4]
  set TM := (trF (L := M) (fun _ : Fin 1 => (snd (topS Rg) B).left) (fun _ => (k : ℤ)) (Φ'.left ≫ ψB) z p.1 p'.1).val
  set TL := (trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2).val
  set TLi := ((trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2)⁻¹).val
  set U' := (gm (𝟙 A'.left) z _ (u p')).val
  set C' := GlobalTheory.HomFixUniv.comb bA ψA A'.hom c z p'.2 j
  linear_combination e3 - (TM * U' * C') * hinv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGeneratorIsoBundleOfMatrixRelationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGenerator_isoBundle_of_matrix_relation : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (R : Type) [CommRing R] (A' B' : Over (Sp R)) (Φ' : A' ⟶ B') (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) (c : Fin mA → Fin mB → Γ(Sp R, ⊤)) (u : ∀ p, Γ(A'.left, (isoLB (L := L) (M := M) k Φ' ψA ψB).U p)ˣ), GlobalTheory.HomFixUniv.Generates bA ψA A'.hom c → (∀ (j : Fin mB) (p : (Fin 1 → M.ι) × (Fin 1 → L.ι)),
      ((Φ'.left ≫ ψB).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        (u p).val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (by simp)).hom (c i j) *
          (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)) → (⟨u⟩ : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)).IsGen := by
  first | (exact @GlobalTheory.HomFixUniv.isGen_of_matRel) | (exact GlobalTheory.HomFixUniv.isGen_of_matRel) | (intros; apply GlobalTheory.HomFixUniv.isGen_of_matRel  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoNormalisationAtZeroSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoNormalisationAtZeroSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
noncomputable section

namespace GlobalTheory.HomFixNorm

theorem gs_finsum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {κ : Type} (s : Finset κ)
    (a : κ → Γ(X, U)) : gs f y U (∑ i ∈ s, a i) = ∑ i ∈ s, gs f y U (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eq f y U h, map_sum]

theorem gs_npow {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) (n : ℕ) :
    gs f y U (a ^ n) = gs f y U a ^ n := by
  simp only [gs_eq f y U h, map_pow]

theorem one_comp_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G]
    [GrpObj G'] {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G f φ) : (η[G']).left ≫ φ = f ≫ (η[G]).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom hφ (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp

theorem stalkMap_gm_pow {Z Y : Scheme.{0}} (t : Z ⟶ Y) (z : Z) (V : Y.Opens) (h : t z ∈ V) (a : Γ(Y, V)ˣ) (n : ℕ) :
    (t.stalkMap z).hom ((gm (𝟙 Y) (t z) V a) ^ n).val = gs t z V a.val ^ n := by
  rw [Units.val_pow_eq_pow_val, ← gs_unit (𝟙 Y) (t z) V h, map_pow, ← gs_stalkMap t z V h]

theorem norm_at_zero : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)) (u : ∀ p, Γ(A'.left, (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)ˣ), (⨆ j, nonzeroLocus (bB j)) = ⊤ → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsTest A B L M t A' B' φA' φB' Φ' → GlobalTheory.HomFixUniv.Normal t c αA βB → (∀ (j : Fin mB) (p : (Fin 1 → M.ι) × (Fin 1 → L.ι)),
      ((Φ'.left ≫ (φB' ≫ GlobalTheory.HomFixUniv.θ B)).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        (u p).val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p) (by simp)).hom (c i j) *
          ((φA' ≫ GlobalTheory.HomFixUniv.θ A).appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)) → ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      ((zeroPt A').appLE ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_left)).hom (u p).val *
        ((t.appLE (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_right)).hom (eA.s (fun _ => p.2 0)).val) ^ k =
      ((t.appLE (LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          inf_le_right).hom (eB.s (fun _ => p.1 0)).val) ^ k := by
  intro Rg _ A B _ _ L M k mA mB bA bB eA eB αA βB R _ t A' B' _ _ φA' φB' Φ' c u hcov hA hB hT hN hrel p
  obtain ⟨gA, gB, hΦ, -⟩ := hT
  haveI : IsMonHom Φ' := hΦ
  have e₀ : zeroPt A' ≫ A'.hom = 𝟙 _ := by simp [zeroPt]
  have eΦ : zeroPt A' ≫ Φ'.left = zeroPt B' := by rw [zeroPt, zeroPt, ← Over.comp_left, IsMonHom.one_hom]
  have eA' : zeroPt A' ≫ φA' ≫ θ A = t ≫ eSec A ≫ θ A := by
    rw [← Category.assoc, zeroPt, one_comp_of_isGrpPullback gA, Category.assoc]; rfl
  have eB' : zeroPt A' ≫ Φ'.left ≫ φB' ≫ θ B = t ≫ eSec B ≫ θ B := by
    rw [← Category.assoc, eΦ, ← Category.assoc, zeroPt, one_comp_of_isGrpPullback gB, Category.assoc]; rfl
  refine fn_ext fun z hz => ?_

  have hz0 := hz
  obtain ⟨⟨hzU', hzA'⟩, hzB'⟩ := hz
  have hzU : zeroPt A' z ∈ (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p := hzU'
  have hzA : t z ∈ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) := hzA'
  have hzB : t z ∈ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0) := hzB'
  have pA : eSec A (t z) ∈ L.U (p.2 0) := Set.mem_iInter.1 hzA PUnit.unit
  have pB : eSec B (t z) ∈ M.U (p.1 0) := Set.mem_iInter.1 hzB PUnit.unit
  have mA : (eSec A ≫ θ A) (t z) ∈ LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2 := by
    refine Set.mem_iInter.2 fun i => ?_
    show (snd (topS Rg) A).left ((eSec A ≫ θ A) (t z)) ∈ L.U (p.2 i)
    rw [← Scheme.Hom.comp_apply, Category.assoc, θ_snd, Category.comp_id, Subsingleton.elim i 0]
    exact pA
  have mB : (eSec B ≫ θ B) (t z) ∈ LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1 := by
    refine Set.mem_iInter.2 fun i => ?_
    show (snd (topS Rg) B).left ((eSec B ≫ θ B) (t z)) ∈ M.U (p.1 i)
    rw [← Scheme.Hom.comp_apply, Category.assoc, θ_snd, Category.comp_id, Subsingleton.elim i 0]
    exact pB
  have sB : ∀ j, gs (zeroPt A') z ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
      (((Φ'.left ≫ (φB' ≫ θ B)).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1)) =
        gs t z ⊤ (βB j) * gs t z (LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0)) (eB.s (fun _ => p.1 0)).val ^ k := by
    intro j
    have v := hB j (t z) p.1 mB
    erw [gs_appLE _ _ _ _ _ _ hzU]
    rw [eB']
    erw [gs_comp t _ z _ mB]
    erw [v]
    simp only [GlobalTheory.HomFixUniv.uFr]
    rw [map_mul]
    erw [stalkMap_gm_pow t z _ hzB, ← gs_stalkMap t z ⊤ trivial]
  have sA : ∀ i, gs (zeroPt A') z ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
      (((φA' ≫ θ A).appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)) =
        gs t z ⊤ (αA i) * gs t z (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0)) (eA.s (fun _ => p.2 0)).val ^ k := by
    intro i
    have v := hA i (t z) p.2 mA
    erw [gs_appLE _ _ _ _ _ _ hzU]
    rw [eA']
    erw [gs_comp t _ z _ mA]
    erw [v]
    simp only [GlobalTheory.HomFixUniv.uFr]
    rw [map_mul]
    erw [stalkMap_gm_pow t z _ hzA, ← gs_stalkMap t z ⊤ trivial]
  have sC : ∀ i j, gs (zeroPt A') z ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
      ((A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p) (by simp)).hom (c i j)) =
        gs (𝟙 _) z ⊤ (c i j) := by
    intro i j
    erw [gs_appLE _ _ _ _ _ _ hzU]
    rw [e₀]
  have gt : ∀ x : Γ(Sp Rg, ⊤), gs t z ⊤ x = gs (𝟙 _) z ⊤ (t.appTop x) := by
    intro x
    have e := gs_pull (𝟙 (Sp R)) t z ⊤ trivial x
    rw [Category.id_comp] at e
    exact e.symm
  have nN : ∀ j, ∑ i, gs (𝟙 _) z ⊤ (c i j) * gs t z ⊤ (αA i) = gs t z ⊤ (βB j) := by
    intro j
    rw [gt, hN j, gs_finsum _ z ⊤ trivial]
    exact Finset.sum_congr rfl fun i _ => by rw [gt, gs_mul _ z ⊤ trivial]
  have hcz : (eSec B ≫ θ B) (t z) ∈ (⨆ j, nonzeroLocus (bB j)) := by rw [hcov]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hcz
  have hu := (GlobalTheory.mem_nonzeroLocus_iff_pull (bB j) (eSec B ≫ θ B) (t z) mB).1 hj
  erw [hB j (t z) p.1 mB] at hu
  have hβ : IsUnit (gs t z ⊤ (βB j)) := by
    rw [gs_stalkMap t z ⊤ trivial]
    exact (isUnit_of_mul_isUnit_left hu).map _
  have E := congrArg (gs (zeroPt A') z ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)) (hrel j p)
  rw [sB j, gs_mul _ _ _ hzU, gs_finsum _ _ _ hzU] at E
  simp only [gs_mul _ _ _ hzU, sC, sA] at E
  have hs : ∑ i, gs (𝟙 _) z ⊤ (c i j) * (gs t z ⊤ (αA i) * gs t z (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0)) (eA.s (fun _ => p.2 0)).val ^ k) =
      (∑ i, gs (𝟙 _) z ⊤ (c i j) * gs t z ⊤ (αA i)) * gs t z (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0)) (eA.s (fun _ => p.2 0)).val ^ k := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
  rw [hs, nN j] at E
  rw [gs_mul _ z _ hz0, gs_npow _ z _ hz0, gs_npow _ z _ hz0]
  erw [gs_appLE _ _ _ _ _ _ hz0, gs_appLE _ _ _ _ _ _ hz0, gs_appLE _ _ _ _ _ _ hz0]
  simp only [Category.id_comp]
  exact hβ.mul_left_cancel (by rw [E]; ring)

end GlobalTheory.HomFixNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoNormalisationAtZeroSectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isoNormalisation_at_zeroSection : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)) (u : ∀ p, Γ(A'.left, (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)ˣ), (⨆ j, nonzeroLocus (bB j)) = ⊤ → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsTest A B L M t A' B' φA' φB' Φ' → GlobalTheory.HomFixUniv.Normal t c αA βB → (∀ (j : Fin mB) (p : (Fin 1 → M.ι) × (Fin 1 → L.ι)),
      ((Φ'.left ≫ (φB' ≫ GlobalTheory.HomFixUniv.θ B)).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        (u p).val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p) (by simp)).hom (c i j) *
          ((φA' ≫ GlobalTheory.HomFixUniv.θ A).appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)) → ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      ((zeroPt A').appLE ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_left)).hom (u p).val *
        ((t.appLE (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_right)).hom (eA.s (fun _ => p.2 0)).val) ^ k =
      ((t.appLE (LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          inf_le_right).hom (eB.s (fun _ => p.1 0)).val) ^ k := by
  first | (exact @GlobalTheory.HomFixNorm.norm_at_zero) | (exact GlobalTheory.HomFixNorm.norm_at_zero) | (intros; apply GlobalTheory.HomFixNorm.norm_at_zero  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTestHomMatrixOfProportionalGeneratingCombinati
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixCond

theorem unit_of_proportional {X : Scheme.{0}} {V : X.Opens} {m : ℕ} (B C : Fin m → Γ(X, V))
    (hC : ∀ x ∈ V, ∃ j, IsUnit (gs (𝟙 X) x V (C j)))
    (hB : ∀ x ∈ V, ∃ j, IsUnit (gs (𝟙 X) x V (B j)))
    (hP : ∀ x ∈ V, ∀ j j', gs (𝟙 X) x V (B j) * gs (𝟙 X) x V (C j') =
      gs (𝟙 X) x V (B j') * gs (𝟙 X) x V (C j)) :
    ∃ u : Γ(X, V)ˣ, ∀ j, B j = u.val * C j := by
  let W : Fin m → X.Opens := fun j => X.basicOpen (C j)
  have lW : ∀ j, W j ≤ V := fun j => X.basicOpen_le _
  have uC : ∀ j, ∀ y ∈ W j, IsUnit (gs (𝟙 X) y V (C j)) := fun j y hy =>
    (GlobalTheory.LBGerm.isUnit_gs_iff (𝟙 X) y V (lW j hy) (C j)).2 hy
  have uB : ∀ j, ∀ y ∈ W j, IsUnit (gs (𝟙 X) y V (B j)) := fun j y hy => by
    obtain ⟨j', hj'⟩ := hB y (lW j hy)
    have e := hP y (lW j hy) j' j
    have h2 := hj'.mul (uC j y hy)
    rw [e] at h2
    exact isUnit_of_mul_isUnit_left h2
  have hu : ∀ j, IsUnit (resG X (lW j) (C j)) := fun j =>
    X.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      have := uC j y hy
      rw [← gs_res (𝟙 X) y (lW j) hy, gs_eq _ y _ hy] at this
      exact this
  let w : ∀ j, Γ(X, W j) := fun j => resG X (lW j) (B j) * ((hu j).unit⁻¹).val
  have hw : ∀ j, ∀ y ∈ W j, gs (𝟙 X) y (W j) (w j) * gs (𝟙 X) y V (C j) = gs (𝟙 X) y V (B j) := fun j y hy => by
    rw [← gs_res (𝟙 X) y (lW j) hy (C j), ← gs_mul _ y _ hy, _root_.mul_assoc]
    show gs (𝟙 X) y (W j) (resG X (lW j) (B j) * (((hu j).unit⁻¹).val * (hu j).unit.val)) = _
    rw [Units.inv_mul, _root_.mul_one, gs_res _ y _ hy]
  have wu : ∀ j, IsUnit (w j) := fun j => X.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    have e := hw j y hy
    have h1 : IsUnit (gs (𝟙 X) y (W j) (w j)) := by
      have := uB j y hy
      rw [← e] at this
      exact isUnit_of_mul_isUnit_left this
    rw [gs_eq _ y _ hy] at h1
    exact h1
  obtain ⟨s, hs⟩ := glue_unit V W lW (fun y hy => by
      obtain ⟨j, hj⟩ := hC y hy
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, (GlobalTheory.LBGerm.isUnit_gs_iff (𝟙 X) y V hy (C j)).1 hj⟩)
    (fun j => (wu j).unit) (fun i j y hy => by
      apply Units.ext
      rw [← gs_unit _ y _ hy.1, ← gs_unit _ y _ hy.2]
      refine (uC i y hy.1).mul_right_cancel ?_
      refine (uC j y hy.2).mul_right_cancel ?_
      show gs (𝟙 X) y (W i) (w i) * gs (𝟙 X) y V (C i) * gs (𝟙 X) y V (C j) =
        gs (𝟙 X) y (W j) (w j) * gs (𝟙 X) y V (C i) * gs (𝟙 X) y V (C j)
      rw [hw i y hy.1, mul_right_comm, hw j y hy.2, hP y (lW i hy.1) i j])
  refine ⟨s, fun j => fn_ext fun y hy => ?_⟩
  obtain ⟨i, hi⟩ := hC y hy
  have yi : y ∈ W i := (GlobalTheory.LBGerm.isUnit_gs_iff (𝟙 X) y V hy (C i)).1 hi
  have es : gs (𝟙 X) y V s.val = gs (𝟙 X) y (W i) (w i) := by
    rw [← gs_res (𝟙 X) y (lW i) yi]
    exact congrArg (fun q : Γ(X, W i)ˣ => gs (𝟙 X) y (W i) q.val) (hs i)
  rw [gs_mul _ y _ hy, es]
  refine hi.mul_right_cancel ?_
  rw [mul_right_comm, hw i y yi, hP y hy i j]

theorem gs_finsum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {n : ℕ} (a : Fin n → Γ(X, U)) :
    gs f y U (∑ i, a i) = ∑ i, gs f y U (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eq f y U h, map_sum]

theorem isMat_of_conditions : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), L.IsLB → M.IsLB → eA.IsGen → eB.IsGen → (⨆ j, nonzeroLocus (bB j)) = ⊤ → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsTest A B L M t A' B' φA' φB' Φ' → GlobalTheory.HomFixUniv.Generates bA (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom c → GlobalTheory.HomFixUniv.Proport bA bB (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom (Φ'.left ≫ φB' ≫ GlobalTheory.HomFixUniv.θ B) c → GlobalTheory.HomFixUniv.Normal t c αA βB → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c := by
  intro Rg _ A B _ _ L M k mA mB bA bB eA eB αA βB R _ t A' B' _ _ φA' φB' Φ' c hL hM heA heB hcov hvA hvB hT hgen
    hprop hnorm
  have key : ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      ∃ u : Γ(A'.left, (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)ˣ, ∀ j : Fin mB,
        ((Φ'.left ≫ φB' ≫ θ B).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        u.val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p) (by simp)).hom
          (c i j) *
          ((φA' ≫ θ A).appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2) := by
    intro p
    set V := (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p with hV
    have mB' : ∀ z ∈ V, (Φ'.left ≫ φB' ≫ θ B) z ∈ LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1 :=
      fun z hz => GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1 hz.1
    have mA' : ∀ z ∈ V, (φA' ≫ θ A) z ∈ LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2 :=
      fun z hz => GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2 hz.2
    have gB : ∀ z ∈ V, ∀ j : Fin mB, gs (𝟙 A'.left) z V
        (((Φ'.left ≫ φB' ≫ θ B).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1) V
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1)) =
        gs (Φ'.left ≫ φB' ≫ θ B) z (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1) ((bB j).f p.1) :=
      fun z hz j => (gs_appLE _ _ _ _ (𝟙 A'.left) z hz _).trans (by rw [Category.id_comp])
    have gC : ∀ z ∈ V, ∀ j : Fin mB, gs (𝟙 A'.left) z V (∑ i, (A'.hom.appLE ⊤ V (by simp)).hom (c i j) *
          ((φA' ≫ θ A).appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2) V
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)) =
        comb bA (φA' ≫ θ A) A'.hom c z p.2 j := fun z hz j => by
      rw [gs_finsum _ z _ hz]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [gs_mul _ z _ hz]
      refine congrArg₂ (· * ·) ((gs_appLE _ _ _ _ (𝟙 A'.left) z hz _).trans (by rw [Category.id_comp]))
        ((gs_appLE _ _ _ _ (𝟙 A'.left) z hz _).trans (by rw [Category.id_comp]; rfl))
    obtain ⟨u, hu⟩ := unit_of_proportional (V := V)
      (fun j => ((Φ'.left ≫ φB' ≫ θ B).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1) V
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1))
      (fun j => ∑ i, (A'.hom.appLE ⊤ V (by simp)).hom (c i j) *
          ((φA' ≫ θ A).appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2) V
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2))
      (fun z hz => by
        obtain ⟨j, hj⟩ := hgen z p.2 (mA' z hz)
        exact ⟨j, by rw [gC z hz j]; exact hj⟩)
      (fun z hz => by
        obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge (Set.mem_univ ((Φ'.left ≫ φB' ≫ θ B) z)))
        exact ⟨j, by rw [gB z hz j]; exact (GlobalTheory.mem_nonzeroLocus_iff_pull (bB j) _ z (mB' z hz)).1 hj⟩)
      (fun z hz j j' => by
        rw [gB z hz j, gB z hz j', gC z hz j, gC z hz j']
        exact hprop z p.2 p.1 (mA' z hz) (mB' z hz) j j')
    exact ⟨u, hu⟩
  choose u hu using key
  refine ⟨φA' ≫ θ A, φB' ≫ θ B, ⟨u⟩, by rw [Category.assoc, θ_snd, Category.comp_id],
    by rw [Category.assoc, θ_snd, Category.comp_id], ?_, ?_, fun j p => hu p j⟩
  · exact GlobalTheory.T.isGenerator_isoBundle_of_matrix_relation Rg A B L M k mA mB bA bB R A' B' Φ' (φA' ≫ θ A) (φB' ≫ θ B) c u hgen (fun j p => hu p j)
  · exact GlobalTheory.T.isoNormalisation_at_zeroSection Rg A B L M k mA mB bA bB eA eB αA βB R t A' B' φA' φB' Φ' c u hcov hvA hvB hT hnorm
      (fun j p => hu p j)

end GlobalTheory.HomFixCond
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTestHomMatrixOfProportionalGeneratingCombinatiStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTestHomMatrix_of_proportional_generating_combinations : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), L.IsLB → M.IsLB → eA.IsGen → eB.IsGen → (⨆ j, nonzeroLocus (bB j)) = ⊤ → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsTest A B L M t A' B' φA' φB' Φ' → GlobalTheory.HomFixUniv.Generates bA (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom c → GlobalTheory.HomFixUniv.Proport bA bB (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom (Φ'.left ≫ φB' ≫ GlobalTheory.HomFixUniv.θ B) c → GlobalTheory.HomFixUniv.Normal t c αA βB → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c := by
  first | (exact @GlobalTheory.HomFixCond.isMat_of_conditions) | (exact GlobalTheory.HomFixCond.isMat_of_conditions) | (intros; apply GlobalTheory.HomFixCond.isMat_of_conditions  <;> assumption)
end
