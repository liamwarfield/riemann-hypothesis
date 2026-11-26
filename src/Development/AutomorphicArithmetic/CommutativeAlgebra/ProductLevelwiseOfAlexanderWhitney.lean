module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.HomAcyclicOfIsoOfIsZeroOfBiproduct

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.MemPullbackImageIffFactorsThroughOpen
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private noncomputable abbrev evF (p : ℕ) (W : Scheme.{0}) : Spc ⥤ Type :=
  ((evaluation SimplexCategoryᵒᵖ PSh).obj (op (SimplexCategory.mk p))) ⋙
    ((evaluation Scheme.{0}ᵒᵖ Type).obj (op W))

theorem UpperTheory.mem_pullbackImage_iff_factors_through_open :
    ∀ {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (p : ℕ) (W : Scheme.{0}) (z : Sx E p W), ((Sub.img (E := E) (pullback.fst π (sch.map U.ι))).mem p W z ↔ ∃ w : W ⟶ U.toScheme, w ≫ U.ι = under π z) ∧ (∀ (V : Scheme.{0}) (g : V ⟶ W), under π (z.res g) = g ≫ under π z) ∧ ∀ (r : ℕ) (θ : SimplexCategory.mk r ⟶ SimplexCategory.mk p), under π (z.along θ) = under π z := by
  intro X U E π p W z
  have hpb : IsPullback ((evF p W).map (pullback.fst π (sch.map U.ι)))
      ((evF p W).map (pullback.snd π (sch.map U.ι))) ((evF p W).map π)
      ((evF p W).map (sch.map U.ι)) := (IsPullback.of_hasPullback π (sch.map U.ι)).map (evF p W)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨y, rfl⟩
    refine ⟨(evF p W).map (pullback.snd π (sch.map U.ι)) y, ?_⟩
    exact (ConcreteCategory.congr_hom hpb.w y).symm
  · rintro ⟨w, hw⟩
    obtain ⟨y, hy, -⟩ := Types.exists_of_isPullback hpb z (show Sx (sch.obj U.toScheme) p W from w) hw.symm
    exact ⟨y, hy⟩
  · intro V g
    exact ConcreteCategory.congr_hom ((π.app (op (SimplexCategory.mk p))).naturality g.op) z
  · intro r θ
    exact congrFun (congrArg (fun t => t.app (op W)) (π.naturality θ.op)) z
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.RelativeCupProductLevelwiseCompat
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ColumnExactZeroOfTotalExactOfVerticalZero
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

namespace UpperTheory.ExtensionByZero

private noncomputable def ext0 (C : DC) (s : ℤ) (a : C.A 0 s) : C.Tot
  | 0, t => (Pi.single s a : ∀ t, C.A 0 t) t
  | _ + 1, _ => 0

private theorem extByZero_same (C : DC) (s : ℤ) (a : C.A 0 s) : ext0 C s a 0 s = a :=
  Pi.single_eq_same (M := fun t => C.A 0 t) s a

private theorem unitCharacterExtendByZero_ne_zero_of_isUnit (C : DC) (s : ℤ) (a : C.A 0 s) {t : ℤ} (h : t ≠ s) : ext0 C s a 0 t = 0 :=
  Pi.single_eq_of_ne (M := fun t => C.A 0 t) h a

private theorem extByZero_succ (C : DC) (s : ℤ) (a : C.A 0 s) (p : ℕ) (t : ℤ) : ext0 C s a (p + 1) t = 0 := rfl

private theorem extByZero_degree (C : DC) (s : ℤ) (a : C.A 0 s) : C.Deg s (ext0 C s a) := by
  intro p t h
  rcases p with _ | p
  · exact unitCharacterExtendByZero_ne_zero_of_isUnit C s a (fun e => h (by simp [e]))
  · rfl

private theorem d_idx (C : DC) (f : ∀ t, C.A 0 t) {u s : ℤ} (t : ℤ) (h : u = s) :
    C.d 0 u t (f u) = C.d 0 s t (f s) := by
  subst h; rfl

end UpperTheory.ExtensionByZero

open UpperTheory.ExtensionByZero in
theorem UpperTheory.columnExact_zero_of_totalExact_of_vertical_zero :
    ∀ (C C' : DC) (Φ : C.Hom C'), (∀ s x, C.δ 0 s x = 0) → (∀ s x, C'.δ 0 s x = 0) → Φ.TotEx → Φ.ColEx 0 := by
  intro C C' Φ h0 h0' hT s a y hda hΦ
  have hD : C.D (s + 1) (ext0 C (s + 1) a) = 0 := by
    funext p t
    rcases p with _ | p
    · change C.d 0 (t - 1) t (ext0 C (s + 1) a 0 (t - 1)) = 0
      by_cases h : t - 1 = s + 1
      · obtain rfl : t = s + 1 + 1 := by omega
        rw [d_idx C (ext0 C (s + 1) a 0) _ h, extByZero_same]
        exact hda
      · rw [unitCharacterExtendByZero_ne_zero_of_isUnit C _ a h, map_zero]
    · change C.d (p + 1) (t - 1) t (ext0 C (s + 1) a (p + 1) (t - 1)) +
        (s + 1 + 1).negOnePow • C.δ p t (ext0 C (s + 1) a p t) = 0
      rw [extByZero_succ, map_zero, zero_add]
      rcases p with _ | p
      · rw [h0, smul_zero]
      · rw [extByZero_succ, map_zero, smul_zero]
  have hE : Φ.tot (ext0 C (s + 1) a) = C'.D s (ext0 C' s y) := by
    funext p t
    rcases p with _ | p
    · change Φ 0 t (ext0 C (s + 1) a 0 t) = C'.d 0 (t - 1) t (ext0 C' s y 0 (t - 1))
      by_cases h : t = s + 1
      · subst h
        rw [d_idx C' (ext0 C' s y 0) _ (by omega : s + 1 - 1 = s), extByZero_same, extByZero_same]
        exact hΦ
      · rw [unitCharacterExtendByZero_ne_zero_of_isUnit C _ a h, unitCharacterExtendByZero_ne_zero_of_isUnit C' _ y (fun e => h (by omega)), map_zero, map_zero]
    · change Φ (p + 1) t (ext0 C (s + 1) a (p + 1) t) =
        C'.d (p + 1) (t - 1) t (ext0 C' s y (p + 1) (t - 1)) +
          (s + 1).negOnePow • C'.δ p t (ext0 C' s y p t)
      rw [extByZero_succ, extByZero_succ, map_zero, map_zero, zero_add]
      rcases p with _ | p
      · rw [h0', smul_zero]
      · rw [extByZero_succ, map_zero, smul_zero]
  obtain ⟨a', y', -, -, h1, h2⟩ :=
    hT s (ext0 C (s + 1) a) (ext0 C' s y) (extByZero_degree C _ a) (extByZero_degree C' _ y) hD hE
  refine ⟨a' 0 s, y' 0 (s - 1), ?_, ?_⟩
  · have h := congrFun (congrFun h1 0) (s + 1)
    change C.d 0 (s + 1 - 1) (s + 1) (a' 0 (s + 1 - 1)) = ext0 C (s + 1) a 0 (s + 1) at h
    rw [d_idx C (a' 0) _ (by omega : s + 1 - 1 = s), extByZero_same] at h
    exact h
  · have h := congrFun (congrFun h2 0) s
    rw [show ext0 C' s y 0 s = y from extByZero_same C' s y] at h
    exact h
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem units_map_smul {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) (η : ℤˣ) (x : A) :
    f (η • x) = η • f x := by
  simp [Units.smul_def]

private theorem colEx_transfer {C C' D D' : DC} (Φ : C.Hom C') (Ψ : D.Hom D') (p : ℕ) (η : ℤˣ)
    (e : ∀ s, C.A p s ≃+ D.A 0 s) (e' : ∀ s, C'.A p s ≃+ D'.A 0 s)
    (hd : ∀ s t x, e t (C.d p s t x) = D.d 0 s t (e s x))
    (hd' : ∀ s t x, e' t (C'.d p s t x) = D'.d 0 s t (e' s x))
    (hΦ : ∀ s x, e' s (Φ p s x) = η • Ψ 0 s (e s x)) (h : Ψ.ColEx 0) : Φ.ColEx p := by
  have hηη : ∀ {A : Type 1} [AddCommGroup A] (x : A), η • η • x = x := fun x => by
    rw [smul_smul, Int.units_mul_self, one_smul]
  intro s a y ha hy
  have hΨ : ∀ s x, Ψ 0 s (e s x) = η • e' s (Φ p s x) := fun s x => by rw [hΦ, hηη]
  obtain ⟨a', y', h1, h2⟩ := h s (e _ a) (η • e' s y)
    (by rw [← hd, ha, map_zero])
    (by rw [hΨ, hy, hd', units_map_smul])
  refine ⟨(e s).symm a', η • (e' _).symm y', ?_, ?_⟩
  · apply (e _).injective
    rw [hd, AddEquiv.apply_symm_apply, h1]
  · apply (e' _).injective
    have h3 : e' s y = η • (Ψ 0 s a' + D'.d 0 (s - 1) s y') := by rw [← h2, hηη]
    have h4 : e' (s - 1) (η • (e' (s - 1)).symm y') = η • y' := by
      have := units_map_smul (e' (s - 1)).toAddMonoidHom η ((e' (s - 1)).symm y')
      simpa using this
    rw [h3, map_add (f := _), hΦ, hd', AddEquiv.apply_symm_apply, h4, units_map_smul, smul_add]

private def lvl {R : Type} [CommRing R] {E : Spc} {p : ℕ} (Z : Sub E)
    (Z' : Sub (disc.obj (E.obj (op (SimplexCategory.mk p)))))
    (h : ∀ (W : Scheme.{0}) (z : Sx E p W), Z'.mem 0 W z ↔ Z.mem p W z) (M : Shv R) :
    Fam Z p M ≃+ Fam Z' 0 M where
  toFun a := ⟨a.1, a.2.1, fun U x hx => a.2.2 U x ((h U x).1 hx)⟩
  invFun a := ⟨a.1, a.2.1, fun U x hx => a.2.2 U x ((h U x).2 hx)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

private theorem disc_δ {R : Type} [CommRing R] {F : PSh} (Z : Sub (disc.obj F)) (L : Cx R) (m s : ℤ)
    (x : (famDC Z L m).A 0 s) : (famDC Z L m).δ 0 s x = 0 := by
  apply Subtype.ext
  funext U z
  have hf : ∀ i, Sx.face (E := disc.obj F) z i = z := fun _ => rfl
  change m.negOnePow • ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (show Fam Z 0 (L.X (s + m)) from x).1 U (Sx.face (E := disc.obj F) z i) = 0
  simp [Fin.sum_univ_two, hf]

private theorem fam_smul {R : Type} [CommRing R] {E : Spc} (Z : Sub E) (p : ℕ) (M : Shv R) (η : ℤˣ) (a : Fam Z p M)
    (W : Scheme.{0}) (z : Sx E p W) : (η • a).1 W z = η • a.1 W z := by
  rcases Int.units_eq_one_or η with rfl | rfl <;> simp

theorem UpperTheory.relativeCupProduct_levelwise_compat :
    ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (m : ℤ) (β : Sec (J.X m) X) (p : ℕ)
    (Φ : (famDC (Sub.bot E) I 0).Hom (famDC (Sub.img (E := E) (pullback.fst π (sch.map U.ι))) K m))
    (Ψ : (famDC (Sub.bot (disc.obj (E.obj (op (SimplexCategory.mk p))))) I 0).Hom (famDC (Sub.img (E := disc.obj (E.obj (op (SimplexCategory.mk p)))) (pullback.fst (show disc.obj (E.obj (op (SimplexCategory.mk p))) ⟶ sch.obj X from disc.map (π.app (op (SimplexCategory.mk p)))) (sch.map U.ι))) K m)),
    IsProd μ π β Φ → IsProd μ (show disc.obj (E.obj (op (SimplexCategory.mk p))) ⟶ sch.obj X from disc.map (π.app (op (SimplexCategory.mk p)))) β Ψ → Ψ.TotEx → Φ.ColEx p := by
  intro R _ I J K μ X U E π m β p Φ Ψ hΦ hΨ hT
  have h0 : Ψ.ColEx 0 := UpperTheory.columnExact_zero_of_totalExact_of_vertical_zero _ _ Ψ (disc_δ _ _ _) (disc_δ _ _ _) hT
  have hbot : ∀ (W : Scheme.{0}) (z : Sx E p W),
      (Sub.bot (disc.obj (E.obj (op (SimplexCategory.mk p))))).mem 0 W z ↔ (Sub.bot E).mem p W z :=
    fun _ _ => Iff.rfl
  have himg : ∀ (W : Scheme.{0}) (z : Sx E p W),
      (Sub.img (E := disc.obj (E.obj (op (SimplexCategory.mk p)))) (pullback.fst (show disc.obj (E.obj (op (SimplexCategory.mk p))) ⟶ sch.obj X from disc.map (π.app (op (SimplexCategory.mk p)))) (sch.map U.ι))).mem 0 W z ↔
        (Sub.img (E := E) (pullback.fst π (sch.map U.ι))).mem p W z := fun W z =>
    ((UpperTheory.mem_pullbackImage_iff_factors_through_open U (show disc.obj (E.obj (op (SimplexCategory.mk p))) ⟶ sch.obj X from disc.map (π.app (op (SimplexCategory.mk p)))) 0 W z).1).trans
      ((UpperTheory.mem_pullbackImage_iff_factors_through_open U π p W z).1).symm
  refine colEx_transfer Φ Ψ p (m * (p : ℤ)).negOnePow (fun s => lvl _ _ hbot _) (fun s => lvl _ _ himg _)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) ?_ h0
  intro s x
  apply Subtype.ext
  funext W z
  have h1 := hΦ p s x W z
  have h2 := hΨ 0 s (lvl _ _ hbot _ x) W z
  refine Eq.trans h1 (Eq.trans ?_ (fam_smul _ _ _ (m * (p : ℤ)).negOnePow (Ψ 0 s (lvl _ _ hbot _ x)) W z).symm)
  refine congrArg _ (Eq.trans ?_ h2.symm)
  have h0' : (m * ((0 : ℕ) : ℤ)).negOnePow = 1 := by simp
  rw [h0', one_smul]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.RelativeCupProductRealizesProductOfRepresentativ
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem inl_fold' (P : Arrow Spc) : dbl.inl P ≫ dbl.fold P = 𝟙 _ := pushout.inl_desc (f := P.hom) (g := P.hom) _ _ _

private theorem inl_map' {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P :=
  pushout.inl_desc (f := P'.hom) (g := P'.hom) _ _ _

private theorem aw_last {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {D : Spc} {n m : ℤ}
    (α : Cochain ((chains R).obj D) I n) (β : Cochain ((chains R).obj D) J m) {W : Scheme.{0}} {p : ℕ}
    (x : Sx D p W) (b : Sec (J.X m) W) (hp : p + 0 ≤ p)
    (hb : ev β 0 m (by simp) W (x.sub p 0 hp) = b) (r k : ℕ) (hr : r = p) (hk : k = 0) (s t w : ℤ) (h : s + t = w)
    (hs : -(r : ℤ) + n = s) (ht : -(k : ℤ) + m = t) (h0 : 0 + r ≤ p) (h1 : r + k ≤ p)
    (s' : ℤ) (hs' : -(p : ℤ) + n = s') (h' : s' + m = w) :
    μ.mul W s t w h (ev α r s hs W (x.sub 0 r h0)) (ev β k t ht W (x.sub r k h1)) =
      μ.mul W s' m w h' (ev α p s' hs' W x) b := by
  subst hr hk
  have ht' : m = t := by simpa using ht
  subst ht'
  subst hs
  subst hs'
  rw [(GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite x).2.1, hb]

private theorem aw_eval {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {D : Spc} {n m : ℤ}
    (α : Cochain ((chains R).obj D) I n) (β : Cochain ((chains R).obj D) J m)
    (γ : Cochain ((chains R).obj D) K (n + m)) (hγ : μ.IsAW rfl α β γ)
    (hβ : ∀ (k : ℕ), 0 < k → ∀ (s : ℤ) h (W : Scheme.{0}) (y : Sx D k W), ev β k s h W y = 0)
    {W : Scheme.{0}} {p : ℕ} (x : Sx D p W) (b : Sec (J.X m) W) (hp : p + 0 ≤ p)
    (hb : ev β 0 m (by simp) W (x.sub p 0 hp) = b) (w : ℤ) (h : -(p : ℤ) + (n + m) = w)
    (s : ℤ) (hs : -(p : ℤ) + n = s) (h' : s + m = w) :
    ev γ p w h W x = (m * (p : ℕ)).negOnePow • μ.mul W s m w h' (ev α p s hs W x) b := by
  rw [hγ p w h W x, Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add]
  · exact congrArg _ (aw_last μ α β x b hp hb _ _ rfl (Nat.sub_self p) _ _ _ _ _ _ _ _ s hs h')
  · intro r _
    have hk : 0 < p - ((Fin.castSucc r : Fin (p + 1)) : ℕ) := by
      have := r.2
      simp only [Fin.val_castSucc]
      omega
    rw [hβ _ hk, map_zero, smul_zero]

private theorem last_vertex {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) {p : ℕ} {W : Scheme.{0}}
    (z : Sx E p W) (h : p + 0 ≤ p) (ι' : E ⟶ dbl (abv U π)) (ι : sch.obj X ⟶ dbl (opn U))
    (hι : ι' ≫ dbl.map (abvMap U π) = π ≫ ι) :
    ((z.map ι').sub p 0 h).map (dbl.map (abvMap U π)) = Sx.map (E := sch.obj X) (p := 0) ι (under π z) := by
  rw [((GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite z).2.2.1 p 0 h).2.1 ι']
  have h1 : ((z.sub p 0 h).map ι').map (dbl.map (abvMap U π)) = (z.sub p 0 h).map (ι' ≫ dbl.map (abvMap U π)) := rfl
  rw [h1, hι]
  have h2 : (z.sub p 0 h).map (π ≫ ι) = Sx.map (E := sch.obj X) (p := 0) ι (under π (z.sub p 0 h)) := rfl
  rw [h2, ((GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite z).2.2.1 p 0 h).2.2, (UpperTheory.mem_pullbackImage_iff_factors_through_open U π p W z).2.2 0 _]

theorem UpperTheory.relativeCupProduct_realizes_product_of_representative :
    LeafAW → ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (m j i n : ℤ) (c : Hs q (opn U) m j) (β : Sec ((res _ (tw q j)).X m) X), IsRep U β c.1 →
    ∀ Φ : (famDC (Sub.bot E) (res _ (tw q i)) 0).Hom (famDC (Sub.img (E := E) (pullback.fst π (sch.map U.ι))) (res _ (tw q (i + j))) m), IsProd (twPair q i j) π β Φ →
    ∀ (x : (famDC (Sub.bot E) (res _ (tw q i)) 0).Tot) (a : Ht q E n i), HRel x a → SRel (P := abv U π) (N := n + m) (Φ.tot x) (Hs.act q (P := abv U π) a (Hs.pull q (abvMap U π) _ _ c)).1 := by
  intro hAW q _ X U E π m j i n c β hrep Φ hΦ x a hx
  obtain ⟨-, -, γ₀, hγ₀, h0l, h0r, h0p⟩ := hrep
  obtain ⟨α, hα, hαx⟩ := hx
  let α' : Cocycle ((chains _).obj (dbl (abv U π))) (res _ (tw q i)) n :=
    zcomp (Cocycle.ofHom ((chains _).map (dbl.fold (abv U π)))) α (zero_add n)
  let β' : Cocycle ((chains _).obj (dbl (abv U π))) (res _ (tw q j)) m :=
    zcomp (Cocycle.ofHom ((chains _).map (dbl.map (abvMap U π)))) γ₀ (zero_add m)
  obtain ⟨γ, hγ, hcup⟩ := (hAW q i j).2 (dbl (abv U π)) n m α' β'
  have evα : ∀ (p : ℕ) (s : ℤ) h (W : Scheme.{0}) (y : Sx (dbl (abv U π)) p W),
      ev α'.1 p s h W y = ev α.1 p s h W (y.map (dbl.fold (abv U π))) := fun p s h W y =>
    (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties _).2.2.2.1 (dbl.fold (abv U π)) α.1 p s h W y
  have evβ : ∀ (p : ℕ) (s : ℤ) h (W : Scheme.{0}) (y : Sx (dbl (abv U π)) p W),
      ev β'.1 p s h W y = ev γ₀.1 p s h W (y.map (dbl.map (abvMap U π))) := fun p s h W y =>
    (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties _).2.2.2.1 (dbl.map (abvMap U π)) γ₀.1 p s h W y
  have hvan : ∀ (k : ℕ), 0 < k → ∀ (s : ℤ) h (W : Scheme.{0}) (y : Sx (dbl (abv U π)) k W), ev β'.1 k s h W y = 0 := by
    intro k hk s h W y
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [evβ]
    exact h0p k s _ W _
  have hinr : ∀ (p : ℕ) (s : ℤ) h (W : Scheme.{0}) (z : Sx (abv U π).right p W),
      ev γ.1 p s h W (z.map (dbl.inr (abv U π))) = 0 := by
    intro p s h W z
    have hb : ev β'.1 0 m (by simp) W ((z.map (dbl.inr (abv U π))).sub p 0 (by omega)) = 0 := by
      rw [evβ]
      refine (congrArg (fun y => ev γ₀.1 0 m (by simp) W y)
        (last_vertex U π z (by omega) (dbl.inr (abv U π)) (dbl.inr (opn U)) (dbl.inr_map (abvMap U π)))).trans ?_
      exact h0r W _
    rw [aw_eval _ α'.1 β'.1 γ.1 hγ hvan _ 0 (by omega) hb s h (-(p : ℤ) + n) rfl (by omega), map_zero, smul_zero]
  refine ⟨γ, ?_, ?_, hinr⟩
  · have hC : cup q (pull _ (dbl.fold (abv U π)) _ n a) (Hs.pull q (abvMap U π) _ _ c).1 = CohomologyClass.mk γ := by
      rw [← hcup, ← hα]
      change cup q _ (pull _ (dbl.map (abvMap U π)) _ m c.1) = _
      rw [← hγ₀]
      rfl
    have hz : pull _ (dbl.inr (abv U π)) (tw q (i + j)) (n + m) (CohomologyClass.mk γ) = 0 := by
      have h0 : zcomp (Cocycle.ofHom ((chains _).map (dbl.inr (abv U π)))) γ (zero_add (n + m)) = 0 := by
        have hc : (zcomp (Cocycle.ofHom ((chains _).map (dbl.inr (abv U π)))) γ (zero_add (n + m))).1 = 0 := by
          refine (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties _).2.2.1 _ _ fun p s h W z => ?_
          rw [((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties _).1 0 0 p s h W z).2.2.1]
          exact ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties _).2.2.2.1 (dbl.inr (abv U π)) γ.1 p s h W z).trans (hinr p s h W z)
        exact Cocycle.ext hc
      exact (congrArg CohomologyClass.mk h0).trans (CohomologyClass.mk_zero _ _ _)
    change CohomologyClass.mk γ = cup q (pull _ (dbl.fold (abv U π)) _ n a) (Hs.pull q (abvMap U π) _ _ c).1 -
      pull _ (dbl.fold (abv U π)) _ _ (pull _ (dbl.inr (abv U π)) _ _
        (cup q (pull _ (dbl.fold (abv U π)) _ n a) (Hs.pull q (abvMap U π) _ _ c).1))
    rw [hC, hz, map_zero, sub_zero]
  · intro p s h W z
    have hs : -(p : ℤ) + n = s + 0 := by omega
    have hb : ev β'.1 0 m (by simp) W ((z.map (dbl.inl (abv U π))).sub p 0 (by omega)) = Sec.res (under π z) β := by
      rw [evβ]
      refine (congrArg (fun y => ev γ₀.1 0 m (by simp) W y)
        (last_vertex U π z (by omega) (dbl.inl (abv U π)) (dbl.inl (opn U)) (inl_map' (abvMap U π)))).trans ?_
      exact h0l W _
    have e := hΦ p s (x p s) W z
    rw [hαx p s hs W z] at e
    refine e.trans ?_
    rw [aw_eval _ α'.1 β'.1 γ.1 hγ hvan _ _ (by omega) hb (s + m) h (s + 0) hs (by omega), evα]
    have hf : (z.map (dbl.inl (abv U π))).map (dbl.fold (abv U π)) = z.map (𝟙 E) := by
      have h1 : (z.map (dbl.inl (abv U π))).map (dbl.fold (abv U π)) = z.map (dbl.inl (abv U π) ≫ dbl.fold (abv U π)) := rfl
      rw [h1, inl_fold']
      rfl
    rw [hf]
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsCupProductHomOfCocycleVanishingOnOpen
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem leib {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) (W : Scheme.{0})
    (s s' t w w' : ℤ) (h : s + t = w) (h' : s' + t = w') (hs : s' = s + 1)
    (a : Sec (I.X s) W) (b : Sec (J.X t) W) (hb : Sec.map (J.d t (t + 1)) b = 0) :
    Sec.map (K.d w w') (μ.mul W s t w h a b) = μ.mul W s' t w' h' (Sec.map (I.d s s') a) b := by
  subst hs
  obtain rfl : w' = w + 1 := by omega
  rw [μ.leibniz W s t w h a b, hb, map_zero, smul_zero, add_zero]

private theorem res_usmul {R : Type} [CommRing R] {F : Shv R} {V W : Scheme.{0}} (g : V ⟶ W)
    (u : ℤˣ) (x : Sec F W) : Sec.res g (u • x) = u • Sec.res g x := by
  simp only [Sec.res, Units.smul_def, map_zsmul]

private theorem map_usmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {W : Scheme.{0}}
    (u : ℤˣ) (x : Sec F W) : Sec.map φ (u • x) = u • Sec.map φ x := by
  simp only [Sec.map, Units.smul_def, map_zsmul]

private theorem res_comp {R : Type} [CommRing R] {F : Shv R} {V W X : Scheme.{0}} (g : V ⟶ W)
    (f : W ⟶ X) (x : Sec F X) : Sec.res (g ≫ f) x = Sec.res g (Sec.res f x) := by
  simp only [Sec.res, op_comp, Functor.map_comp]
  rfl

private theorem map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V W : Scheme.{0}}
    (g : V ⟶ W) (x : Sec F W) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) :=
  ConcreteCategory.congr_hom (φ.hom.naturality g.op) x

private noncomputable def prodFam {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K)
    {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (m : ℤ) (β : Sec (J.X m) X)
    (hU : Sec.res U.ι β = 0) (p : ℕ) (s : ℤ) :
    Fam (Sub.bot E) p (I.X (s + 0)) →+
      Fam (Sub.img (E := E) (pullback.fst π (sch.map U.ι))) p (K.X (s + m)) where
  toFun a := ⟨fun W z => (m * (p : ℕ)).negOnePow •
      μ.mul W (s + 0) m (s + m) (by omega) (a.1 W z) (Sec.res (under π z) β), fun V W g z => by
      beta_reduce
      rw [res_usmul, μ.nat, a.2.1 V W g z, (UpperTheory.mem_pullbackImage_iff_factors_through_open U π p W z).2.1 V g, res_comp],
    fun W z h => by
      obtain ⟨w, hw⟩ := (UpperTheory.mem_pullbackImage_iff_factors_through_open U π p W z).1.1 h
      beta_reduce
      rw [← hw, res_comp, hU]
      simp⟩
  map_zero' := by ext W z; simp
  map_add' a b := by ext W z; simp

theorem UpperTheory.exists_cupProduct_hom_of_cocycle_vanishing_on_open :
    ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (m : ℤ) (β : Sec (J.X m) X), Sec.map (J.d m (m + 1)) β = 0 → Sec.res U.ι β = 0 →
    ∃ Φ : (famDC (Sub.bot E) I 0).Hom (famDC (Sub.img (E := E) (pullback.fst π (sch.map U.ι))) K m), IsProd μ π β Φ ∧ Φ.Ok := by
  intro R _ I J K μ X U E π m β hd hU
  refine ⟨fun p s => prodFam μ U π m β hU p s, fun p s a W z => rfl, ?_, ?_⟩
  · intro p s a
    refine Subtype.ext (funext fun W => funext fun z => ?_)
    change (m * (p : ℕ)).negOnePow • μ.mul W (s + 1 + 0) m (s + 1 + m) (by omega)
        (Sec.map (I.d (s + 0) (s + 1 + 0)) (a.1 W z)) (Sec.res (under π z) β) =
      Sec.map (K.d (s + m) (s + 1 + m)) ((m * (p : ℕ)).negOnePow •
        μ.mul W (s + 0) m (s + m) (by omega) (a.1 W z) (Sec.res (under π z) β))
    rw [map_usmul, leib μ W (s + 0) (s + 1 + 0) m (s + m) (s + 1 + m) (by omega) (by omega) (by omega)
      _ _ (by rw [map_res, hd]; simp)]
  · intro p s a
    refine Subtype.ext (funext fun W => funext fun z => ?_)
    have hf : ∀ i : Fin (p + 2), under π (z.face i) = under π z := fun i =>
      (UpperTheory.mem_pullbackImage_iff_factors_through_open U π (p + 1) W z).2.2 p (SimplexCategory.δ i)
    change ((m * ((p + 1 : ℕ) : ℤ))).negOnePow • μ.mul W (s + 0) m (s + m) (by omega)
        ((0 : ℤ).negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • a.1 W (z.face i)) (Sec.res (under π z) β) =
      m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ((m * (p : ℕ)).negOnePow •
        μ.mul W (s + 0) m (s + m) (by omega) (a.1 W (z.face i)) (Sec.res (under π (z.face i)) β))
    simp only [hf]
    have hsign : (m * ((p + 1 : ℕ) : ℤ)).negOnePow = m.negOnePow * (m * (p : ℕ)).negOnePow := by
      rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, add_comm, Int.negOnePow_add]
    generalize Sec.res (under π z) β = b
    let f := ((μ.mul W (s + 0) m (s + m) (by omega)).flip b).toAddMonoidHom
    change _ • f _ = _ • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (_ • f _)
    have e : ∀ (u : ℤˣ) (i : Fin (p + 2)) (y : Sec (K.X (s + m)) W),
        (-1 : ℤ) ^ (i : ℕ) • (u • y) = u • ((-1 : ℤ) ^ (i : ℕ) • y) := by
      intro u i y
      simp only [Units.smul_def]
      exact smul_comm _ _ _
    simp only [e]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.smul_sum, hsign, mul_smul, Int.negOnePow_zero, one_smul, map_sum]
    simp only [map_zsmul]
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.BijectiveIffTotalQuasiIsoOfTotalModels
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

namespace UpperTheory.DegreeAdditivity

private theorem D_add {C : DC} (n : ℤ) (x y : C.Tot) : C.D n (x + y) = C.D n x + C.D n y := by
  funext p t
  rcases p with _ | p
  · simp [DC.D, map_add (f := _)]
  · simp only [DC.D, Pi.add_apply, map_add (f := _), smul_add]
    abel

private theorem D_sub {C : DC} (n : ℤ) (x y : C.Tot) : C.D n (x - y) = C.D n x - C.D n y := by
  funext p t
  rcases p with _ | p
  · simp [DC.D, map_sub]
  · simp only [DC.D, Pi.sub_apply, map_sub, smul_sub]
    abel

private theorem D_zero {C : DC} (n : ℤ) : C.D n (0 : C.Tot) = 0 := by
  funext p t
  rcases p with _ | p <;> simp [DC.D]

private theorem Deg_zero {C : DC} {n : ℤ} : C.Deg n (0 : C.Tot) := fun _ _ _ => rfl

private theorem Deg_add {C : DC} {n : ℤ} {x y : C.Tot} (hx : C.Deg n x) (hy : C.Deg n y) :
    C.Deg n (x + y) := fun p s h => by
  change x p s + y p s = 0
  rw [hx p s h, hy p s h, add_zero]

private theorem Deg_sub {C : DC} {n : ℤ} {x y : C.Tot} (hx : C.Deg n x) (hy : C.Deg n y) :
    C.Deg n (x - y) := fun p s h => by
  change x p s - y p s = 0
  rw [hx p s h, hy p s h, sub_zero]

private theorem tot_add {C C' : DC} (Φ : C.Hom C') (x y : C.Tot) :
    Φ.tot (x + y) = Φ.tot x + Φ.tot y := by
  funext p s
  exact map_add _ _ _

private theorem tot_sub {C C' : DC} (Φ : C.Hom C') (x y : C.Tot) :
    Φ.tot (x - y) = Φ.tot x - Φ.tot y := by
  funext p s
  exact map_sub _ _ _

private theorem tot_zero {C C' : DC} (Φ : C.Hom C') : Φ.tot (0 : C.Tot) = 0 := by
  funext p s
  exact map_zero _

private theorem Deg_tot {C C' : DC} (Φ : C.Hom C') {n : ℤ} {x : C.Tot} (h : C.Deg n x) :
    C'.Deg n (Φ.tot x) := fun p s hne => by
  change Φ p s (x p s) = 0
  rw [h p s hne, map_zero]

private theorem hom_d {C C' : DC} {Φ : C.Hom C'} (h : Φ.Ok) (p : ℕ) (s t : ℤ) (e : t = s + 1)
    (x : C.A p s) : Φ p t (C.d p s t x) = C'.d p s t (Φ p s x) := by
  subst e
  exact h.1 p s x

private theorem tot_D {C C' : DC} {Φ : C.Hom C'} (h : Φ.Ok) (n : ℤ) (x : C.Tot) :
    Φ.tot (C.D n x) = C'.D n (Φ.tot x) := by
  funext p t
  rcases p with _ | p
  · simp only [DC.D, DC.Hom.tot]
    exact hom_d h 0 (t - 1) t (by ring) _
  · simp only [DC.D, DC.Hom.tot, map_add (f := _), Units.smul_def, map_zsmul]
    rw [hom_d h (p + 1) (t - 1) t (by ring), h.2]

private theorem rel_zero {C : DC} {n : ℤ} {H : Type 1} [AddCommGroup H] {rel : C.Tot → H → Prop}
    (h : TModel C n rel) : rel 0 0 := by
  obtain ⟨x, -, -, r⟩ := h.surj 0
  have := h.sub x 0 x 0 r r
  simpa using this

end UpperTheory.DegreeAdditivity

open UpperTheory.DegreeAdditivity in
theorem UpperTheory.bijective_iff_totalQuasiIso_of_totalModels :
    ∀ (C C' : DC) (Φ : C.Hom C'), C.Ok → C'.Ok → Φ.Ok → ∀ (H H' : ℤ → Type 1) [∀ n, AddCommGroup (H n)] [∀ n, AddCommGroup (H' n)] (rel : ∀ n, C.Tot → H n → Prop) (rel' : ∀ n, C'.Tot → H' n → Prop) (F : ∀ n, H n → H' n),
    (∀ n, TModel C n (rel n)) → (∀ n, TModel C' n (rel' n)) → (∀ n x a, rel n x a → rel' n (Φ.tot x) (F n a)) → ((∀ n, Function.Bijective (F n)) ↔ Φ.TotEx) := by
  intro C C' Φ hC hC' hΦ H H' _ _ rel rel' F hM hM' hF
  constructor
  · intro hbij n a y ha hy hDa hΦa
    obtain ⟨ca, ra⟩ := (hM (n + 1)).ex a ha hDa
    have r0 : rel' (n + 1) 0 (F (n + 1) 0) := by
      have := hF (n + 1) 0 0 (rel_zero (hM (n + 1)))
      rwa [tot_zero] at this
    have hF0 : F (n + 1) 0 = 0 :=
      ((hM' (n + 1)).zero 0 (F (n + 1) 0) Deg_zero r0).2 ⟨0, Deg_zero, D_zero _⟩
    have hFa : F (n + 1) ca = 0 := by
      refine ((hM' (n + 1)).zero _ _ (Deg_tot Φ ha) (hF (n + 1) a ca ra)).2 ⟨y, ?_, ?_⟩
      · simpa using hy
      · simpa using hΦa.symm
    have hca : ca = 0 := (hbij (n + 1)).1 (hFa.trans hF0.symm)
    obtain ⟨a', ha', hDa'⟩ := ((hM (n + 1)).zero a ca ha ra).1 hca
    simp only [add_sub_cancel_right] at ha' hDa'
    have hz : C'.Deg n (y - Φ.tot a') := Deg_sub hy (Deg_tot Φ ha')
    have hDz : C'.D n (y - Φ.tot a') = 0 := by
      rw [D_sub, ← tot_D hΦ, hDa', hΦa, sub_self]
    obtain ⟨cz, rz⟩ := (hM' n).ex _ hz hDz
    obtain ⟨c, hc⟩ := (hbij n).2 cz
    obtain ⟨w, hw, hDw, rw⟩ := (hM n).surj c
    have r2 := (hM' n).sub _ _ _ _ rz (hF n w c rw)
    rw [hc, sub_self] at r2
    obtain ⟨y', hy', hDy'⟩ :=
      ((hM' n).zero _ _ (Deg_sub hz (Deg_tot Φ hw)) r2).1 rfl
    refine ⟨a' + w, y', Deg_add ha' hw, hy', ?_, ?_⟩
    · rw [D_add, hDa', hDw, add_zero]
    · rw [tot_add, hDy']
      abel
  · intro hT m
    constructor
    · intro c1 c2 h12
      obtain ⟨x1, hx1, hD1, r1⟩ := (hM m).surj c1
      obtain ⟨x2, hx2, hD2, r2⟩ := (hM m).surj c2
      have r12 := (hM m).sub _ _ _ _ r1 r2
      have r12' := (hM' m).sub _ _ _ _ (hF m _ _ r1) (hF m _ _ r2)
      rw [h12, sub_self, ← tot_sub] at r12'
      obtain ⟨y, hy, hDy⟩ :=
        ((hM' m).zero _ 0 (Deg_tot Φ (Deg_sub hx1 hx2)) r12').1 rfl
      obtain ⟨a', -, ha', -, hDa', -⟩ := hT (m - 1) (x1 - x2) y
        (by simpa using Deg_sub hx1 hx2) hy
        (by rw [sub_add_cancel, D_sub, hD1, hD2, sub_self]) hDy.symm
      exact sub_eq_zero.mp (((hM m).zero _ _ (Deg_sub hx1 hx2) r12).2 ⟨a', ha', hDa'⟩)
    · intro c'
      obtain ⟨y, hy, hDy, ry⟩ := (hM' m).surj c'
      obtain ⟨a', y', ha', hy', hDa', hyeq⟩ :=
        hT m 0 y Deg_zero hy (D_zero _) (by rw [tot_zero, hDy])
      obtain ⟨c, rc⟩ := (hM m).ex a' ha' hDa'
      refine ⟨c, ?_⟩
      have r := (hM' m).sub _ _ _ _ ry (hF m _ _ rc)
      have h0 : c' - F m c = 0 :=
        ((hM' m).zero _ _ (Deg_sub hy (Deg_tot Φ ha')) r).2 ⟨y', hy', by rw [hyeq]; abel⟩
      exact (sub_eq_zero.mp h0).symm
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.SupportDoubleComplexIsAdmissible
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem sx_face_face {E : Spc} {p : ℕ} {U : Scheme} (y : Sx E (p+2) U) {a b : Fin (p+2)}
    (h : a ≤ b) : (y.face b.succ).face a = (y.face a.castSucc).face b := by
  unfold Sx.face
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← NatTrans.comp_app,
    SimplicialObject.δ_comp_δ E h]

private theorem sum_neg_one_pow_face_face_eq_zero {A : Type*} [AddCommGroup A] {E : Spc} {p : ℕ} {U : Scheme}
    (f : Sx E p U → A) (y : Sx E (p+2) U) :
    ∑ j : Fin (p+3), ∑ i : Fin (p+2), ((-1 : ℤ) ^ ((j : ℕ) + (i : ℕ))) • f ((y.face j).face i) = 0 := by
  have ff : ∀ {a b : Fin (p+2)}, a ≤ b → (y.face b.succ).face a = (y.face a.castSucc).face b :=
    fun h => sx_face_face y h
  rw [← Finset.sum_product' (f := fun (j : Fin (p+3)) (i : Fin (p+2)) => ((-1 : ℤ) ^ ((j : ℕ) + (i : ℕ))) • f ((y.face j).face i)), Finset.univ_product_univ]
  let g : Fin (p+3) × Fin (p+2) → Fin (p+3) × Fin (p+2) := fun ji =>
    if h : (ji.1 : ℕ) ≤ ji.2 then (ji.2.succ, ji.1.castLT (by omega))
    else (ji.2.castSucc, ji.1.pred (by intro h0; simp [h0] at h))
  have gg : ∀ ji, g (g ji) = ji := by
    rintro ⟨j, i⟩
    by_cases h : (j : ℕ) ≤ i
    · have h1 : ¬ ((i.succ : Fin (p+3)) : ℕ) ≤ (j.castLT (by omega) : Fin (p+2)) := by simp; omega
      simp only [g, dif_pos h, dif_neg h1]
      ext <;> simp
    · have h1 : ((i.castSucc : Fin (p+3)) : ℕ) ≤ (j.pred (by intro h0; simp [h0] at h) : Fin (p+2)) := by simp; omega
      simp only [g, dif_neg h, dif_pos h1]
      ext <;> simp
  refine Finset.sum_involution (fun ji _ => g ji) ?_ ?_ (fun _ _ => Finset.mem_univ _) (fun ji _ => gg ji)
  · rintro ⟨j, i⟩ _
    by_cases h : (j : ℕ) ≤ i
    · simp only [g, dif_pos h]
      have hj : j = (j.castLT (by omega) : Fin (p+2)).castSucc := by ext; simp
      have hle : j.castLT (by omega) ≤ i := by rw [Fin.le_def]; simpa using h
      rw [ff hle, ← hj]
      simp only [Fin.val_succ, Fin.coe_castLT]
      rw [← add_smul]
      convert zero_smul ℤ _
      rw [show (i : ℕ) + 1 + j = (j + i) + 1 by ring, pow_succ]; ring
    · simp only [g, dif_neg h]
      have hj0 : j ≠ 0 := by intro h0; simp [h0] at h
      have hle : i ≤ j.pred hj0 := by rw [Fin.le_def]; simp; omega
      have key : (y.face j).face i = (y.face i.castSucc).face (j.pred hj0) := by
        have := ff hle
        rwa [Fin.succ_pred] at this
      rw [key]
      simp only [Fin.coe_castSucc, Fin.coe_pred]
      rw [← add_smul]
      convert zero_smul ℤ _
      have : (j : ℕ) = (j : ℕ) - 1 + 1 := by omega
      rw [this, show (j : ℕ) - 1 + 1 - 1 = (j:ℕ) - 1 by omega, show (j:ℕ) - 1 + 1 + i = (i + (j - 1)) + 1 by ring, pow_succ]; ring
  · rintro ⟨j, i⟩ _ _ heq
    by_cases h : (j : ℕ) ≤ i
    · simp only [g, dif_pos h, Prod.mk.injEq] at heq
      have := congrArg Fin.val heq.1; simp at this; omega
    · simp only [g, dif_neg h, Prod.mk.injEq] at heq
      have := congrArg Fin.val heq.1; simp at this; omega

theorem UpperTheory.supportDoubleComplex_isAdmissible :
    ∀ (R : Type) [CommRing R] (E : Spc) (Z : Sub E) (K : Cx R) (m : ℤ), (famDC Z K m).Ok := by
  intro R _ E Z K m
  unfold famDC
  constructor
  · intro p s t u x
    apply Subtype.ext
    funext U y
    change Sec.map (K.d (s + m) (t + m) ≫ K.d (t + m) (u + m)) (x.1 U y) = 0
    rw [HomologicalComplex.d_comp_d]
    rfl
  · intro p s x
    apply Subtype.ext
    funext U y
    simp [Fam.δ]
    have hz := sum_neg_one_pow_face_face_eq_zero (fun z => (x : (V : Scheme) → Sx E p V → Sec (K.X (s + m)) V) U z) y
    have hj : ∀ j : Fin (p+3), (-1 : ℤ) ^ (j : ℕ) • m.negOnePow • ∑ i : Fin (p+2), (-1 : ℤ) ^ (i : ℕ) •
        (x : (V : Scheme) → Sx E p V → Sec (K.X (s + m)) V) U ((y.face j).face i) =
        m.negOnePow • ∑ i : Fin (p+2), ((-1 : ℤ) ^ ((j : ℕ) + (i : ℕ))) •
        (x : (V : Scheme) → Sx E p V → Sec (K.X (s + m)) V) U ((y.face j).face i) := by
      intro j
      rw [smul_comm, Finset.smul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul, pow_add]
    simp_rw [hj, ← Finset.smul_sum]
    rw [hz, smul_zero, smul_zero]
  · intro p s t x
    apply Subtype.ext
    funext U y
    simp [Fam.map, Fam.δ]
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.TotalExactOfColumnExact
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem map_us {G H : Type*} [AddCommGroup G] [AddCommGroup H] (f : G →+ H) (e : ℤˣ) (x : G) :
    f (e • x) = e • f x := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

private theorem D_zero (C : DC) (n : ℤ) (x : C.Tot) (s t : ℤ) (h : s + 1 = t) :
    C.D n x 0 t = C.d 0 s t (x 0 s) := by
  obtain rfl : s = t - 1 := by omega
  rfl

private theorem D_succ (C : DC) (n : ℤ) (x : C.Tot) (p : ℕ) (s t : ℤ) (h : s + 1 = t) :
    C.D n x (p + 1) t = C.d (p + 1) s t (x (p + 1) s) + (n + 1).negOnePow • C.δ p t (x p t) := by
  obtain rfl : s = t - 1 := by omega
  rfl

private theorem col {C C' : DC} {Φ : C.Hom C'} {p : ℕ} (h : Φ.ColEx p) (r s t u : ℤ) (e1 : r + 1 = s)
    (e2 : s + 1 = t) (e3 : t + 1 = u) (a : C.A p t) (y : C'.A p s) (ha : C.d p t u a = 0)
    (hy : Φ p t a = C'.d p s t y) :
    ∃ (a' : C.A p s) (y' : C'.A p r), C.d p s t a' = a ∧ y = Φ p s a' + C'.d p r s y' := by
  subst e2
  subst e3
  obtain rfl : r = s - 1 := by omega
  exact h s a y ha hy

private structure Cl {C C' : DC} (Φ : C.Hom C') (n : ℤ) (p : ℕ) (b : ∀ s, C.A p s) (z : ∀ s, C'.A p s) : Prop where
  sb : ∀ s, (p : ℤ) + s ≠ n + 1 → b s = 0
  sz : ∀ s, (p : ℤ) + s ≠ n → z s = 0
  db : ∀ s t, s + 1 = t → C.d p s t (b s) = 0
  pz : ∀ s t, s + 1 = t → Φ p t (b t) = C'.d p s t (z s)

private structure Sv {C C' : DC} (Φ : C.Hom C') (n : ℤ) (p : ℕ) (b : ∀ s, C.A p s) (z : ∀ s, C'.A p s)
    (u : ∀ s, C.A p s) (v : ∀ s, C'.A p s) : Prop where
  su : ∀ s, (p : ℤ) + s ≠ n → u s = 0
  sv : ∀ s, (p : ℤ) + s ≠ n - 1 → v s = 0
  du : ∀ s t, s + 1 = t → C.d p s t (u s) = b t
  yv : ∀ r s, r + 1 = s → z s = Φ p s (u s) + C'.d p r s (v r)

private theorem solve {C C' : DC} {Φ : C.Hom C'} {n : ℤ} {p : ℕ} (hcol : Φ.ColEx p)
    {b : ∀ s, C.A p s} {z : ∀ s, C'.A p s} (h : Cl Φ n p b z) : ∃ u v, Sv Φ n p b z u v := by
  obtain ⟨s0, hs0⟩ : ∃ s0 : ℤ, s0 = n - p := ⟨_, rfl⟩
  obtain ⟨a', y', ha', hy'⟩ := col hcol (s0 - 1) s0 (s0 + 1) (s0 + 1 + 1) (by ring) rfl rfl
    (b (s0 + 1)) (z s0) (h.db _ _ rfl) (h.pz _ _ rfl)
  refine ⟨Function.update (fun _ => 0) s0 a', Function.update (fun _ => 0) (s0 - 1) y',
    ⟨?_, ?_, ?_, ?_⟩⟩
  · intro s hs
    rw [Function.update_of_ne (by omega)]
  · intro s hs
    rw [Function.update_of_ne (by omega)]
  · intro s t hst
    by_cases hs : s = s0
    · subst hst
      subst hs
      rw [Function.update_self, ha']
    · simp [Function.update_of_ne hs, h.sb t (by omega)]
  · intro r s hrs
    by_cases hs : s = s0
    · have hr : r = s - 1 := by omega
      subst hr
      subst hs
      rw [Function.update_self, Function.update_self, hy']
    · have hr : r ≠ s0 - 1 := by omega
      simp [Function.update_of_ne hs, Function.update_of_ne hr, h.sz s (by omega)]

private structure St {C C' : DC} (Φ : C.Hom C') (n : ℤ) (a : C.Tot) (y : C'.Tot) (p : ℕ) where
  b : ∀ s, C.A p s
  z : ∀ s, C'.A p s
  u : ∀ s, C.A p s
  v : ∀ s, C'.A p s
  cl : Cl Φ n p b z
  sv : Sv Φ n p b z u v
  hb : ∀ s, C.δ p s (a p s) = C.δ p s (b s)
  hz : ∀ s, C'.δ p s (y p s) = C'.δ p s (z s)

private theorem cl_zero {C C' : DC} {Φ : C.Hom C'} {n : ℤ} {a : C.Tot} {y : C'.Tot}
    (ha : C.Deg (n + 1) a) (hy : C'.Deg n y) (hD : C.D (n + 1) a = 0) (hP : Φ.tot a = C'.D n y) :
    Cl Φ n 0 (a 0) (y 0) := by
  refine ⟨fun s hs => ha 0 s hs, fun s hs => hy 0 s hs, ?_, ?_⟩
  · intro s t e
    have h1 := congrFun (congrFun hD 0) t
    rw [D_zero C (n + 1) a s t e] at h1
    exact h1
  · intro s t e
    have h1 := congrFun (congrFun hP 0) t
    rw [D_zero C' n y s t e] at h1
    exact h1

private theorem cl_next {C C' : DC} {Φ : C.Hom C'} {n : ℤ} {a : C.Tot} {y : C'.Tot} {p : ℕ}
    (hC : C.Ok) (hC' : C'.Ok) (hΦ : Φ.Ok)
    (ha : C.Deg (n + 1) a) (hy : C'.Deg n y) (hD : C.D (n + 1) a = 0) (hP : Φ.tot a = C'.D n y)
    (x : St Φ n a y p) :
    Cl Φ n (p + 1) (fun s => a (p + 1) s - (n + 1).negOnePow • C.δ p s (x.u s))
      (fun s => y (p + 1) s + (n + 1).negOnePow • C'.δ p s (x.v s)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    simp only [ha (p + 1) s hs, x.sv.su s (by omega), map_zero, smul_zero, sub_zero]
  · intro s hs
    simp only [hy (p + 1) s hs, x.sv.sv s (by omega), map_zero, smul_zero, add_zero]
  · intro s t e
    have h1 := congrFun (congrFun hD (p + 1)) t
    rw [D_succ C (n + 1) a p s t e, Int.negOnePow_succ, Units.neg_smul, x.hb t] at h1
    simp only [Pi.zero_apply] at h1
    have h2 : C.d (p + 1) s t (C.δ p s (x.u s)) = C.δ p t (x.b t) := by
      rw [hC.comm, x.sv.du s t e]
    simp only [map_sub, map_us, h2]
    rwa [← sub_eq_add_neg] at h1
  · intro s t e
    have h1 := congrFun (congrFun hP (p + 1)) t
    rw [D_succ C' n y p s t e] at h1
    change Φ (p + 1) t (a (p + 1) t) = _ at h1
    have h3 : C'.δ p t (y p t) =
        C'.δ p t (Φ p t (x.u t)) + C'.d (p + 1) s t (C'.δ p s (x.v s)) := by
      rw [x.hz t, x.sv.yv s t e, map_add (f := _), hC'.comm]
    have h4 : Φ (p + 1) t (C.δ p t (x.u t)) = C'.δ p t (Φ p t (x.u t)) := hΦ.2 p t (x.u t)
    simp only [map_sub, map_add (f := _), map_us, h4]
    rw [h1, h3, smul_add]
    abel

theorem UpperTheory.totalExact_of_columnExact :
    ∀ (C C' : DC) (Φ : C.Hom C'), C.Ok → C'.Ok → Φ.Ok → (∀ p, Φ.ColEx p) → Φ.TotEx := by
  intro C C' Φ hC hC' hΦ hcol n a y ha hy hD hP
  have hcl0 := cl_zero (Φ := Φ) ha hy hD hP
  have hs0 := solve (hcol 0) hcl0
  let S0 : St Φ n a y 0 := ⟨a 0, y 0, hs0.choose, hs0.choose_spec.choose, hcl0,
    hs0.choose_spec.choose_spec, fun _ => rfl, fun _ => rfl⟩
  let step : ∀ p, St Φ n a y p → St Φ n a y (p + 1) := fun p x =>
    { b := fun s => a (p + 1) s - (n + 1).negOnePow • C.δ p s (x.u s)
      z := fun s => y (p + 1) s + (n + 1).negOnePow • C'.δ p s (x.v s)
      u := (solve (hcol (p + 1)) (cl_next hC hC' hΦ ha hy hD hP x)).choose
      v := (solve (hcol (p + 1)) (cl_next hC hC' hΦ ha hy hD hP x)).choose_spec.choose
      cl := cl_next hC hC' hΦ ha hy hD hP x
      sv := (solve (hcol (p + 1)) (cl_next hC hC' hΦ ha hy hD hP x)).choose_spec.choose_spec
      hb := fun s => by simp only [map_sub, map_us, hC.δδ, smul_zero, sub_zero]
      hz := fun s => by simp only [map_add (f := _), map_us, hC'.δδ, smul_zero, add_zero] }
  let S : ∀ p, St Φ n a y p := fun p => Nat.rec (motive := fun p => St Φ n a y p) S0 step p
  refine ⟨fun p s => (S p).u s, fun p s => (S p).v s, ?_, ?_, ?_, ?_⟩
  · intro p s hps
    exact (S p).sv.su s hps
  · intro p s hps
    exact (S p).sv.sv s hps
  · funext p t
    rcases p with _ | p
    · rw [D_zero C n _ (t - 1) t (by ring)]
      exact (S 0).sv.du (t - 1) t (by ring)
    · rw [D_succ C n _ p (t - 1) t (by ring)]
      have h1 := (S (p + 1)).sv.du (t - 1) t (by ring)
      change C.d (p + 1) (t - 1) t ((S (p + 1)).u (t - 1)) =
        a (p + 1) t - (n + 1).negOnePow • C.δ p t ((S p).u t) at h1
      beta_reduce
      rw [h1, sub_add_cancel]
  · funext p t
    rcases p with _ | p
    · show y 0 t = Φ 0 t ((S 0).u t) + C'.D (n - 1) (fun p s => (S p).v s) 0 t
      rw [D_zero C' (n - 1) _ (t - 1) t (by ring)]
      exact (S 0).sv.yv (t - 1) t (by ring)
    · show y (p + 1) t = Φ (p + 1) t ((S (p + 1)).u t) +
        C'.D (n - 1) (fun p s => (S p).v s) (p + 1) t
      rw [D_succ C' (n - 1) _ p (t - 1) t (by ring)]
      have h1 := (S (p + 1)).sv.yv (t - 1) t (by ring)
      change y (p + 1) t + (n + 1).negOnePow • C'.δ p t ((S p).v t) =
        Φ (p + 1) t ((S (p + 1)).u t) + C'.d (p + 1) (t - 1) t ((S (p + 1)).v (t - 1)) at h1
      have e : (n - 1 + 1).negOnePow = -(n + 1).negOnePow := by
        rw [sub_add_cancel, Int.negOnePow_succ, neg_neg]
      beta_reduce
      rw [e, Units.neg_smul, eq_sub_of_add_eq h1]
      abel
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem key (aw : LeafAW) (q : ℕ) [NeZero q] {X : Scheme.{0}} (U : X.Opens) {E : Spc}
    (π : E ⟶ sch.obj X) (m j i : ℤ) (c : Hs q (opn U) m j) (β : Sec ((res _ (tw q j)).X m) X)
    (hβ : IsRep U β c.1)
    (Φ : (famDC (Sub.bot E) (res _ (tw q i)) 0).Hom
      (famDC (Sub.img (E := E) (pullback.fst π (sch.map U.ι))) (res _ (tw q (i + j))) m))
    (hP : IsProd (twPair q i j) π β Φ) (hO : Φ.Ok) :
    (∀ n : ℤ, Function.Bijective fun a : Ht q E n i =>
      Hs.act q (P := abv U π) a (Hs.pull q (abvMap U π) _ _ c)) ↔ Φ.TotEx := by
  exact UpperTheory.bijective_iff_totalQuasiIso_of_totalModels _ _ Φ (UpperTheory.supportDoubleComplex_isAdmissible _ _ _ _ _) (UpperTheory.supportDoubleComplex_isAdmissible _ _ _ _ _) hO
    (fun n => Ht q E n i) (fun n => ↥(Hs q (abv U π) (n + m) (i + j)))
    (fun n x a => HRel x a) (fun n x b => SRel x (b : Ht q (dbl (abv U π)) (n + m) (i + j)))
    (fun n a => Hs.act q (P := abv U π) a (Hs.pull q (abvMap U π) _ _ c))
    (fun n => UpperTheory.supportDoubleComplex_bot_totalModel _ _ _ n) (fun n => UpperTheory.relativeCohomology_isTotalModel_of_image q (abv U π) (i + j) m n (n + m) rfl)
    (fun n x a h => UpperTheory.relativeCupProduct_realizes_product_of_representative aw q U π m j i n c β hβ Φ hP x a h)

theorem UpperTheory.productLevelwise_of_alexanderWhitney :
    LeafAW → LeafPrdLevel := by
  intro aw _ q _ X U E π m j c hlev n i
  obtain ⟨β, hβ⟩ := UpperTheory.exists_section_representing_relativeClass q X U m j c
  obtain ⟨Φ, hP, hO⟩ := UpperTheory.exists_cupProduct_hom_of_cocycle_vanishing_on_open _ (twPair q i j) U π m β hβ.1 hβ.2.1
  have hT : Φ.TotEx := by
    refine UpperTheory.totalExact_of_columnExact _ _ Φ (UpperTheory.supportDoubleComplex_isAdmissible _ _ _ _ _) (UpperTheory.supportDoubleComplex_isAdmissible _ _ _ _ _) hO ?_
    intro p
    obtain ⟨Ψ, hPΨ, hOΨ⟩ := UpperTheory.exists_cupProduct_hom_of_cocycle_vanishing_on_open _ (twPair q i j) U
      (disc.map (π.app (op { len := p }))) m β hβ.1 hβ.2.1
    refine UpperTheory.relativeCupProduct_levelwise_compat _ (twPair q i j) U π m β p Φ Ψ hP hPΨ ?_
    exact (key aw q U (disc.map (π.app (op { len := p }))) m j i c β hβ Ψ hPΨ hOΨ).1
      (fun n' => hlev (op { len := p }) n' i)
  exact (key aw q U π m j i c β hβ Φ hP hO).2 hT n
