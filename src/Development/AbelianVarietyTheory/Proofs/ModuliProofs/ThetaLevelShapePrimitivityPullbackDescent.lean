module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverBaseChangeOfProperQuasiProjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModelFiniteOverModuliModelDescends
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteLiftRestrict
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AmpleDeterminantFramesPullbackOfIsAffineHom
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.EqIdOfFixesTorsion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPolAVGenericFibre

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescent
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescent
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ShapePull

section Bundles

variable {X X' Y Y' : Scheme.{0}}

theorem iso_linComb_pull {L : LB X} {L' : LB X'} {F : X' ⟶ X} (H : LBIso L' (L.pull F)) {K : Type} [Fintype K]
    (ψ' : K → (Y' ⟶ X')) (ψ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) (e : ∀ k, ψ' k ≫ F = h ≫ ψ k) :
    LBIso (LB.LinComb L' ψ' ε) ((LB.LinComb L ψ ε).pull h) := by
  obtain ⟨w, hw⟩ := H
  exact LBIso.chartPull (chartPullId _) (chartPullOut L ψ ε h _ e) (iso_linComb ((isGen_iff w).1 hw) ψ' ε)

theorem iso_up {M N : LB Y} {M' N' : LB Y'} {h : Y' ⟶ Y} (hM : M.IsLB) (hN : N.IsLB) (hM' : M'.IsLB) (hN' : N'.IsLB)
    (a : LBIso M' (M.pull h)) (b : LBIso N' (N.pull h)) (H : LBIso M N) : LBIso M' N' :=
  LBIso.trans hM' (pull_isLB hM h) hN' a (LBIso.trans (pull_isLB hM h) (pull_isLB hN h) hN'
    (H.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M h h rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull N h h rfl)) b.symm)

end Bundles

section Field

variable {K : Type} [Field K] {S' : Scheme.{0}} (f : S' ⟶ Sp K)

theorem exists_point [Nonempty S'] :
    ∃ (K' : Type) (_ : Field K') (i : K →+* K') (x : Sp K' ⟶ S'), x ≫ f = spMap i := by
  obtain ⟨y⟩ := ‹Nonempty S'›
  obtain ⟨i, hi⟩ := Spec.map_surjective (S'.fromSpecResidueField y ≫ f)
  exact ⟨S'.residueField y, inferInstance, i.hom, S'.fromSpecResidueField y, hi.symm⟩

variable {f}

theorem epi_of_isPullback [Nonempty S'] {X₀ X : Scheme.{0}} {p₀ : X₀ ⟶ Sp K} {p : X ⟶ S'} {h : X ⟶ X₀}
    (H : IsPullback h p p₀ f) : Epi h := by
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have a : Flat f := inferInstance
  have b : Surjective f := inferInstance
  have : Flat h := MorphismProperty.of_isPullback (P := @Flat) H.flip a
  have : Surjective h := MorphismProperty.of_isPullback (P := @Surjective) H.flip b
  exact Flat.epi_of_flat_of_surjective h

theorem iso_down [Nonempty S'] {X₀ X : Scheme.{0}} {p₀ : X₀ ⟶ Sp K} {p : X ⟶ S'} {h : X ⟶ X₀}
    (H : IsPullback h p p₀ f) (h₁ : Smooth p₀) (h₂ : IsProper p₀) (h₃ : GeometricallyConnected p₀)
    {M N : LB X₀} {M' N' : LB X} (hM : M.IsLB) (hN : N.IsLB) (hM' : M'.IsLB) (hN' : N'.IsLB)
    (a : LBIso M' (M.pull h)) (b : LBIso N' (N.pull h)) (c : LBIso M' N') : LBIso M N := by
  obtain ⟨K', _, i, x, hx⟩ := exists_point f
  have P : IsPullback (pullback.fst p x ≫ h) (pullback.snd p x) p₀ (spMap i) :=
    hx ▸ (IsPullback.of_hasPullback p x).paste_horiz H
  have d : LBIso (M.pull h) (N.pull h) := LBIso.trans (pull_isLB hM h) hM' (pull_isLB hN h) a.symm
    (LBIso.trans hM' hN' (pull_isLB hN h) c b)
  exact (GlobalTheory.T.lineBundle_trivial_iso_descend_field K K' i X₀ _ p₀ _ _ h₁ h₂ h₃ P).2 M N hM hN (d.chartPull
    (chartPullSame M _ _ _ (pullback.fst p x) fun _ => rfl) (chartPullSame N _ _ _ (pullback.fst p x) fun _ => rfl))

theorem relAmple_down [Nonempty S'] {A : Over (Sp K)} [GrpObj A] (hA : IsAbelianScheme A) {A' : Over S'}
    {φ : A'.left ⟶ A.left} (H : IsPullback φ A'.hom A.hom f) {M : LB A.left} {M' : LB A'.left} (hM : M.IsLB)
    (hM' : M'.IsLB) (a : LBIso M' (M.pull φ)) (c : Out.RelAmple A' M') : Out.RelAmple A M := by
  obtain ⟨K', _, i, x, hx⟩ := exists_point f
  have : IsProper A'.hom := MorphismProperty.of_isPullback (P := @IsProper) H hA.proper
  have P : IsPullback (pullback.fst A.hom (spMap i)) (pullback.snd A.hom (spMap i)) A.hom (x ≫ f) :=
    hx ▸ IsPullback.of_hasPullback A.hom (spMap i)
  let ψ : pullback A.hom (spMap i) ⟶ A'.left := H.lift (pullback.fst _ _) (pullback.snd _ _ ≫ x)
    (P.w.trans (Category.assoc _ _ _).symm)
  have hψ : ψ ≫ φ = pullback.fst _ _ := H.lift_fst _ _ _
  have Q : IsPullback ψ (pullback.snd A.hom (spMap i)) A'.hom x :=
    IsPullback.of_right (hψ ▸ P) (H.lift_snd _ _ _) H
  exact GlobalTheory.T.relAmple_of_fieldExtension_baseChange K K' i A ((Over.pullback (spMap i)).obj A) (pullback.fst _ _) M (M'.pull ψ) hA
    (isGrpPullback_pullback A _) hM (pull_isLB hM' ψ)
    (a.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M' ψ ψ rfl) (chartPullSame M _ _ _ ψ fun _ => hψ.symm))
    (AmpleBaseChange.relAmple_of_isPullback hM' c Q)

end Field

section Group

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
  (h : IsGrpPullback G' G f φ)

section Points

variable {T : Over S} {T' : Over S'} (U : Over.mk (T'.hom ≫ f) ⟶ T)

theorem eq_up {x' y' : T' ⟶ G'} {x y : T ⟶ G} (hx : pushPt h.1.w x' = U ≫ x) (hy : pushPt h.1.w y' = U ≫ y)
    (e : x = y) : x' = y' :=
  Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) (hx.trans (e ▸ hy.symm))) (by rw [Over.w, Over.w]))

theorem eq_down (hU : Epi U.left) {x' y' : T' ⟶ G'} {x y : T ⟶ G} (hx : pushPt h.1.w x' = U ≫ x)
    (hy : pushPt h.1.w y' = U ≫ y) (e : x' = y') : x = y :=
  Over.OverMorphism.ext ((cancel_epi U.left).1 (congrArg (fun q => q.left) (hx.symm.trans (e ▸ hy))))

theorem push_mul {x' y' : T' ⟶ G'} {x y : T ⟶ G} (hx : pushPt h.1.w x' = U ≫ x) (hy : pushPt h.1.w y' = U ≫ y) :
    pushPt h.1.w (x' * y') = U ≫ (x * y) :=
  (map_mul (pushHom h T') x' y').trans ((congrArg₂ (· * ·) hx hy).trans (MonObj.comp_mul U x y).symm)

theorem push_linComb {n : ℕ} {x' : Fin n → (T' ⟶ G')} {x : Fin n → (T ⟶ G)} (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i)
    (a : Fin n → ℕ) : pushPt h.1.w (Out.linComb x' a) = U ≫ Out.linComb x a := by
  refine (map_list_prod (pushHom h T') _).trans (Eq.trans ?_ (map_list_prod (preHom (G := G) U) _).symm)
  rw [List.map_ofFn, List.map_ofFn]
  refine congrArg (fun z => (List.ofFn z).prod) (funext fun i => ?_)
  exact (map_pow (pushHom h T') _ _).trans ((congrArg (· ^ a i) (hx i)).trans (map_pow (preHom (G := G) U) _ _).symm)

theorem push_comp {x' : T' ⟶ G'} {x : T ⟶ G} (hx : pushPt h.1.w x' = U ≫ x) {a' : G' ⟶ G'} {a : G ⟶ G}
    (ha : a'.left ≫ φ = φ ≫ a.left) : pushPt h.1.w (x' ≫ a') = U ≫ x ≫ a := by
  rw [← Category.assoc, ← hx]
  refine Over.OverMorphism.ext ?_
  show (x'.left ≫ _) ≫ _ = (x'.left ≫ _) ≫ _
  rw [Category.assoc, ha, Category.assoc]

theorem iso_cubeLB_pull [IsCommMonObj G] [IsCommMonObj G'] {L : LB G.left} {L' : LB G'.left}
    (H : LBIso L' (L.pull φ)) {a' b' : T' ⟶ G'} {a b : T ⟶ G} (ha : pushPt h.1.w a' = U ≫ a)
    (hb : pushPt h.1.w b' = U ≫ b) : LBIso (cubeLB G' ![a', b'] L') ((cubeLB G ![a, b] L).pull U.left) :=
  iso_linComb_pull H _ _ _ U.left fun I => psum_push h _ _ U (fun i => by
    fin_cases i
    exacts [ha, hb]) I.down

end Points

def sqMap : Over.mk ((G' ⊗ G').hom ≫ f) ⟶ G ⊗ G := lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))

theorem push_fst : pushPt h.1.w (fst G' G') = sqMap h ≫ fst G G := (lift_fst _ _).symm

theorem push_snd : pushPt h.1.w (snd G' G') = sqMap h ≫ snd G G := (lift_snd _ _).symm

theorem isPullback_sqMap : IsPullback (sqMap h).left (G' ⊗ G').hom (G ⊗ G).hom f := by
  have e₁ : (sqMap h).left ≫ (fst G G).left = (fst G' G').left ≫ φ := congrArg (fun q => q.left) (push_fst h).symm
  have e₂ : (sqMap h).left ≫ (snd G G).left = (snd G' G').left ≫ φ := congrArg (fun q => q.left) (push_snd h).symm
  have A : IsPullback (snd G G).left (fst G G).left G.hom G.hom := (IsPullback.of_hasPullback G.hom G.hom).flip
  have A' : IsPullback (snd G' G').left (fst G' G').left G'.hom G'.hom := (IsPullback.of_hasPullback G'.hom G'.hom).flip
  have B := A'.paste_horiz h.1
  rw [← e₂, ← h.1.w] at B
  have C := (IsPullback.of_right B e₁ A).paste_vert h.1
  rwa [Over.w, Over.w] at C

def selfMap : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ h.1.w

theorem push_id : pushPt h.1.w (𝟙 G') = selfMap h ≫ 𝟙 G :=
  Over.OverMorphism.ext ((Category.id_comp _).trans (Category.comp_id _).symm)

theorem push_end {a' : G' ⟶ G'} {a : G ⟶ G} (ha : a'.left ≫ φ = φ ≫ a.left) : pushPt h.1.w a' = selfMap h ≫ a :=
  Over.OverMorphism.ext ha

end Group

def baseMap {S S' : Scheme.{0}} (f : S' ⟶ S) : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ Out.baseOver S :=
  Over.homMk f ((Category.comp_id _).trans (Category.id_comp _).symm)

end GlobalTheory.ShapePull

namespace GlobalTheory

open ShapePull

theorem shape_prim_pull_and_descend :
    ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) Mat κ (w w' : J) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (t : TObj g k J b s) (t' : TObj g k J b s'), TMap t' t f → (t.Shape Mat κ → t'.Shape Mat κ) ∧ (t.Prim w w' → t'.Prim w w') ∧ ∀ (K : Type) [Field K] (e : S = Sp K), IsAffine S' → Nonempty S' → (t'.Shape Mat κ → t.Shape Mat κ) ∧ (IsIntegral S' → t'.Prim w w' → t.Prim w w') := by
  intro o _ g k J b Mat κ w w' S S' s s' f t t' ⟨φ, h, hL, hpt, hact⟩
  letI := t.ab.comm
  letI := t'.ab.comm
  have lb : ∀ {X Y : Scheme.{0}} {L : LB X} (_ : L.IsLB) {K : Type} [Fintype K] (ψ : K → (Y ⟶ X)) (ε : K → ℤ),
      (LB.LinComb L ψ ε).IsLB := fun hL _ _ _ _ => DVR.linComb_isLB _ hL _ _
  have pt : ∀ i, pushPt h.1.w (t'.pt i) = baseMap f ≫ t.pt i := fun i => Over.OverMorphism.ext (hpt i)
  have p₁ := fun i j => push_comp h _ (pt i) (hact j)
  have p₂ : ∀ a, pushPt h.1.w (t'.lab a) = baseMap f ≫ t.lab a := fun a => push_linComb h _ pt _
  have i₁ : ∀ j, LBIso (LB.LinComb t'.L (K := Fin 2) ![𝟙 t'.A.left, (t'.act j).left] ![(κ : ℤ), -1])
      ((LB.LinComb t.L (K := Fin 2) ![𝟙 t.A.left, (t.act j).left] ![(κ : ℤ), -1]).pull φ) := fun j =>
    iso_linComb_pull hL _ _ _ φ fun i => by
      fin_cases i
      exacts [(Category.id_comp _).trans (Category.comp_id _).symm, hact j]
  have p₃ := push_mul h _ (push_end h (hact w)) (push_end h (hact w'))
  have i₂ := iso_cubeLB_pull h _ hL (push_comp h _ (push_fst h) (hact w)) (push_snd h)
  have i₃ := iso_cubeLB_pull h _ hL (push_fst h) (push_comp h _ (push_snd h) (hact w'))
  have i₄ := iso_cubeLB_pull h _ hL (push_id h) (push_end h (hact w))
  refine ⟨fun H j => ⟨fun i => eq_up h _ (p₁ i j) (p₂ _) ((H j).1 i), ?_⟩, fun H => ⟨eq_up h _ p₃ (push_id h) H.1,
    iso_up (lb t.isLB _ _) (lb t.isLB _ _) (lb t'.isLB _ _) (lb t'.isLB _ _) i₂ i₃ H.2.1,
    iso_up t.isLB (lb t.isLB _ _) t'.isLB (lb t'.isLB _ _) hL i₄ H.2.2⟩, ?_⟩
  · exact (pol_pull S S' t.A t'.A f φ _ _ (lb t.isLB _ _) (lb t'.isLB _ _) t.ab h (i₁ j)).2.1 (H j).2
  rintro K _ rfl - _
  have hf : Epi f := epi_of_isPullback (IsPullback.id_vert f)
  have hφ : Epi φ := epi_of_isPullback h.1
  have := t.ab.smooth
  have := t.ab.proper
  have := t.ab.geomConnected
  have pr : IsProper (t.A ⊗ t.A).hom := by
    rw [Over.tensorObj_hom]
    infer_instance
  exact ⟨fun H j => ⟨fun i => eq_down h _ hf (p₁ i j) (p₂ _) ((H j).1 i),
      relAmple_down t.ab h.1 (lb t.isLB _ _) (lb t'.isLB _ _) (i₁ j) (H j).2⟩,
    fun _ H => ⟨eq_down h _ hφ p₃ (push_id h) H.1,
      iso_down (isPullback_sqMap h) (smooth_tensorObj_hom _ _) pr (geometricallyConnected_tensorObj_hom _ _)
        (lb t.isLB _ _) (lb t.isLB _ _) (lb t'.isLB _ _) (lb t'.isLB _ _) i₂ i₃ H.2.1,
      iso_down h.1 ‹_› ‹_› ‹_› t.isLB (lb t.isLB _ _) t'.isLB (lb t'.isLB _ _) hL i₄ H.2.2⟩⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) Mat κ (w w' : J) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (t : TObj g k J b s) (t' : TObj g k J b s'), TMap t' t f → (t.Shape Mat κ → t'.Shape Mat κ) ∧ (t.Prim w w' → t'.Prim w w') ∧ ∀ (K : Type) [Field K] (e : S = Sp K), IsAffine S' → Nonempty S' → (t'.Shape Mat κ → t.Shape Mat κ) ∧ (IsIntegral S' → t'.Prim w w' → t.Prim w w') := by
  first | exact @GlobalTheory.shape_prim_pull_and_descend | exact GlobalTheory.shape_prim_pull_and_descend | (intros; apply GlobalTheory.shape_prim_pull_and_descend <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LambdaBundleAdjointOfWeilPairingAdjoint
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LambdaBundleAdjointOfWeilPairingAdjoint
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory


open AdjointOfPairing in
theorem lbIso_cubeLB_of_pairing_adjoint : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (P : Out.PolAV (Sp k)) (a a' : P.A ⟶ P.A), IsMonHom a → IsMonHom a' → (∀ (n : ℕ) (x y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ), 0 < n → x ^ n = 1 → y ^ n = 1 → Out.WeilIs P.A P.L n (x ≫ a) y c → Out.WeilIs P.A P.L n x (y ≫ a') c) → LBIso (cubeLB P.A ![fst P.A P.A ≫ a, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ a'] P.L) := by
  intro hl k _ _ _ P a a' ha ha' H
  have := P.isAb.comm
  have out : ∀ r : P.A ⟶ P.A ⊗ P.A, (∃ t : LB.Gen (LB.LinComb P.L (fun i => r.left ≫ Out.rosatiφ P.A a a' i)
      Out.rosatiε), t.IsGen) → ∃ t : ((LB.LinComb P.L (Out.rosatiφ P.A a a') Out.rosatiε).pull r.left).Gen,
        t.IsGen := fun r ⟨t, ht⟩ => gen_chartPull (chartPullOut P.L _ _ _ _ fun _ => rfl) t ht
  obtain ⟨t, ht⟩ := GlobalTheory.T.seesaw_triviality_on_dense_fibres_product_abelian hl.globalFns k P.A P.A (LB.LinComb P.L (Out.rosatiφ P.A a a') Out.rosatiε) P.L
    P.isAb P.isAb P.isLB P.ample
    (DVR.linComb_isLB P.L P.isLB _ _)
    (out _ (exists_gen_of_formEq_zero P.isLB fun U _ h => by
      rw [prod_ros, MonObj.one_comp, _root_.one_mul, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel))
    ((TorsionDense.dense_torsion P hl.irred hl.kerPow).mono (by
      intro z hz
      simp only [Set.mem_iUnion] at hz ⊢
      obtain ⟨x, ⟨n, hn, hxn⟩, q, rfl⟩ := hz
      exact ⟨x, out _ (exists_gen_fibre hl P a a' n (Nat.cast_ne_zero.2 hn.ne') x hxn
        fun y c hy => H n x y c hn hxn hy), q, rfl⟩))
    (out _ (exists_gen_of_formEq_zero P.isLB fun U _ h => by
      rw [prod_ros, MonObj.one_comp, _root_.mul_one, _root_.mul_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel))
  obtain ⟨u, hu, -⟩ := exists_gen P.isLB
    (φ' := Sum.elim (fun I : ULift.{0} (Finset (Fin 2)) => (psum P.A ![fst P.A P.A, snd P.A P.A ≫ a'] I.down).left)
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum P.A ![fst P.A P.A ≫ a, snd P.A P.A] I.down).left))
    (ε' := Sum.elim (fun I => (-1) ^ (2 - I.down.card)) (fun I => -(-1) ^ (2 - I.down.card)))
    (fun V _ h => by
      have p := prod_ros a a' (fst P.A P.A) (snd P.A P.A) h
      rw [lift_fst_snd] at p
      simp only [Over.id_left, Category.id_comp] at p
      refine (DVR.prod_neg _ _ p).trans (Eq.trans ?_ (DVR.prod_sum₂ (K := ULift.{0} (Finset (Fin 2)))
        (K' := ULift.{0} (Finset (Fin 2))) (U := V) _ (NormRos.prod_square (fst P.A P.A) (snd P.A P.A ≫ a') h)
        (DVR.prod_neg _ _ (NormRos.prod_square (fst P.A P.A ≫ a) (snd P.A P.A) h))).symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.invGen P.L _ _ t) (DVR.invGen_isGen _ _ _ _ ht)
  exact lbIso_of_gen u hu

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LambdaBundleAdjointOfWeilPairingAdjointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lambdaBundle_adjoint_of_weilPairing_adjoint : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (P : Out.PolAV (Sp k)) (a a' : P.A ⟶ P.A), IsMonHom a → IsMonHom a' → (∀ (n : ℕ) (x y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ), 0 < n → x ^ n = 1 → y ^ n = 1 → Out.WeilIs P.A P.L n (x ≫ a) y c → Out.WeilIs P.A P.L n x (y ≫ a') c) → LBIso (cubeLB P.A ![fst P.A P.A ≫ a, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ a'] P.L) := by
  first | exact @GlobalTheory.lbIso_cubeLB_of_pairing_adjoint | exact GlobalTheory.lbIso_cubeLB_of_pairing_adjoint | (intros; apply GlobalTheory.lbIso_cubeLB_of_pairing_adjoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalOfFieldExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.SiegelDescent

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'}

private theorem hom_ext_tensor_left_of_fst_snd {B Z : Scheme.{0}} {X : Over B} (g k : Z ⟶ (X ⊗ X).left)
    (h1 : g ≫ (fst X X).left = k ≫ (fst X X).left) (h2 : g ≫ (snd X X).left = k ≫ (snd X X).left) : g = k := by
  have hw : k ≫ (X ⊗ X).hom = g ≫ (X ⊗ X).hom := by
    rw [← Over.w (fst X X), ← Category.assoc, ← h1, Category.assoc]
  have key := CartesianMonoidalCategory.hom_ext (Over.homMk g rfl : Over.mk (g ≫ (X ⊗ X).hom) ⟶ X ⊗ X)
    (Over.homMk k hw) (by ext; simpa using h1) (by ext; simpa using h2)
  exact congrArg CommaMorphism.left key

private theorem pGen_of_isGen_iso_pull {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : L'.Iso (L.pull F))
    (hw : w.IsGen) : PGen w := by
  intro Y f y j j' k k' hj hj' hk hk'
  obtain ⟨J, hJ⟩ : ∃ J : (L.pull F).ι, J = fun _ => j := ⟨_, rfl⟩
  obtain ⟨J', hJ'⟩ : ∃ J' : (L.pull F).ι, J' = fun _ => j' := ⟨_, rfl⟩
  have m1 : f y ∈ (L.pull F).U J := by rw [hJ]; exact mem_pull.2 hj
  have m2 : f y ∈ (L.pull F).U J' := by rw [hJ']; exact mem_pull.2 hj'
  have hy : f y ∈ ((L.pull F).div L').U (J, k) ⊓ ((L.pull F).div L').U (J', k') := ⟨⟨m1, hk⟩, ⟨m2, hk'⟩⟩
  have e := congrArg (gm f y _) (hw (J, k) (J', k'))
  rw [gm_res f y _ hy, map_mul, gm_res f y _ hy] at e
  have eg : gm f y (((L.pull F).div L').U (J, k) ⊓ ((L.pull F).div L').U (J', k'))
      (((L.pull F).div L').g (J, k) (J', k')) =
      gm (f ≫ F) y (L.U j ⊓ L.U j') (L.g j j') * (gm f y (L'.U k ⊓ L'.U k') (L'.g k k'))⁻¹ := by
    have hy' : f y ∈ (L.pull F).U J ⊓ L'.U k ⊓ ((L.pull F).U J' ⊓ L'.U k') := ⟨⟨m1, hk⟩, ⟨m2, hk'⟩⟩
    show gm f y ((L.pull F).U J ⊓ L'.U k ⊓ ((L.pull F).U J' ⊓ L'.U k'))
      (res _ ((L.pull F).g J J') * (res _ (L'.g k k'))⁻¹) = _
    rw [map_mul, map_inv, gm_res f y _ hy', gm_res f y _ hy', gm_pull_g L F f y J J' m1 m2]
    subst hJ hJ'
    rfl
  rw [eg] at e
  unfold gw
  subst hJ hJ'
  exact e

private theorem flat_spMap_of_field_hom' {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) : Flat (spMap i) := by
  unfold spMap
  infer_instance

private theorem surjective_spMap_of_field_hom {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) : Surjective (spMap i) := by
  constructor
  intro x
  exact ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), Subsingleton.elim (α := PrimeSpectrum K₀) _ _⟩

theorem lift_comp_square {φ : A'.left ⟶ A.left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (hs : IsSquare φ φ₂)
    {T : Over S} {T' : Over S'} (u : T'.left ⟶ T.left) (a b : T ⟶ A) (a' b' : T' ⟶ A')
    (ha : a'.left ≫ φ = u ≫ a.left) (hb : b'.left ≫ φ = u ≫ b.left) :
    (lift a' b').left ≫ φ₂ = u ≫ (lift a b).left := by
  have e1 : (lift a' b').left ≫ (fst A' A').left = a'.left := by rw [← Over.comp_left, lift_fst]
  have e2 : (lift a b).left ≫ (fst A A).left = a.left := by rw [← Over.comp_left, lift_fst]
  have e3 : (lift a' b').left ≫ (snd A' A').left = b'.left := by rw [← Over.comp_left, lift_snd]
  have e4 : (lift a b).left ≫ (snd A A).left = b.left := by rw [← Over.comp_left, lift_snd]
  apply hom_ext_tensor_left_of_fst_snd
  · rw [Category.assoc, hs.1, ← Category.assoc, e1, ha, Category.assoc, e2]
  · rw [Category.assoc, hs.2, ← Category.assoc, e3, hb, Category.assoc, e4]

theorem eq_one_of_pull {f : S' ⟶ S} [Flat f] [Surjective f] [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}
    {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} {P : LB (A ⊗ A).left} {P' : LB (A' ⊗ A').left}
    (h : IsGrpPullback A' A f φ) (hs : IsSquare φ φ₂) (hP : P.IsLB) (hP' : P'.IsLB) (hw : LBIso P' (P.pull φ₂))
    (hK : ∀ (T : Over S') (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x = 1)
    (T : Over S) (x : T ⟶ A) (hx : ∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) : x = 1 := by
  obtain ⟨w, hwg⟩ := hw
  obtain ⟨t, ht⟩ := hx
  let T' : Over S' := Over.mk (pullback.snd T.hom f)
  let p : T'.left ⟶ T.left := pullback.fst T.hom f
  have hp : p ≫ T.hom = T'.hom ≫ f := pullback.condition
  have hxl : (p ≫ x.left) ≫ A.hom = T'.hom ≫ f := by rw [Category.assoc, Over.w x]; exact hp
  let xl : T'.left ⟶ A'.left := h.1.lift (p ≫ x.left) T'.hom hxl
  have hxl1 : xl ≫ φ = p ≫ x.left := h.1.lift_fst _ _ _
  have hxl2 : xl ≫ A'.hom = T'.hom := h.1.lift_snd _ _ _
  let x' : T' ⟶ A' := Over.homMk xl hxl2
  have hA : φ ≫ A.hom = A'.hom ≫ f := h.1.w
  let Z : Over S := Over.mk ((A' ⊗ T').hom ≫ f)
  let a0 : Z ⟶ A := Over.homMk ((fst A' T').left ≫ φ) (by
    rw [Category.assoc, hA, ← Category.assoc, Over.w (fst A' T')]; rfl)
  let b0 : Z ⟶ T := Over.homMk ((snd A' T').left ≫ p) (by
    rw [Category.assoc, hp, ← Category.assoc, Over.w (snd A' T')]; rfl)
  let q : (A' ⊗ T').left ⟶ (A ⊗ T).left := (lift a0 b0).left
  have hq1 : q ≫ (fst A T).left = (fst A' T').left ≫ φ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have hq2 : q ≫ (snd A T).left = (snd A' T').left ≫ p := by
    rw [← Over.comp_left, lift_snd]; rfl
  have hc : (lift (snd A' T' ≫ x') (fst A' T')).left ≫ φ₂ = q ≫ (lift (snd A T ≫ x) (fst A T)).left := by
    refine lift_comp_square hs q _ _ _ _ ?_ hq1.symm
    rw [Over.comp_left, Over.comp_left, Category.assoc, ← Category.assoc q, hq2, Category.assoc]
    exact congrArg ((snd A' T').left ≫ ·) hxl1
  obtain ⟨a, ha, -⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_gen_move hP hP' w (pGen_of_isGen_iso_pull w hwg) (K := PUnit)
    (fun _ => (lift (snd A T ≫ x) (fst A T)).left) (fun _ => (lift (snd A' T' ≫ x') (fst A' T')).left)
    (fun _ => 1) q (fun _ => hc) t ht
  have hx' : x' = 1 := hK T' x' ⟨a, ha⟩
  let Zp : Over S := Over.mk (T'.hom ≫ f)
  let z : Zp ⟶ A := Over.homMk (p ≫ x.left) hxl
  have hz : z.left = (1 : T' ⟶ A').left ≫ φ := by
    show p ≫ x.left = _
    rw [← hxl1, ← hx']
    rfl
  have hzz := h.2 T' 1 1 z z hz hz
  rw [_root_.mul_one] at hzz
  have hz1 : z = 1 := by
    have e : z * z = z * 1 := by
      rw [_root_.mul_one]
      exact Over.OverMorphism.ext (hzz.trans hz.symm)
    exact mul_left_cancel e
  have hfl : Flat p := inferInstanceAs (Flat (pullback.fst T.hom f))
  have hsu : Surjective p := inferInstanceAs (Surjective (pullback.fst T.hom f))
  have hpe : Epi p := Flat.epi_of_flat_of_surjective p
  let pO : Zp ⟶ T := Over.homMk p hp
  have e1 : pO ≫ x = z := Over.OverMorphism.ext rfl
  have e2 : pO ≫ (1 : T ⟶ A) = 1 := by
    simp
  have hfin : p ≫ x.left = p ≫ (1 : T ⟶ A).left := by
    have e3 := congrArg CommaMorphism.left ((e1.trans hz1).trans e2.symm)
    exact e3
  exact Over.OverMorphism.ext ((cancel_epi p).1 hfin)

theorem principal_of_fieldExtension : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (s₀ : Sp K₀ ⟶ Sp o) (s : Sp K ⟶ Sp o) (c₀ : SiegPre h M ζ s₀) (c : SiegPre h M ζ s), SiegPB c c₀ (spMap i) → c.Principal → c₀.Principal := by
  intro h M o _ ζ K₀ K _ _ i s₀ s c₀ c hpb hc
  obtain ⟨φ, φ₂, hg, hs, hw, -⟩ := hpb
  have hfl : Flat (spMap i) := flat_spMap_of_field_hom' i
  have hsu : Surjective (spMap i) := surjective_spMap_of_field_hom i
  refine ⟨?_, fun T x hx => eq_one_of_pull hg hs c₀.isLB c.isLB hw hc.2 T x hx⟩
  obtain ⟨w, hwg⟩ := hw
  have hΔ : (lift (𝟙 c.A) (𝟙 c.A)).left ≫ φ₂ = φ ≫ (lift (𝟙 c₀.A) (𝟙 c₀.A)).left :=
    lift_comp_square hs φ _ _ _ _ (by simp) (by simp)
  have i1 : LBIso c.diag (c₀.P.pull (φ ≫ (lift (𝟙 c₀.A) (𝟙 c₀.A)).left)) := by
    have := iso_linComb (pGen_of_isGen_iso_pull w hwg) (K := PUnit) (fun _ => (lift (𝟙 c.A) (𝟙 c.A)).left) (fun _ => 1)
    rw [hΔ] at this
    exact this
  obtain ⟨w₀, hw₀⟩ := exists_iso_linComb c₀.isLB (K := PUnit) (F := (lift (𝟙 c₀.A) (𝟙 c₀.A)).left)
    (fun _ => (lift (𝟙 c₀.A) (𝟙 c₀.A)).left) (fun _ => 1) (fun _ _ _ => rfl)
  have i2 : LBIso (c₀.diag.pull φ) (c₀.P.pull (φ ≫ (lift (𝟙 c₀.A) (𝟙 c₀.A)).left)) :=
    iso_linComb (pGen_of_isGen_iso_pull w₀ hw₀) (K := PUnit) (fun _ => φ) (fun _ => 1)
  have hd : LBIso c.diag (c₀.diag.pull φ) :=
    LBIso.trans (pull_isLB c.isLB _) (pull_isLB c₀.isLB _) (pull_isLB (pull_isLB c₀.isLB _) _) i1 i2.symm
  exact GlobalTheory.AmpleDescent.relAmple_of_fieldExtension K₀ K i c₀.A c.A φ c₀.diag c.diag c₀.ab hg
    (pull_isLB c₀.isLB _) (pull_isLB c.isLB _) hd hc.1

end GlobalTheory.SiegelDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LambdaBundleIsoOfPrimeToPWeilPairings
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LambdaBundleIsoOfPrimeToPWeilPairings
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open PairingDetermines IsoDescent PrimCocycle

theorem lam_iso_of_weil_pairings : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] (P P' : Out.PolAV (Sp k)) (α : P.A ⟶ P'.A) (p d : ℕ), IsMonHom α → p.Prime → CharZero k → (∀ (n : ℕ) (x y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c : kˣ), 0 < n → n.Coprime p → x ^ n = 1 → y ^ n = 1 → Out.WeilIs P.A P.L n x y (unitOn c) → Out.WeilIs P'.A P'.L n (x ≫ α) (y ≫ α) (unitOn (c ^ d))) → LBIso (abelian₂ P.A (lbPow P.L d)) (abelian₂ P.A (P'.L.pull α.left)) := by
  intro hL k _ _ P P' α p d hα hp _ hW
  haveI : IsCommMonObj P.A := P.isAb.comm
  have fib : ∀ (x : 𝟙_ (Over (Sp k)) ⟶ P.A) (n : ℕ), 0 < n → n.Coprime p → x ^ n = 1 →
      ∃ t : LB.Gen ((LB.div (abelian₂ P.A (P'.L.pull α.left)) (abelian₂ P.A (lbPow P.L d))).pull
        (lift (toUnit P.A ≫ x) (𝟙 P.A)).left), t.IsGen := by
    intro x n hn hnp hx
    obtain ⟨u, hu, v⟩ := exists_gen_lam hL.globalFns hL.cube P (𝟙 P.A) d n x hx
    obtain ⟨u', hu', v'⟩ := exists_gen_lam hL.globalFns hL.cube P' α 1 n x hx
    refine exists_gen_div_pull P.L P'.L (𝟙 _) α.left d 1 (lamφ P.A) lamε _ ?_
    refine lbIso_of_invariant P.isLB P'.isLB _ _ _ _ (Out.mulA P.A n).left
      (I := {y : 𝟙_ (Over (Sp k)) ⟶ P.A // y ^ n = 1}) (fun y => ((toUnit P.A ≫ y.1) * 𝟙 P.A).left) (fun y => ?_)
      (fun U f hf => torsion_invariant_descends (fun S _ P n hn => by
        obtain ⟨a, b, c, e, -⟩ := hL.mulN S P n hn
        exact ⟨a, b, c, e⟩) k P n (Nat.cast_ne_zero.2 hn.ne') U f fun y hy => hf ⟨y, hy⟩) u hu u' hu'
      (fun y z J J' hJ hJ' => ?_)
    · rw [← Over.comp_left, Out.mulA, MonObj.comp_pow, Category.comp_id, mul_pow, ← MonObj.comp_pow, y.2,
        MonObj.comp_one, _root_.one_mul]
    · obtain ⟨c, hc, -⟩ := (hL.weil _ P n _).1 x y.1 hx y.2
      obtain ⟨c, rfl⟩ : ∃ c₀ : kˣ, unitOn c₀ = c :=
        ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom c,
          Units.ext ((Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id_apply c.val)⟩
      have e : unitOn (c ^ d) = unitOn c ^ d := map_pow (Units.map _) c d
      have h₁ := v y.1 (unitOn c) y.2 (by rw [Category.comp_id, Category.comp_id]; exact hc) z J hJ
      have h₂ := v' y.1 (unitOn (c ^ d)) y.2 (hW n x y.1 c hn hnp hx y.2 hc) z J' hJ'
      rw [pow_one, e] at h₂
      refine (congrArg₂ (fun a b => a * b⁻¹) h₂ h₁).trans ?_
      exact mul_div_mul_right_eq_div _ _ _ |> fun h => by simpa only [div_eq_mul_inv] using h
  refine T.seesaw_triviality_on_dense_fibres_product_abelian hL.globalFns k P.A P.A (LB.div (abelian₂ P.A (P'.L.pull α.left)) (abelian₂ P.A (lbPow P.L d))) P.L
    P.isAb P.isAb P.isLB P.ample
    (LB.isLB_div (DVR.linComb_isLB _ (LB.isLB_pull P'.isLB _) _ _)
      (DVR.linComb_isLB _ (DVR.linComb_isLB _ P.isLB _ _) _ _)) ?_ ?_ ?_
  · have := fib 1 1 one_pos (Nat.coprime_one_left p) (one_pow _)
    rwa [MonObj.comp_one] at this
  · refine (CoprimeTorsion.dense_torsion hL.ample hL.kerPow hL.irred k P hp).mono ?_
    exact Set.biUnion_subset_biUnion_left fun x ⟨n, hn, hnp, hx⟩ => fib x n hn hnp hx
  · obtain ⟨u, hu⟩ := exists_gen_axis (A := P.A) P.isLB (𝟙 _) d
    obtain ⟨u', hu'⟩ := exists_gen_axis (A := P.A) P'.isLB α.left 1
    exact exists_gen_div_pull P.L P'.L (𝟙 _) α.left d 1 (lamφ P.A) lamε _
      (lbIso_of_gens P.isLB P'.isLB _ _ _ _ u hu u' hu')

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LambdaBundleIsoOfPrimeToPWeilPairingsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lambdaBundleIso_of_primeToP_weilPairings : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] (P P' : Out.PolAV (Sp k)) (α : P.A ⟶ P'.A) (p d : ℕ), IsMonHom α → p.Prime → CharZero k → (∀ (n : ℕ) (x y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c : kˣ), 0 < n → n.Coprime p → x ^ n = 1 → y ^ n = 1 → Out.WeilIs P.A P.L n x y (unitOn c) → Out.WeilIs P'.A P'.L n (x ≫ α) (y ≫ α) (unitOn (c ^ d))) → LBIso (abelian₂ P.A (lbPow P.L d)) (abelian₂ P.A (P'.L.pull α.left)) := by
  first | exact @GlobalTheory.lam_iso_of_weil_pairings | exact GlobalTheory.lam_iso_of_weil_pairings | (intros; apply GlobalTheory.lam_iso_of_weil_pairings <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RaisedModelFiniteCoverAmpleFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RaisedModelFiniteCoverAmpleFrames
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.RaisedAmple

theorem exists_closure {O F F' : Type} [CommRing O] [Field F] [Field F'] [CharZero F] [CharZero F'] (β : O →+* F)
    (k : F →+* F') (hβ : IsDedFrac β) (hk : k.Finite) :
    ∃ (O' : Type) (_ : CommRing O') (β' : O' →+* F') (b : O →+* O'), IsDedFrac β' ∧ β'.comp b = k.comp β ∧ b.Finite ∧
      ∀ x : F', IsIntegral ℤ x → x ∈ β'.range := by
  obtain ⟨⟨_, _⟩, _, hfr⟩ := hβ
  letI := β.toAlgebra
  letI := k.toAlgebra
  letI := (k.comp β).toAlgebra
  have : IsScalarTower O F F' := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional F F' := hk
  have hD : IsDedekindDomain (integralClosure O F') := integralClosure.isDedekindDomain O F F'
  have hF : IsFractionRing (integralClosure O F') F' := integralClosure.isFractionRing_of_finite_extension F F'
  have hfin : Module.Finite O (integralClosure O F') := IsIntegralClosure.finite O F F' _
  refine ⟨integralClosure O F', inferInstance, algebraMap _ F', algebraMap O _, ⟨⟨inferInstance, hD⟩, inferInstance, hF⟩,
    rfl, hfin, fun x hx => ⟨⟨x, hx.tower_top⟩, rfl⟩⟩

theorem lift_lift {T X Y Z W : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (g' : W ⟶ Y) (k : W ⟶ Z) (hk : g' ≫ g = k) (r : T ⟶ X)
    (s : T ⟶ W) (w : r ≫ f = s ≫ k) (r' : T ⟶ pullback f g) (h₁ : r' ≫ pullback.fst _ _ = r)
    (h₂ : r' ≫ pullback.snd _ _ = s ≫ g') :
    ∃ e : pullback f k ≅ pullback (pullback.snd f g) g', pullback.lift r' s h₂ = pullback.lift r s w ≫ e.hom := by
  subst hk
  refine ⟨(pullbackLeftPullbackSndIso f g g').symm, ?_⟩
  rw [Iso.symm_hom, Iso.eq_comp_inv]
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackLeftPullbackSndIso_hom_fst, pullback.lift_fst_assoc, pullback.lift_fst, h₁]
  · rw [Category.assoc, pullbackLeftPullbackSndIso_hom_snd, pullback.lift_snd, pullback.lift_snd]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isIntegral_zeta {A : ℕ} (hA : 0 < A) : IsIntegral ℤ (zeta A) :=
  (Complex.isPrimitiveRoot_exp A hA.ne').isIntegral hA

theorem exists_coeff {l : Level H} (c : Coeff l) (l' : Level H) : ∃ c' : Coeff l', c.F ≤ c'.F := by
  have := c.fin
  have := GlobalTheory.BaseRing.finiteDimensional_KA l'
  have hM : 0 < l'.M' := Nat.lcm_pos (lt_of_lt_of_le (by norm_num) l'.three_le) l'.A_pos
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {zeta l'.M'}) :=
    IntermediateField.adjoin.finiteDimensional (isIntegral_zeta hM).tower_top
  refine ⟨⟨(c.F ⊔ KA l') ⊔ IntermediateField.adjoin ℚ {zeta l'.M'}, inferInstance, fun τ a => ?_, ?_, ?_⟩, ?_⟩
  · exact (le_sup_left.trans le_sup_left : c.F ≤ _) (c.conj τ a)
  · exact (le_sup_right : IntermediateField.adjoin ℚ {zeta l'.M'} ≤ _) (IntermediateField.subset_adjoin _ _ rfl)
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_left.trans le_sup_left

theorem levComp_comp {D : Datum H} {l l' l'' : Level H} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    {b : Base l B} {b' : Base l' B'} {b'' : Base l'' B''} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'}
    {s'' : S'' ⟶ Sp B''} {o'' : Obj D l'' b'' s''} {o' : Obj D l' b' s'} {o : Obj D l b s} {r : S' ⟶ S} {g : S'' ⟶ S'}
    {ξ : SABMap o''.t o'.t g} {ν : SABMap o'.t o.t r} (hd : l.Dvd l') (hd' : l'.Dvd l'') (h' : LevComp o'' o' g ξ)
    (h : LevComp o' o r ν) (ν' : SABMap o''.t o.t (g ≫ r)) (e : ν'.φ = ξ.φ ≫ ν.φ) : LevComp o'' o (g ≫ r) ν' := by
  refine ⟨fun a => ?_, fun a => ?_⟩
  · rw [← Nat.div_mul_div hd'.1 hd.1, pow_mul, e, ← Category.assoc, LevelCover.sec_pow ξ _ _ (h'.1 a), Category.assoc,
      h.1, Category.assoc]
  · rw [← Nat.div_mul_div hd'.2.2 hd.2.2, pow_mul, e, ← Category.assoc, LevelCover.sec_pow ξ _ _ (h'.2 a),
      Category.assoc, h.2, Category.assoc]

theorem exists_isInc_of_mem {O : Type} [CommRing O] (i : O →+* ℂ) (hi : Function.Injective i) {S A : ℕ}
    (h₁ : (1 + H.rt0) / 2 ∈ i.range) (h₂ : (S : ℂ)⁻¹ ∈ i.range) (h₃ : zeta A ∈ i.range) :
    ∃ b : RZ H S A →+* O, IsInc (RZ H S A).subtype i b := by
  have hle : RZ H S A ≤ i.range := by
    unfold RZ
    rw [Subring.closure_le]
    rintro x (rfl | rfl | rfl) <;> assumption
  let e : O ≃+* i.range := RingEquiv.ofBijective i.rangeRestrict
    ⟨fun x y h => hi (congrArg Subtype.val h), i.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (Subring.inclusion hle), fun x => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply (Subring.inclusion hle x))

theorem exists_cover (L₁ : Out.Laws) (L₂ : Out.Laws2) (L₃ : Out.Laws3) {D : Datum H} {Xo : ∀ l : Level H, Moduli D l}
    (hN : ToroidalLevelCompatibility (H := H) (D := D)) {l l' : Level H} {c : Coeff l} {c' : Coeff l'} {O O' : Type} [CommRing O]
    [CommRing O'] {β : O →+* c.F} {β' : O' →+* c'.F} (Y : Model (Xo l) c β) (b : O →+* O') (d : l.Dvd l')
    (hc : c.F ≤ c'.F) (hβ : IsDedFrac β) (hβ' : IsDedFrac β')
    (hb : β'.comp b = (IntermediateField.inclusion hc).toRingHom.comp β) (hfin : b.Finite) :
    ∃ (Y' : Model (Xo l') c' β') (r : (Xo l').XF c' ⟶ (Xo l).XF c) (ν : SABMap Y'.oF.t Y.oF.t r)
      (a : (ofModel Y').Above (ofModel Y) b r ν), LevComp Y'.oF Y.oF r ν ∧ IsFinite a.π ∧ Surjective a.π := by
  obtain ⟨o, ⟨m0⟩⟩ := GlobalTheory.obj_pull E H D l' (KA l') (KA l') (baseKA l') (baseKA l') (RingHom.id _) _ _ (Xo l').s
    (pullback.fst (Xo l').s (spMap (IntermediateField.inclusion c'.le).toRingHom) ≫ (Xo l').s)
    (pullback.fst (Xo l').s (spMap (IntermediateField.inclusion c'.le).toRingHom)) rfl rfl
    (by simp [spMap]) (Xo l').univ
  obtain ⟨k, r, ν, hr, hk, hl, hf, -, hs⟩ :=
    GlobalTheory.LevelMapField.exists_levelMap L₁ L₂ L₃ E H D Xo hN l l' c' o m0 d
  have hkk : k = (IntermediateField.inclusion hc).toRingHom.comp (IntermediateField.inclusion c.le).toRingHom :=
    RingHom.ext fun x => Subtype.ext (hk x)
  obtain ⟨r', hr₁, hr₂⟩ : ∃ r' : (Xo l').XF c' ⟶ (Xo l).XF c, r' ≫ pullback.fst _ _ = r ∧
      r' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc).toRingHom :=
    ⟨pullback.lift r (pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc).toRingHom)
      (by rw [hr, hkk, spMap_comp, Category.assoc]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨ν', hν'⟩ := LevelCover.sab_cancel Y.m0.toSABMap ν r' hr₁
  have hl' : LevComp o Y.oF r' ν' :=
    ⟨fun x => LevelCover.sec_cancel ν' Y.m0.toSABMap _ _ (by
        rw [hν', hl.1, ← hr₁, Category.assoc]; exact congrArg _ (Y.m0.eta x).symm),
      fun x => LevelCover.sec_cancel ν' Y.m0.toSABMap _ _ (by
        rw [hν', hl.2, ← hr₁, Category.assoc]; exact congrArg _ (Y.m0.etaA x).symm)⟩
  obtain ⟨e, he⟩ := lift_lift (Xo l).s _ _ (spMap k) (by rw [hkk, spMap_comp]) r _ hr r' hr₁ hr₂
  have hf' : IsFinite (pullback.lift r' _ hr₂) := by rw [he]; infer_instance
  have hs' : Surjective (pullback.lift r' _ hr₂) := by rw [he]; infer_instance
  have hsm : Smooth (pullback.snd (Xo l').s (spMap (IntermediateField.inclusion c'.le).toRingHom)) := by
    have := (Xo l').smooth
    have : Smooth (Xo l').s := SmoothOfRelativeDimension.smooth D.dim _
    infer_instance
  have hnorm := (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ hsm).2.1
  obtain ⟨C, ⟨a⟩⟩ := GlobalTheory.T.exists_normal_model_above_finite_cover E H _ _ _ _ Y.oF.t β _ _ _
    (pullback.snd (Xo l').s (spMap (IntermediateField.inclusion c'.le).toRingHom)) o.t β' (ofModel Y) b _ r' hr₂ ν' hβ hβ'
    hb (fun x => ⟨hnorm.1 x, hnorm.2 x⟩) hf'
  have hπ : IsFinite a.π := by
    have := a.fin
    have : IsFinite (spMap b) := (IsFinite.SpecMap_iff _).2 hfin
    rw [← pullback.lift_fst a.π C.s a.π_over]
    infer_instance
  have hr' : Surjective r' := by
    have : Surjective (spMap (IntermediateField.inclusion hc).toRingHom) := ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
    rw [← pullback.lift_fst r' _ hr₂]
    infer_instance
  have hj : IsDominant (ofModel Y).j := by
    obtain ⟨⟨_, _⟩, -, hfr⟩ := hβ
    letI := β.toAlgebra
    exact (GlobalTheory.genericPart_dense_proOpen O c.F Y.X _ Y.s Y.jQ Y.flat Y.proj Y.jQ_open Y.jQ_dense).2.2.2.2.2.1
  have hd : IsDominant a.π := by
    have : IsDominant (C.j ≫ a.π) := by rw [a.j_comm]; infer_instance
    exact IsDominant.of_comp C.j a.π
  exact ⟨⟨C.X, C.s, C.normal, C.proj, C.flat, C.jQ, C.jQ_over, C.jQ_open, C.jQ_dense, C.t, o, m0, C.m, C.ab_gen⟩,
    r', ν', a, hl', hπ, surjective_of_isDominant_of_isClosed_range a.π a.π.isClosedMap.isClosed_range⟩

theorem amp_of_raises : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N k : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l : Level H) (B : BaseModel T l₀) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), n.Prime → Odd n → (∃ e, N = n ^ e) → IsUnit (n : O) → l₀.Dvd l → IsDedFrac β → Raises B Y → Nonempty (GlobalTheory.LN.AmpFrames T.t.G T.t.PP.L ((n ^ k) ^ 2)) → GlobalTheory.LN.Amp Y := by
  intro L₁ L₂ L₃ E _ _ _ H D Xo n N k T hN l₀ l B c O _ β Y hn hodd ⟨e, he⟩ hu hd hβ hR ⟨A⟩
  have hNpos : 0 < N := he ▸ pow_pos hn.pos e
  let l' : Level H := { l with A := Nat.lcm l.A N, A_pos := Nat.lcm_pos l.A_pos hNpos }
  have d : l.Dvd l' := ⟨dvd_rfl, le_rfl, Nat.dvd_lcm_left _ _⟩
  have hNA : N ∣ l'.A := Nat.dvd_lcm_right _ _
  obtain ⟨c', hc⟩ := exists_coeff c l'
  have hkfin : (IntermediateField.inclusion hc).toRingHom.Finite := by
    have := c'.fin
    refine RingHom.Finite.of_comp_finite (f := algebraMap ℚ c.F) ?_
    rw [Subsingleton.elim (RingHom.comp _ _) (algebraMap ℚ c'.F)]
    exact RingHom.finite_algebraMap.2 this
  obtain ⟨O', _, β', b, hβ', hb, hfin, hint⟩ := exists_closure β _ hβ hkfin
  obtain ⟨Y', r, ν, a, hl, hf, hs⟩ := exists_cover L₁ L₂ L₃ hN Y b d hc hβ hβ' hb hfin
  obtain ⟨b₁, r₁, ν₁, hb₁, hl₁, ⟨a₁⟩⟩ := hR
  have hbb : ∀ x, (c'.F.val.toRingHom.comp β') (b x) = (c.F.val.toRingHom.comp β) x := fun x =>
    congrArg Subtype.val (RingHom.congr_fun hb x)
  obtain ⟨ν₂, hν₂⟩ := LevelCover.sab_comp ν ν₁ rfl
  have hR' : Raises B Y' := ⟨b.comp b₁, r ≫ r₁, ν₂, fun x => (hbb _).trans (hb₁ x), levComp_comp hd d hl hl₁ ν₂ hν₂,
    ⟨(GlobalTheory.Models.above_comp E H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ B.C (ofModel Y) (ofModel Y') b₁ b r₁ ν₁ r ν ν₂
      a₁ a hν₂).choose⟩⟩
  have hi : Function.Injective (c'.F.val.toRingHom.comp β') := by
    letI := β'.toAlgebra
    have := hβ'.2.2
    exact Subtype.val_injective.comp (IsFractionRing.injective O' c'.F)
  obtain ⟨z, hz⟩ : ∃ z : RZ H n N →+* O', IsInc (RZ H n N).subtype (c'.F.val.toRingHom.comp β') z := by
    refine exists_isInc_of_mem _ hi
      ⟨b (b₁ ⟨(1 + H.rt0) / 2, Subring.subset_closure (by simp)⟩), (hbb _).trans (hb₁ _)⟩ ?_ ?_
    · obtain ⟨u, hu⟩ := hu.exists_right_inv
      refine ⟨b u, eq_inv_of_mul_eq_one_right ?_⟩
      rw [← map_natCast ((c'.F.val.toRingHom.comp β').comp b)]
      exact (map_mul ((c'.F.val.toRingHom.comp β').comp b) _ _).symm.trans (by rw [hu, map_one])
    · have hz : zeta N ∈ c'.F := by
        obtain ⟨m, hm⟩ := hNA
        have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 fun h => l'.A_pos.ne' (by rw [hm, h, mul_zero])
        have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hNpos.ne'
        have : zeta N = zeta l'.A ^ m := by
          rw [zeta, zeta, ← Complex.exp_nat_mul, hm]
          congr 1
          push_cast
          field_simp
        rw [this]
        exact pow_mem (c'.le (baseKA l').ζ.2) m
      obtain ⟨y, hy⟩ := hint ⟨zeta N, hz⟩
        ((isIntegral_algHom_iff c'.F.val.toRingHom.toIntAlgHom Subtype.val_injective).1 (isIntegral_zeta hNpos))
      exact ⟨y, congrArg Subtype.val hy⟩
  obtain ⟨g, hg, mu, -, hgf, -⟩ := GlobalTheory.AbelianLocusMap.exists_map_top L₁ L₂ L₃ hN B Y' z
    ⟨hd.1, hd.2.1, hd.2.2.trans d.2.2⟩ hNA hβ' hz hR'
  have haff : IsAffineHom g := by
    have : IsAffineHom (spMap z) := inferInstance
    have : IsAffineHom (pullback.fst T.s (spMap z)) :=
      isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip this
    rw [← pullback.lift_fst g Y'.s hg]
    infer_instance
  obtain ⟨A', -⟩ := GlobalTheory.T.ampleDeterminantFrames_pullback_of_isAffineHom E H _ _ T.t Y'.t g mu _ A haff
  exact ⟨n ^ k, Y'.X, a.π, Y'.t, a.mu, hodd.pow, by rw [Nat.cast_pow]; exact hu.pow k, hf, hs, ⟨A'⟩⟩

end GlobalTheory.RaisedAmple
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RaisedModelFiniteCoverAmpleFramesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raised_model_finite_cover_ample_frames : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N k : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l : Level H) (B : BaseModel T l₀) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), n.Prime → Odd n → (∃ e, N = n ^ e) → IsUnit (n : O) → l₀.Dvd l → IsDedFrac β → Raises B Y → Nonempty (GlobalTheory.LN.AmpFrames T.t.G T.t.PP.L ((n ^ k) ^ 2)) → GlobalTheory.LN.Amp Y := by
  first | exact @GlobalTheory.RaisedAmple.amp_of_raises | exact GlobalTheory.RaisedAmple.amp_of_raises | (intros; apply GlobalTheory.RaisedAmple.amp_of_raises <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelDataPullbackOfLevelMap
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelDataPullbackOfLevelMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.SiegelDataPull

open GlobalTheory.SiegelPullComp

theorem isSquare_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
    {ψ : G''.left ⟶ G'.left} {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {ψ₂ : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left}
    (h' : Geo.Tor.IsSquare ψ ψ₂) (h : Geo.Tor.IsSquare φ φ₂) : Geo.Tor.IsSquare (ψ ≫ φ) (ψ₂ ≫ φ₂) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc]
  · rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]

theorem siegData_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (O : Type) [CommRing O] (T T' : Scheme.{0}) (sT : T ⟶ Sp O) (f : T' ⟶ T) (t : SAB H T) (t' : SAB H T') (ν : SABMap t' t f) (lev : D.La → (𝟙_ (Over T) ⟶ t.G)) (lev' : D.La → (𝟙_ (Over T') ⟶ t'.G)) (g p N : ℕ) (Ag : SiegelFamily g p N) (z : ZP p N →+* O) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (w : T ⟶ pullback Ag.s (spMap z)), (∀ x, (lev' x).left ≫ ν.φ = f ≫ (lev x).left) → SiegData sT t lev Ag z bas w → SiegData (f ≫ sT) t' lev' Ag z bas (f ≫ w) := by
  intro E _ _ _ H D O _ T T' sT f t t' ν lev lev' g p N Ag z bas w hlev hw
  obtain ⟨o, φ, φ₂, hpb, hsq, hiso, hlv, hsnd, hSPB⟩ := hw
  obtain ⟨⟨o', ho'⟩, -⟩ := GlobalTheory.siegPre_pullback _ _ _ _ _ _ _ ((f ≫ sT) ≫ spMap z) f o
    (Category.assoc f sT (spMap z)).symm
  have hpbo := ho'
  obtain ⟨φ₁, φ₁₂, hpb₁, hsq₁, hiso₁, hlv₁⟩ := hpbo
  have hν : IsGrpPullback t'.G t.G f ν.φ := ν.cart
  have hc : IsGrpPullback o'.A t.G f (φ₁ ≫ φ) := (hpb₁.comp hpb).congr (Category.comp_id f) rfl
  obtain ⟨e, he, hel⟩ := grpPullback_iso hc hν
  haveI := he
  have hpb' : IsGrpPullback o'.A t'.G (𝟙 T') e.hom.left := isGrpPullback_of_iso e
  have hsq' := GlobalTheory.LamPull.exists_isSquare hpb'.1.w
  have hν₂ := GlobalTheory.LamPull.exists_isSquare hν.1.w
  have hΛ : (abelian₂ t.G t.PP.L).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ t.PP.isLB _ _
  have hΛ' : (abelian₂ t'.G t'.PP.L).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ t'.PP.isLB _ _
  have sA := isSquare_comp hsq₁ hsq
  have sB := isSquare_comp hsq' hν₂
  rw [hel] at sB
  have key := GlobalTheory.LamPull.isSquare_unique sA sB
  refine ⟨o', e.hom.left, _, hpb', hsq', ?_, ?_, ?_, ?_⟩
  · have h2 := GlobalTheory.SiegelPullComp.iso_pull φ₁₂ hiso
    have h3 := GlobalTheory.SiegelPullComp.iso_pull_pull hΛ φ₂ φ₁₂
    rw [key] at h3
    have h4 := (GlobalTheory.SiegelPullComp.iso_pull_pull hΛ (lift (pushPt hν.1.w (fst t'.G t'.G))
      (pushPt hν.1.w (snd t'.G t'.G))).left (lift (pushPt hpb'.1.w (fst o'.A o'.A))
      (pushPt hpb'.1.w (snd o'.A o'.A))).left).symm
    have h5 := GlobalTheory.SiegelPullComp.iso_pull (lift (pushPt hpb'.1.w (fst o'.A o'.A))
      (pushPt hpb'.1.w (snd o'.A o'.A))).left ((GlobalTheory.LamPull.lam_pull E H T T' t t' f).2 ν _ hν₂).symm
    have l0 := o'.isLB
    have l1 := pull_isLB o.isLB φ₁₂
    have l2 := pull_isLB (pull_isLB hΛ φ₂) φ₁₂
    refine LBIso.trans l0 l1 (pull_isLB hΛ' _) hiso₁ ?_
    refine LBIso.trans l1 l2 (pull_isLB hΛ' _) h2 ?_
    refine LBIso.trans l2 (pull_isLB hΛ _) (pull_isLB hΛ' _) h3 ?_
    refine LBIso.trans (pull_isLB hΛ _) (pull_isLB (pull_isLB hΛ _) _) (pull_isLB hΛ' _) h4 h5
  · intro u
    apply hν.1.hom_ext
    · rw [Category.assoc, hel, ← Category.assoc, hlv₁ u, Category.assoc, hlv u, hlev]
    · rw [Category.assoc, Over.w e.hom, Over.w (o'.lev u), Over.w (lev' (bas u))]
  · rw [Category.assoc, hsnd]
  · rw [Category.assoc f w (pullback.fst Ag.s (spMap z))]
    exact GlobalTheory.SiegelPullComp.pb_comp hSPB ho'

end GlobalTheory.SiegelDataPull

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelDataPullbackOfLevelMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelData_pullback_of_levelMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (O : Type) [CommRing O] (T T' : Scheme.{0}) (sT : T ⟶ Sp O) (f : T' ⟶ T) (t : SAB H T) (t' : SAB H T') (ν : SABMap t' t f) (lev : D.La → (𝟙_ (Over T) ⟶ t.G)) (lev' : D.La → (𝟙_ (Over T') ⟶ t'.G)) (g p N : ℕ) (Ag : SiegelFamily g p N) (z : ZP p N →+* O) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (w : T ⟶ pullback Ag.s (spMap z)), (∀ x, (lev' x).left ≫ ν.φ = f ≫ (lev x).left) → SiegData sT t lev Ag z bas w → SiegData (f ≫ sT) t' lev' Ag z bas (f ≫ w) := by
  first | exact @GlobalTheory.SiegelDataPull.siegData_pull | exact GlobalTheory.SiegelDataPull.siegData_pull | (intros; apply GlobalTheory.SiegelDataPull.siegData_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClosedTriv
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.SeesawGlobal

theorem isPullback_tensor {S : Scheme.{0}} (T A : Over S) :
    IsPullback (snd T A).left (fst T A).left A.hom T.hom :=
  (IsPullback.of_hasPullback T.hom A.hom).flip

theorem exists_closed_triv :
    Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (T : Over (Sp K)) (N : LB (T ⊗ P.A).left), N.IsLB → (∃ t : (N.pull (lift (𝟙 T) (1 : T ⟶ P.A)).left).Gen, t.IsGen) → ∃ (Z : Scheme.{0}) (i : Z ⟶ T.left), IsClosedImmersion i ∧ ∀ (T' : Over (Sp K)) (h : T' ⟶ T), (∃ t : (N.pull (h ▷ P.A).left).Gen, t.IsGen) ↔ ∃ u : T'.left ⟶ Z, u ≫ i = h.left := by
  intro hL _ K _ _ P T N hN h0
  have hproj : GlobalTheory.AbLaw.IsProjBy P.A.hom := by
    obtain ⟨n, -, m, s, h₁, h₂⟩ := GlobalTheory.AbLaw.polAV_veryAmpleBy hL.polBaseChange (Sp K) P K (𝟙 _) P.A.left
      (𝟙 _) P.A.hom (IsPullback.of_horiz_isIso ⟨by simp⟩)
    exact ⟨_, h₁, m, s, h₂⟩
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.T.exists_closedSubscheme_locallyTrivial_product_lineBundle hL.globalFns K T P.A P.isAb hproj N hN
  refine ⟨H.left, j.left, hj, fun T' h => ⟨?_, ?_⟩⟩
  · rintro ⟨t, ht⟩
    obtain ⟨y, hy⟩ := (hH T' h).1 fun p => ⟨⊤, trivial, GlobalTheory.TorsionFixedAut.exists_gen_pull _ t ht _⟩
    exact ⟨y.left, congrArg (·.left) hy⟩
  · rintro ⟨u, hu⟩
    have hw : u ≫ H.hom = T'.hom := by rw [← Over.w j, ← Category.assoc, hu, Over.w h]
    have hloc := (hH T' h).2 ⟨Over.homMk u hw, Over.OverMorphism.ext hu⟩
    refine GlobalTheory.exists_gen_of_local_of_section (T' ⊗ P.A).left T'.left (fst T' P.A).left
      (lift (𝟙 T') (1 : T' ⟶ P.A)).left _ (pull_isLB hN _)
      (congrArg (·.left) (lift_fst (𝟙 T') (1 : T' ⟶ P.A)))
      (GlobalTheory.BaseChangeFns.app_surjective hL.globalFns _ P.A P.isAb _ _ T'.hom _ _ (isPullback_tensor T' P.A))
      hloc ?_
    refine GlobalTheory.AbLaw.CubeOpen.triv_pull_pull _ _ (GlobalTheory.AbLaw.CubeOpen.triv_comp h.left ?_ h0)
    have e : h ≫ lift (𝟙 T) (1 : T ⟶ P.A) = lift (𝟙 T') (1 : T' ⟶ P.A) ≫ h ▷ P.A := by
      ext <;> simp
    exact congrArg (·.left) e

end GlobalTheory.SeesawGlobal
end
end
