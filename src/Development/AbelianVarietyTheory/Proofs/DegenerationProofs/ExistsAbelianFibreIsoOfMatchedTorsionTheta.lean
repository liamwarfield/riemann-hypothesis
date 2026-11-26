module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsIsSymplecticFamilySpan
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceEqFinrankMulSum
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAbelianFibreIsoOfMatchedTorsionTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAbelianFibreIsoOfMatchedTorsionTheta
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso

namespace GlobalTheory.Ex.FibIso

theorem isThetaPt_mul {S : Scheme.{0}} {P : PolAV S} {k : ℕ} {T : Over S} {I : Type}
    {x : I → (T ⟶ P.A)} {v : I → Γ(T.left, ⊤)} (c : Γ(T.left, ⊤)) (hc : IsUnit c)
    (H : IsThetaPt P k x v) : IsThetaPt P k x (fun i => c * v i) := by
  obtain ⟨h1, h2, h3⟩ := H
  refine ⟨h1, h2, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h3 p
  obtain ⟨c', hc'⟩ := hc.map V.ι.appTop.hom
  refine ⟨V, hV, th, s1, α, τ, U, s2, w, (c' * (show Γ(V.toScheme, ⊤)ˣ from u) : Γ(V.toScheme, ⊤)ˣ), a1, a2, a3, a4,
    a5, a6, a7, fun i => ?_⟩
  have aux : ∀ (a : Γ(T.left, ⊤)) (u₀ : Γ(V.toScheme, ⊤)ˣ) (w₀ : Γ(V.toScheme, ⊤)),
      V.ι.appTop.hom a = u₀.val * w₀ → V.ι.appTop.hom (c * a) = (c' * u₀).val * w₀ := by
    intro a u₀ w₀ h
    rw [map_mul, h, Units.val_mul, hc', _root_.mul_assoc]
  exact aux (v i) u (w i) (a8 i)

def Reads {F : Type} [Field F] (B : NumB F) (Q : PolAV (Sp F)) (E : B.A ≃* (baseOver (Sp F) ⟶ Q.A)) : Prop :=
  (∀ k : ℕ, 1 ≤ k → ∀ b b' : B.A, b ^ k = 1 → b' ^ k = 1 →
    WeilIs Q.A Q.L k (E b) (E b') (unitOn (B.weil k b b'))) ∧
  ∀ m : ℕ, Odd m → (m : F) ≠ 0 → ∀ (Ix : Type) (b : Ix → B.A), (∀ i, b i ^ m ^ 2 = 1) →
    IsThetaPt Q m (fun i => E (b i)) (fun i => fnOf (B.uth m (b i) 1))

theorem exists_reads (hU : BrUthSt) {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (h₁ : D.PsiEven)
    (h₂ : D.TauBimult) {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] {N : NumD F}
    (ν : NumOf D F N) {Q : PolAV (Sp F)} {Φ : Q.A.left ⟶ D.P.A.left} (hΦ : IsFib D F Q Φ) :
    ∃ E : N.A ≃* (baseOver (Sp F) ⟶ Q.A), (∀ b, (ν.eA b).left = (E b).left ≫ Φ) ∧ Reads N.toNumB Q E := by
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hΦ.1 (𝟙 (Sp F)) (TF (R := R) F).hom (Category.id_comp _).symm
  obtain ⟨w, t⟩ := hU R D h₁ h₂ F N ν
  have hE : ∀ b, (ν.eA b).left = ((ν.eA.trans e.symm) b).left ≫ Φ := fun b =>
    (congrArg (fun z => z.left) (e.apply_symm_apply (ν.eA b)).symm).trans (he _)
  refine ⟨ν.eA.trans e.symm, hE, fun k hk b b' hb hb' => ?_, fun m hm hm' Ix b hb => ?_⟩
  · have key : ∀ (s : Sp F ⟶ Sp R) (_ : s = 𝟙 _ ≫ (TF (R := R) F).hom) (x y : baseOver (Sp F) ⟶ Q.A)
        (x₀ y₀ : Over.mk s ⟶ D.P.A) (c : Γ(Sp F, ⊤)ˣ), x₀.left = x.left ≫ Φ → y₀.left = y.left ≫ Φ →
        WeilIs D.P.A D.P.L k x₀ y₀ c → WeilIs Q.A Q.L k x y c := by
      rintro s rfl x y x₀ y₀ c hx hy h
      have := Q.isAb.comm
      exact (weilIs_grpPullback_of_comm' _ _ _ _ _ Φ _ _ D.P.isLB Q.isLB hΦ.1 hΦ.2.1 (baseOver _) k x y x₀ y₀ c
        hx hy).2 h
    exact key _ (Category.id_comp _).symm _ _ _ _ _ (hE b) (hE b') (w k hk b b' hb hb')
  · have key : ∀ (s : Sp F ⟶ Sp R) (_ : s = 𝟙 _ ≫ (TF (R := R) F).hom) (x : Ix → (baseOver (Sp F) ⟶ Q.A))
        (x₀ : Ix → (Over.mk s ⟶ D.P.A)) (v : Ix → Γ(Sp F, ⊤)), (∀ i, (x₀ i).left = (x i).left ≫ Φ) →
        (∀ i, x i ^ m ^ 2 = 1) → IsThetaPt D.P m x₀ v → IsThetaPt Q m x v := by
      rintro s rfl x x₀ v hx hp h
      exact (ThetaPtUp.isThetaPt_iff (T := baseOver (Sp F)) hΦ.1 hΦ.2.1 hx hp _).2 h
    exact key _ (Category.id_comp _).symm _ _ _ (fun i => hE (b i))
      (fun i => by rw [← map_pow, hb, map_one]) (t m hm hm' Ix b hb).1

theorem linComb_map {S : Scheme.{0}} {A T : Over S} [GrpObj A] {G : Type} [Group G] (f : G →* (T ⟶ A)) {r : ℕ}
    (y : Fin r → G) (a : Fin r → ℕ) :
    linComb (fun i => f (y i)) a = f (List.ofFn fun i => y i ^ a i).prod := by
  rw [map_list_prod, List.map_ofFn]
  exact congrArg List.prod (congrArg List.ofFn (funext fun i => (map_pow f (y i) (a i)).symm))

theorem exists_level (hL : Laws) {F : Type} [Field F] (Q : PolAV (Sp F)) {g : ℕ} (hg : Q.g = g) {M : ℕ}
    (hM : (M : F) ≠ 0) {ζ : Fˣ} (hζ : IsPrimitiveRoot ζ M) (x : Fin (2 * g) → (baseOver (Sp F) ⟶ Q.A))
    (hx : ∀ i, x i ^ M = 1) (hp : ∀ i j, WeilIs Q.A Q.L M (x i) (x j) (unitOn ζ ^ stdSymp g i j)) :
    ∃ lev : Out.Level Q M (unitOn ζ), levelBasis lev hg = x := by
  subst hg
  have inj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.injective
  refine exists_level_of_pairing hL.globalFns hL.weil hL.mulN _ Q M _
    (hζ.map_of_injective (Units.map_injective inj)) (fun K _ s => ⟨?_, ?_⟩) x hx hp
  · rw [← map_natCast (Spec.preimage s).hom]
    exact (map_ne_zero _).2 hM
  · have : Nontrivial Γ(Spec (CommRingCat.of K), ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.injective.nontrivial
    exact hζ.map_of_injective (Units.map_injective
      (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom).injective)

theorem exists_iso_of_reads (hL : Laws) (hT : ThetaPtDeterminesSt) {F : Type} [Field F] [IsAlgClosed F]
    {B B' : NumB F} {Q Q' : PolAV (Sp F)} (hg : Q'.g = Q.g) {E : B.A ≃* (baseOver (Sp F) ⟶ Q.A)}
    {E' : B'.A ≃* (baseOver (Sp F) ⟶ Q'.A)} (hE : Reads B Q E) (hE' : Reads B' Q' E') {n : ℕ} (hn : n.Prime)
    (ho : Odd n) (hF : (n : F) ≠ 0) : ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (c : F) (ρ : B.A → B'.A), c ≠ 0 →
      TorsMap B B' (n ^ j) c ρ → ∃ σ : Q.A ≅ Q'.A, IsPolIso Q Q' σ ∧
        ∀ b, b ^ (n ^ j) ^ 2 = 1 → E b ≫ σ.hom = E' (ρ b) := by
  refine ⟨((n ^ 2) ^ 2) ^ Q.g * Q.g.factorial + 4, fun J hJ c ρ hc hρ => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, J = j + 4 := ⟨J - 4, by omega⟩
  have hB : ((n ^ 2) ^ 2) ^ Q.g * Q.g.factorial < n ^ (j + 4) :=
    lt_of_le_of_lt (by omega) (Nat.lt_pow_self hn.one_lt)
  have hm : ((n ^ (j + 4) : ℕ) : F) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hF
  have hM : (((n ^ (j + 4)) ^ 2 : ℕ) : F) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hm
  have hM1 : 1 ≤ (n ^ (j + 4)) ^ 2 := pow_pos (pow_pos hn.pos _) _
  have hlev := nonempty_level_prime_pow hL F Q n ((j + 4) * 2) hn hF
  rw [pow_mul] at hlev
  have hT' := hT Q.g n 2 j _ (n ^ (j + 4)) hn ho le_rfl rfl (by ring) hB F hF Q Q' rfl hg
  have hom : Odd (n ^ (j + 4)) := ho.pow
  generalize n ^ (j + 4) = m at *
  have : NeZero ((m ^ 2 : ℕ) : F) := ⟨hM⟩
  have : NeZero (m ^ 2) := ⟨by omega⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F (m ^ 2)
  have hζ := hz.isUnit_unit (NeZero.ne _)
  generalize (hz.isUnit (NeZero.ne _)).unit = ζ at hζ
  have inj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.injective
  obtain ⟨lev⟩ := hlev (unitOn ζ) (hζ.map_of_injective (Units.map_injective inj))
  let T : Subgroup B.A := (powMonoidHom (m ^ 2)).ker
  let f : T →* (baseOver (Sp F) ⟶ Q.A) := E.toMonoidHom.comp T.subtype
  let f' : T →* (baseOver (Sp F) ⟶ Q'.A) :=
    E'.toMonoidHom.comp (MonoidHom.mk' (fun t => ρ t.1) fun s t => (hρ.1 s.1 t.1 s.2 t.2).1)
  let b : Fin (2 * Q.g) → T := fun i => ⟨E.symm (lev.pt i), by
    show E.symm (lev.pt i) ^ m ^ 2 = 1
    rw [← map_pow, lev.torsion, map_one]⟩
  have hb : lev.pt = fun i => f (b i) := funext fun i => (E.apply_symm_apply _).symm
  obtain ⟨lev', hb'⟩ := exists_level hL Q' hg hM hζ (fun i => f' (b i))
    (fun i => by
      show E' (ρ (b i).1) ^ m ^ 2 = 1
      rw [← map_pow, (hρ.2 _ (b i).2).1, map_one])
    (fun i k => by
      have p₁ := hE.1 _ hM1 _ _ (b i).2 (b k).2
      have p₂ := hE'.1 _ hM1 _ _ (hρ.2 _ (b i).2).1 (hρ.2 _ (b k).2).1
      rw [(hρ.1 _ _ (b i).2 (b k).2).2] at p₂
      simp only [b, MulEquiv.apply_symm_apply] at p₁
      rw [← ((hL.weil _ Q (m ^ 2) (baseOver _)).1 _ _ (lev.torsion i) (lev.torsion k)).unique p₁ (lev.pairing i k)]
      exact p₂)
  let t : (Fin (2 * Q.g) → ℕ) → T := fun a => (List.ofFn fun i => b i ^ a i).prod
  have e : ∀ a, linComb lev.pt a = E (t a).1 := fun a => by rw [hb]; exact linComb_map f b a
  have e' : ∀ a, linComb (levelBasis lev' hg) a = E' (ρ (t a).1) := fun a => by rw [hb']; exact linComb_map f' b a
  let u : (Fin (2 * Q.g) → ZMod (m ^ 2)) → B.A := fun a => (t fun i => (a i).val).1
  have hu : ∀ a, u a ^ m ^ 2 = 1 := fun a => (t _).2
  have v₁ := isThetaPt_mul (fnOf c) ((IsUnit.mk0 c hc).map _) (hE.2 m hom hm _ u hu)
  have v₂ := hE'.2 m hom hm _ (fun a => ρ (u a)) fun a => (hρ.2 _ (hu a)).1
  have q : (fun a => fnOf (B'.uth m (ρ (u a)) 1)) = fun a => fnOf c * fnOf (B.uth m (u a) 1) :=
    funext fun a => by rw [(hρ.2 _ (hu a)).2]; exact map_mul _ _ _
  rw [q] at v₂
  have l : levelPoint lev rfl = fun a => E (u a) := funext fun a => e _
  have l' : levelPoint lev' hg = fun a => E' (ρ (u a)) := funext fun a =>
    (ThetaPtDet.levelPoint_eq _ _ _).trans (e' _)
  obtain ⟨σ, hσ, hσb⟩ := hT' _ lev lev' _ (l ▸ v₁) (l' ▸ v₂)
  refine ⟨σ, hσ, fun x hx => ?_⟩
  have := hσ.1
  obtain ⟨d, hd⟩ := lev.span F (𝟙 _) (E x) (by rw [← map_pow, hx, map_one])
  have hd' : linComb lev.pt (fun i => (d i : ℕ)) = E x :=
    (congrArg (linComb · _) (funext fun i => (Category.id_comp (lev.pt i)).symm)).trans hd
  have hx' : x = (t fun i => (d i : ℕ)).1 := E.injective (hd'.symm.trans (e _))
  rw [← hd', ThetaPtDet.linComb_comp, hx', ← e']
  exact congrArg (linComb · _) (funext hσb)

theorem exists_iso_fib : Laws → ThetaPtDeterminesSt → BrUthSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R), D.PsiEven → D.TauBimult → D'.PsiEven → D'.TauBimult → D.P.g = D'.P.g → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (Q Q' : PolAV (Sp F)) (Φ : Q.A.left ⟶ D.P.A.left) (Φ' : Q'.A.left ⟶ D'.P.A.left), IsFib D F Q Φ → IsFib D' F Q' Φ' → ∀ n : ℕ, n.Prime → Odd n → (n : F) ≠ 0 → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (c : F) (ρ : N.A → N'.A), c ≠ 0 → TorsMap N.toNumB N'.toNumB (n ^ j) c ρ → ∃ σ : Q.A ≅ Q'.A, IsPolIso Q Q' σ ∧ ∀ (x : baseOver (Sp F) ⟶ Q.A) (b : N.A), b ^ (n ^ j) ^ 2 = 1 → (ν.eA b).left = x.left ≫ Φ → (ν'.eA (ρ b)).left = (x ≫ σ.hom).left ≫ Φ' := by
  intro hL hT hU R _ _ D D' a₁ a₂ a₃ a₄ hg F _ _ _ N N' ν ν' Q Q' Φ Φ' hΦ hΦ' n hn ho hF
  obtain ⟨E, hE, rE⟩ := exists_reads hU a₁ a₂ ν hΦ
  obtain ⟨E', hE', rE'⟩ := exists_reads hU a₃ a₄ ν' hΦ'
  obtain ⟨j₀, h⟩ := exists_iso_of_reads hL hT (hΦ'.2.2.trans (hg.symm.trans hΦ.2.2.symm)) rE rE' hn ho hF
  refine ⟨j₀, fun j hj c ρ hc hρ => ?_⟩
  obtain ⟨σ, hσ, hb⟩ := h j hj c ρ hc hρ
  refine ⟨σ, hσ, fun x b hb' hx => ?_⟩
  obtain rfl : x = E b := Over.OverMorphism.ext
    (hΦ.1.1.hom_ext (hx.symm.trans (hE b)) (by rw [Over.w, Over.w]))
  rw [hb b hb', hE']

end GlobalTheory.Ex.FibIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAbelianFibreIsoOfMatchedTorsionThetaStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianFibre_iso_of_matched_torsion_theta : Laws → ThetaPtDeterminesSt → BrUthSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R), D.PsiEven → D.TauBimult → D'.PsiEven → D'.TauBimult → D.P.g = D'.P.g → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (Q Q' : PolAV (Sp F)) (Φ : Q.A.left ⟶ D.P.A.left) (Φ' : Q'.A.left ⟶ D'.P.A.left), IsFib D F Q Φ → IsFib D' F Q' Φ' → ∀ n : ℕ, n.Prime → Odd n → (n : F) ≠ 0 → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (c : F) (ρ : N.A → N'.A), c ≠ 0 → TorsMap N.toNumB N'.toNumB (n ^ j) c ρ → ∃ σ : Q.A ≅ Q'.A, IsPolIso Q Q' σ ∧ ∀ (x : baseOver (Sp F) ⟶ Q.A) (b : N.A), b ^ (n ^ j) ^ 2 = 1 → (ν.eA b).left = x.left ≫ Φ → (ν'.eA (ρ b)).left = (x ≫ σ.hom).left ≫ Φ' := by
  first | exact @GlobalTheory.Ex.FibIso.exists_iso_fib | exact GlobalTheory.Ex.FibIso.exists_iso_fib | (intros; apply GlobalTheory.Ex.FibIso.exists_iso_fib <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValIsoChart
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Ex.Arch
open GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter GlobalTheory.EigenNorm GlobalTheory.FrameValue

theorem val_iso_chart {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} (hL' : L'.IsLB) {F : X' ⟶ X}
    {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) (x : Sp ℂ ⟶ X') (j j' : L.ι) (i : L'.ι)
    (hj : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j) (hj' : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j') (hi : ⊤ ≤ x ⁻¹ᵁ L'.U i) :
    valAt' x _ (w.s (fun _ => j, i)).val =
      valAt' (x ≫ F) (L.U j ⊓ L.U j') (L.g j j').val * valAt' x _ (w.s (fun _ => j', i)).val := by
  have a : ⊤ ≤ x ⁻¹ᵁ L.wchart (fun _ : PUnit => F) (fun _ => j) := (le_preimage_wchart x L _ _).2 fun _ => hj
  have a' : ⊤ ≤ x ⁻¹ᵁ L.wchart (fun _ : PUnit => F) (fun _ => j') := (le_preimage_wchart x L _ _).2 fun _ => hj'
  have b := (le_preimage_inf x _ _).2 ⟨a, hi⟩
  have b' := (le_preimage_inf x _ _).2 ⟨a', hi⟩
  have c := (le_preimage_inf x _ _).2 ⟨b, b'⟩
  refine (val_sec x (genSec w hw) (fun _ => j, i) (fun _ => j', i) b b').trans (congrArg₂ (· * ·) ?_ rfl)
  have e₁ := val_linComb x valueRules L (fun _ : PUnit => F) (fun _ => 1) (fun _ => j) (fun _ => j') a a'
  rw [Fintype.prod_unique, zpow_one] at e₁
  have e₂ : valAt' x (L'.U i ⊓ L'.U i) (L'.g i i).val = 1 := by
    obtain ⟨e, he⟩ := (valueRules X' x).2.1 _ hi
    rw [← val_res x valueRules (le_inf le_rfl le_rfl) hi, hL'.g_self i, he]
    exact map_one e
  obtain ⟨e, he⟩ := (valueRules X' x).2.1 _ c
  refine (val_unit_mul x valueRules c _ _).trans ?_
  refine (congrArg₂ (· * ·) ((val_res x valueRules _ c _).trans e₁) ((he _).trans ((map_units_inv e _).trans
    (congrArg (·⁻¹) ((he _).symm.trans ((val_res x valueRules _ c _).trans e₂)))))).trans ?_
  simp

theorem fibSec : FibSecSt := by
  intro R _ _ _ D J g Λ Hm χ ex fr h s
  obtain ⟨hJ, P', φ, w, u, hΛ, -, hw, -, -, -, -, hex, hfr⟩ := h
  refine ⟨fun z => sF s (ex z).left J / fr z, fun z₀ => ?_, fun z => (div_mul_cancel₀ _ (fr z).ne_zero).symm⟩
  obtain ⟨i, hi⟩ : ∃ i, ⊤ ≤ (u.ex z₀).left ⁻¹ᵁ P'.L.U i := ⟨_, le_chartAt P'.isLB _⟩
  obtain ⟨j, hj⟩ : ∃ j, ⊤ ≤ ((u.ex z₀).left ≫ φ) ⁻¹ᵁ D.P.L.U j := ⟨_, hJ _⟩
  have ch : ∀ (y : Sp ℂ ⟶ D.P.A.left) (k : D.P.L.ι), ⊤ ≤ y ⁻¹ᵁ D.P.L.U k →
      ⊤ ≤ y ⁻¹ᵁ D.P.L.wchart (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => k) := fun y k hk =>
    (le_preimage_wchart y _ _ _).2 fun _ => by rwa [Category.comp_id]
  have a : ⊤ ≤ (u.ex z₀).left ⁻¹ᵁ (D.P.L.wchart (fun _ : PUnit => φ) (fun _ => j) ⊓ P'.L.U i) :=
    (le_preimage_inf _ _ _).2 ⟨(le_preimage_wchart _ _ _ _).2 fun _ => hj, hi⟩
  obtain ⟨o₁, d₁⟩ := u.hol (φ ⁻¹ᵁ D.P.L.wchart (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => j))
    ((φ.app _).hom (s.f fun _ => j))
  obtain ⟨o₂, d₂⟩ := u.hol _ (w.s (fun _ => j, i)).val
  have n₂ := o₂.mem_nhds a
  have d := (d₁.differentiableAt (o₁.mem_nhds (ch _ j hj))).fun_mul (((d₂.differentiableAt n₂).fun_mul
    ((u.fr_hol i).differentiableAt ((u.hol _ 0).1.mem_nhds hi))).fun_inv
    (mul_ne_zero (val_unit_ne_zero _ valueRules a _) (u.fr_ne i _ hi)))
  refine d.congr_of_eventuallyEq ?_
  filter_upwards [n₂] with z hz
  obtain ⟨h₁, h₂⟩ := (le_preimage_inf _ _ _).1 hz
  have h₃ := (le_preimage_wchart _ _ _ _).1 h₁ PUnit.unit
  have e₀ : sF s (ex z).left J = valAt' (ex z).left _ (s.f fun _ => J (ex z).left) := by
    rfl
  have e₁ := val_sec (ex z).left s (fun _ => J (ex z).left) (fun _ => j) (ch _ _ (hJ _)) (ch _ _ (hex z ▸ h₃))
  have e₂ := val_linComb (ex z).left valueRules D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => ((1 : ℕ) : ℤ))
    (fun _ => J (ex z).left) (fun _ => j) (ch _ _ (hJ _)) (ch _ _ (hex z ▸ h₃))
  rw [Fintype.prod_unique, Nat.cast_one, zpow_one, Category.comp_id] at e₂
  have e₃ := val_iso_chart P'.isLB hw (u.ex z).left (J (ex z).left) j i (hex z ▸ hJ _) h₃ h₂
  have n := val_unit_ne_zero (ex z).left valueRules ((le_preimage_inf _ _ _).2 ⟨hJ _, hex z ▸ h₃⟩)
    (D.P.L.g (J (ex z).left) j)
  have e₄ := (valueRules _ (u.ex z).left).2.2.2.1 _ φ _ (s.f fun _ => j)
  rw [← hex z] at e₃ e₄
  rw [e₀, e₁, hfr z i h₂, e₃, _root_.mul_assoc]
  exact (congrArg (fun q => q * _ / _) e₂).trans ((mul_div_mul_left _ _ n).trans ((div_eq_mul_inv _ _).trans
    (congrArg₂ (· * ·) e₄.symm rfl)))

end GlobalTheory.Ex.Arch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullEndo
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section

namespace GlobalTheory.Ex.Arch

theorem exists_pull_endo {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {b : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (hg : IsGrpPullback G' G b φ) (f : G ⟶ G) (hf : IsMonHom f) :
    ∃ f' : G' ⟶ G', IsMonHom f' ∧ f'.left ≫ φ = φ ≫ f.left := by
  have inj : ∀ {T : Over S'} {x y : T ⟶ G'}, pushPt hg.1.w x = pushPt hg.1.w y → x = y := fun {T x y} h =>
    Over.OverMorphism.ext (hg.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  let f' : G' ⟶ G' := Over.homMk (hg.1.lift (φ ≫ f.left) G'.hom
    (by rw [Category.assoc, Over.w, hg.1.w])) (hg.1.lift_snd _ _ _)
  have ha : f'.left ≫ φ = φ ≫ f.left := hg.1.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ G'), pushPt hg.1.w (x ≫ f') = pushPt hg.1.w x ≫ f := fun x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  have pm : ∀ {T : Over S'} (x y : T ⟶ G'), pushPt hg.1.w (x * y) = pushPt hg.1.w x * pushPt hg.1.w y := fun x y =>
    map_mul (pushHom hg _) x y
  refine ⟨f', isMonHom_of_mul _ fun T x y => inj ?_, ha⟩
  rw [pa, pm, pm, pa, pa, MonObj.mul_comp]

theorem fibGrp : FibGrpSt := by
  intro R _ _ _ D J g Λ Hm χ ex fr hF
  obtain ⟨-, P', φ, w, u, hΛ, hg, -, hAH, -, -, hlift, hex, hfr⟩ := hF
  subst hΛ
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv hg (𝟙_ (Over (Sp ℂ))) (TF (R := R) ℂ).hom (Category.id_comp _).symm
  have hee : ∀ z, ex z = e (u.ex z) := fun z => Over.OverMorphism.ext ((hex z).trans (he _).symm)
  have hadd : ∀ z w, ex (z + w) = ex z * ex w := fun z w => by
    rw [hee, hee, hee, u.ex_add]
    exact map_mul e _ _
  have hker : ∀ z, ex z = 1 ↔ z ∈ u.Λ := fun z => by
    rw [hee, ← u.ker]
    exact e.map_eq_one_iff
  refine ⟨u.discrete, u.full, hAH.1, hAH.2.1, hAH.2.2.1, fun l m => FrameValue.chi_add P'.isLB hAH l m, hadd,
    fun y => ?_, hker, fun l z => ?_, fun f hf => ?_⟩
  · obtain ⟨x, hx⟩ := e.surjective y
    obtain ⟨z, rfl⟩ := u.ex_onto x
    exact ⟨z, (hee z).trans hx⟩
  · have hi := FrameValue.le_chartAt P'.isLB (u.ex z).left
    set i := FrameValue.chartAt P'.isLB (u.ex z).left
    have h₁ : u.ex (z + l) = u.ex z := by rw [u.ex_add, (u.ker _).2 l.2, _root_.mul_one]
    have h₂ : ex (z + l) = ex z := by rw [hee, hee, h₁]
    have a := hfr z i hi
    have b := hfr (z + l) i (by rw [h₁]; exact hi)
    rw [h₁, h₂] at b
    rw [a, b, hAH.2.2.2 l i z hi]
    simp only [hermForm]
    ring
  · obtain ⟨f', hf', hc⟩ := exists_pull_endo hg f hf
    obtain ⟨F, hF⟩ := hlift f' hf'
    have hF' : ∀ z, ex (F z) = ex z ≫ f := fun z => Over.OverMorphism.ext (by
      rw [Over.comp_left, hex, hex, hF, Over.comp_left, Category.assoc, hc, Category.assoc])
    refine ⟨F, hF', fun G hG => ?_⟩
    have hm : ∀ z, (G - F) z ∈ u.Λ := fun z => by
      rw [← hker]
      have h := hadd ((G - F) z) (F z)
      rw [LinearMap.sub_apply, sub_add_cancel, hG, hF'] at h
      exact mul_eq_right.1 h.symm
    haveI := u.discrete
    have hc : Continuous fun w => (⟨(G - F) w, hm w⟩ : u.Λ) :=
      (G - F).continuous_of_finiteDimensional.subtype_mk _
    refine sub_eq_zero.1 (LinearMap.ext fun z => ?_)
    have := PreconnectedSpace.constant inferInstance hc (x := z) (y := 0)
    simpa using congrArg Subtype.val this

end GlobalTheory.Ex.Arch

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionActionInValues
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionActionInValues
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

noncomputable section
namespace GlobalTheory.Relabel
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Ex.GtValues

section
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.X]

theorem gtAct_pt (hG : GlobalFnsSt) {y : (TF (R := R) F).left} {J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι}
    (hJ : Good D.P.L y J) (oa : D.OAct O) (a : O)
    {u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε)}
    (hu : TorusExt.IsRos D.P.L _ _ u) (g g' : GtPtF D F) :
    GtAct oa a g g' ↔ g'.b = g.b ≫ oa.onB.act a ∧ ∀ χ,
      val (g'.s χ) (𝟙 _) y J = val (g.s (star a • χ)) (𝟙 _) y J * val₂ u y J (cP D _ χ) g.b := by
  have vv : ∀ (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε)) χ,
      val (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left)) (𝟙 (TF (R := R) F).left) y J =
        val (g.s (star a • χ)) (𝟙 _) y J * val₂ u y J (cP D _ χ) g.b := fun u χ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)))
  refine ⟨fun h => ⟨h.1, fun χ => (val_corr hJ (h.2 _ hu.1 hu.2 χ) _).symm.trans (vv _ χ)⟩,
    fun ⟨hb, hv⟩ => ⟨hb, fun u' hu' u₀ χ => GtValues.corr_pt D.P.isLB (fun U _ h => ?_)
      (mulGen_isGen _ _ _ _ _ _ _ (g.isGen _) (pullGen_isGen _ _ _ _ hu' _)) (g'.isGen χ) hJ
      ((vv u' χ).trans ((congrArg₂ (· * ·) rfl
        (TorusExt.IsRos.unique hG D.P.isAb D.P.isLB ⟨hu', u₀⟩ hu hJ _ _)).trans (hv χ).symm))⟩⟩
  refine (prod_sum₂ (K := Fin 4) (K' := Fin 6) (U := U) _ (prod_gt g.b (star a • χ) h)
    (prod_ros _ _ (cP D _ χ) g.b h)).trans ?_
  rw [prod_gt, TorusExt.cPoint_smul oa, hb]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel
end

theorem gtAct_values : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : NumD F) (ν : NumOf D F N) (O : Type) [CommRing O] [StarRing O], (∀ (oa : D.P.OAct O) (x : O), ∃ ρ, RosV ν oa x ρ) ∧ ∀ [Module O D.X] (oa : D.OAct O) (x : O) (ρ : N.A → N.A → F), RosV ν oa.onB x ρ → ∀ g g' v v', ν.Pt g v → ν.Pt g' v' → (GtAct oa x g g' ↔ v'.b = actV ν oa.onB x v.b ∧ ∀ χ, (v'.s χ : F) = v.s (ν.eX.symm (star x • ν.eX χ)) * ρ (N.c χ) v.b) := by
  intro hG R _ _ D F _ _ N ν O _ _
  refine ⟨fun oa x => ?_, fun oa x ρ ⟨u, hu, u₀, hρ⟩ g g' v v' h h' => ?_⟩
  · have := oa.hom x
    have := oa.hom (star x)
    have hr := oa.rosati (star x)
    rw [star_star] at hr
    obtain ⟨u, hu, u₀⟩ := exists_ros hG D.P.isAb D.P.isLB _ _ hr
    exact ⟨_, u, hu, u₀, fun _ _ => rfl⟩
  · let y : Sp F := (⊥ : PrimeSpectrum F)
    have hJ := good ν y
    obtain ⟨a, b⟩ := (pt_iff ν y _ _).1 h
    obtain ⟨a', b'⟩ := (pt_iff ν y _ _).1 h'
    rw [gtAct_pt hG hJ oa x ⟨hu, u₀⟩, ν.eX.surjective.forall]
    refine and_congr ?_ (forall_congr' fun χ => ?_)
    · rw [← a, ← a', actV, ν.eA.eq_symm_apply]
    · have e := b (ν.eX.symm (star x • ν.eX χ))
      rw [ν.eX.apply_symm_apply] at e
      have r : toStk y (ρ (N.c χ) v.b) = (val₂ u y ν.J (cP D _ (ν.eX χ)) g.b).val := by
        rw [hρ, toStk_vF _ _ hJ, c_eq, a]; rfl
      rw [← (toStk y).injective.eq_iff, map_mul, r, ← e, ← b', ← Units.val_inj, Units.val_mul]
      rfl

end GlobalTheory.Relabel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionActionInValuesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtension_action_in_values : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : NumD F) (ν : NumOf D F N) (O : Type) [CommRing O] [StarRing O], (∀ (oa : D.P.OAct O) (x : O), ∃ ρ, RosV ν oa x ρ) ∧ ∀ [Module O D.X] (oa : D.OAct O) (x : O) (ρ : N.A → N.A → F), RosV ν oa.onB x ρ → ∀ g g' v v', ν.Pt g v → ν.Pt g' v' → (GtAct oa x g g' ↔ v'.b = actV ν oa.onB x v.b ∧ ∀ χ, (v'.s χ : F) = v.s (ν.eX.symm (star x • ν.eX χ)) * ρ (N.c χ) v.b) := by
  first | exact @GlobalTheory.Relabel.gtAct_values | exact GlobalTheory.Relabel.gtAct_values | (intros; apply GlobalTheory.Relabel.gtAct_values <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelTraitExtensionPolarisedFlatBundleIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelTraitExtensionPolarisedFlatBundleIso
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section

namespace GlobalTheory.ModelFacts

theorem exists_extend {X B : Scheme.{0}} (f : X ⟶ B) (hp : IsProper f) {W : Type} [CommRing W] [IsDomain W]
    [ValuationRing W] (y : Sp (FractionRing W) ⟶ X) (s : Sp W ⟶ B) (h : y ≫ f = jK W ≫ s) :
    ∃ χ : Sp W ⟶ X, y = jK W ≫ χ := by
  have hv : ValuativeCriterion f := by
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1
  let S : ValuativeCommSq f := { R := W, K := FractionRing W, i₁ := y, i₂ := s, commSq := ⟨h⟩ }
  obtain ⟨U⟩ := hv S
  exact ⟨U.default.l, U.default.fac_left.symm⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem polAt_open {D : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O]
    {β : O →+* c.F} (Y : Model Xo c β) {K : Type} [Field K] (y : Sp K ⟶ Xo.XF c) : PolAt Y.t (y ≫ Y.j) := by
  have semiPull {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G]
      (h : IsSemiAbelian G) : IsSemiAbelian ((Over.pullback f).obj G) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := h.comm; infer_instance
    · have := h.smooth; change Smooth (pullback.snd G.hom f); infer_instance
    · have := h.separated; change IsSeparated (pullback.snd G.hom f); infer_instance
    · have := h.quasiCompact; change QuasiCompact (pullback.snd G.hom f); infer_instance
    · have := h.geomConnected; change GeometricallyConnected (pullback.snd G.hom f); infer_instance
    · intro Ω _ _ q
      obtain ⟨e⟩ := h.fibres Ω (q ≫ f)
      exact ⟨torusExtOfIso (pullCompIso q f G) e⟩
  have sabPull (hC : Out.CubePullSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
      ∃ (PP' : RigLB ((Over.pullback f).obj t.G)) (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric) (adj : _) (prim : _)
        (m : SABMap ⟨(Over.pullback f).obj t.G, semiPull f t.G t.semi, OAct.pullback f t.G t.act, PP', cub,
          sym, adj, prim⟩ t f), m.φ = pullback.fst t.G.hom f := by
    have h := isGrpPullback_pullback t.G f
    obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := hC S S' t.G _ (cubeMapOf h) t.PP t.cub
    have hact : ∀ a, ((OAct.pullback f t.G t.act).act a).left ≫ pullback.fst t.G.hom f =
        pullback.fst t.G.hom f ≫ (t.act.act a).left := fun a => pullback.lift_fst _ _ _
    have pa : ∀ {T : Over S'} (x : T ⟶ (Over.pullback f).obj t.G) a,
        pushPt h.1.w (x ≫ (OAct.pullback f t.G t.act).act a) = pushPt h.1.w x ≫ t.act.act a := fun x a =>
      Over.OverMorphism.ext (by
        show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
        rw [Category.assoc, hact, Category.assoc])
    refine ⟨(cubeMapOf h).rigLB t.PP hL hr, c', hs t.sym, fun a => ?_, ?_, ⟨cubeMapOf h, h, rfl, hact, hc'⟩, rfl⟩
    · let U := lift (pushPt h.1.w (fst ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
        (pushPt h.1.w (snd ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
      refine LBIso.chartPull (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
        (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t.adj a)
      · fin_cases i
        · exact (pa _ a).trans (by simp [U])
        · simp [U]
      · fin_cases i
        · simp [U]
        · exact (pa _ _).trans (by simp [U])
    · let U := pushPt h.1.w (𝟙 ((Over.pullback f).obj t.G))
      refine LBIso.chartPull (chartPullPull t.PP.L _)
        (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
      fin_cases i
      · simp [U]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
  obtain ⟨PP', cub, sym, adj, prim, m₂, hm₂⟩ := sabPull Out.CubePf.cubePull (y ≫ Y.j) Y.t
  obtain ⟨m₃, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m m₂
  have h₂ : LBIso PP'.L (Y.t.PP.L.pull m₂.φ) := m₂.lin.imp fun _ h => h.1
  rw [hm₂] at h₂
  have h₃ : LBIso PP'.L (Y.oF.t.PP.L.pull m₃.φ) := m₃.lin.imp fun _ h => h.1
  have hL := LB.isLB_pull Y.t.PP.isLB (pullback.fst Y.t.G.hom (y ≫ Y.j))
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) m₃.cart.1 Y.oF.proper,
    amplePt _ _ y _ _ m₃.φ m₃.cart _ _ Y.oF.t.PP.isLB hL
      (LBIso.trans hL PP'.isLB (LB.isLB_pull Y.oF.t.PP.isLB _) h₂.symm h₃) Y.oF.ample Y.oF.ktriv⟩

theorem exists_rigPull {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {χ : S' ⟶ S} (m : SABMap t' t χ) :
    ∃ ω : LB.Iso t'.PP.L (t.PP.L.pull m.φ), RigPull t'.G t.G χ m.φ ω t'.PP.rig t.PP.rig := by
  obtain ⟨w, g, r, -⟩ := (isPullCubical_iff m.cm t.cub t'.cub).1 m.lin
  rw [m.base] at r
  exact ⟨w, m.cart, (isGen_iff w).2 g, t'.PP.rigGen, r⟩

theorem model_facts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), (∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (y : Sp (FractionRing W) ⟶ Y.X) (s : Sp W ⟶ Sp O), y ≫ Y.s = jK W ≫ s → ∃ χ : Sp W ⟶ Y.X, y = jK W ≫ χ) ∧ (∀ (K : Type) [Field K] (y : Sp K ⟶ Xo.XF c), PolAt Y.t (y ≫ Y.j)) ∧ Flat Y.t.G.hom ∧ ∀ (S : Scheme.{0}) (t : SAB H S) (χ : S ⟶ Y.X) (m : SABMap t Y.t χ) (L : RigLB t.G), L = t.PP → ∃ ω : LB.Iso L.L (Y.t.PP.L.pull m.φ), RigPull t.G Y.t.G χ m.φ ω L.rig Y.t.PP.rig := by
  intro E _ _ _ H D l Xo c O _ β Y
  refine ⟨fun W _ _ _ y s h => exists_extend Y.s (projProper O _ _ Y.proj) y s h, fun K _ y => polAt_open Y y, ?_, ?_⟩
  · have := Y.t.semi.smooth
    infer_instance
  · rintro S t χ m L rfl
    exact exists_rigPull m

end GlobalTheory.ModelFacts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelTraitExtensionPolarisedFlatBundleIsoStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_trait_extension_polarised_flat_bundleIso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), (∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (y : Sp (FractionRing W) ⟶ Y.X) (s : Sp W ⟶ Sp O), y ≫ Y.s = jK W ≫ s → ∃ χ : Sp W ⟶ Y.X, y = jK W ≫ χ) ∧ (∀ (K : Type) [Field K] (y : Sp K ⟶ Xo.XF c), PolAt Y.t (y ≫ Y.j)) ∧ Flat Y.t.G.hom ∧ ∀ (S : Scheme.{0}) (t : SAB H S) (χ : S ⟶ Y.X) (m : SABMap t Y.t χ) (L : RigLB t.G), L = t.PP → ∃ ω : LB.Iso L.L (Y.t.PP.L.pull m.φ), RigPull t.G Y.t.G χ m.φ ω L.rig Y.t.PP.rig := by
  first | exact @GlobalTheory.ModelFacts.model_facts | exact GlobalTheory.ModelFacts.model_facts | (intros; apply GlobalTheory.ModelFacts.model_facts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LevelConditionOfOneAlgClosedField
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LevelConditionOfOneAlgClosedField
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

noncomputable section

namespace GlobalTheory.LevelField

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ArcDataDescent

theorem qkExt_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F₀ F₁ F₂ : Type} [Field F₀] [Field F₁]
    [Field F₂] [Algebra (FractionRing R) F₀] [Algebra (FractionRing R) F₁] [Algebra (FractionRing R) F₂]
    {f : F₀ →+* F₁} {g : F₁ →+* F₂} {k : ℕ} {p₀ : QkPt D F₀ k} {p₁ : QkPt D F₁ k} {p₂ : QkPt D F₂ k}
    (h : QkExt f p₀ p₁) (h' : QkExt g p₁ p₂) : QkExt (g.comp f) p₀ p₂ := by
  refine ⟨h'.1.trans h.1, ?_, fun χ => corr_of_val D.P.isLB fun (y : Sp F₂) J hJ => ?_⟩
  · exact h'.2.1.trans ((congrArg (spMap g ≫ ·) h.2.1).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ p₀.g.b.left) (spMap_comp f g).symm)))
  · refine (val_corr hJ (h'.2.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (h.2.2 χ) _).trans
      ((val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))))
    exact congrArg (fun q => val (p₀.g.s χ) q y J) ((Category.assoc _ _ _).trans
      (congrArg (𝟙 (Sp F₂) ≫ ·) (spMap_comp f g).symm))

theorem val_eq_of_genRel {F : Type} [Field F] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} (hM₀ : M₀.IsLB)
    {φ : B ⟶ B₀} {w : LB.Iso M (M₀.pull φ)} {K : Type} [Fintype K] {pt pt' : K → (Sp F ⟶ B)} {pt₀ : K → (Sp F ⟶ B₀)}
    {ε : K → ℤ} {t : LB.Gen (LB.LinComb M pt ε)} {t' : LB.Gen (LB.LinComb M pt' ε)}
    {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} {x : F} (hp : pt = pt') (h : GenRel w t t₀ x) (h' : GenRel w t' t₀ x)
    (z : Sp F) {J} (hJ : Good M z J) : val t (𝟙 _) z J = val t' (𝟙 _) z J := by
  subst hp
  choose J₀ hJ₀ using fun χ : Sp F ⟶ B₀ => exists_chart hM₀ (χ z)
  have e := ((genRel_iff w t t₀ x z).1 h).2 (fun k => J (pt k)) (fun k => J₀ (pt k ≫ φ))
    (fun k => hJ₀ (pt k ≫ φ)) (fun k => hJ (pt k))
  have e' := ((genRel_iff w t' t₀ x z).1 h').2 (fun k => J (pt k)) (fun k => J₀ (pt k ≫ φ))
    (fun k => hJ₀ (pt k ≫ φ)) (fun k => hJ (pt k))
  rw [val_of t _ z J (fun k => J (pt k)) (fun k => by rw [Category.id_comp]),
    val_of t' _ z J (fun k => J (pt k)) (fun k => by rw [Category.id_comp])]
  exact mul_left_cancel (Units.ext (e.trans e'.symm))

variable {R O' : Type} [CommRing R] [IsDomain R] [CommRing O'] [IsDomain O'] {D : DegPre R} {D₀ : DegPre O'}
  {ψ : D.P.A.left ⟶ D₀.P.A.left} {w : LB.Iso D.P.L (D₀.P.L.pull ψ)} {k : ℕ}

theorem genRel_ext {F F' : Type} [Field F] [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F']
    [Algebra (FractionRing O') F] [Algebra (FractionRing O') F'] {σ : F →+* F'}
    (hσ : σ.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')
    (hσ₀ : σ.comp (algebraMap (FractionRing O') F) = algebraMap (FractionRing O') F')
    {q : QkPt D F k} {q' : QkPt D F' k} {q₀ : QkPt D₀ F k} {q₀' : QkPt D₀ F' k} (h : QkExt σ q q')
    (h₀ : QkExt σ q₀ q₀') {χ : D.X} {χ₀ : D₀.X} {x : F} (H : GenRel w (q.g.s χ) (q₀.g.s χ₀) x) :
    GenRel w (q'.g.s χ) (q₀'.g.s χ₀) (σ x) :=
  (genRel_congr D.P.isLB D₀.P.isLB w (gtφ_ext hσ h χ) (gtφ_ext hσ₀ h₀ χ₀) (q'.g.isGen _)
    (pullGen_isGen _ _ _ _ (q.g.isGen _) _) (q₀'.g.isGen _) (pullGen_isGen _ _ _ _ (q₀.g.isGen _) _)
    (fun _ _ hJ => val_corr hJ (h.2.2 χ) _) (fun _ _ hJ => val_corr hJ (h₀.2.2 χ₀) _) _).2
    ((genRel_pull_iff σ w _ _ x).2 H)

theorem eq_of_genRel {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F] {f : O' →+* R}
    (gp : IsGrpPullback D.P.A D₀.P.A (spMap f) ψ) (e : D₀.X ≃+ D.X) {q q' : QkPt D F k} {q₀ : QkPt D₀ F k}
    {x : D₀.X → F} (hy : q.y = q'.y) (H : ∀ χ, GenRel w (q.g.s (e χ)) (q₀.g.s χ) (x χ))
    (H' : ∀ χ, GenRel w (q'.g.s (e χ)) (q₀.g.s χ) (x χ)) : q = q' := by
  have hb : q.g.b = q'.g.b :=
    Over.OverMorphism.ext (gp.1.hom_ext (((H 0).1 2).trans ((H' 0).1 2).symm) (by rw [Over.w, Over.w]))
  refine TorusExt.qk_ext hy (TorusExt.gt_ext hb fun χ => corr_of_val D.P.isLB fun y J hJ => ?_)
  obtain ⟨χ, rfl⟩ := e.surjective χ
  exact val_eq_of_genRel D₀.P.isLB (by rw [hb]) (H χ) (H' χ) y hJ

theorem toA_of_toA : GlobalTheory.UT.LL → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R O' : Type) [CommRing R] [IsDomain R] [CharZero R] [CommRing O'] [IsDomain O'] (I : Ideal R), AdmBase R I → ∀ (t : SAB H (Sp R)) (P : PELUnif I t) (D₀ : DegPre O'), D₀.TauBimult → ∀ (f : O' →+* R) (ψ : P.D.toPre.P.A.left ⟶ D₀.P.A.left) (w : LB.Iso P.D.toPre.P.L (D₀.P.L.pull ψ)) (e : D₀.X ≃+ P.D.toPre.X), IsGrpPullback P.D.toPre.P.A D₀.P.A (spMap f) ψ → w.IsGen → ∀ k : ℕ, 1 ≤ k → ∀ (p₀ : QkPt D₀ (FractionRing O') k) (s : D₀.X → FractionRing R) (x₀ : Sp (FractionRing R) ⟶ P.A.A.left) (C : Type) [Field C] [IsAlgClosed C] [Algebra (FractionRing R) C] [Algebra (FractionRing O') C], Along f C → ∀ (q₀ : QkPt D₀ C k) (q : QkPt P.D.toPre C k) (x : TFK (R := R) C ⟶ P.A.A), QkExt (algebraMap _ C) p₀ q₀ → q.y = e q₀.y → (∀ χ, GenRel w (q.g.s (e χ)) (q₀.g.s χ) (algebraMap _ C (s χ))) → x.left = jFK (R := R) C ≫ x₀ → P.ToA C k q x → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F], Along f F → ∀ (q₀' : QkPt D₀ F k) (q' : QkPt P.D.toPre F k) (x' : TFK (R := R) F ⟶ P.A.A), QkExt (algebraMap _ F) p₀ q₀' → q'.y = e q₀'.y → (∀ χ, GenRel w (q'.g.s (e χ)) (q₀'.g.s χ) (algebraMap _ F (s χ))) → x'.left = jFK (R := R) F ≫ x₀ → P.ToA F k q' x' := by
  intro hL E _ _ _ H R O' _ _ _ _ _ I _ t P D₀ hB f ψ w e gp _ k hk p₀ s x₀ C _ _ _ _ hC q₀ q x h₀ hy hg hx hA
    F _ _ _ _ hF q₀' q' x' h₀' hy' hg' hx'
  obtain ⟨F', _, _, σ, τ, hστ⟩ := exists_common_field (algebraMap (FractionRing R) C) (algebraMap (FractionRing R) F)
  letI : Algebra (FractionRing R) F' := (σ.comp (algebraMap _ C)).toAlgebra
  letI : Algebra (FractionRing O') F' := (σ.comp (algebraMap _ C)).toAlgebra
  have hσ : σ.comp (algebraMap (FractionRing R) C) = algebraMap (FractionRing R) F' := rfl
  have hσ₀ : σ.comp (algebraMap (FractionRing O') C) = algebraMap (FractionRing O') F' := rfl
  have hτ : τ.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' := hστ.symm
  have hτ₀ : τ.comp (algebraMap (FractionRing O') F) = algebraMap (FractionRing O') F' :=
    IsLocalization.ringHom_ext (nonZeroDivisors O') (RingHom.ext fun a =>
      (congrArg τ (hF a).symm).trans ((RingHom.congr_fun hστ _).symm.trans (congrArg σ (hC a))))
  obtain ⟨r, hr, -⟩ := TorusExt.existsUnique_qkExt P.D.tau_bimult σ hσ q
  obtain ⟨r', hr', -⟩ := TorusExt.existsUnique_qkExt P.D.tau_bimult τ hτ q'
  obtain ⟨r₀, hr₀, -⟩ := TorusExt.existsUnique_qkExt hB σ hσ₀ q₀
  obtain ⟨r₀', hr₀', -⟩ := TorusExt.existsUnique_qkExt hB τ hτ₀ q₀'
  have a := qkExt_trans h₀ hr₀
  have a' := qkExt_trans h₀' hr₀'
  rw [hσ₀] at a
  rw [hτ₀] at a'
  obtain rfl : r₀ = r₀' :=
    (TorusExt.existsUnique_qkExt hB (algebraMap (FractionRing O') F') (RingHom.ext fun _ => rfl) p₀).unique a a'
  obtain rfl : r = r' := eq_of_genRel gp e (q₀ := r₀) (x := fun χ => algebraMap (FractionRing R) F' (s χ))
    (by rw [hr.1, hr'.1, hy, hy', h₀.1, h₀'.1]) (fun χ => genRel_ext hσ hσ₀ hr hr₀ (hg χ))
    (fun χ => by
      have b := genRel_ext hτ hτ₀ hr' hr₀' (hg' χ)
      rwa [show τ (algebraMap (FractionRing R) F (s χ)) = algebraMap (FractionRing R) F' (s χ) from
        RingHom.congr_fun hτ _] at b)
  letI : Algebra C F' := σ.toAlgebra
  letI : Algebra F F' := τ.toAlgebra
  haveI : IsScalarTower (FractionRing R) C F' := IsScalarTower.of_algebraMap_eq' hσ.symm
  haveI : IsScalarTower (FractionRing R) F F' := IsScalarTower.of_algebraMap_eq' hτ.symm
  have hj : spMap σ ≫ jFK (R := R) C = jFK (R := R) F' := (spMap_comp _ _).symm.trans (congrArg spMap hσ)
  have hj' : spMap τ ≫ jFK (R := R) F = jFK (R := R) F' := (spMap_comp _ _).symm.trans (congrArg spMap hτ)
  have ex : TorsionExt.fieldMap (R := R) C F' ≫ x = TorsionExt.fieldMap (R := R) F F' ≫ x' := by
    refine Over.OverMorphism.ext ?_
    show spMap σ ≫ x.left = spMap τ ≫ x'.left
    rw [hx, hx', ← Category.assoc, ← Category.assoc, hj, hj']
  refine (TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow P.U hk hr' x').2 ?_
  rw [← ex]
  exact (TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow P.U hk hr x).1 hA

end GlobalTheory.LevelField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LevelConditionOfOneAlgClosedFieldStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCondition_of_one_algClosed_field : GlobalTheory.UT.LL → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R O' : Type) [CommRing R] [IsDomain R] [CharZero R] [CommRing O'] [IsDomain O'] (I : Ideal R), AdmBase R I → ∀ (t : SAB H (Sp R)) (P : PELUnif I t) (D₀ : DegPre O'), D₀.TauBimult → ∀ (f : O' →+* R) (ψ : P.D.toPre.P.A.left ⟶ D₀.P.A.left) (w : LB.Iso P.D.toPre.P.L (D₀.P.L.pull ψ)) (e : D₀.X ≃+ P.D.toPre.X), IsGrpPullback P.D.toPre.P.A D₀.P.A (spMap f) ψ → w.IsGen → ∀ k : ℕ, 1 ≤ k → ∀ (p₀ : QkPt D₀ (FractionRing O') k) (s : D₀.X → FractionRing R) (x₀ : Sp (FractionRing R) ⟶ P.A.A.left) (C : Type) [Field C] [IsAlgClosed C] [Algebra (FractionRing R) C] [Algebra (FractionRing O') C], Along f C → ∀ (q₀ : QkPt D₀ C k) (q : QkPt P.D.toPre C k) (x : TFK (R := R) C ⟶ P.A.A), QkExt (algebraMap _ C) p₀ q₀ → q.y = e q₀.y → (∀ χ, GenRel w (q.g.s (e χ)) (q₀.g.s χ) (algebraMap _ C (s χ))) → x.left = jFK (R := R) C ≫ x₀ → P.ToA C k q x → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F], Along f F → ∀ (q₀' : QkPt D₀ F k) (q' : QkPt P.D.toPre F k) (x' : TFK (R := R) F ⟶ P.A.A), QkExt (algebraMap _ F) p₀ q₀' → q'.y = e q₀'.y → (∀ χ, GenRel w (q'.g.s (e χ)) (q₀'.g.s χ) (algebraMap _ F (s χ))) → x'.left = jFK (R := R) F ≫ x₀ → P.ToA F k q' x' := by
  first | exact @GlobalTheory.LevelField.toA_of_toA | exact GlobalTheory.LevelField.toA_of_toA | (intros; apply GlobalTheory.LevelField.toA_of_toA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.StalkUnitsSymmGm
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch GlobalTheory.ArcPull GlobalTheory.FrameValue

noncomputable section
namespace GlobalTheory.Ex.Arch.FibRos

theorem exists_ros_down {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] [IsCommMonObj A]
    [IsCommMonObj A'] {f : S' ⟶ S} {Φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}
    (gp : IsGrpPullback A' A f Φ) (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull Φ)} (hw : w.IsGen) {a b : A ⟶ A} {a' b' : A' ⟶ A'}
    (a₁ : (1 : 𝟙_ (Over S') ⟶ A') ≫ a' = 1) (b₁ : (1 : 𝟙_ (Over S') ⟶ A') ≫ b' = 1)
    (ha : a'.left ≫ Φ = Φ ≫ a.left) (hb : b'.left ≫ Φ = Φ ≫ b.left)
    {r : LB.Gen (LB.LinComb L (rosatiφ A a b) rosatiε)} (hr : TorusExt.IsRos L a b r) :
    ∃ t : LB.Gen (LB.LinComb L' (rosatiφ A' a' b') rosatiε), TorusExt.IsRos L' a' b' t ∧
      ∀ {T' : Over S'} (x' y' : T' ⟶ A') (m : T'.left ⟶ (A ⊗ A).left), x'.left ≫ Φ = m ≫ (fst A A).left →
        y'.left ≫ Φ = m ≫ (snd A A).left → ∀ (z : T'.left) J J', Good L z J → Good L' z J' →
        val r m z J = (∏ k, om w z J J' ((lift x' y').left ≫ rosatiφ A' a' b' k) ^ rosatiε k) *
          val t (lift x' y').left z J' := by
  let Φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left := (lift (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A'))).left
  have f₁ : (fst A' A').left ≫ Φ = Φ₂ ≫ (fst A A).left :=
    (congrArg (fun q => q.left) (lift_fst (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A')))).symm
  have f₂ : (snd A' A').left ≫ Φ = Φ₂ ≫ (snd A A).left :=
    (congrArg (fun q => q.left) (lift_snd (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A')))).symm
  have f₃ : (fst A' A' ≫ a').left ≫ Φ = Φ₂ ≫ (fst A A ≫ a).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc, f₁, Category.assoc]
  have f₄ : (snd A' A' ≫ b').left ≫ Φ = Φ₂ ≫ (snd A A ≫ b).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, hb, ← Category.assoc, f₂, Category.assoc]
  have hψ : ∀ i, rosatiφ A' a' b' i ≫ Φ = Φ₂ ≫ rosatiφ A a b i := fun i => by
    fin_cases i
    exacts [mul_push gp Φ₂ f₃ f₂, f₃, f₂, mul_push gp Φ₂ f₁ f₄, f₁, f₄]
  have cmp : ∀ {T' : Over S'} (x' y' : T' ⟶ A') (m : T'.left ⟶ (A ⊗ A).left), x'.left ≫ Φ = m ≫ (fst A A).left →
      y'.left ≫ Φ = m ≫ (snd A A).left → (lift x' y').left ≫ Φ₂ = m := fun x' y' m hx hy => by
    apply pullback.hom_ext
    · refine Eq.trans ?_ hx
      refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) f₁.symm).trans ?_)
      rw [← Category.assoc, ← Over.comp_left, lift_fst]
    · refine Eq.trans ?_ hy
      refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) f₂.symm).trans ?_)
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
  obtain ⟨t, ht, vt⟩ := exists_down_om hw hL hL' Φ₂ hψ r hr.1
  refine ⟨t, ⟨ht, corr_of_val hL' fun y I' hI' => ?_⟩, fun x' y' m hx hy z J J' hJ hJ' => ?_⟩
  · obtain ⟨I, hI⟩ := DegPull.exists_good' hL y
    have o : lift (1 : 𝟙_ (Over S') ⟶ A') (1 : 𝟙_ (Over S') ⟶ A') = lift η[A'] η[A'] := by simp [Hom.one_def]
    have he : eSec A' ≫ Φ = f ≫ eSec A := (cubeMapOf gp).e_comm
    have o₁ : (1 : 𝟙_ (Over S') ⟶ A').left = eSec A' := Category.id_comp _
    have e := vt _ (lift (1 : 𝟙_ (Over S') ⟶ A') (1 : 𝟙_ (Over S') ⟶ A')).left y I I' hI hI'
    rw [prod_ros, cmp 1 1 (f ≫ zero2 A) (by
        rw [o₁, he, Category.assoc, ← Over.comp_left, lift_fst]; rfl) (by
        rw [o₁, he, Category.assoc, ← Over.comp_left, lift_snd]; rfl),
      a₁, b₁, _root_.mul_one, o] at e
    have e₁ := (val_pull hI _ _ _).symm.trans ((val_corr hI hr.2 f).trans (val_one _))
    rw [e₁] at e
    rw [val_pull hI', val_one, Category.id_comp]
    simpa using e.symm
  · have e := vt _ (lift x' y').left z J J' hJ hJ'
    rwa [cmp x' y' m hx hy] at e

theorem stalkUnits_symm_gm {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F) (h : x z ∈ U)
    (a : Γ(X, U)ˣ) : (((TorusExt.stalkUnits z).symm (gm x z U a) : Fˣ) : F) = valF x U a.val := by
  refine (TorusExt.stalkConst z).injective ?_
  rw [← TorusExt.stalkUnits_val, MulEquiv.apply_symm_apply]
  exact (toStk_valF x U z h a).symm

theorem vF_eq_genVal {X Y Y' : Scheme.{0}} {L : LB X} {A : Over (Sp ℂ)} [GrpObj A] {L' : LB A.left} {g : ℕ}
    {u : HolUnif A L' g} (hL' : L'.IsLB) {Φ : A.left ⟶ X} {w : LB.Iso L' (L.pull Φ)} {J : (Sp ℂ ⟶ X) → L.ι}
    (hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) {fr : (Fin g → ℂ) → ℂˣ}
    (hfr : ∀ z i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U i →
      (fr z : ℂ) = valAt' (u.ex z).left _ (w.s (fun _ => J ((u.ex z).left ≫ Φ), i)).val * u.fr i z)
    {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ A.left)} {ε : K → ℤ}
    (r : LB.Gen (LB.LinComb L φ ε)) {t : LB.Gen (LB.LinComb L' φ' ε)} (ht : t.IsGen) (m : Sp ℂ ⟶ Y) {y : Sp ℂ ⟶ Y'}
    {z : K → Fin g → ℂ} (hz : IsLift u φ' y z)
    (h : ∀ (p : Sp ℂ) J', Good L' p J' → val r m p J = (∏ k, om w p J J' (y ≫ φ' k) ^ ε k) * val t y p J') :
    vF r m J = genVal u hL' t y z * ((∏ k, fr (z k) ^ ε k : ℂˣ) : ℂ) := by
  let p : Sp ℂ := IsLocalRing.closedPoint ℂ
  have gJ : Good L p J := fun ψ => hJ ψ trivial
  have gJ' : Good L' p (chartAt hL') := fun ψ => le_chartAt hL' ψ trivial
  have e := congrArg (fun q => (((TorusExt.stalkUnits p).symm q : ℂˣ) : ℂ)) (h p _ gJ')
  simp only [map_mul, map_prod, map_zpow, Units.val_mul, Units.coe_prod, Units.val_zpow_eq_zpow_val] at e ⊢
  have e₁ : (((TorusExt.stalkUnits p).symm (val r m p J) : ℂˣ) : ℂ) = vF r m J :=
    stalkUnits_symm_gm _ _ p (gJ.mem φ m) _
  have e₂ : (((TorusExt.stalkUnits p).symm (val t y p (chartAt hL')) : ℂˣ) : ℂ) =
      genVal u hL' t y z * frameProd u ε z fun k => chartAt hL' (y ≫ φ' k) :=
    (stalkUnits_symm_gm _ _ p (gJ'.mem φ' y) _).trans (valAt'_gen hL' ht hz (le_wchart_chartAt hL' φ' y))
  rw [e₁, e₂, mul_left_comm, frameProd, ← Finset.prod_mul_distrib] at e
  refine e.trans (congrArg _ (Finset.prod_congr rfl fun k _ => ?_))
  rw [← mul_zpow, hz k, hfr _ _ (le_chartAt hL' _)]
  refine congrArg (fun q => (q * _) ^ ε k) ?_
  have hm : (u.ex (z k)).left p ∈ (L.pull Φ).U (fun _ => J ((u.ex (z k)).left ≫ Φ)) ⊓
      L'.U (chartAt hL' (u.ex (z k)).left) := ⟨mem_pull.2 (gJ ((u.ex (z k)).left ≫ Φ)), gJ' _⟩
  exact stalkUnits_symm_gm _ _ p hm _

theorem fibRosSt : Laws → FibRosSt := by
  rintro - R _ _ _ D J g Λ Hm χ ex fr ⟨hJ, P', φ, w, u, hΛ, gp, hw, hAH, -, -, -, hex, hfr⟩ f f' - - F G hF hG r hr
  have down : ∀ (a : D.P.A ⟶ D.P.A) (H : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ z, ex (H z) = ex z ≫ a) →
      ∃ a' : P'.A ⟶ P'.A, a'.left ≫ φ = φ ≫ a.left ∧ (∀ z, u.ex (H z) = u.ex z ≫ a') ∧
        (1 : 𝟙_ (Over (Sp ℂ)) ⟶ P'.A) ≫ a' = 1 := fun a H hH => by
    let a' : P'.A ⟶ P'.A := Over.homMk (gp.1.lift (φ ≫ a.left) P'.A.hom
      (by rw [Category.assoc, Over.w, gp.1.w])) (gp.1.lift_snd _ _ _)
    have ha : a'.left ≫ φ = φ ≫ a.left := gp.1.lift_fst _ _ _
    have hu : ∀ z, u.ex (H z) = u.ex z ≫ a' := fun z =>
      Over.OverMorphism.ext (gp.1.hom_ext (by
        rw [← hex, hH, Over.comp_left, Over.comp_left, hex, Category.assoc, Category.assoc, ha]) (by rw [Over.w, Over.w]))
    refine ⟨a', ha, hu, ?_⟩
    have h0 : u.ex 0 = 1 := (u.ker 0).2 (zero_mem _)
    rw [← h0, ← hu, map_zero]
  obtain ⟨a, ha, ua, a₁⟩ := down f F hF
  obtain ⟨b, hb, ub, b₁⟩ := down f' G hG
  obtain ⟨t, ht, vt⟩ := exists_ros_down gp D.P.isLB P'.isLB hw a₁ b₁ ha hb (r := r) hr
  obtain ⟨adj, one⟩ := genVal_rosati P'.isLB hAH ua ub t ht.1 ht.2
  refine ⟨adj, fun x z => ?_⟩
  have e := vF_eq_genVal P'.isLB hJ (fun z i hi => by rw [← hex]; exact hfr z i hi) r ht.1 (lift (ex x) (ex z)).left
    (isLift_rosati ua ub x z) (fun p J' hJ' => vt (u.ex x) (u.ex z) _
      ((hex x).symm.trans (congrArg (fun q => q.left) (lift_fst (ex x) (ex z)).symm))
      ((hex z).symm.trans (congrArg (fun q => q.left) (lift_snd (ex x) (ex z)).symm)) p J J'
      (fun ψ => hJ ψ trivial) hJ')
  rw [e, one, _root_.one_mul]
  simp only [Fin.prod_univ_six, rosatiLift, rosatiε, Matrix.cons_val, zpow_neg, zpow_one, Units.val_mul,
    Units.val_inv_eq_inv_val]
  field_simp

end GlobalTheory.Ex.Arch.FibRos
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TraceEqSumFinrank
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.Ex.Arch

variable {E : Type} [Field E] [NumberField E]

theorem exists_types (m : (E →+* ℂ) → ℕ) : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)),
    (∀ φ, Nat.card {i // ty i = φ} = m φ) ∧ ∀ a : E, ∑ i, ty i a = ∑ φ : E →+* ℂ, (m φ : ℂ) * φ a := by
  classical
  let e := (Fintype.equivFin (Σ φ : E →+* ℂ, Fin (m φ))).symm
  refine ⟨_, fun i => (e i).1, fun φ => ?_, fun a => ?_⟩
  · rw [Nat.card_congr (e.subtypeEquiv (q := fun k => k.1 = φ) fun _ => Iff.rfl),
      Nat.card_congr (Equiv.sigmaSubtype φ)]
    simp
  · rw [e.sum_comp fun k => k.1 a, Fintype.sum_sigma]
    simp

theorem trace_eq_sum_finrank {g : ℕ} (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (a : 𝓞 E) :
    LinearMap.trace ℂ _ (ρ a) = ∑ φ : E →+* ℂ,
      (Module.finrank ℂ (EigenSplit.eigenSub ρ (φ.comp (algebraMap (𝓞 E) E))) : ℂ) * φ (a : E) := by
  obtain ⟨g', ty, hc, hs⟩ :=
    exists_types fun φ : E →+* ℂ => Module.finrank ℂ (EigenSplit.eigenSub ρ (φ.comp (algebraMap (𝓞 E) E)))
  obtain ⟨h, hh⟩ := PointUnif.exists_equiv_of_finrank_eq (PointUnif.isSplitting_embeddings (E := E))
    (PointUnif.diagRep ty) ρ fun φ => by rw [PointUnif.finrank_eigenSub_diagRep, hc]
  have h1 : ρ a = h.conj (PointUnif.diagRep ty a) := LinearMap.ext fun v => by simp [LinearEquiv.conj_apply, hh]
  have h2 : PointUnif.diagRep ty a = Matrix.toLin' (Matrix.diagonal fun i => ty i (a : E)) :=
    LinearMap.ext fun z => funext fun i => by simp [PointUnif.diagRep_apply, Matrix.mulVec_diagonal]
  rw [h1, LinearMap.trace_conj', h2, ← hs]
  simp

theorem typeSt : TypeSt := by
  intro E _ _ _ H D
  let _ := H.starRing
  intro B hB
  classical
  obtain ⟨g, ty, hc, hs⟩ := exists_types fun φ : E →+* ℂ => if φ (H.rt : E) = H.rt0 then D.p else D.q
  have hbar : ∀ a : 𝓞 E, ∑ τ : E →+* ℂ, τ (H.bar a : E) = ∑ τ : E →+* ℂ, τ (a : E) := fun a => by
    refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro τ _; exact Finset.mem_univ _
    · intro τ _; exact Finset.mem_univ _
    · intro τ _; ext x; simp
    · intro τ _; ext x; simp
    · intro τ _
      rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
  have := HomTrace.finite_hom B.X
  obtain ⟨h, hh⟩ := PeriodNonempty.exists_diag B.actV ty fun a => by
    let f : (B.X →+ ℂ) →ₗ[ℂ] (B.X →+ ℂ) := LinearMap.fst ℂ _ _ ∘ₗ B.actV a ∘ₗ LinearMap.inl ℂ _ _
    have h1 : B.actV a = f.prodMap (B.F a) := LinearMap.ext fun v => rfl
    rw [h1, LinearMap.trace_prodMap', HomTrace.trace_eq_finrank_mul_sum E B.X (H.bar a) f fun _ _ => rfl, hbar,
      trace_eq_sum_finrank, hs, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun φ _ => ?_
    have h2 : Module.finrank ℂ (EigenSplit.eigenSub B.F (φ.comp (algebraMap (𝓞 E) E))) + Module.finrank (𝓞 E) B.X =
        if φ (H.rt : E) = H.rt0 then D.p else D.q := by
      have h3 := hB (φ.comp (algebraMap (𝓞 E) E))
      by_cases hφ : φ (H.rt : E) = H.rt0
      · rw [if_pos hφ]; exact h3.trans (if_pos hφ)
      · rw [if_neg hφ]; exact h3.trans (if_neg hφ)
    rw [← h2]
    push_cast
    ring
  exact ⟨g, ty, h, fun φ => ⟨fun hφ => (hc φ).trans (if_pos hφ), fun hφ => (hc φ).trans (if_neg hφ)⟩, hh⟩

end GlobalTheory.Ex.Arch

end
end
