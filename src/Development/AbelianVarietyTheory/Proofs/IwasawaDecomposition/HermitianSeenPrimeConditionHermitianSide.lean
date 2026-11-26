module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
public import Formalism.LocalToGlobal.UnitaryNorms.UnramT
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetStab
public import Formalism.LocalToGlobal.Divisibility.QLocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleOfFixedLine
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValSubLtOfHasRes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionModPrimeLevelPrimeSmulEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianSeenPrimeConditionHermitianSide
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianSeenPrimeConditionHermitianSide
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.HAt

variable {D : D7} {u : D.what₂.Word}

theorem exists_intF_of_conj_eq (z : 𝓞 D.host.E) (hz : D.host.conj (z : D.host.E) = z) :
    ∃ zF : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF = z := by
  have hF : (z : D.host.E) ∈ D.host.F := (D.host.conjE_mem_hostF_iff _).2 hz
  refine ⟨⟨⟨z, hF⟩, ?_⟩, ?_⟩
  · exact (isIntegral_algHom_iff (D.host.F.subtype.toIntAlgHom) Subtype.val_injective).mp
      (RingOfIntegers.isIntegral_coe z)
  · rfl

theorem pos_iff_mem_Pv (A : AtTTied u) (v : (D.mem u).A.vT) (ν : AddValuation D.host.E (WithTop ℤ))
    (hTau : ∀ zF : 𝓞 D.host.F, zF ∈ (A.eV v).1.asIdeal ↔
      0 < ν ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF : 𝓞 D.host.E) : D.host.E))
    (hπ : 0 < ν (A.piU : D.host.E)) (y : 𝓞 D.host.E) : 0 < ν (y : D.host.E) ↔ y ∈ A.Pv v := by
  let cO : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv
  have hcO : ∀ y : 𝓞 D.host.E, ((cO y : 𝓞 D.host.E) : D.host.E) = D.host.conj (y : D.host.E) := fun y => rfl
  have hinv := Formalism.L2.Host.conj_conj (D := D) D.host
  have hpb : A.res v (cO A.piU) ≠ 0 := A.res_conj v (cO A.piU) rfl
  have hπb : ν ((cO A.piU : 𝓞 D.host.E) : D.host.E) = 0 := by
    obtain ⟨zF, hzF⟩ := exists_intF_of_conj_eq (D := D) (A.piU + cO A.piU) (by
      push_cast; simp only [hcO, map_add (f := _), hinv]; ring)
    have hnot : zF ∉ (A.eV v).1.asIdeal := by
      rw [A.res_v, hzF, map_add (f := _), A.res_pi, zero_add]; exact hpb
    rw [hTau, hzF] at hnot
    refine le_antisymm (not_lt.mp fun h => hnot ?_) (Formalism.L2.Host.addVal_nonneg ν _)
    push_cast
    exact lt_of_lt_of_le (lt_min hπ h) (ν.map_add _ _)
  have hpos : ∀ y ∈ A.Pv v, 0 < ν (y : D.host.E) := by
    intro y hy
    have hy' : A.res v y = 0 := hy
    obtain ⟨zF, hzF⟩ := exists_intF_of_conj_eq (D := D) (y * cO A.piU + cO y * A.piU) (by
      push_cast; simp only [hcO, map_add (f := _), map_mul, hinv]; ring)
    have hin : zF ∈ (A.eV v).1.asIdeal := by
      rw [A.res_v, hzF, map_add (f := _), map_mul, map_mul, hy', A.res_pi]; simp
    rw [hTau, hzF] at hin
    push_cast at hin
    have h2 : 0 < ν (((cO y : 𝓞 D.host.E) : D.host.E) * A.piU) := by
      rw [ν.map_mul]; exact lt_of_lt_of_le hπ (le_add_of_nonneg_left (Formalism.L2.Host.addVal_nonneg ν _))
    have h3 : 0 < ν ((y : D.host.E) * (cO A.piU : 𝓞 D.host.E)) := by
      have : (y : D.host.E) * (cO A.piU : 𝓞 D.host.E) =
          ((y : D.host.E) * (cO A.piU : 𝓞 D.host.E) + ((cO y : 𝓞 D.host.E) : D.host.E) * A.piU) -
            ((cO y : 𝓞 D.host.E) : D.host.E) * A.piU := by ring
      rw [this]
      exact lt_of_lt_of_le (lt_min hin h2) (ν.map_sub _ _)
    rwa [ν.map_mul, hπb, add_zero] at h3
  have hPmax : (A.Pv v).IsMaximal := RingHom.ker_isMaximal_of_surjective (A.res v) (A.res_surj v)
  refine ⟨fun h => ?_, hpos y⟩
  by_contra hy
  rw [Formalism.L2.Host.addVal_eq_zero_of_not_mem ν (A.Pv v) hPmax hpos y hy] at h
  exact lt_irrefl _ h

theorem mem_conjIdeal_Pv (P : Ideal (𝓞 D.host.E)) (x y : 𝓞 D.host.E) (hxy : (y : D.host.E) = D.host.conj (x : D.host.E)) :
    x ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P ↔ y ∈ P := by
  have e : (y : D.host.E) = star (x : D.host.E) := hxy.trans (Formalism.BasicNotions.bridge_star_holds D.R D.host _).symm
  rw [Formalism.L2.Col.mem_conjIdeal]
  have : Formalism.L2.Col.cO D.host.E x = y := RingOfIntegers.ext (by rw [e]; exact Formalism.L2.Col.algebraMap_cO x)
  rw [this]

theorem seenCl_of (A : AtTTied u) : SeenCl A := by
  intro w hw v x y hy
  let σ : D.host.E ≃ₐ[ℚ] D.host.E := D.host.sigmaOf (D.eTau ((D.fm u).tauOf w v) : D.R.GG)
  let ν : AddValuation D.host.E (WithTop ℤ) :=
    (D.what₂.places.val w).comap (D.embE.comp (σ : D.host.E →+* D.host.E))
  have hyx : y = D.embE (σ (x : D.host.E)) :=
    D.what₂.embLL.injective (hy.trans (RingHom.congr_fun D.embE_φ₀ (σ (x : D.host.E))).symm)
  have hTau : ∀ zF : 𝓞 D.host.F, zF ∈ (A.eV v).1.asIdeal ↔
      0 < ν ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF : 𝓞 D.host.E) : D.host.E) := fun zF =>
    A.tauOf w hw v zF
  have hseen := A.seenP w hw ((D.fm u).tauOf w v)
  subst hyx
  by_cases hs : (D.fm u).seenP w = true
  · rw [if_pos hs] at hseen ⊢
    exact pos_iff_mem_Pv A v ν hTau hseen x
  · rw [if_neg hs] at hseen ⊢
    let cO : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv
    let ν' : AddValuation D.host.E (WithTop ℤ) := ν.comap (D.host.conj : D.host.E →+* D.host.E)
    have hinv := Formalism.L2.Host.conj_conj (D := D) D.host
    have hfix : ∀ zF : 𝓞 D.host.F, D.host.conj (((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF : 𝓞 D.host.E) : D.host.E)) =
        ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF : 𝓞 D.host.E) : D.host.E) := fun zF =>
      (D.host.conjE_mem_hostF_iff _).1 (zF : D.host.F).2
    have hTau' : ∀ zF : 𝓞 D.host.F, zF ∈ (A.eV v).1.asIdeal ↔
        0 < ν' ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF : 𝓞 D.host.E) : D.host.E) := fun zF => by
      rw [hTau]
      show _ ↔ 0 < ν (D.host.conj _)
      rw [hfix]
    have h1 := pos_iff_mem_Pv A v ν' hTau' hseen (cO x)
    rw [mem_conjIdeal_Pv (A.Pv v) x (cO x) rfl, ← h1]
    show _ ↔ 0 < ν (D.host.conj (D.host.conj (x : D.host.E)))
    rw [hinv]
    rfl

theorem seenCl_atT : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u, SeenCl (F u).atT :=
  fun _ _ _ _ _ _ F _ _ u => seenCl_of (F u).atT

end GlobalTheory.Mem.Col2.HAt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianSeenPrimeConditionHermitianSideStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianSeenPrimeCondition_hermitianSide : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u, SeenCl (F u).atT := by
  first | exact @GlobalTheory.Mem.Col2.HAt.seenCl_atT | exact GlobalTheory.Mem.Col2.HAt.seenCl_atT | (intros; apply GlobalTheory.Mem.Col2.HAt.seenCl_atT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicRelationClassesCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicRelationClassesCoordinates
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.HAt

open scoped TensorProduct

theorem reGL_rfl (n : ℕ) (R : Type) [CommRing R] (g : GL (Fin n) R) : Formalism.L2.Forms.reGL (rfl : n = n) R g = g := by
  ext a b
  simp [Formalism.L2.Forms.reGL]

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem adStep_re {a b : ℕ} (h : a = b) (σ : E →ₐ[F] E) (J : Matrix (Fin a) (Fin a) E)
    (U : Subgroup (GL (Fin a) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) (y y' : GL (Fin a) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (γ : GL (Fin a) E) (w : HeightOneSpectrum (𝓞 F)) (J' : Matrix (Fin b) (Fin b) E)
    (U' : Subgroup (GL (Fin b) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) (z z' : GL (Fin b) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (δ : GL (Fin b) E) (hJ : J' = J.reindex (finCongr h) (finCongr h)) (hU : U' = U.map (Formalism.L2.Forms.reGL h _).toMonoidHom)
    (hz : z = Formalism.L2.Forms.reGL h _ y) (hz' : z' = Formalism.L2.Forms.reGL h _ y') (hδ : δ = Formalism.L2.Forms.reGL h _ γ)
    (H : Formalism.L2.Herm.AdStep σ J' U' z z' δ w) : Formalism.L2.Herm.AdStep σ J U y y' γ w := by
  subst h hJ hU hz hz' hδ
  have hm : U.map (Formalism.L2.Forms.reGL (rfl : a = a) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).toMonoidHom = U := by
    ext g
    simp [reGL_rfl]
  rw [hm, reGL_rfl, reGL_rfl, reGL_rfl] at H
  simpa using H

end

theorem toGLb_reindex {E V : Type} [Field E] [AddCommGroup V] [Module E V] {n k : ℕ} (b : Module.Basis (Fin n) E V)
    (h : n = k) (f : V ≃ₗ[E] V) :
    Formalism.L2.Herm.toGLb (b.reindex (finCongr h)) f = Formalism.L2.Forms.reGL h E (Formalism.L2.Herm.toGLb b f) := by
  subst h
  rw [reGL_rfl]
  ext a c
  simp [Formalism.L2.Herm.toGLb]

theorem reGL_trans {a b c : ℕ} (h1 : a = b) (h2 : b = c) (R : Type) [CommRing R] (g : GL (Fin a) R) :
    Formalism.L2.Forms.reGL h2 R (Formalism.L2.Forms.reGL h1 R g) = Formalism.L2.Forms.reGL (h1.trans h2) R g := by
  subst h1 h2
  rw [reGL_rfl, reGL_rfl]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen
variable {D : D7}

theorem ad0 (H : Formalism.L2.Herm.HermColsCh D) (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)) (hcar : CarH H F) (u : D.what₂.Word)
    (hi : 0 ≤ D.R.m) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 hi))
    (hA : AdC (F u) 0 hi c c' γ.1 ((F u).atT.eV v).1) : AdOf H u 0 c c' (gx 0 hi γ) v := by
  have h0 := hA.1 (Or.inl rfl)
  have hc := hcar.car0 u
  rw [hcar.eV u] at h0
  show Formalism.L2.Herm.Ad0S D H u c c' (gx 0 hi γ) v
  unfold Formalism.L2.Herm.Ad0S
  refine adStep_re (rank_eq_first_level D.R) _ _ _ _ _ _ _ _ _ _ _ _ ?_ hc.U_eq (hc.y_eq c) (hc.y_eq c') ?_ h0
  · ext a b
    simp [gramN, Formalism.BasicNotions.Spaces.gram0]
  · rw [toGLb_reindex, reGL_trans]
    exact (reGL_lin (D.sp.X 0) (rankN D 0 hi) γ.1).symm

theorem adC (H : Formalism.L2.Herm.HermColsCh D) (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)) (hcar : CarH H F) (u : D.what₂.Word)
    (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (hA : AdC (F u) i hi c c' γ.1 ((F u).atT.eV v).1) : Formalism.L2.Herm.AdIS D H u i h1 hi c c' (gx i hi γ) v := by
  obtain ⟨hβ, h0⟩ := hA.2 h1 h2
  have hc := hcar.carC u i h1 h2 (H.chOf u i c)
  rw [hcar.eV u] at h0
  refine ⟨hβ, ?_⟩
  refine adStep_re (rankN D i hi) _ _ _ _ _ _ _ _ _ _ _ _ rfl hc.U_eq (hc.y_eq _) (hc.y_eq _) ?_ h0
  exact (reGL_lin (D.sp.X i) (rankN D i hi) γ.1).symm

theorem adM (H : Formalism.L2.Herm.HermColsCh D) (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)) (hcar : CarH H F) (u : D.what₂.Word)
    (i : ℕ) (h1 : 1 ≤ i) (hm : i = D.R.m) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (hA : AdC (F u) i hi c c' γ.1 ((F u).atT.eV v).1) : Formalism.L2.Herm.AdIS D H u i h1 hi c c' (gx i hi γ) v := by
  subst hm
  have h0 := hA.1 (Or.inr rfl)
  have hc := hcar.carM u
  rw [hcar.eV u] at h0
  have hβ : H.chOf u D.R.m c' = H.chOf u D.R.m c := (chOf_m H u c').trans (chOf_m H u c).symm
  refine ⟨hβ, ?_⟩
  have key : ∀ (β : H.Ch u D.R.m) (e : β = chM H u) (hb : H.chOf u D.R.m c = β) (hb' : H.chOf u D.R.m c' = β),
      Formalism.L2.Herm.AdStep D.sp.cm.sig (D.sp.X D.R.m).gram (H.lev u D.R.m h1 hi β).U
        ((H.cls u D.R.m h1 hi β).y ⟨c, hb⟩) ((H.cls u D.R.m h1 hi β).y ⟨c', hb'⟩)
        (Formalism.L2.Herm.toGLb (D.sp.X D.R.m).frame (gx D.R.m hi γ).1) (H.vT u v).1 := by
    intro β e hb hb'
    subst e
    refine adStep_re (rankN D D.R.m hi) _ _ _ _ _ _ _ _ _ _ _ _ rfl hc.U_eq (hc.y_eq c) (hc.y_eq c') ?_ h0
    exact (reGL_lin (D.sp.X D.R.m) (rankN D D.R.m hi) γ.1).symm
  exact key _ (chOf_m H u c) rfl hβ

theorem adOf_of_adC_gen (H : Formalism.L2.Herm.HermColsCh D) (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)) (hcar : CarH H F)
    (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (hA : AdC (F u) i hi c c' γ.1 ((F u).atT.eV v).1) : AdOf H u i c c' (gx i hi γ) v := by
  cases i with
  | zero => exact ad0 H F hcar u hi v c c' γ hA
  | succ i =>
    intro hm
    rcases Nat.lt_or_eq_of_le hi with h | h
    · exact adC H F hcar u (i + 1) (Nat.succ_pos i) h hi v c c' γ hA
    · exact adM H F hcar u (i + 1) (Nat.succ_pos i) h hi v c c' γ hA

end Gen

theorem adOf_of_adC : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i (hi : i ≤ (I.rec7 l Z).R.m) v (c c' : ((I.rec7 l Z).mem u).C.cls i) (γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)), AdC (F u) i hi c c' γ.1 ((F u).atT.eV v).1 → AdOf H u i c c' (gx i hi γ) v := by
  intro B X I _ _ l Z H F _ hcar u i hi v c c' γ hA
  exact adOf_of_adC_gen H F hcar u i hi v c c' γ hA

end GlobalTheory.Mem.Col2.HAt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicRelationClassesCoordinatesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_relation_classes_coordinates : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i (hi : i ≤ (I.rec7 l Z).R.m) v (c c' : ((I.rec7 l Z).mem u).C.cls i) (γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)), AdC (F u) i hi c c' γ.1 ((F u).atT.eV v).1 → AdOf H u i c c' (gx i hi γ) v := by
  first | exact @GlobalTheory.Mem.Col2.HAt.adOf_of_adC | exact GlobalTheory.Mem.Col2.HAt.adOf_of_adC | (intros; apply GlobalTheory.Mem.Col2.HAt.adOf_of_adC <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCouplingCosetWithGivenReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCouplingCosetWithGivenReduction
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2.MemChart.CosetLift

section Local

variable {E : Type} [Field E] [NumberField E]

theorem exists_pow_intAt_div (P : HeightOneSpectrum (𝓞 E)) {m : ℕ} (hm : m ≠ 0) :
    ∃ K : ℕ, ∀ e ∈ P.asIdeal ^ K, Formalism.L2.Col.IntAt P (algebraMap (𝓞 E) E e / (m : E)) := by
  have h0 : P.intValuation (m : 𝓞 E) ≠ 0 := P.intValuation_ne_zero _ (Nat.cast_ne_zero.2 hm)
  refine ⟨(-WithZero.log (P.intValuation (m : 𝓞 E))).toNat, fun e he => ?_⟩
  have hv : P.valuation E (algebraMap (𝓞 E) E e / (m : E)) ≤ 1 := by
    rw [← map_natCast (algebraMap (𝓞 E) E) m, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap]
    have h1 := (P.intValuation_le_pow_iff_mem e _).2 he
    have h2 : WithZero.exp (-((-WithZero.log (P.intValuation (m : 𝓞 E))).toNat : ℤ)) ≤ P.intValuation (m : 𝓞 E) := by
      conv_rhs => rw [← WithZero.exp_log h0]
      rw [WithZero.exp_le_exp]
      omega
    exact (div_le_one₀ (zero_lt_iff.2 h0)).2 (h1.trans h2)
  obtain ⟨r, s, hrs⟩ := P.exists_primeCompl_mul_eq_of_integer _ hv
  exact ⟨r, s, s.2, by rw [mul_comm]; exact hrs⟩

theorem exists_one_intAt_div (T : Finset (HeightOneSpectrum (𝓞 E))) (w : HeightOneSpectrum (𝓞 E)) {m : ℕ} (hm : m ≠ 0) :
    ∃ e : 𝓞 E, Ideal.Quotient.mk w.asIdeal e = 1 ∧
      ∀ w' ∈ T, w' ≠ w → Formalism.L2.Col.IntAt w' (algebraMap (𝓞 E) E e / (m : E)) := by
  classical
  choose K hK using fun w' : HeightOneSpectrum (𝓞 E) => exists_pow_intAt_div w' hm
  have ht : ∀ w' : HeightOneSpectrum (𝓞 E), ∃ t : 𝓞 E, t ∉ w.asIdeal ∧ (w' ≠ w → t ∈ w'.asIdeal) := by
    intro w'
    by_cases hne : w' = w
    · exact ⟨1, Formalism.L2.Col.one_notMem w, fun h => absurd hne h⟩
    · by_contra hc
      refine hne (HeightOneSpectrum.ext (w'.isMaximal.eq_of_le w.isPrime.ne_top fun t h => ?_))
      by_contra h'
      exact hc ⟨t, h', fun _ => h⟩
  choose t ht1 ht2 using ht
  have := w.isMaximal
  have := w.isPrime
  have he0 : (∏ w' ∈ T, t w' ^ K w') ∉ w.asIdeal :=
    w.asIdeal.primeCompl.prod_mem fun w' _ => w.asIdeal.primeCompl.pow_mem (ht1 w') _
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv (Formalism.L2.Col.mk_ne_zero he0)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨(∏ w' ∈ T, t w' ^ K w') * b, by rw [map_mul, hb], fun w' hw' hne => hK w' _ (Ideal.mul_mem_right _ _ ?_)⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun w' => t w' ^ K w') hw'
  rw [hc]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (ht2 w' hne) _)

variable [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem exists_vec (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (v : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal) :
    ∃ y : Sp E n, ∀ w : SG, ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y ∈ d.1.at w.1 ∧
      d.1.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y) = v w := by
  classical
  choose x hxN hxv using fun w : SG => d.2.be_surj w (v w)
  choose e he1 he2 using fun w : SG => exists_one_intAt_div SG w.1 (m := Formalism.L2.Col.qOf w.1)
    (Nat.cast_ne_zero.1 (TopStep.qOf_ne_zero (P := w.1)))
  refine ⟨∑ w : SG, (algebraMap (𝓞 E) E (e w) / ((Formalism.L2.Col.qOf w.1 : ℕ) : E)) • x w, fun w0 => ?_⟩
  have hc : ((Formalism.L2.Col.qOf w0.1 : ℕ) : E) * (algebraMap (𝓞 E) E (e w0) / ((Formalism.L2.Col.qOf w0.1 : ℕ) : E)) =
      algebraMap (𝓞 E) E (e w0) := mul_div_cancel₀ _ TopStep.qOf_ne_zero
  have hi : ∀ w : SG, Formalism.L2.Col.IntAt w0.1
      (((Formalism.L2.Col.qOf w0.1 : ℕ) : E) * (algebraMap (𝓞 E) E (e w) / ((Formalism.L2.Col.qOf w.1 : ℕ) : E))) := fun w => by
    by_cases h : w = w0
    · rw [h, hc]
      exact Formalism.L2.Col.IntAt.coe _ _
    · exact (TopStep.intAt_nat _).mul (he2 w w0.1 w0.2 fun h' => h (Subtype.ext h'.symm))
  have hx : ∀ w : SG, x w ∈ d.1.at w0.1 := fun w => Formalism.L2.Col.le_locP _ _ (hxN w)
  simp only [Finset.smul_sum, smul_smul]
  refine ⟨Submodule.sum_mem _ fun w _ => TopStep.smul_mem_locP (hi w) (hx w), ?_⟩
  rw [TopStep.be_sum d.2 w0 _ fun w _ => TopStep.smul_mem_locP (hi w) (hx w), Finset.sum_eq_single w0]
  · rw [TopStep.be_smul_int d.2 w0 (hi w0) (hx w0), hc, Formalism.L2.Col.reduction_coe, he1, one_smul, hxv]
  · intro w _ h
    rw [TopStep.be_smul_int d.2 w0 (hi w) (hx w), Formalism.L2.Col.reduction_mul (TopStep.intAt_nat _)
      (he2 w w0.1 w0.2 fun h' => h (Subtype.ext h'.symm)), TopStep.reduction_absNorm_eq_zero, zero_mul, zero_smul]
  · exact fun h => absurd (Finset.mem_univ _) h

theorem coset_be (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (SB : Finset (HeightOneSpectrum (𝓞 E))) (w : SG) (hw : w.1 ∈ SB) (e0 : SB → ℤ)
    (h0 : e0 ⟨w.1, hw⟩ = 0) {y : Sp E n} (hy : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y ∈ d.1.at w.1) :
    {v | ∃ z ∈ {z | z - y ∈ Formalism.L2.Col.locLat SB d.1.N e0}, v = d.1.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • z)} =
      {d.1.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y)} := by
  ext v
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : z - y ∈ d.1.at w.1 := by
      have := (Formalism.L2.Col.mem_locLat _ _ _ _).1 hz ⟨w.1, hw⟩
      rwa [h0, zpow_zero, inv_one, one_smul] at this
    have e : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • z =
        ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y + ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • (z - y) := by
      rw [← smul_add, add_sub_cancel]
    rw [Set.mem_singleton_iff, e, d.2.be_add w _ hy _ (TopStep.smul_mem_locP (TopStep.intAt_nat _) hz'),
      TopStep.be_smul_int d.2 w (TopStep.intAt_nat _) hz', TopStep.reduction_absNorm_eq_zero, zero_smul, add_zero]
  · intro hv
    exact ⟨y, by rw [Set.mem_setOf_eq, sub_self]; exact zero_mem _, hv⟩

end Local

theorem exists_ptAt_bar_eq {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}
    (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (_hq : ∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2)
    (q : PtAt R sel mu cst u j) (d : DecoSet (E := X.E) (n := R.N j) (ST := Pr.vT u) (SG := Pr.vGs)) :
    ∃ q' : PtAt R sel mu cst u j, q'.1.1.deco = d ∧ MemChart.bar q' = MemChart.bar q := by
  classical
  by_cases h : j + 1 = R.m
  · obtain ⟨y, hy, hY⟩ := q.mem_ybSet h
    have hG : ∀ w : Pr.vGs, w.1 ∈ rowSG Pr sel mu := fun w => Finset.mem_union_left _ w.2
    have hG' : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs := fun P =>
      (Finset.mem_union.mp P.2).resolve_right fun h' => chfok_false hQ ⟨P.1, h'⟩
    obtain ⟨y', hy'⟩ := exists_vec d fun w => q.1.1.deco.1.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : X.E) • y)
    refine ⟨⟨(chfokLift hQ d, {z | z - y' ∈ Formalism.L2.Col.locLat (rowSG Pr sel mu) d.1.N
      (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))}), ?_⟩, rfl, ?_⟩
    · rw [ysAt_ys_of_eq sel mu cst h]
      refine ⟨y', (Formalism.L2.Col.mem_locLat _ _ _ _).2 fun P => ?_, by congr!⟩
      rw [if_pos (hG' P), _root_.zpow_neg_one, inv_inv]
      exact (hy' ⟨P.1, hG' P⟩).1
    · funext w
      have h1 := (Formalism.L2.Col.mem_locLat _ _ _ _).1 hy ⟨w.1, hG w⟩
      rw [if_pos w.2, _root_.zpow_neg_one, inv_inv] at h1
      refine (coset_be d _ w (hG w) _ (if_pos w.2) (hy' w).1).trans ?_
      rw [(hy' w).2, MemChart.bar, hY]
      exact (coset_be q.1.1.deco _ w (hG w) _ (if_pos w.2) h1).symm
  · have hY : q.1.2 = ∅ := by
      have := q.2
      rwa [ysAt_ys_of_ne sel mu cst h] at this
    refine ⟨⟨(chfokLift hQ d, ∅), by rw [ysAt_ys_of_ne sel mu cst h]; rfl⟩, rfl, ?_⟩
    funext w
    simp [MemChart.bar, hY]

end GlobalTheory.Mem.Col2.MemChart.CosetLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCouplingCosetWithGivenReductionStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_couplingCoset_with_given_reduction : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, QE sel (mu : Chr X.F X.E X.K) = ∅ → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) → ∀ (q : PtAt R sel mu cst u j) (d : DecoSet (E := X.E) (n := R.N j) (ST := Pr.vT u) (SG := Pr.vGs)), ∃ q' : PtAt R sel mu cst u j, q'.1.1.deco = d ∧ MemChart.bar q' = MemChart.bar q := by
  exact @GlobalTheory.Mem.Col2.MemChart.CosetLift.exists_ptAt_bar_eq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsUnrM
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRepEqBlocks
open MeasureTheory Topology

noncomputable section

namespace GlobalTheory.SphCyclic

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix ValuativeRel

def eqBlocks (j t : ℕ) : (Σ _ : Fin j, Fin t) ≃ Fin (j * t) :=
  (Equiv.sigmaEquivProd (Fin j) (Fin t)).trans finProdFinEquiv

theorem val_eqBlocks {j t : ℕ} (a : Fin j) (s : Fin t) : (eqBlocks j t ⟨a, s⟩ : ℕ) = s + t * a := rfl

theorem eqBlocks_div {j t : ℕ} (a : Fin j) (s : Fin t) : (eqBlocks j t ⟨a, s⟩ : ℕ) / t = a := by
  rw [val_eqBlocks, Nat.add_mul_div_left _ _ s.pos, Nat.div_eq_of_lt s.2, zero_add]

theorem modExp_eqBlocks {j t : ℕ} (a : Fin j) :
    modExp (fun _ : Fin j => Fin t) a = (j * t : ℤ) - t - 2 * (a : ℕ) * t := by
  have h1 : (Finset.univ.filter fun b => a < b) = Finset.Ioi a := by ext; simp
  have h2 : (Finset.univ.filter fun b => b < a) = Finset.Iio a := by ext; simp
  rw [modExp, h1, h2, Finset.sum_const, Finset.sum_const, Fin.card_Ioi, Fin.card_Iio, Fintype.card_fin,
    nsmul_eq_mul, nsmul_eq_mul]
  have := a.2
  rw [show ((j - 1 - a : ℕ) : ℤ) = j - 1 - (a : ℕ) by omega]
  ring

theorem mem_parab_eqBlocks {R : Type} [CommRing R] {j t : ℕ} {b : GL (Fin (j * t)) R}
    (hb : ∀ x y, y < x → b.val x y = 0) : b ∈ parab R (eqBlocks j t) := by
  refine mem_parab_iff.2 fun a a' s s' h => hb _ _ ?_
  rw [Fin.lt_def, val_eqBlocks, val_eqBlocks]
  have h1 : t * (a' + 1) ≤ t * a := Nat.mul_le_mul_left _ h
  have := s'.2
  rw [mul_add, mul_one] at h1
  omega

theorem det_block {R : Type} [CommRing R] {j t : ℕ} {b : GL (Fin (j * t)) R}
    (hb : ∀ x y, y < x → b.val x y = 0) (u : Fin (j * t) → Rˣ) (hu : ∀ x, (u x : R) = b.val x x) (a : Fin j) :
    GeneralLinearGroup.det (leviProj R (eqBlocks j t) ⟨b, mem_parab_eqBlocks hb⟩ a) =
      ∏ s, u (eqBlocks j t ⟨a, s⟩) := by
  ext
  rw [GeneralLinearGroup.val_det_apply, det_of_upperTriangular, Units.coe_prod]
  · exact Finset.prod_congr rfl fun s _ => (hu _).symm
  · intro s s' h
    refine hb _ _ ?_
    rw [Fin.lt_def, val_eqBlocks, val_eqBlocks]
    exact Nat.add_lt_add_right h _

theorem exists_rep_eqBlocks (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (j t : ℕ) [MeasurableSpace (GL (Fin (j * t)) k)]
    [BorelSpace (GL (Fin (j * t)) k)] (ν : ℕ → kˣ →* ℂˣ) (hu : ∀ a x, ‖(ν a x : ℂ)‖ = 1) (hν : ∀ a, IsUnram (ν a))
    (H : Type) [Group H] [TopologicalSpace H] :
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V)
      (ρ : H × GL (Fin (j * t)) k →* (V ≃ₗᵢ[ℂ] V)),
      (∀ x, IsOpen {g | ρ g x = x}) ∧
      (∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤) ∧
      ∃ v : V, ‖v‖ = 1 ∧ (∀ h, ∀ x ∈ KO k (Fin (j * t)), ρ (h, x) v = v) ∧
        ∃ (φ : GL (Fin (j * t)) k → ℂ) (κ : Measure (GL (Fin (j * t)) k)),
          (∀ (b : GL (Fin (j * t)) k) (u : Fin (j * t) → kˣ), (∀ x y, y < x → b.val x y = 0) →
            (∀ x, (u x : k) = b.val x x) → ∀ g, φ (b * g) = (∏ x : Fin (j * t), (ν (x / t) (u x) : ℂ) *
              (nabs k (u x) ^ ((((j * t : ℕ) : ℝ) - t) / 2 - ((x / t : ℕ) : ℝ) * t) : ℝ)) * φ g) ∧
          (∀ x, ∀ y ∈ KO k (Fin (j * t)), φ (x * y) = φ x) ∧ φ 1 = 1 ∧ κ.IsHaarMeasure ∧
          κ (KO k (Fin (j * t))) = 1 ∧
          ∀ g, inner ℂ v (ρ (1, g) v) = ∫ x in (KO k (Fin (j * t)) : Set (GL (Fin (j * t)) k)), φ (x * g) ∂κ := by
  obtain ⟨V, _, _, ρ, h1, h2, v, h3, h4, φ, κ, h5, h6⟩ :=
    exists_rep_blocks k (eqBlocks j t) (fun a => ν a) (fun a => hu a) (fun a => hν a) H
  refine ⟨V, inferInstance, inferInstance, ρ, h1, h2, v, h3, h4, φ, κ, fun b u hb hbu g => ?_, h6⟩
  rw [h5 ⟨b, mem_parab_eqBlocks hb⟩ g, ← val_deltaHalf, deltaHalf_apply, Units.coe_prod, ← Finset.prod_mul_distrib,
    ← (eqBlocks j t).prod_comp, Fintype.prod_sigma]
  congr 1
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [det_block hb u hbu, map_prod, map_prod, Units.coe_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [eqBlocks_div, mul_comm, ← val_absPow_ofReal, modExp_eqBlocks]
  congr 3
  push_cast
  ring

end GlobalTheory.SphCyclic
end
end

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.SphCyclic

variable {L : Type} [Field L] [NumberField L] {P : HeightOneSpectrum (𝓞 L)}

theorem nrm_eq {nrm : AbsoluteValue (P.adicCompletion L) ℝ} (h : IsNrm P nrm) (x : (P.adicCompletion L)ˣ) :
    nrm x = (qP P : ℝ) ^ (WithZero.log (Valued.v (x : P.adicCompletion L))) := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective L P (WithZero.exp (-1 : ℤ))
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact WithZero.exp_ne_zero (hπ.symm.trans (map_zero _))
  set m := WithZero.log (Valued.v (x : P.adicCompletion L)) with hm
  have hx : Valued.v (x : P.adicCompletion L) = WithZero.exp m := (WithZero.exp_log (by simp)).symm
  have h1 : nrm π = (qP P : ℝ)⁻¹ := (h (Units.mk0 π hπ0)).2 hπ
  have h2 := (h (x * (Units.mk0 π hπ0) ^ m)).1 (by
    show Valued.v ((x * (Units.mk0 π hπ0) ^ m : (P.adicCompletion L)ˣ) : P.adicCompletion L) = 1
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, Units.val_mk0,
      hπ, hx, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp)
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, Units.val_mk0, h1, _root_.inv_zpow] at h2
  exact eq_of_div_eq_one h2

theorem exists_isUnrM : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (nrm : AbsoluteValue (P.adicCompletion L) ℝ), IsNrm P nrm → ∀ (ν : ℕ → (P.adicCompletion L)ˣ →* ℂˣ), (∀ i, IsNu P (ν i)) → ∀ r t j : ℕ, 1 ≤ t → ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V) (ρ : GL (Fin r) (P.adicCompletion L) × GL (Fin (j * t)) (P.adicCompletion L) →* (V ≃ₗᵢ[ℂ] V)), IsUnrM (OP P) nrm r (j * t) (satC nrm ν t (j * t)) ρ := by
  intro L _ _ P nrm hn ν hν r t j _
  letI := GlobalTheory.LocalData.complRel P
  haveI := GlobalTheory.LocalData.isLocalField P
  haveI : (Valued.v : Valuation (P.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (ValuativeRel.valuation (P.adicCompletion L))
    (Valued.v : Valuation (P.adicCompletion L) (WithZero (Multiplicative ℤ)))
  have hK : GlobalTheory.SplitWeil.KO (P.adicCompletion L) (Fin (j * t)) = GLint (OP P) (j * t) := by
    ext g
    rw [GlobalTheory.SplitFlip.mem_KO_iff]
    simp only [he.le_one_iff_le_one, Valuation.mem_integer_iff]
    exact Iff.rfl
  obtain ⟨V, _, _, ρ, h1, h2, v, h3, h4, φ, κ, h5, h6, h7, h8, h9, h10⟩ :=
    @exists_rep_eqBlocks (P.adicCompletion L) _ _ _ _ j t (instMeasGL _) (instBorelGL _) (fun a => ν (a + 1))
      (fun a => (hν _).unitary) (fun a x hx => (hν _).unr x (he.eq_one_iff_eq_one.1 hx))
      (GL (Fin r) (P.adicCompletion L)) _ _
  rw [hK] at h4 h6 h9 h10
  refine ⟨V, inferInstance, inferInstance, ρ, h1, h2, v, h3, fun k₁ _ => h4 k₁, φ, κ, fun b hb k hk => ?_,
    h8.toIsMulLeftInvariant, h9, h10⟩
  have hd : ∀ x, b.val x x ≠ 0 := by
    have := b.det_ne_zero
    rw [det_of_upperTriangular hb] at this
    exact fun x => Finset.prod_ne_zero_iff.1 this x (Finset.mem_univ _)
  have h11 := h5 b (fun x => Units.mk0 _ (hd x)) (fun x y h => hb h) (fun _ => rfl) 1
  rw [mul_one, h7, mul_one] at h11
  rw [h6 b k hk, h11]
  refine Finset.prod_congr rfl fun x _ => ?_
  have h12 : GlobalTheory.SplitWeil.nabs (P.adicCompletion L) (Units.mk0 _ (hd x)) = nrm (b.val x x) :=
    (GlobalTheory.LGrp.BorelCompletion.nabs_completion P _).trans (nrm_eq hn (Units.mk0 _ (hd x))).symm
  rw [h12, satC, chi0, dite_eq_right (hd x), mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (nrm.pos (hd x))]
  congr 3
  have : ((x : ℕ) : ℝ) = (((x : ℕ) % t : ℕ) : ℝ) + (((x : ℕ) / t : ℕ) : ℝ) * t := by
    exact_mod_cast (Nat.mod_add_div' (x : ℕ) t).symm
  linarith

end GlobalTheory.SphCyclic
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSetAutWdTieLabConj
noncomputable section

namespace GlobalTheory.HeightCounting.TrueConjLabels

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial
open GlobalTheory.WeilDeligne Pointwise

section General

variable {Ω : Type} [Field Ω]

theorem val_lt_iff {A B : ValuationSubring Ω} (c : Ω ≃+* Ω) (hc : ∀ x, x ∈ A ↔ c x ∈ B) (y : Ω) :
    B.valuation (c y) < 1 ↔ A.valuation y < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ← hc, ← map_inv₀, ← hc, map_eq_zero_iff _ c.injective]

variable {E : Type} [Field E] [NumberField E] [Algebra E Ω]

theorem exists_transport_elt (s : E ≃+* E) (c : Ω ≃+* Ω) (hs : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (s x))
    (t : G E Ω) : ∃ γ : G E Ω, ∀ x, γ (c x) = c (t x) := by
  refine ⟨{ (c.symm.trans (t.toRingEquiv.trans c)) with commutes' := fun y => ?_ }, fun x => ?_⟩
  · obtain ⟨x, rfl⟩ := s.surjective y
    show c (t (c.symm _)) = _
    rw [← hs, c.symm_apply_apply, t.commutes]
  · show c (t (c.symm (c x))) = _
    rw [c.symm_apply_apply]

end General

section Host

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

def conjInt (H : Host R) : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv

theorem coe_conjInt (x : 𝓞 H.E) : ((conjInt H x : 𝓞 H.E) : H.E) = H.conj (x : H.E) := rfl

theorem isConjPl_iff {w w' : PlE H} : IsConjPl H w w' ↔ ∀ x, x ∈ w.asIdeal ↔ conjInt H x ∈ w'.asIdeal := by
  refine ⟨fun h x => h x _ (coe_conjInt x), fun h x y hy => ?_⟩
  have : y = conjInt H x := RingOfIntegers.ext (hy.trans (coe_conjInt x).symm)
  rw [this]; exact h x

theorem eq_of_isConjPl {w₀ w₁ w : PlE H} (h₀ : IsConjPl H w₀ w) (h₁ : IsConjPl H w₁ w) : w₀ = w₁ := by
  apply HeightOneSpectrum.ext
  ext x
  rw [isConjPl_iff.1 h₀, isConjPl_iff.1 h₁]

theorem exists_ext (N : NData R H what₂) {w₀ w : PlE H} (h : IsConjPl H w₀ w) : ∃ c : N.Om ≃+* N.Om,
    (∀ x : H.E, c (algebraMap H.E N.Om x) = algebraMap H.E N.Om (H.conj x)) ∧
    ∀ x, x ∈ N.plOm.1 w₀ ↔ c x ∈ N.plOm.1 w := by
  let c₀ : N.Om ≃+* N.Om := IsAlgClosure.equivOfEquiv N.Om N.Om H.conj.toRingEquiv
  have h₀ : ∀ x : H.E, c₀ (algebraMap H.E N.Om x) = algebraMap H.E N.Om (H.conj x) := fun x =>
    IsAlgClosure.equivOfEquiv_algebraMap N.Om N.Om H.conj.toRingEquiv x
  let B : ValuationSubring N.Om := (N.plOm.1 w₀).comap c₀.symm.toRingHom
  have hB : ∀ x, x ∈ N.plOm.1 w₀ ↔ c₀ x ∈ B := fun x => by
    simp [B, ValuationSubring.mem_comap]
  have hBw : IsPlaceOver (F := H.E) B w := fun y => by
    obtain ⟨x, rfl⟩ := (conjInt H).surjective y
    rw [coe_conjInt, ← h₀, val_lt_iff c₀ hB, ← isConjPl_iff.1 h]
    exact N.plOm.2 w₀ x
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hBw (N.plOm.2 w)
  refine ⟨c₀.trans σ.toRingEquiv, fun x => ?_, fun x => ?_⟩
  · show σ (c₀ _) = _
    rw [h₀, σ.commutes]
  · show _ ↔ σ (c₀ x) ∈ _
    rw [hB, ← hσ, ← AlgEquiv.smul_def]
    exact ValuationSubring.smul_mem_pointwise_smul_iff.symm

end Host

theorem exists_gamma (D : D7) (k : Fin 2) : ∃ γ : PlE D.host → G D.host.E D.nd.Om,
    (∀ v, γ (D.naut.plGw k v) = D.ntypes.tg k v) ∧
    ∀ v w, IsConjPl D.host (D.naut.plGw k v) w → ∃ c : D.nd.Om ≃+* D.nd.Om,
      (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) ∧
      (∀ x, x ∈ D.nd.plOm.1 (D.naut.plGw k v) ↔ c x ∈ D.nd.plOm.1 w) ∧ ∀ x, γ w (c x) = c (D.ntypes.tg k v x) := by
  have key : ∀ w : PlE D.host, ∃ γ : G D.host.E D.nd.Om, (∀ v, w = D.naut.plGw k v → γ = D.ntypes.tg k v) ∧
      ∀ v, IsConjPl D.host (D.naut.plGw k v) w → ∃ c : D.nd.Om ≃+* D.nd.Om,
      (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) ∧
      (∀ x, x ∈ D.nd.plOm.1 (D.naut.plGw k v) ↔ c x ∈ D.nd.plOm.1 w) ∧ ∀ x, γ (c x) = c (D.ntypes.tg k v x) := by
    intro w
    by_cases h : ∃ v, IsConjPl D.host (D.naut.plGw k v) w
    · obtain ⟨v, hv⟩ := h
      obtain ⟨c, h1, h2⟩ := exists_ext D.nd hv
      obtain ⟨γ, hγ⟩ := exists_transport_elt D.host.conj.toRingEquiv c h1 (D.ntypes.tg k v)
      refine ⟨γ, fun v' e => absurd (e ▸ hv) (D.naut.plGw_nconj k v v'), fun v' hv' => ?_⟩
      obtain rfl : v = v' := D.naut.plGw_inj k (eq_of_isConjPl hv hv')
      exact ⟨c, h1, h2, hγ⟩
    · refine ⟨Function.extend (D.naut.plGw k) (D.ntypes.tg k) (fun _ => 1) w, fun v e => ?_, fun v hv => absurd ⟨v, hv⟩ h⟩
      rw [e]; exact (D.naut.plGw_inj k).extend_apply _ _ v
  choose γ h1 h2 using key
  exact ⟨γ, fun v => h1 _ v rfl, fun v w hw => h2 w v hw⟩


set_option maxHeartbeats 1000000 in
theorem exists_labels_true_conj : ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (Rw : RowWD D), ∃ lab h A C tm tg hl,
    (∀ k v, A.plGw k v = D.naut.plGw k v) ∧
    ∃ T : GlobalTheory.RowTie.WDTie (setAut D hE lab h A C tm tg hl).nd (setAut D hE lab h A C tm tg hl).naut,
      LabTrue (setAut D hE lab h A C tm tg hl) T ∧ LabConj (setAut D hE lab h A C tm tg hl) T ∧
      ∃ Rs : RowSide (setAut D hE lab h A C tm tg hl),
        (∀ σ w, T.e w (Rs.locR σ w) = Rw.par σ w) ∧ ∀ σ w, Rs.satR σ w = Rw.sat σ w := by
  intro D hE Rw
  have hS : ∀ k v, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      TeichmullerInertiaLabelCondition (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) (D.ntypes.teichC k) (D.ntypes.tg k v) :=
    fun k v => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      .of_tameGenAt (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k)
      (D.naut.plGw_over k v)) (D.ntypes.tg_gen k v) (D.ntypes.teichC_inj k)
  let lab : ∀ k, D.what₂.FT → D.nd.PlG k → Polynomial (ZMod (D.host.g k)) := fun k σ v =>
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (Rw.par σ (D.naut.plGw k v))
  have h : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = D.R.r := fun k σ v =>
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ⟨WD.lab_monic _ _ _, ((WD.natDegree_lab_eq_iff (hS k v) _).2 (Rw.tame σ k v)).trans (Rw.dim σ _)⟩
  choose γ hγ1 hγ2 using exists_gamma D
  let A : NAut (ndLab D.nd lab h) := nAutWD (ndLab D.nd lab h) hE D.naut.plGw D.naut.plGw_over D.naut.plGw_inj
    D.naut.plGw_nconj D.ntypes.teichC γ
  have hA : ∀ k v (a : A.LP (A.plGw k v)), haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      A.items₂ k (A.plGw k v) a = WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (show WDAt D.nd (D.naut.plGw k v) from a) := fun k v a => by
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    exact congrArg (fun x => WD.lab (h := D.nd.plOm.2 (D.naut.plGw k v)) (D.ntypes.teichC k) x (show WDAt D.nd (D.naut.plGw k v) from a)) (hγ1 k v)
  have hl : ∀ k v (L : A.LP (A.plGw k v)), (A.items₂ k (A.plGw k v) L).natDegree = A.lpDim L →
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      A.inePol L (D.ntypes.tg k v) =
        ((Formalism.CyclotomicNorms.rootsBar (A.items₂ k (A.plGw k v) L)).map fun x => X - Polynomial.C (D.ntypes.teichC k x)).prod := by
    intro k v L hL
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    rw [hA k v L] at hL ⊢
    exact WD.inePol_eq_of_natDegree_lab _ _ _ hL
  obtain ⟨C⟩ := GlobalTheory.MemN.nonempty_nbc_of_isEmpty_loc _ _ _ _ A hE
  refine ⟨lab, h, A, C, D.ntypes.tg_mem, D.ntypes.tg_gen, hl, fun _ _ => rfl,
    wdTieWD (ndLab D.nd lab h) hE D.naut.plGw D.naut.plGw_over D.naut.plGw_inj D.naut.plGw_nconj D.ntypes.teichC γ,
    fun k v a => hA k v a, fun k v w hw => ?_, ⟨Rw.par, Rw.sat, fun k σ v => (hA k v _).symm⟩, fun _ _ => rfl, fun _ _ => rfl⟩
  obtain ⟨c, h1, h2, h3⟩ := hγ2 k v w hw
  exact ⟨c, γ k w, h1, h2, h3, fun _ => rfl⟩

end GlobalTheory.HeightCounting.TrueConjLabels

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial

theorem exists_setAut_wdTie_labConj : ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (Rw : RowWD D), ∃ lab h A C tm tg hl, (∀ k v, A.plGw k v = D.naut.plGw k v) ∧ ∃ T : GlobalTheory.RowTie.WDTie (setAut D hE lab h A C tm tg hl).nd (setAut D hE lab h A C tm tg hl).naut, LabTrue (setAut D hE lab h A C tm tg hl) T ∧ LabConj (setAut D hE lab h A C tm tg hl) T ∧ ∃ Rs : RowSide (setAut D hE lab h A C tm tg hl), (∀ σ w, T.e w (Rs.locR σ w) = Rw.par σ w) ∧ ∀ σ w, Rs.satR σ w = Rw.sat σ w :=
  TrueConjLabels.exists_labels_true_conj

end GlobalTheory.HeightCounting

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedFormsCommensurableOfUStableInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedFormsCommensurableOfUStableInjective
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelCommensurable

theorem exists_nsmul_map_mem {K V W : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (A : Submodule (𝓞 K) W) (hA : A.FG) (L : Submodule (𝓞 K) V) (hL : Submodule.span K (L : Set V) = ⊤)
    (f : W →ₗ[K] V) : ∃ n : ℕ, n ≠ 0 ∧ ∀ x ∈ A, n • f x ∈ L := by
  classical
  obtain ⟨s, rfl⟩ := hA
  have h : ∀ x : W, ∃ n : ℕ, n ≠ 0 ∧ n • f x ∈ L := fun x =>
    GlobalTheory.Mem.Full.exists_nsmul_mem_of_span L (f x) (by rw [hL]; trivial)
  choose c hc0 hc using h
  refine ⟨∏ x ∈ s, c x, Finset.prod_ne_zero_iff.2 fun x _ => hc0 x, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem c (Finset.mem_coe.1 hy)
    rw [hk, mul_comm, mul_smul]
    exact L.toAddSubmonoid.nsmul_mem (hc y) k
  | zero => simp
  | add y z _ _ hy hz => rw [map_add (f := _), smul_add]; exact L.add_mem hy hz
  | smul r y _ hy =>
    rw [← algebraMap_smul K r y, map_smul, smul_comm, algebraMap_smul]
    exact L.smul_mem r hy


open GlobalTheory.LevelIndexCompare GlobalTheory.IndefiniteRowSideFullHecke.IndexAtLevelRanks in
theorem commensurable : ∀ (D : D7) (u : D.what₂.Word), (∀ v, ∀ x ∈ (D.fm u).ramSub, ∃ y ∈ (D.fm u).ramSub, (D.fm u).emb 0 y = LT.Uop D u 0 v ((D.fm u).emb 0 x)) → (∀ v, ∀ φ ∈ (D.mem u).A.Mram, LT.Uop D u 0 v φ = 0 → φ = 0) → ∀ w : D.what₂.places.Pl, ∃ n : ℕ, n ≠ 0 ∧ (∀ x ∈ DV.MramL D u, D.nuIn u (n • x) ∈ LT.Nlam D u w) ∧ ∀ x, D.nuIn u x ∈ LT.Nlam D u w → InLoc (D.plEq w) (DV.MramL D u) (n • x) := by
  classical
  intro D u hst hinj w
  have hex : ∀ v, ∃ g, IsScaledU D u w v g := fun v => (exists_isScaledU_iff D u w v).2 (hst v)
  choose g hg using hex
  haveI : Module.Finite D.what₂.LL (LT.Vl D u 0) := Module.Finite.of_basis ((D.fm u).lat 0).b
  have hgi : ∀ v, IsUnit (g v) := by
    intro v
    rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := hg v x
    rw [hx, Submodule.coe_zero, map_zero] at h1
    have h2 := (smul_eq_zero.1 h1.symm).resolve_left (zpow_ne_zero _ (T_ne_zero D u))
    have h3 := hinj v _ x.2 h2
    exact Subtype.ext ((D.fm u).emb_inj 0 (h3.trans (map_zero _).symm))
  set G : Module.End D.what₂.LL (D.fm u).ramSub := ((LT.VVT D u w).toList.map g).prod ^ D.R.m with hG
  have hGu : IsUnit G := by
    refine IsUnit.pow _ (List.prod_isUnit fun a ha => ?_)
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 ha
    exact hgi v
  obtain ⟨H, hH⟩ := hGu.exists_right_inv
  have hmem : ∀ x, D.nuIn u x ∈ (D.fm u).ramSub := fun x => D.nuIn_range u ▸ ⟨x, rfl⟩
  let e : (D.div.Nu u).V →ₗ[D.what₂.LL] (D.fm u).ramSub := LinearMap.codRestrict _ (D.nuIn u) hmem
  obtain ⟨n₁, hn₁, h₁⟩ := exists_nsmul_map_mem (DV.MramL D u) (D.MramL_fg u) ((D.fm u).lat 0).L
    ((D.fm u).lat_good 0).2.2 ((D.fm u).ramSub.subtype ∘ₗ H ∘ₗ e)
  obtain ⟨n₂, hn₂, h₂⟩ := exists_nsmul_map_mem (DV.MramL D u) (D.MramL_fg u) ((D.fm u).lat 0).L
    ((D.fm u).lat_good 0).2.2 ((D.fm u).ramSub.subtype ∘ₗ G ∘ₗ e)
  refine ⟨n₁ * n₂, mul_ne_zero hn₁ hn₂, fun x hx => ?_, fun x hx => ?_⟩
  · rw [mem_Nlam_iff D u w g (fun v _ => hg v)]
    have hL : (((n₁ * n₂) • H (e x) : (D.fm u).ramSub) : LT.Vl D u 0) ∈ ((D.fm u).lat 0).L := by
      rw [mul_comm, mul_smul, Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower]
      exact ((D.fm u).lat 0).L.toAddSubmonoid.nsmul_mem (h₁ x hx) n₂
    refine ⟨⟨_, ⟨Submodule.subset_span hL, ((n₁ * n₂) • H (e x)).2⟩⟩, ?_⟩
    show _ = ((G ((n₁ * n₂) • H (e x)) : (D.fm u).ramSub) : LT.Vl D u 0)
    rw [map_nsmul G, ← Module.End.mul_apply, hH, map_nsmul]
    rfl
  · rw [mem_Nlam_iff D u w g (fun v _ => hg v)] at hx
    obtain ⟨y, hy⟩ := hx
    obtain ⟨s, hs, hsy⟩ := D.inLoc_of_mem_locW w _ _ y.2.1
    obtain ⟨z, hz⟩ : (y : LT.Vl D u 0) ∈ LinearMap.range (D.nuIn u) := by
      rw [D.nuIn_range u]; exact y.2.2
    have hsm : ∀ t, D.nuIn u (s • t) = s • D.nuIn u t := fun t =>
      map_smul ((D.nuIn u).restrictScalars (𝓞 D.what₂.LL)) s t
    have hzM : s • z ∈ DV.MramL D u := by
      show D.nuIn u (s • z) ∈ ((D.fm u).lat 0).L
      rw [hsm, hz]; exact hsy
    have h3 := h₂ _ hzM
    have hez : e z = incl D u w y := Subtype.ext hz
    have h4 : ((D.fm u).ramSub.subtype ∘ₗ G ∘ₗ e) (s • z) = s • D.nuIn u x := by
      rw [← algebraMap_smul D.what₂.LL s z, map_smul, algebraMap_smul, hy]
      show s • ((G (e z) : (D.fm u).ramSub) : LT.Vl D u 0) = _
      rw [hez]
    rw [h4] at h3
    refine ⟨s, hs, ?_⟩
    show D.nuIn u (s • (n₁ * n₂) • x) ∈ ((D.fm u).lat 0).L
    rw [hsm, map_nsmul, smul_comm, mul_smul]
    exact ((D.fm u).lat 0).L.toAddSubmonoid.nsmul_mem h3 n₁

end GlobalTheory.LevelCommensurable
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedFormsCommensurableOfUStableInjectiveStatement
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramifiedForms_commensurable_of_U_stable_injective : ∀ (D : D7) (u : D.what₂.Word), (∀ v, ∀ x ∈ (D.fm u).ramSub, ∃ y ∈ (D.fm u).ramSub, (D.fm u).emb 0 y = LT.Uop D u 0 v ((D.fm u).emb 0 x)) → (∀ v, ∀ φ ∈ (D.mem u).A.Mram, LT.Uop D u 0 v φ = 0 → φ = 0) → ∀ w : D.what₂.places.Pl, ∃ n : ℕ, n ≠ 0 ∧ (∀ x ∈ DV.MramL D u, D.nuIn u (n • x) ∈ LT.Nlam D u w) ∧ ∀ x, D.nuIn u x ∈ LT.Nlam D u w → InLoc (D.plEq w) (DV.MramL D u) (n • x) := by
  first | exact @GlobalTheory.LevelCommensurable.commensurable | exact GlobalTheory.LevelCommensurable.commensurable | (intros; apply GlobalTheory.LevelCommensurable.commensurable <;> assumption)
end
end
