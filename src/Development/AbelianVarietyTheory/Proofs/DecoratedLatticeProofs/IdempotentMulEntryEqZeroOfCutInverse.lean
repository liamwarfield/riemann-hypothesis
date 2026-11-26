module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open IsDedekindDomain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitCut

variable {D : D7}

theorem cut_mul {R : Type} [CommRing R] {n : ℕ} (e f : R) (hef : e * f = 0) (M : Matrix (Fin n) (Fin n) R) :
    (e • M + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)) * (f • M + (1 - f) • 1) = (e + f) • M + (1 - (e + f)) • 1 := by
  have h1 : e * (1 - f) = e := by rw [mul_sub, mul_one, hef, sub_zero]
  have h2 : (1 - e) * f = f := by rw [sub_mul, one_mul, hef, sub_zero]
  have h3 : (1 - e) * (1 - f) = 1 - (e + f) := by linear_combination hef
  simp only [add_mul, mul_add, smul_mul_smul_comm, Matrix.mul_one, Matrix.one_mul, hef, h1, h2, h3, zero_smul, zero_add]
  rw [add_smul]; abel

theorem mt_mul (V : HSp D) (x y : GA D V) : mt V (x * y) = mt V x * mt V y := by
  show (matHom V (x * y)).1 = (matHom V x).1 * (matHom V y).1
  rw [map_mul, Units.val_mul]

theorem mt_one (V : HSp D) : mt V 1 = 1 := by
  show (matHom V 1).1 = 1
  rw [map_one, Units.val_one]

theorem mt_injective (V : HSp D) : Function.Injective (mt V) := by
  intro x y h
  exact Subtype.ext (Units.ext h)

theorem cA_algebraMap (a : AF D.host.F) : cA D (algebraMap (AF D.host.F) (AE D) a) = algebraMap (AF D.host.F) (AE D) a := by
  show (Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) (D.sp.cm.sig)).toRingHom (a ⊗ₜ 1) = a ⊗ₜ 1
  simp

theorem cut_exists (V : HSp D) (g : GA D V) (ε : AE D) (hεε : ε * ε = ε) (hε : cA D ε = ε) :
    ∃ k : GA D V, mt V k = ε • mt V g + (1 - ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  set M := mt V g with hM
  have hinv : M * ((matHom V g)⁻¹).1 = 1 := (matHom V g).mul_inv
  have hinv' : ((matHom V g)⁻¹).1 * M = 1 := (matHom V g).inv_mul
  let K : GL (Fin V.rank) (AE D) := ⟨ε • M + (1 - ε) • 1, ε • ((matHom V g)⁻¹).1 + (1 - ε) • 1,
    GlobalTheory.GfCut.idem_mul ε hεε _ _ hinv, GlobalTheory.GfCut.idem_mul ε hεε _ _ hinv'⟩
  have hgU : Formalism.UG.cT (cA D) M * V.gram.map (incA D) * M = V.gram.map (incA D) :=
    (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2
  have hKU : K ∈ HR (AF D.host.F) D.sp.cm.sig V.gram :=
    GlobalTheory.GfCut.idem_unitary (cA D) ε hε hεε _ M hgU
  exact ⟨(⟨K, hKU⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram), rfl⟩

theorem entry_mem (V : HSp D) (P : Pl D → Prop) (g : GA D V) (hg : g ∈ grpOff V P) (i j : Fin V.rank) (u : Pl D) (hu : P u) :
    compAt D u ((mt V g - 1) i j) = 0 := by
  have h := congrArg (fun x : GL (Fin V.rank) (AE D ⧸ idOff D P) => x.1 i j) (show _ = (1 : GL _ _) from hg)
  change Ideal.Quotient.mk (idOff D P) (mt V g i j) = _ at h
  have h2 : Ideal.Quotient.mk (idOff D P) (mt V g i j) =
      Ideal.Quotient.mk (idOff D P) ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [h, Units.val_one]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have h4 : (mt V g - 1) i j ∈ idOff D P := by
    rw [Matrix.sub_apply]; exact Ideal.Quotient.eq.mp h2
  unfold idOff at h4
  rw [Ideal.mem_iInf] at h4
  exact (RingHom.mem_ker).mp (h4 ⟨u, hu⟩)

open GlobalTheory.LocWeil.PlaceIdem in
theorem eFin_of_placeIdem {v : Pl D} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) : ε = eFin D.host.F v := by
  obtain ⟨α, rfl, h1, h2⟩ := h
  unfold eFin
  congr 1
  refine af_ext _ fun u => ?_
  by_cases hu : u = v
  · subst hu; rw [h1, evalV_single_same]
  · rw [h2 u hu, evalV_single_ne _ hu]

open GlobalTheory.LocWeil.PlaceIdem in
theorem eFin_idem (v : Pl D) : eFin D.host.F v * eFin D.host.F v = eFin D.host.F v := by
  refine Prod.ext (mul_zero _) ?_
  change singleV D.host.F v 1 * singleV D.host.F v 1 = singleV D.host.F v 1
  refine af_ext _ fun u => ?_
  rw [map_mul]
  by_cases hu : u = v
  · subst hu; rw [evalV_single_same, mul_one]
  · rw [evalV_single_ne _ hu, mul_zero]

theorem compAt_eq (u : Pl D) (y : AE D) : compAt D u y = Algebra.TensorProduct.map (evalV D.host.F u) (AlgHom.id D.host.F D.host.E)
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) y) := rfl

theorem baseAdele_ext_infinite_finite {a b : AF D.host.F} (h1 : fstA D.host.F a = fstA D.host.F b) (h2 : sndA D.host.F a = sndA D.host.F b) :
    a = b := Prod.ext h1 h2

open GlobalTheory.LocWeil.PlaceIdem in
theorem c_mul {W : Type} [Fintype W] (v : W → Pl D) (hv : Function.Injective v) (a : AF D.host.F)
    (ha : ∀ u, u ∉ Set.range v → evalV D.host.F u (sndA D.host.F a) = 0) :
    (1 - pairA D.host.F 1 0 - ∑ w, eFin D.host.F (v w)) * a = 0 := by
  classical
  have hf : ∀ w, fstA D.host.F (eFin D.host.F (v w)) = 0 := fun w => rfl
  have hs : ∀ w, sndA D.host.F (eFin D.host.F (v w)) = singleV D.host.F (v w) 1 := fun w => rfl
  have hp1 : fstA D.host.F (pairA D.host.F 1 0) = 1 := rfl
  have hp2 : sndA D.host.F (pairA D.host.F 1 0) = 0 := rfl
  refine baseAdele_ext_infinite_finite ?_ ?_
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_zero, map_sub, map_sub, map_sum, map_one, hp1]
    simp [hf]
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_zero, map_sub, map_sub, map_sum, map_one, hp2]
    simp only [hs, sub_zero]
    refine af_ext _ fun u => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_zero, map_sub, map_one, map_sum]
    by_cases hu : u ∈ Set.range v
    · obtain ⟨w0, rfl⟩ := hu
      rw [Finset.sum_eq_single w0 (fun w _ hw => evalV_single_ne _ (fun e => hw (hv e).symm))
        (by simp), evalV_single_same, sub_self, zero_mul]
    · rw [ha u hu, mul_zero]

theorem repr_zero2 {F E A A' A'' ι : Type} [Field F] [CommRing E] [Algebra F E] [CommRing A] [Algebra F A]
    [CommRing A'] [Algebra F A'] [CommRing A''] [Algebra F A''] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
    (f : A →ₐ[F] A') (g : A' →ₐ[F] A'') (y : A ⊗[F] E)
    (hy : Algebra.TensorProduct.map g (AlgHom.id F E) (Algebra.TensorProduct.map f (AlgHom.id F E) y) = 0) (k : ι) :
    g (f ((Algebra.TensorProduct.basis A b).repr y k)) = 0 := by
  rw [← GlobalTheory.InfZeroFinSum.repr_map_id b f, ← GlobalTheory.InfZeroFinSum.repr_map_id b g, hy, map_zero, Finsupp.zero_apply]

theorem key_gen {F E A ι : Type} [Field F] [CommRing E] [Algebra F E] [CommRing A] [Algebra F A]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E) (c : A) (y : A ⊗[F] E)
    (hy : ∀ k, c * (Algebra.TensorProduct.basis A b).repr y k = 0) : algebraMap A (A ⊗[F] E) c * y = 0 := by
  refine (Algebra.TensorProduct.basis A b).ext_elem fun k => ?_
  rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply]
  exact hy k

open GlobalTheory.LocWeil.PlaceIdem in
theorem key {W : Type} [Fintype W] (v : W → Pl D) (hv : Function.Injective v) (y : AE D)
    (hy : ∀ u, u ∉ Set.range v → compAt D u y = 0) :
    algebraMap (AF D.host.F) (AE D) (1 - pairA D.host.F 1 0 - ∑ w, eFin D.host.F (v w)) * y = 0 := by
  refine key_gen (Module.finBasis D.host.F D.host.E) _ y fun k => c_mul v hv _ fun u hu => ?_
  exact repr_zero2 (Module.finBasis D.host.F D.host.E) (sndA D.host.F) (evalV D.host.F u) y ((compAt_eq u y).symm.trans (hy u hu)) k

theorem idempotent_mul_entry_eq_zero_of_cut_inverse {R : Type} [CommRing R] {n : ℕ} (E : R) (hE : E * E = E) (M N : Matrix (Fin n) (Fin n) R)
    (h1 : (E • M + (1 - E) • (1 : Matrix (Fin n) (Fin n) R)) * N = 1) (i j : Fin n) : E * (M * N - 1) i j = 0 := by
  have h2 : E • (M * N) = E • (1 : Matrix (Fin n) (Fin n) R) := by
    have h3 := congrArg (fun X => E • X) h1
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, smul_add, smul_smul, hE] at h3
    have h4 : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hE, sub_self]
    rw [h4, zero_smul, add_zero] at h3
    exact h3
  have := congrArg (fun X => X i j) h2
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  rw [Matrix.sub_apply, mul_sub, this, sub_self]

theorem idempotent_mul_cut_sub_one_entry {R : Type} [CommRing R] {n : ℕ} (E : R) (hE : E * E = E) (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    E * (E • M + (1 - E) • (1 : Matrix (Fin n) (Fin n) R) - 1) i j = (E • M + (1 - E) • (1 : Matrix (Fin n) (Fin n) R) - 1) i j := by
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  linear_combination (M i j - (1 : Matrix (Fin n) (Fin n) R) i j) * hE

theorem exists_widePullback_of_iteratedLine {R : Type} [CommRing R] {n : ℕ} (t : R) (M : Matrix (Fin n) (Fin n) R)
    (hk : ∀ i j, (1 - t) * (M - 1) i j = 0) : M = t • M + (1 - t) • (1 : Matrix (Fin n) (Fin n) R) := by
  ext i j
  have := hk i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply] at this ⊢
  linear_combination this

theorem mt_list_prod (V : HSp D) {W : Type} (h : W → GA D V) (E : W → AE D)
    (M : Matrix (Fin V.rank) (Fin V.rank) (AE D))
    (hh : ∀ w, mt V (h w) = E w • M + (1 - E w) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)))
    (horth : ∀ w w', w ≠ w' → E w * E w' = 0) :
    ∀ l : List W, l.Nodup → mt V ((l.map h).prod) = (l.map E).sum • M + (1 - (l.map E).sum) • 1
  | [], _ => by simp
  | w :: l, hl => by
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, mt_mul, mt_list_prod V h E M hh horth l hl.2, hh, List.map_cons,
      List.sum_cons]
    apply cut_mul
    rw [← List.sum_map_mul_left l E (E w)]
    exact List.sum_eq_zero (List.forall_mem_map.mpr fun y hy =>
      horth w y (fun e => hl.1 (e ▸ hy)))


set_option maxHeartbeats 800000 in
open GlobalTheory.LocWeil.PlaceIdem in
theorem prod_of_trivOff : ∀ (D : D7) (V : HSp D) (W : Type) [Fintype W] [DecidableEq W] (v : W → Pl D) (e : W → AE D),
    Function.Injective v → (∀ w, IsSplitIdem D (e w) ∧ ∃ ε, IsPlaceIdem D (v w) ε ∧
      e w + cA D (e w) = algebraMap (AF D.host.F) (AE D) ε) →
    ∀ g ∈ grpOff V (fun x => x ∉ Set.range v), ∃ a ∈ GinfC V, ∃ h : W → GA D V, (∀ w, SuppAt (e w) V (h w)) ∧
      (∀ w w', w ≠ w' → Commute (h w) (h w')) ∧ (∀ w, Commute a (h w)) ∧
      g = a * (Finset.univ.toList.map h).prod ∧
      ∀ w, ∀ i j, (e w + cA D (e w)) * (mt V (g * (h w)⁻¹) - 1) i j = 0 := by
  intro D V W _ _ v e hv he g hg
  set E : W → AE D := fun w => algebraMap (AF D.host.F) (AE D) (eFin D.host.F (v w)) with hEdef
  have hE : ∀ w, e w + cA D (e w) = E w := fun w => by
    obtain ⟨_, ε, hε, h⟩ := he w
    rw [h, eFin_of_placeIdem hε]
  have hEE : ∀ w, E w * E w = E w := fun w => by
    simp only [hEdef, ← map_mul, eFin_idem]
  have hEc : ∀ w, cA D (E w) = E w := fun w => cA_algebraMap _
  have hEo : ∀ w w', w ≠ w' → E w * E w' = 0 := fun w w' hww => by
    simp only [hEdef, ← map_mul]
    rw [eFin_mul_eFin _ (fun h => hww (hv h)), map_zero]
  set r : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) with hrdef
  have hrr : r * r = r := by
    rw [hrdef, ← map_mul]
    congr 1
    exact baseAdele_ext_infinite_finite (by rw [map_mul]; exact mul_one _) (by rw [map_mul]; exact mul_zero _)
  have hrE : ∀ w, r * E w = 0 := fun w => by
    rw [hrdef, hEdef, ← map_mul]
    have : pairA D.host.F 1 0 * eFin D.host.F (v w) = 0 :=
      baseAdele_ext_infinite_finite (by rw [map_mul, map_zero]; exact mul_zero _) (by rw [map_mul, map_zero]; exact zero_mul _)
    rw [this, map_zero]
  choose h hh using fun w => cut_exists V g (E w) (hEE w) (hEc w)
  obtain ⟨a, ha⟩ := cut_exists V g r hrr (cA_algebraMap _)
  set M := mt V g with hM
  have hsum : (Finset.univ.toList.map E).sum = ∑ w, E w := Finset.sum_map_toList _ _
  refine ⟨a, ?_, h, ?_, ?_, ?_, ?_, ?_⟩
  · show finHom V a = 1
    have h0 : finPart D r = 0 := by
      rw [hrdef, finPart_algebraMap]
      exact TensorProduct.zero_tmul _ _
    apply Units.ext
    change (mt V a).map (finPart D) = 1
    rw [ha, GlobalTheory.GfCut.map_idem, h0, zero_smul, zero_add, sub_zero, one_smul]
  · intro w i j
    rw [hE w, hh w]
    exact idempotent_mul_cut_sub_one_entry _ (hEE w) M i j
  · intro w w' hww
    show h w * h w' = h w' * h w
    apply mt_injective
    rw [mt_mul, mt_mul, hh, hh, cut_mul _ _ (hEo w w' hww), cut_mul _ _ (hEo w' w (Ne.symm hww)), add_comm (E w)]
  · intro w
    show a * h w = h w * a
    apply mt_injective
    rw [mt_mul, mt_mul, hh, ha, cut_mul _ _ (hrE w), cut_mul _ _ (by rw [mul_comm]; exact hrE w), add_comm r]
  · apply mt_injective
    rw [mt_mul, mt_list_prod V h E M hh hEo _ (Finset.nodup_toList _), ha, hsum]
    have hrS : r * ∑ w, E w = 0 := by
      rw [Finset.mul_sum]; exact Finset.sum_eq_zero fun w _ => hrE w
    rw [cut_mul _ _ hrS]
    have hk : ∀ i j, (1 - r - ∑ w, E w) * (M - 1) i j = 0 := fun i j => by
      have := key v hv ((M - 1) i j) (fun u hu => entry_mem V _ g hg i j u hu)
      rwa [map_sub, map_sub, map_one, map_sum] at this
    exact exists_widePullback_of_iteratedLine _ M fun i j => by rw [← sub_sub]; exact hk i j
  · intro w i j
    rw [hE w]
    have h1 : (E w • M + (1 - E w) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) * mt V (h w)⁻¹ = 1 := by
      rw [← hh w, ← mt_mul, mul_inv_cancel, mt_one]
    rw [mt_mul]
    exact idempotent_mul_entry_eq_zero_of_cut_inverse _ (hEE w) _ _ h1 i j

end GlobalTheory.SplitCut
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormalFramesAndBasePointSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormalFramesAndBasePointSplitPlace
noncomputable section
open scoped TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mt_mul_gaMat (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem mt_one_gaMat (V : HSp D) : mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one]; rfl

theorem Place.pi_idem (p : Place D k) : p.π p.e = 1 := by
  have h1 := p.ι_π 1
  rw [mul_one, map_one] at h1
  rw [← h1, p.π_ι]

theorem Place.pi_eq_of_toEAf (p : Place D k) {a b : AE D} (h : toEAf D a = toEAf D b) : p.π a = p.π b := by
  have hf : finPart D a = finPart D b :=
    (Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E).injective h
  have key : p.e * a = p.e * b := GlobalTheory.SplitScalar.adele_ext
    (by rw [map_mul, map_mul, GlobalTheory.SplitScalar.infPart_splitIdem p.split, zero_mul, zero_mul])
    (by rw [map_mul, map_mul, hf])
  calc p.π a = p.π (p.e * a) := by rw [map_mul, p.pi_idem, one_mul]
    _ = p.π (p.e * b) := by rw [key]
    _ = p.π b := by rw [map_mul, p.pi_idem, one_mul]

theorem Place.map_pi_eq_of_toEAf (p : Place D k) {m n : ℕ} {a b : Matrix (Fin m) (Fin n) (AE D)}
    (h : a.map (toEAf D) = b.map (toEAf D)) : a.map p.π = b.map p.π := by
  ext i j
  exact p.pi_eq_of_toEAf (congrFun (congrFun h i) j)

theorem exists_toEAf_lift (z : EAf D) : ∃ w : AE D, toEAf D w = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | tmul b α => exact ⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] b, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩

def liftM {m n : ℕ} (x : Matrix (Fin m) (Fin n) (EAf D)) : Matrix (Fin m) (Fin n) (AE D) :=
  x.map fun z => (exists_toEAf_lift z).choose

theorem liftM_map {m n : ℕ} (x : Matrix (Fin m) (Fin n) (EAf D)) : (liftM x).map (toEAf D) = x := by
  ext i j
  exact (exists_toEAf_lift (x i j)).choose_spec

def stdFrame (k : Type) [Field k] (N : ℕ) : Frame k N (Fin N) := ⟨1, 1, by simp, by simp⟩

theorem exists_GL_mul_of_mul_eq_one {n : ℕ} (M : GL (Fin n) k) (N Ni : Matrix (Fin n) (Fin n) k) (h : N * Ni = 1) :
    ∃ gk : GL (Fin n) k, gk.val = M.val * Ni := by
  have h' : Ni * N = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).1 h
  exact ⟨M * ⟨Ni, N, h', h⟩, rfl⟩

theorem Place.exists_movedTo (p : Place D k) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (M : GL (Fin V.rank) k) (g₀ : GA D V) : ∃ g, SuppAt p.e V g ∧ MovedTo p V (g * g₀) β M.val := by
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : Matrix (Fin V.rank) (Fin V.rank) (AE D), b₀.map (toEAf D) = β.val :=
    ⟨liftM β.val, liftM_map _⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : Matrix (Fin V.rank) (Fin V.rank) (AE D), c₀.map (toEAf D) = (β⁻¹).val :=
    ⟨liftM (β⁻¹).val, liftM_map _⟩
  have hbc : b₀.map p.π * c₀.map p.π = 1 := by
    rw [← Matrix.map_mul]
    have h1 : (b₀ * c₀).map (toEAf D) = (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (toEAf D) := by
      rw [Matrix.map_mul, hb₀, hc₀, Matrix.map_one _ (map_zero _) (map_one _), ← Units.val_mul, mul_inv_cancel,
        Units.val_one]
    rw [p.map_pi_eq_of_toEAf h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have hN : ((mt V g₀).map p.π * b₀.map p.π) * (c₀.map p.π * (mt V g₀⁻¹).map p.π) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (b₀.map p.π), hbc, Matrix.one_mul, ← Matrix.map_mul, ← mt_mul_gaMat,
      mul_inv_cancel, mt_one_gaMat, Matrix.map_one _ (map_zero _) (map_one _)]
  have hN' : (c₀.map p.π * (mt V g₀⁻¹).map p.π) * ((mt V g₀).map p.π * b₀.map p.π) = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).1 hN
  obtain ⟨gk, hgk⟩ := exists_GL_mul_of_mul_eq_one M _ _ hN
  obtain ⟨g, hg, -⟩ := ((GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D k p).1 V (Fin V.rank) (stdFrame k V.rank)).1 gk
  refine ⟨g, hg.1, fun b hb => ?_⟩
  have h2 : (mt V g).map p.π = gk.val := by
    rw [hg.2]
    change (1 : Matrix (Fin V.rank) (Fin V.rank) k) * gk.val * 1 = gk.val
    rw [Matrix.one_mul, Matrix.mul_one]
  have hbb : b.map p.π = b₀.map p.π := p.map_pi_eq_of_toEAf (by rw [hb, hb₀])
  rw [mt_mul_gaMat, Matrix.map_mul, Matrix.map_mul, h2, hbb, hgk, Matrix.mul_assoc (M.val * _), Matrix.mul_assoc M.val,
    hN', Matrix.mul_one]

theorem normalFrames_and_basePoint_exist : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k), p.xi ≠ 0 → (∀ (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n), s ≠ 0 → (∃ F : Frame k B.V₀.rank (n ⊕ Unit), p.IsCoreFrame B s FA F) ∧ ∃ F : Frame k B.V.rank (n ⊕ Fin (2 * ρ + 1)), p.IsBesFrame B s FA F) ∧ (∀ (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (J : JacLev D ρ) (s hh : k) (F₀ : Frame k J.W₀.rank n), s ≠ 0 → hh ≠ 0 → ∃ F : Frame k J.W.rank (n ⊕ Fin (2 * ρ)), p.IsJacFrame J s hh F₀ F) ∧ ∀ (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (M : GL (Fin V.rank) k) (g₀ : GA D V), ∃ g, SuppAt p.e V g ∧ MovedTo p V (g * g₀) β M.val :=
  fun _ _ _ _ _ _ p _ =>
    ⟨fun _ _ _ _ B _ FA hs => ⟨p.exists_isCoreFrame hs B FA, p.exists_isBesFrame hs B FA⟩,
      fun _ _ _ _ J _ _ F₀ hs hh0 => p.exists_isJacFrame hs J hh0 F₀,
      fun V β M g₀ => p.exists_movedTo V β M g₀⟩

end GlobalTheory.LocMod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormalFramesAndBasePointSplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_frames_and_base_point_split_place : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k), p.xi ≠ 0 → (∀ (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n), s ≠ 0 → (∃ F : Frame k B.V₀.rank (n ⊕ Unit), p.IsCoreFrame B s FA F) ∧ ∃ F : Frame k B.V.rank (n ⊕ Fin (2 * ρ + 1)), p.IsBesFrame B s FA F) ∧ (∀ (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (J : JacLev D ρ) (s hh : k) (F₀ : Frame k J.W₀.rank n), s ≠ 0 → hh ≠ 0 → ∃ F : Frame k J.W.rank (n ⊕ Fin (2 * ρ)), p.IsJacFrame J s hh F₀ F) ∧ ∀ (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (M : GL (Fin V.rank) k) (g₀ : GA D V), ∃ g, SuppAt p.e V g ∧ MovedTo p V (g * g₀) β M.val := by
  first | exact @GlobalTheory.LocMod.normalFrames_and_basePoint_exist | exact GlobalTheory.LocMod.normalFrames_and_basePoint_exist | (intros; apply GlobalTheory.LocMod.normalFrames_and_basePoint_exist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjPlEqCP
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelPlaces

open IsDedekindDomain NumberField GlobalTheory.IdemSupport

variable {D : D7} {Φ : Formalism.L2.Theta.AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E}

theorem ev_sum {ι : Type} (s : Finset ι) (f : ι → Formalism.L2.Theta.AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Φ (∑ i ∈ s, f i) Q = ∑ i ∈ s, Φ (f i) Q := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, ev_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ev_add, ih]

theorem conjPl_eq_cP (P : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.DivisionValues.conjPl P = cP P :=
  (GlobalTheory.IdemSupport.isConjPl_iff P _).1 (GlobalTheory.GoodPrimes.isConjPl_iff.2 rfl)

theorem under_injOn {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D} (h : Formalism.IndefR.Datum.IsIdemSum e P) :
    Set.InjOn (fun PP : Formalism.L2.DIV.Pl D.host.E => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) (P : Set (Formalism.L2.DIV.Pl D.host.E)) := by
  classical
  obtain ⟨⟨es, hes, rfl⟩, h0⟩ := h
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  intro PP hPP PP' hPP' hu
  by_contra hne
  have hd : ∀ Q ∈ P, IsDelta Φ Q (es Q) := fun Q hQ => delta_of_isIdemAt hΦ (hes Q hQ)
  have hc' : PP' = cP PP := by
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq (D := D) hu.symm with h1 | h1
    · exact absurd h1.symm hne
    · rw [h1, conjPl_eq_cP]
  have hc : PP = cP PP' := by
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq (D := D) hu with h1 | h1
    · exact absurd h1 hne
    · rw [h1, conjPl_eq_cP]
  have e1 : Φ (∑ Q ∈ P, es Q) PP = 1 := by
    rw [ev_sum, Finset.sum_eq_single PP (fun Q hQ hQP => (hd Q hQ).2.2 PP (Ne.symm hQP))
      (fun h => absurd (Finset.mem_coe.1 hPP) h), (hd PP (Finset.mem_coe.1 hPP)).2.1]
  have e2 : Φ (cA D (∑ Q ∈ P, es Q)) PP = 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ev_sum, Finset.sum_eq_single PP' ?_ (fun h => absurd (Finset.mem_coe.1 hPP') h)]
    · have := (delta_conj hΦ (hd PP' (Finset.mem_coe.1 hPP'))).2.1
      rwa [← hc] at this
    · intro Q hQ hQP
      refine (delta_conj hΦ (hd Q hQ)).2.2 PP fun hQc => ?_
      have hv : Q.under (𝓞 D.host.F) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := by rw [← under_cP Q, ← hQc]
      rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq (D := D) hv with h1 | h1
      · rw [h1] at hQc
        exact hne (hc'.trans hQc.symm).symm
      · rw [conjPl_eq_cP, ← hc'] at h1
        exact hQP h1
  have e3 := ev_mul (Φ := Φ) (∑ Q ∈ P, es Q) (cA D (∑ Q ∈ P, es Q)) PP
  rw [h0, ev_zero, e1, e2, one_mul] at e3
  exact zero_ne_one e3

theorem injOn_under : ∀ (D : D7) (c : GlobalTheory.ChainOnto.Com D), c.Is → Set.InjOn (fun PP : Formalism.L2.DIV.Pl D.host.E => PP.under (NumberField.RingOfIntegers D.host.F)) (c.Pg : Set (Formalism.L2.DIV.Pl D.host.E)) := by
  intro D c hc
  obtain ⟨e, he⟩ := hc.split
  exact under_injOn he

end GlobalTheory.LevelPlaces
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointComponentMemSpanOfLatticeGenerators
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocMod.FullLatFrame

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (q : GlobalTheory.FinPl.SplitPt D k)

theorem e_int : finPart D q.e ∈ intAE D := by
  rw [← GlobalTheory.FinPl.FrameLat.sec_one q]; exact (q.int_iff 1).1 (one_mem _)

theorem pr_int_mem (o : 𝓞 D.host.E) : q.pr (incA D (o : D.host.E)) ∈ 𝒪[k] := by
  rw [q.int_iff, q.sec_pr, map_mul]
  refine GlobalTheory.FinPl.FrameLat.mul_mem_intAE (e_int q) (AddSubgroup.subset_closure ⟨1, fun v => ?_, o, ?_⟩)
  · rw [map_one]; exact one_mem _
  · rfl

theorem pr_pair_mem {α : Af D.host.F} (hα : α ∈ intAf D.host.F) :
    q.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ 𝒪[k] := by
  rw [q.int_iff, q.sec_pr, map_mul]
  refine GlobalTheory.FinPl.FrameLat.mul_mem_intAE (e_int q) (AddSubgroup.subset_closure ⟨α, hα, 1, ?_⟩)
  rfl

variable {S : HSp D}

def aux₃ (x : Fin S.rank → D.host.E) : Fin S.rank → k := fun a => q.pr (incA D (x a))

theorem splitPointComponent_mem_span_of_lattice_generators {L : GlobalTheory.FinPl.Lat S} (G : Finset (Fin S.rank → D.host.E))
    (hG : Submodule.span (𝓞 D.host.E) (G : Set (Fin S.rank → D.host.E)) = L) {x : Fin S.rank → D.host.E} (hx : x ∈ L) :
    aux₃ q x ∈ Submodule.span 𝒪[k] (aux₃ q '' (G : Set (Fin S.rank → D.host.E))) := by
  rw [← hG] at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero =>
    have h : aux₃ q (0 : Fin S.rank → D.host.E) = 0 := by funext a; simp [aux₃]
    rw [h]; exact zero_mem _
  | add x y _ _ hx hy =>
    have h : aux₃ q (x + y) = aux₃ q x + aux₃ q y := by funext a; simp [aux₃]
    rw [h]; exact add_mem hx hy
  | smul o x _ hx =>
    have h : aux₃ q (o • x) = (⟨_, pr_int_mem q o⟩ : 𝒪[k]) • aux₃ q x := by
      funext a
      show q.pr (incA D (o • x a)) = q.pr (incA D (o : D.host.E)) * q.pr (incA D (x a))
      rw [Algebra.smul_def, map_mul, map_mul]
    rw [h]; exact Submodule.smul_mem _ _ hx

theorem pr_mem_span {L : GlobalTheory.FinPl.Lat S} (G : Finset (Fin S.rank → D.host.E))
    (hG : Submodule.span (𝓞 D.host.E) (G : Set (Fin S.rank → D.host.E)) = L) {y : Fin S.rank → AE D}
    (hy : y ∈ GlobalTheory.FinPl.latV S L (· = q.v)) :
    (fun a => q.pr (y a)) ∈ Submodule.span 𝒪[k] (aux₃ q '' (G : Set (Fin S.rank → D.host.E))) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    have h : (fun a => q.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x a))) =
        (⟨_, pr_pair_mem q hα⟩ : 𝒪[k]) • aux₃ q x := by
      funext a
      show _ = q.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * q.pr (incA D (x a))
      rw [← map_mul]
      congr 1
      change _ = (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x a)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h]; exact Submodule.smul_mem _ _ (splitPointComponent_mem_span_of_lattice_generators q G hG hx)
  | zero =>
    have h : (fun a => q.pr ((0 : Fin S.rank → AE D) a)) = 0 := by funext a; simp
    rw [h]; exact zero_mem _
  | add y z _ _ hy hz =>
    have h : (fun a => q.pr ((y + z) a)) = (fun a => q.pr (y a)) + fun a => q.pr (z a) := by funext a; simp
    rw [h]; exact add_mem hy hz
  | neg y _ hy =>
    have h : (fun a => q.pr ((-y) a)) = -fun a => q.pr (y a) := by funext a; simp
    rw [h]; exact neg_mem hy

def latW (L : GlobalTheory.FinPl.Lat S) : Submodule 𝒪[k] (Fin S.rank → k) where
  carrier := {w | (fun i => q.sec (w i)) ∈ GlobalTheory.FinPl.latV S L (· = q.v)}
  add_mem' := by
    intro x y hx hy
    have h : (fun i => q.sec ((x + y) i)) = (fun i => q.sec (x i)) + fun i => q.sec (y i) := by funext i; simp
    simp only [Set.mem_setOf_eq] at *
    rw [h]; exact add_mem hx hy
  zero_mem' := by
    have h : (fun i => q.sec ((0 : Fin S.rank → k) i)) = 0 := by funext i; simp
    simp only [Set.mem_setOf_eq]
    rw [h]; exact zero_mem _
  smul_mem' := by
    intro c x hx
    have h : (fun i => q.sec ((c • x) i)) = fun i => q.sec (c : k) * q.sec (x i) := by
      funext i; rw [← GlobalTheory.FinPl.FrameLat.sec_mul q]; rfl
    simp only [Set.mem_setOf_eq] at *
    rw [h]
    exact GlobalTheory.FinPl.LatIndHalf.mul_mem_latV ((q.int_iff c).1 c.2) hx

theorem mem_latW {L : GlobalTheory.FinPl.Lat S} (w : Fin S.rank → k) :
    w ∈ latW q L ↔ (fun i => q.sec (w i)) ∈ GlobalTheory.FinPl.latV S L (· = q.v) := Iff.rfl

end GlobalTheory.LocMod.FullLatFrame

namespace GlobalTheory.LocMod.FullLatFrame

end GlobalTheory.LocMod.FullLatFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixSupportedAtPlaceOfIsHalfSplitPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixSupportedAtPlaceOfIsHalfSplitPoint
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.FinPl.SplitHalfSupp

theorem mxAt_of_isHalf_above : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : SplitPt D k) (m n : ℕ) (w : Mx D m n), IsHalf (q.e + cA D q.e) w → MxAt (· = q.v) w := by
  intro D k _ _ _ _ q m n w hw i j
  obtain ⟨ε, hε, heq⟩ := q.above
  rw [(placeIdem_acts D q.v ε hε).1, ← heq]
  exact hw i j

end GlobalTheory.FinPl.SplitHalfSupp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixSupportedAtPlaceOfIsHalfSplitPointStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixSupportedAtPlace_of_isHalf_splitPoint : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : SplitPt D k) (m n : ℕ) (w : Mx D m n), IsHalf (q.e + cA D q.e) w → MxAt (· = q.v) w := by
  first | exact @GlobalTheory.FinPl.SplitHalfSupp.mxAt_of_isHalf_above | exact GlobalTheory.FinPl.SplitHalfSupp.mxAt_of_isHalf_above | (intros; apply GlobalTheory.FinPl.SplitHalfSupp.mxAt_of_isHalf_above <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralMatrixUpImageCompletedHomLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralMatrixUpImageCompletedHomLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HalfIntUp

theorem sec_mul' {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (a b : k) : q.sec (a * b) = q.sec a * q.sec b := by

  have he : ∀ c : k, q.sec c = q.e * q.sec c := fun c => by rw [← q.sec_pr, q.pr_sec]
  have h1 : q.sec (a * b) = q.e * (q.sec a * q.sec b) := by
    rw [← q.sec_pr, map_mul q.pr, q.pr_sec, q.pr_sec]
  rw [h1, ← mul_assoc, ← he]

private lemma mulVec_sec_eq_sec_mulVec {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {m n : Type} [Fintype n]
    (u : Matrix m n (AE D)) (z : n → k) :
    u *ᵥ (fun j => q.sec (z j)) = fun i => q.sec ((u.map q.pr *ᵥ z) i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have he : q.sec (z j) = q.e * q.sec (z j) := by rw [← q.sec_pr, q.pr_sec]
  rw [sec_mul', q.sec_pr]
  conv_lhs => rw [he]
  ring

theorem exists_int_up : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → ∀ u : WO S T, u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) → IsHalf q.e u → ∃ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) ∧ u = (ofSplit q).up FS FT x := by
  intro D k _ _ _ _ q hU Y Y' _ _ _ _ S T FS FT LS LT hSd _ hS hT u hu hh
  refine ⟨(ofSplit q).down FS FT u, ?_, (GlobalTheory.LocMod.Witness.up_down (ofSplit q) FS FT hh).symm⟩
  intro r s

  have hz : (fun i => q.sec ((FS.β *ᵥ Pi.single s 1) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v) := by
    refine (hS (Pi.single s 1)).1 fun i => ?_
    rcases eq_or_ne i s with rfl | h
    · rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _

  have hmem := GlobalTheory.FinPl.LatMem.latO_maps hSd hu hz
  rw [hU.2 T LT, mulVec_sec_eq_sec_mulVec q u (FS.β *ᵥ Pi.single s 1)] at hmem

  have hcol : FT.β *ᵥ (fun r => (ofSplit q).down FS FT u r s) =
      (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map q.pr *ᵥ (FS.β *ᵥ Pi.single s 1) := by
    have e1 : (fun r => (ofSplit q).down FS FT u r s) = (ofSplit q).down FS FT u *ᵥ Pi.single s 1 := by
      funext r; simp [Matrix.mulVec_single]
    rw [e1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    simp only [GlobalTheory.LocMod.Place.down, ← Matrix.mul_assoc, FT.βγ, Matrix.one_mul]
    rfl
  have hin : (fun i => q.sec ((FT.β *ᵥ (fun r => (ofSplit q).down FS FT u r s)) i)) ∈
      GlobalTheory.FinPl.latV T LT (· = q.v) := by
    rw [hcol]; exact hmem
  exact (hT _).2 hin r

end GlobalTheory.HalfIntUp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralMatrixUpImageCompletedHomLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_matrix_up_image_completed_hom_lattice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → ∀ u : WO S T, u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) → IsHalf q.e u → ∃ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) ∧ u = (ofSplit q).up FS FT x := by
  first | exact @GlobalTheory.HalfIntUp.exists_int_up | exact GlobalTheory.HalfIntUp.exists_int_up | (intros; apply GlobalTheory.HalfIntUp.exists_int_up <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualOrthAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OrthSumLat

variable {D : D7}

theorem rat_mulVec_mem_latV {S T : HSp D} (m : Matrix (Fin T.rank) (Fin S.rank) D.host.E) {L : Lat S} {L' : Lat T}
    (h : ∀ x ∈ L, m *ᵥ x ∈ L') {P : Pl D → Prop} {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    (rat m : Mx D T.rank S.rank) *ᵥ y ∈ latV T L' P := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hα', c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨α, hα, hα', 1, rfl, m *ᵥ x, h x hx, ?_⟩
    funext i
    simp only [mulVec, dotProduct, one_mul, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change ((1 : AF D.host.F) ⊗ₜ[D.host.F] m i j) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [mulVec_neg]; exact neg_mem hx

theorem dsum_eq' {S : HSp D} (x y : Fin S.rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * S.gram i j * y j = star x ⬝ᵥ S.gram *ᵥ y := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

theorem pair_iA' {S A B : HSp D} (o : OrthDec S A B) (a : Fin A.rank → D.host.E) (y : Fin S.rank → D.host.E) :
    star (o.iA *ᵥ a) ⬝ᵥ S.gram *ᵥ y = star a ⬝ᵥ A.gram *ᵥ (o.qA *ᵥ y) := by
  have h : A.gram * o.qA = o.iAᴴ * S.gram := by
    rw [OrthDec.qA, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (gram_isUnit_det A), Matrix.one_mul]
  rw [mulVec_mulVec, h, star_mulVec, ← mulVec_mulVec, dotProduct_mulVec (star a)]

theorem exists_selfDual_orthAt : ∀ (D : D7) (S A B : HSp D) (o : OrthDec S A B) (LA : Lat A) (LB : Lat B), IsSelfDualC A LA →
    IsSelfDualC B LB → ∃ L : Lat S, IsSelfDualC S L ∧ ∀ v, OrthAt o L LA LB v := by
  intro D S A B o LA LB hA hB
  let fA := (mulVecLin o.iA).restrictScalars (𝓞 D.host.E)
  let fB := (mulVecLin o.iB).restrictScalars (𝓞 D.host.E)
  have hsum : ∀ y : Fin S.rank → D.host.E, y = o.iA *ᵥ (o.qA *ᵥ y) + o.iB *ᵥ (o.qB *ᵥ y) := fun y => by
    rw [mulVec_mulVec, mulVec_mulVec, ← add_mulVec, o.iA_qA_add, one_mulVec]
  have hiA : ∀ x ∈ LA, o.iA *ᵥ x ∈ LA.map fA ⊔ LB.map fB := fun x hx => Submodule.mem_sup_left ⟨x, hx, rfl⟩
  have hiB : ∀ x ∈ LB, o.iB *ᵥ x ∈ LA.map fA ⊔ LB.map fB := fun x hx => Submodule.mem_sup_right ⟨x, hx, rfl⟩
  have hmem : ∀ y, y ∈ LA.map fA ⊔ LB.map fB ↔ o.qA *ᵥ y ∈ LA ∧ o.qB *ᵥ y ∈ LB := fun y => by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩ := Submodule.mem_sup.1 h
      change o.qA *ᵥ (o.iA *ᵥ a + o.iB *ᵥ b) ∈ LA ∧ o.qB *ᵥ (o.iA *ᵥ a + o.iB *ᵥ b) ∈ LB
      simp only [mulVec_add, mulVec_mulVec, o.qA_iA, o.qA_iB, o.qB_iA, o.qB_iB, one_mulVec, zero_mulVec, add_zero, zero_add]
      exact ⟨ha, hb⟩
    · rw [hsum y]; exact add_mem (hiA _ h.1) (hiB _ h.2)
  refine ⟨LA.map fA ⊔ LB.map fB, ⟨Submodule.IsLattice.of_fg D.host.E ((hA.1.fg.map _).sup (hB.1.fg.map _)), fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩,
    fun v y => ⟨fun hy => ⟨rat_mulVec_mem_latV _ (fun x hx => ((hmem x).1 hx).1) hy,
      rat_mulVec_mem_latV _ (fun x hx => ((hmem x).1 hx).2) hy⟩, fun h => ?_⟩⟩
  · obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, hc⟩ := (hA.2 _).1 ((hmem y).1 hy).1 a ha
    obtain ⟨d, hd⟩ := (hB.2 _).1 ((hmem y).1 hy).2 b hb
    refine ⟨c + d, ?_⟩
    rw [dsum_eq'] at hc hd ⊢
    change _ = star (o.iA *ᵥ a + o.iB *ᵥ b) ⬝ᵥ _
    have e2 : star (o.iB *ᵥ b) ⬝ᵥ S.gram *ᵥ y = star b ⬝ᵥ B.gram *ᵥ (o.qB *ᵥ y) := pair_iA' o.symm b y
    rw [star_add, add_dotProduct, pair_iA', e2, ← hc, ← hd]
    rfl
  · refine (hmem y).2 ⟨(hA.2 _).2 fun a ha => ?_, (hB.2 _).2 fun b hb => ?_⟩
    · have := h _ (hiA a ha)
      rwa [dsum_eq', pair_iA', ← dsum_eq'] at this
    · have := h _ (hiB b hb)
      have e2 : star (o.iB *ᵥ b) ⬝ᵥ S.gram *ᵥ y = star b ⬝ᵥ B.gram *ᵥ (o.qB *ᵥ y) := pair_iA' o.symm b y
      rwa [dsum_eq', e2, ← dsum_eq'] at this
  · have e : y = o.jA *ᵥ (o.pA *ᵥ y) + o.jB *ᵥ (o.pB *ᵥ y) := by
      have hs : o.jA * o.pA + o.jB * o.pB = 1 := by
        change (o.iA.map (incA D)) * (o.qA.map (incA D)) + (o.iB.map (incA D)) * (o.qB.map (incA D)) = 1
        rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add (incA D)), o.iA_qA_add, Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))]
      rw [mulVec_mulVec, mulVec_mulVec, ← add_mulVec, hs, one_mulVec]
    rw [e]
    exact add_mem (rat_mulVec_mem_latV _ hiA h.1) (rat_mulVec_mem_latV _ hiB h.2)

end GlobalTheory.OrthSumLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletedHomLatticeStableSplitIdempotent
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletedHomLatticeStableSplitIdempotent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SplitVac

open GlobalTheory.LatVac NumberField

variable {D : D7}

def finIncl (D : D7) : (Af D.host.F ⊗[D.host.F] D.host.E) →ₗ[D.host.F] AE D :=
  (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)).rTensor D.host.E

theorem finIncl_tmul (β : Af D.host.F) (x : D.host.E) :
    finIncl D (β ⊗ₜ[D.host.F] x) = pairA D.host.F 0 β ⊗ₜ[D.host.F] x := rfl

theorem infPart_finIncl (y : Af D.host.F ⊗[D.host.F] D.host.E) : infPart D (finIncl D y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul β x => rw [finIncl_tmul]; exact infPart_pair β x
  | add y z hy hz => rw [LinearMap.map_add (f := _), RingHom.map_add (f := _), hy, hz, add_zero]

theorem finPart_finIncl (y : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (finIncl D y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul β x => rw [finIncl_tmul]; exact finPart_pair β x
  | add y z hy hz => rw [LinearMap.map_add (f := _), RingHom.map_add (f := _), hy, hz]

theorem eq_finIncl {z : AE D} (hz : infPart D z = 0) : z = finIncl D (finPart D z) := by
  rw [← sub_eq_zero]
  apply eq_zero_of_parts
  · rw [RingHom.map_sub, hz, infPart_finIncl, sub_zero]
  · rw [RingHom.map_sub, finPart_finIncl, sub_self]

theorem finIncl_mul_mem {S T : HSp D} (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T) (v : GlobalTheory.FinPl.Pl D)
    {α : Af D.host.F} (hα : α ∈ intAf D.host.F) (hsupp : ∀ w, ¬ w = v → evalV D.host.F w α = 0)
    {a : D.host.E} (ha : a ∈ D.host.AA) {s : Fin S.rank → D.host.E} (hs : s ∈ LS)
    {t : Fin T.rank → D.host.E} (ht : t ∈ LT) {y : Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D) :
    (Matrix.of fun i j => finIncl D y *
      (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) : WO S T) ∈
      latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = v) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβ, x, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨β * α, mul_mem_intAf hβ hα, fun w hw => ?_, a, ha, s, hs, x • t,
      LT.smul_mem x ht, ?_⟩
    · rw [map_mul, hsupp w hw, mul_zero]
    · ext i j
      simp only [Matrix.of_apply, finIncl_tmul, Algebra.TensorProduct.tmul_mul_tmul, pair_mul]
      congr 1
      change (x : D.host.E) * (a * t i * _) = a * ((x : D.host.E) * t i) * _
      ring
  | zero =>
    convert (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = v)).zero_mem using 1
    ext i j; simp
  | add y z _ _ hy hz =>
    convert add_mem hy hz using 1
    ext i j; simp only [Matrix.of_apply, Matrix.add_apply, LinearMap.map_add (f := _), add_mul]
  | neg y _ hy =>
    convert neg_mem hy using 1
    ext i j; simp only [Matrix.of_apply, Matrix.neg_apply, LinearMap.map_neg, neg_mul]

theorem idem_latO : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S T : HSp D) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T) (u : WO S T), u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) → (Matrix.of fun i j => q.e * u i j : WO S T) ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) ∧ ∀ i j, (q.e + cA D q.e) * u i j = u i j := by
  intro D k _ _ _ _ q S T LS LT u hu
  obtain ⟨ε, ⟨α₀, rfl, h1, h0⟩, hε⟩ := q.above
  have hee : q.e * q.e = q.e := q.split.1
  have hec : q.e * cA D q.e = 0 := q.split.2.1
  have hεinf : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α₀)) = 0 := infPart_pair α₀ 1
  have hinf : infPart D q.e = 0 := by
    have : q.e = q.e * (q.e + cA D q.e) := by rw [mul_add, hee, hec, add_zero]
    rw [this, RingHom.map_mul, hε, hεinf, mul_zero]
  have hfin : finPart D q.e ∈ intAE D := by
    have h := q.sec_pr 1
    rw [map_one, mul_one] at h
    rw [← h]
    exact (q.int_iff 1).1 (one_mem _)
  have he := eq_finIncl hinf
  refine ⟨?_, ?_⟩
  · induction hu using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, hsupp, a, ha, s, hs, t, ht, rfl⟩ := hw
      have h := finIncl_mul_mem LS LT q.v hα hsupp ha hs ht hfin
      rw [← he] at h
      simpa only [Matrix.of_apply] using h
    | zero =>
      convert (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v)).zero_mem using 1
      ext i j; simp
    | add x y _ _ hx hy =>
      convert add_mem hx hy using 1
      ext i j; simp only [Matrix.of_apply, Matrix.add_apply, mul_add]
    | neg x _ hx =>
      convert neg_mem hx using 1
      ext i j; simp only [Matrix.of_apply, Matrix.neg_apply, mul_neg]
  · induction hu using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, hsupp, a, ha, s, hs, t, ht, rfl⟩ := hw
      intro i j
      have hmul : α₀ * α = α := by
        apply RestrictedProduct.ext
        intro w
        change evalV D.host.F w (α₀ * α) = evalV D.host.F w α
        rw [map_mul]
        by_cases hw : w = q.v
        · subst hw; rw [h1, one_mul]
        · rw [hsupp w hw, mul_zero]
      rw [hε, Matrix.of_apply]
      change (pairA D.host.F 0 α₀ ⊗ₜ[D.host.F] (1 : D.host.E)) * _ = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, pair_mul, hmul]
    | zero => intro i j; simp
    | add x y _ _ hx hy => intro i j; rw [Matrix.add_apply, mul_add, hx, hy]
    | neg x _ hx => intro i j; rw [Matrix.neg_apply, mul_neg, hx]

end GlobalTheory.SplitVac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletedHomLatticeStableSplitIdempotentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completed_hom_lattice_stable_split_idempotent : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S T : HSp D) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T) (u : WO S T), u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) → (Matrix.of fun i j => q.e * u i j : WO S T) ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) ∧ ∀ i j, (q.e + cA D q.e) * u i j = u i j := by
  first | exact @GlobalTheory.SplitVac.idem_latO | exact GlobalTheory.SplitVac.idem_latO | (intros; apply GlobalTheory.SplitVac.idem_latO <;> assumption)
end
end
