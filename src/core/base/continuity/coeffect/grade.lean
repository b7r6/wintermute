/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                   // CONTINUITY // ALGEBRA // GRADE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━


                             The Grade Lattice

                                                                        - straylight.software · 2026

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Continuity.Coeffect.Grade

inductive GradeLabel where
  | Net
  | Auth
  | Config
  | Log
  | Crypto
  | Fs
  | FsCA
  | Gpu
  | Sandbox
  | Time
  | Random
  | Env
  | Identity
  deriving DecidableEq, Repr, Inhabited

abbrev Grade := List GradeLabel

namespace Grade

def unit : Grade := []

def full : Grade :=
  [.Net, .Auth, .Config, .Log, .Crypto, .Fs, .FsCA, .Gpu, .Sandbox, .Time, .Random, .Env, .Identity]

def mem (leftValue : GradeLabel) (grade : Grade) : Bool := grade.any (· == leftValue)

def plus (gradeOne gradeTwo : Grade) : Grade :=
  gradeOne ++ gradeTwo.filter (fun label => !gradeOne.any (· == label))

def subset (gradeOne gradeTwo : Grade) : Prop := ∀ l, mem l gradeOne = true → mem l gradeTwo = true

instance : HasSubset Grade where
  Subset := subset

def isPure (grade : Grade) : Bool := grade.isEmpty

def isReproducible (grade : Grade) : Bool :=
  !mem .Time grade && !mem .Random grade && !mem .Env grade && !mem .Identity grade
      && !mem .Net grade
      && !mem .Fs grade

-- ══════════════════════════════════════════════════════════════════════════════
--                                                            // CONCRETE // FACTS
-- ══════════════════════════════════════════════════════════════════════════════

theorem unit_is_reproducible : isReproducible unit = true := rfl

theorem unit_is_pure : isPure unit = true := rfl

theorem plus_unit_right (grade : Grade) : plus grade unit = grade := by
  unfold plus unit; simp [List.filter_nil, List.append_nil]

-- Concrete domain grades
def gateway : Grade := [.Net, .Auth, .Config, .Log, .Crypto]

def build : Grade := [.Fs, .FsCA, .Net, .Env, .Sandbox]
def gatewayPure : Grade := [.Crypto]
def gatewayNet : Grade := [.Net, .Auth]

-- Concrete reproducibility facts
theorem pure_is_reproducible : isReproducible unit = true := rfl

theorem time_not_reproducible : isReproducible [.Time] = false := by native_decide

theorem random_not_reproducible : isReproducible [.Random] = false := by native_decide

theorem ca_only_reproducible : isReproducible [.FsCA, .Crypto] = true := by native_decide

theorem gateway_not_reproducible : isReproducible gateway = false := by native_decide

-- Concrete subset facts
theorem gateway_mem_net : mem .Net gateway = true := by native_decide

theorem gateway_mem_auth : mem .Auth gateway = true := by native_decide

theorem gateway_mem_crypto : mem .Crypto gateway = true := by native_decide

theorem unit_no_mem (leftValue : GradeLabel) : mem leftValue unit = false := by
  cases leftValue <;> native_decide

-- ══════════════════════════════════════════════════════════════════════════════
--                                                             // ABSTRACT // LAWS
-- ══════════════════════════════════════════════════════════════════════════════

theorem plus_unit_left (grade : Grade) : plus unit grade = grade := by simp [plus, unit]

theorem plus_le_left (gradeOne gradeTwo : Grade) : subset gradeOne (plus gradeOne gradeTwo) := by
  intro label labelMem; simp [plus, mem] at *; exact Or.inl labelMem

theorem plus_le_right (gradeOne gradeTwo : Grade) : subset gradeTwo (plus gradeOne gradeTwo) := by
  intro label labelMem; simp [plus, mem] at *
  by_cases hg1 : label ∈ gradeOne
  · exact Or.inl hg1
  · exact Or.inr ⟨labelMem, fun candidate membership equality => hg1 (equality ▸ membership)⟩

theorem plus_idem (grade : Grade) : subset (plus grade grade) grade := by
  intro label labelMem; simp [plus, mem] at *
  rcases labelMem with labelInGrade | ⟨labelInGrade, _⟩ <;> exact labelInGrade

theorem plus_comm_subset
        (gradeOne gradeTwo : Grade)
        : subset (plus gradeOne gradeTwo) (plus gradeTwo gradeOne) := by
  intro label labelMem; simp [plus, mem] at *
  rcases labelMem with labelInFirst | ⟨labelInSecond, distinctFromFirst⟩
  · by_cases labelInSecond : label ∈ gradeTwo
    · exact Or.inl labelInSecond
    · exact
        Or.inr
          ⟨labelInFirst, fun candidate membership equality => labelInSecond (equality ▸ membership)⟩
  · exact Or.inl labelInSecond

theorem gateway_subset_full : subset gateway full := by
  intro label labelMem; simp [mem, gateway, full] at *; cases label <;> simp_all

end Grade
end Continuity.Coeffect.Grade
