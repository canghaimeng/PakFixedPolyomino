import PakFixedPolyomino.ULogCompiler

/-! Actual unary bytecode fields give numerical resource bounds from the
literal encoded program, without a supplied state-size certificate. -/
namespace PakFixedPolyomino.ULogEncodedRuleSize
open ULogBytecode ULogCompiler

theorem source_field_le_rule_length (r : RuleCode) :
    r.source + 1 ≤ (encodeRule r).length := by
  simp only [encodeRule, List.length_append, length_encodeNatField, List.length_singleton]
  omega

theorem member_rule_length_le_rules_length (r : RuleCode) (rs : List RuleCode)
    (member : r ∈ rs) : (encodeRule r).length ≤ (encodeRules rs).length := by
  induction rs with
  | nil => simp at member
  | cons s ss ih =>
    rcases List.mem_cons.mp member with same | rest
    · subst s
      simp only [encodeRules, List.length_append]
      omega
    · have smaller := ih rest
      simp only [encodeRules, List.length_append]
      omega

theorem member_source_le_program_length (r : RuleCode) (rs : ProgramCode)
    (member : r ∈ rs) : r.source + 1 ≤ (encodeProgram rs).length := by
  have field := source_field_le_rule_length r
  have record := member_rule_length_le_rules_length r rs member
  simp only [encodeProgram, List.length_append, length_encodeNatField]
  omega

theorem occupied_source_le_compiled_program_length {ns nt : Nat}
    (p : BoundedProgram ns nt) (q : Fin ns) (read : Fin nt) (slot : Bool)
    (a : BoundedAction ns nt) (rule : p.rule q read slot = some a) :
    q.val + 1 ≤ (encodeProgram (compile p)).length :=
  member_source_le_program_length (ruleCode q read slot a) (compile p)
    (compile_mem_ruleCode p q read slot a rule)

end PakFixedPolyomino.ULogEncodedRuleSize
