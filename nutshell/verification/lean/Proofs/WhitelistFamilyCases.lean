import Proofs.WhitelistFamilies
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 4096
theorem allowed_instruction_family (instr : BitVec 64) (allowed : AllowedInstruction instr) :
    AllowedInstructionFamily instr := by
  have cases := (allowed_instruction_cases instr).mp allowed
  unfold WhitelistCases at cases
  unfold AllowedInstructionFamily
  rcases cases with ((((((((((((((((((h0 | h1) | h2) | h3) | h4) | h5) | h6) | h7) | h8) | h9) | h10) | h11) | h12) | h13) | h14) | h15) | ((((((((((h16 | h17) | h18) | h19) | h20) | h21) | h22) | h23) | h24) | h25) | h26)) | (((((((((h27 | h28) | h29) | h30) | h31) | h32) | h33) | h34) | h35) | h36)) | (((((((h37 | h38) | h39) | h40) | h41) | h42) | h43) | h44))
  · exact Or.inl (⟨.add, instruction_mask_low32_lift instr (28799 : BitVec 32) (19 : BitVec 32) h0.symm⟩)
  · exact Or.inl (⟨.slt, instruction_mask_low32_lift instr (28799 : BitVec 32) (8211 : BitVec 32) h1.symm⟩)
  · exact Or.inl (⟨.sltu, instruction_mask_low32_lift instr (28799 : BitVec 32) (12307 : BitVec 32) h2.symm⟩)
  · exact Or.inl (⟨.and, instruction_mask_low32_lift instr (28799 : BitVec 32) (28691 : BitVec 32) h3.symm⟩)
  · exact Or.inl (⟨.or, instruction_mask_low32_lift instr (28799 : BitVec 32) (24595 : BitVec 32) h4.symm⟩)
  · exact Or.inl (⟨.xor, instruction_mask_low32_lift instr (28799 : BitVec 32) (16403 : BitVec 32) h5.symm⟩)
  · exact Or.inr (Or.inl (⟨.sll, instruction_mask_low32_lift instr (4227887231 : BitVec 32) (4115 : BitVec 32) h6.symm⟩))
  · exact Or.inr (Or.inl (⟨.srl, instruction_mask_low32_lift instr (4227887231 : BitVec 32) (20499 : BitVec 32) h7.symm⟩))
  · exact Or.inr (Or.inl (⟨.sra, instruction_mask_low32_lift instr (4227887231 : BitVec 32) (1073762323 : BitVec 32) h8.symm⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨.lui, instruction_mask_low32_lift instr (127 : BitVec 32) (55 : BitVec 32) h9.symm⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨.auipc, instruction_mask_low32_lift instr (127 : BitVec 32) (23 : BitVec 32) h10.symm⟩))))
  · exact Or.inr (Or.inr (Or.inl (⟨.add, instruction_mask_low32_lift instr (28799 : BitVec 32) (27 : BitVec 32) h11.symm⟩)))
  · exact Or.inr (Or.inr (Or.inl (⟨.sll, instruction_mask_low32_lift instr (4261441663 : BitVec 32) (4123 : BitVec 32) h12.symm⟩)))
  · exact Or.inr (Or.inr (Or.inl (⟨.srl, instruction_mask_low32_lift instr (4261441663 : BitVec 32) (20507 : BitVec 32) h13.symm⟩)))
  · exact Or.inr (Or.inr (Or.inl (⟨.srl, instruction_mask_low32_lift instr (4261441663 : BitVec 32) (20507 : BitVec 32) h14.symm⟩)))
  · exact Or.inr (Or.inr (Or.inl (⟨.sra, instruction_mask_low32_lift instr (4261441663 : BitVec 32) (1073762331 : BitVec 32) h15.symm⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨.lb, instruction_mask_low32_lift instr (28799 : BitVec 32) (3 : BitVec 32) h16.symm⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨.lh, instruction_mask_low32_lift instr (28799 : BitVec 32) (4099 : BitVec 32) h17.symm⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨.lw, instruction_mask_low32_lift instr (28799 : BitVec 32) (8195 : BitVec 32) h18.symm⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨.lbu, instruction_mask_low32_lift instr (28799 : BitVec 32) (16387 : BitVec 32) h19.symm⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨.lhu, instruction_mask_low32_lift instr (28799 : BitVec 32) (20483 : BitVec 32) h20.symm⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨.sb, instruction_mask_low32_lift instr (28799 : BitVec 32) (35 : BitVec 32) h21.symm⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨.sh, instruction_mask_low32_lift instr (28799 : BitVec 32) (4131 : BitVec 32) h22.symm⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨.sw, instruction_mask_low32_lift instr (28799 : BitVec 32) (8227 : BitVec 32) h23.symm⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨.lwu, instruction_mask_low32_lift instr (28799 : BitVec 32) (24579 : BitVec 32) h24.symm⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨.ld, instruction_mask_low32_lift instr (28799 : BitVec 32) (12291 : BitVec 32) h25.symm⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨.sd, instruction_mask_low32_lift instr (28799 : BitVec 32) (12323 : BitVec 32) h26.symm⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨.add, instruction_mask_low32_lift instr (4261441663 : BitVec 32) (51 : BitVec 32) h27.symm⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨.slt, instruction_mask_low32_lift instr (4261441663 : BitVec 32) (8243 : BitVec 32) h28.symm⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨.sltu, instruction_mask_low32_lift instr (4261441663 : BitVec 32) (12339 : BitVec 32) h29.symm⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨.and, instruction_mask_low32_lift instr (4261441663 : BitVec 32) (28723 : BitVec 32) h30.symm⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨.or, instruction_mask_low32_lift instr (4261441663 : BitVec 32) (24627 : BitVec 32) h31.symm⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨.xor, instruction_mask_low32_lift instr (4261441663 : BitVec 32) (16435 : BitVec 32) h32.symm⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨.sll, instruction_mask_low32_lift instr (4261441663 : BitVec 32) (4147 : BitVec 32) h33.symm⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨.srl, instruction_mask_low32_lift instr (4261441663 : BitVec 32) (20531 : BitVec 32) h34.symm⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨.sub, instruction_mask_low32_lift instr (4261441663 : BitVec 32) (1073741875 : BitVec 32) h35.symm⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨.sra, instruction_mask_low32_lift instr (4261441663 : BitVec 32) (1073762355 : BitVec 32) h36.symm⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨.jal, instruction_mask_low32_lift instr (127 : BitVec 32) (111 : BitVec 32) h37.symm⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨.jalr, instruction_mask_low32_lift instr (28799 : BitVec 32) (103 : BitVec 32) h38.symm⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨.beq, instruction_mask_low32_lift instr (28799 : BitVec 32) (99 : BitVec 32) h39.symm⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨.bne, instruction_mask_low32_lift instr (28799 : BitVec 32) (4195 : BitVec 32) h40.symm⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨.blt, instruction_mask_low32_lift instr (28799 : BitVec 32) (16483 : BitVec 32) h41.symm⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨.bltu, instruction_mask_low32_lift instr (28799 : BitVec 32) (24675 : BitVec 32) h42.symm⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨.bge, instruction_mask_low32_lift instr (28799 : BitVec 32) (20579 : BitVec 32) h43.symm⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨.bgeu, instruction_mask_low32_lift instr (28799 : BitVec 32) (28771 : BitVec 32) h44.symm⟩))))))
#print axioms allowed_instruction_family
end NutShellProofs
