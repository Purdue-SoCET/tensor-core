import re
from enum import Enum, auto
import argparse
import mmap

match_opcode = r"^\s*(?P<opcode>\w+)\s+"

class RISCV():
    class Opcode(Enum):
        LUI    = 0b0110111  # Load Upper Immediate
        AUIPC  = 0b0010111  # Add Upper Immediate to PC
        JAL    = 0b1101111  # Jump and Link
        JALR   = 0b1100111  # Jump and Link Register
        BRANCH = 0b1100011  # Branch instructions (BEQ, BNE, etc.)
        LOAD   = 0b0000011  # Load instructions (LB, LH, LW, LBU, LHU)
        STORE  = 0b0100011  # Store instructions (SB, SH, SW)
        ALU_IMM= 0b0010011  # ALU operations with immediate (ADDI, SLTI, etc.)
        ALU    = 0b0110011  # Register-to-register ALU operations (ADD, SUB, etc.)
    
    class Funct3(Enum):
        ADD_SUB  = 0b000  # ADD, SUB
        SLL      = 0b001  # Shift Left Logical
        SLT      = 0b010  # Set Less Than
        SLTU     = 0b011  # Set Less Than Unsigned
        XOR      = 0b100  # XOR
        SRL_SRA  = 0b101  # Shift Right Logical/Arithmetic
        OR       = 0b110  # OR
        AND      = 0b111  # AND

        # Branches (for BRANCH opcode)
        BEQ      = 0b000  # Branch if Equal
        BNE      = 0b001  # Branch if Not Equal
        BLT      = 0b100  # Branch if Less Than
        BGE      = 0b101  # Branch if Greater or Equal
        BLTU     = 0b110  # Branch if Less Than Unsigned
        BGEU     = 0b111  # Branch if Greater or Equal Unsigned
        
    funct3_dict = {
        "add": Funct3.ADD_SUB,
        "addi": Funct3.ADD_SUB,
        "sub": Funct3.ADD_SUB,
        "subi": Funct3.ADD_SUB,
        "sll": Funct3.SLL,
        "slli": Funct3.SLL,
        "slt": Funct3.SLT,
        "slti": Funct3.SLT,
        "sltu": Funct3.SLTU,
        "sltui": Funct3.SLTU,
        "xor": Funct3.XOR,
        "xori": Funct3.XOR,
        "srl": Funct3.SRL_SRA,
        "srli": Funct3.SRL_SRA,
        "sra": Funct3.SRL_SRA,
        "srai": Funct3.SRL_SRA,
        "or": Funct3.OR,
        "ori": Funct3.OR,
        "and": Funct3.AND,
        "andi": Funct3.AND,
        "beq": Funct3.BEQ,
        "bne": Funct3.BNE,
        "blt": Funct3.BLT,
        "bge": Funct3.BGE,
        "bltu": Funct3.BLTU,
        "bgeu": Funct3.BGEU
    }
    
    class Funct7(Enum):
        DEFAULT  = 0b0000000  # Most instructions
        SUB_SRA  = 0b0100000  # SUB, SRA (arithmetic shift)
    
    @staticmethod
    def get_funct3(opcode: str):
        assert opcode in RISCV.funct3_dict, f"could not find funct3 for opcode: {opcode}"
        return RISCV.funct3_dict[opcode]
    
    @staticmethod
    def get_funct7(opcode: str):
        if opcode in {'sub', 'sra'}: return RISCV.Funct7.SUB_SRA
        return RISCV.Funct7.DEFAULT


class Operand():
    
    def render(self) -> str:
        raise ValueError("cannot render abstract op")
    
    @staticmethod
    def parse(l: str, type: type):
        operandtype = re.search(match_opcode, l)
    
    def __repr__(self): return self.__str__()
        
class GPRegister(Operand):
    num: int
    def __init__(self, l: str):
        match_gpreg = r"\$(?P<reg>\d+)"
        match = re.search(match_gpreg, l)
        assert match is not None, f"couldn't parse general-purpose register: {l}"
        self.num = int(match.groups()[0])
    def __str__(self): return f"${self.num}"
        
class MatRegister(Operand):
    num: int
    def __init__(self, l: str): 
        match_matreg = r"\$m(?P<reg>\d+)"
        match = re.search(match_matreg, l)
        assert match is not None, f"couldn't parse matrix register: {l}"
        self.num = match.groups()[0]
    def __str__(self): return f"$m{self.num}"
    
class Immediate(Operand):
    value: int
    is_symbol: bool
    was_symbol: bool
    symbol: str
    def __init__(self, l: str):
        self.is_symbol = False
        self.was_symbol = False
        if re.search(r"0x", l): self.value = int(l, 16)
        elif re.search(r"0d", l): self.value = int(l, 10)
        elif re.search(r"0b", l): self.value = int(l, 2)
        elif re.match(r"^-?\d+$", l): self.value = int(l, 10)
        else:
            self.is_symbol = True
            self.symbol = l
            
    def fill_symbol(self, symbol_table: dict[str, int]):
        if self.is_symbol and self.symbol in symbol_table:
            self.value = symbol_table[self.symbol]
            self.is_symbol = False
            self.was_symbol = True
        return self
            
    def __str__(self):
        if self.was_symbol: return f"({self.symbol}={self.value})"
        elif self.is_symbol: return f"{self.symbol}"
        return f"{self.value}"
        

class Symbol():
    line_number: int
    filename: str
    line: str
    
    symbol: str
    
    def __init__(self, l, line_number, filename):
        self.line = l
        self.line_number = line_number
        self.filename = filename
        
        match = re.match(r"^\s*(?P<name>\w+):\s*$", self.line)
        assert match is not None, f"cannot parse symbol {self.line} at {self.filename}:{self.line_number}"
        self.symbol = match.groups()[0]
    
    def __str__(self): return f"{self.symbol}:"
    def __repr__(self): return self.__str__()

# Ops -------------------------------------------------------------------------

class Op():
    line_number: int
    filename: str
    line: str
    
    opcode: str
    pc: int
    args: tuple[Operand]
    destination: Operand | None
    
    macro: bool
    
    def __init__(self, l, opcode, line_number, filename):
        self.line = l
        self.args = tuple()
        self.opcode = opcode
        self.line_number = line_number
        self.filename = filename
        self.destination = None
        self.macro = False
        
        self.pc = -1
    
    def render(self) -> str:
        raise ValueError("cannot render abstract op")
    def parseoperands(self, l:str):
        raise ValueError("cannot parse abstract op")
    def encode(self):
        raise ValueError(f"cannot encode abstract op: {self} at {self.filename}: {self.line_number}")
    def fill_symbols(self, symbol_table: dict[str, Symbol]):
        self.args = tuple(arg.fill_symbol(symbol_table) if isinstance(arg, Immediate) else arg for arg in self.args)
    
    def set_debug_info(self, line_number, filename):
        self.line_number = line_number
        self.filename = filename
    def throw_parse_error(self, cond):
        assert cond, f"couldn't parse {self.opcode} at {self.filename}: {self.line_number}"
        
    def __str__(self):
        return  (f"[{self.pc:8x}]: " if self.pc > 0 else "") + \
                (f"{self.destination.__str__()} <- " if self.destination is not None else "") + \
                f"{self.opcode}( {', '.join(arg.__str__() for arg in self.args)} )"
    def __repr__(self):
        return  self.__str__()

class Org(Op):
    def __init__(self, l, opcode, line_number, filename):
        super().__init__(l, opcode, line_number, filename)
        self.opcode = opcode
        self.parseoperands()
    def parseoperands(self):
        match_org = r"^\s*(?P<opcode>\w+)\s+(?P<addr>\w+)"
        match = re.match(match_org, self.line)
        self.throw_parse_error(match is not None)
        self.args = Immediate(match.groups()[1]),
    def __str__(self): return f"{self.opcode} {self.args[0]}"
    
class Cfw(Op):
    def __init__(self, l, opcode, line_number, filename):
        super().__init__(l, opcode, line_number, filename)
        self.opcode = opcode
        self.parseoperands()
    def parseoperands(self):
        match_cfw = r"^\s*(?P<opcode>\w+)\s+(?P<val>\w+)"
        match = re.match(match_cfw, self.line)
        self.throw_parse_error(match is not None)
        self.args = Immediate(match.groups()[1]),
        
    def encode(self): self.bytes = 0x00000000 | self.args[0].value
        
    def __str__(self): return (f"[{self.pc:8x}]: " if self.pc > 0 else "") + f"{self.args[0].value:8x}"

class Halt(Op):
    def __init__(self, l, opcode, filename, line_number):
        super().__init__(l, opcode, filename, line_number)
        
    def parseoperands(self):
        pass
    
    def encode(self): self.bytes = 0xffffffff
    def __str__(self): return (f"[{self.pc:8x}]: " if self.pc > 0 else "") + f"{self.opcode}"

class Lui(Op):
    def __init__(self, l, opcode, filename, line_number):
        super().__init__(l, opcode, filename, line_number)
        self.parseoperands()
    def parseoperands(self):
        match_aluop = r"^\s*(?P<opcode>\w+)\s+(?P<dest>\$\d+)\s*,\s*(?P<b>-?\w+)"
        match = re.match(match_aluop, self.line)
        self.throw_parse_error(match is not None)
        self.destination = GPRegister(match.groups()[1])
        self.args = (Immediate(match.groups()[2])),
    def encode(self):
        opcode = int(RISCV.Opcode.LUI.value)
        imm = self.args[0].value
        self.bytes = (imm << 12) | (self.destination.num << 7) | opcode
class Auipc(Op):
    def __init__(self, l): super(l)
    def parseoperands(self, l: str):
        return super().parseoperands(l)

# Jumps
class Jal(Op):
    args: tuple[Immediate, GPRegister]
    
    def __init__(self, l, opcode, filename, line_number):
        super().__init__(l, opcode, filename, line_number)
        self.parseoperands()
        self.args = (self.args[0], GPRegister("$1"))
    def parseoperands(self):
        match_jal = r"^\s*(?P<opcode>\w+)\s+(?P<imm>-?\w+)"
        match = re.match(match_jal, self.line)
        self.throw_parse_error(match is not None)
        self.args = Immediate(match.groups()[1]),
    def encode(self):
        opcode = int(RISCV.Opcode.JAL.value)
        imm = self.args[0].value
        imm20 = (imm >> 20) & 0x1
        imm10_1 = (imm >> 1) & 0x3FF
        imm11 = (imm >> 11) & 0x1
        imm19_12 = (imm >> 12) & 0xFF
        self.bytes =  (imm20 << 31) | (imm19_12 << 12) | (imm11 << 20) | (imm10_1 << 21) | (self.args[1].num << 7) | opcode
class Jalr(Op):
    args: tuple[Immediate, GPRegister]
    
    def __init__(self, l, opcode, filename, line_number):
        super().__init__(l, opcode, filename, line_number)
        self.parseoperands()
        self.args = (self.args[0], GPRegister("$1"))
    def parseoperands(self):
        match_jal = r"^\s*(?P<opcode>\w+)\s+(?P<reg>\$\d+)"
        match = re.match(match_jal, self.line)
        self.throw_parse_error(match is not None)
        self.args = GPRegister(match.groups()[1]),
    def encode(self):
        opcode = int(RISCV.Opcode.JALR.value)
        print(self.args)
        imm = self.args[1].value
        funct3 = 0b000 
        self.bytes = (imm & 0xFFF) << 20 | (self.args[0].num << 15) | (funct3 << 12) | (self.args[1].num << 7) | opcode

class Load(Op):
    args: tuple[GPRegister, Immediate]
    destination: GPRegister
    
    def __init__(self, l, opcode, filename, line_number):
        super().__init__(l, opcode, filename, line_number)
        self.parseoperands()
    def parseoperands(self):
        match_aluop = r"^\s*(?P<opcode>\w+)\s+(?P<dest>\$\d+)\s*,\s*(?P<imm>-?\w+)\((?P<addr>\$\d+)\)"
        match = re.match(match_aluop, self.line)
        self.throw_parse_error(match is not None)
        self.destination = GPRegister(match.groups()[1])
        self.args = (GPRegister(match.groups()[3]), Immediate(match.groups()[2]))
    def encode(self):
        opcode = RISCV.Opcode.LOAD.value
        funct3 = 0b010
        imm = self.args[1].value & 0xFFF  # Ensure imm is 12-bit
        self.bytes = (imm << 20) | (self.args[0].num << 15) | (funct3 << 12) | (self.destination.num << 7) | opcode
class Store(Op):
    args: tuple[GPRegister, GPRegister, Immediate]
    
    def __init__(self, l, opcode, filename, line_number):
        super().__init__(l, opcode, filename, line_number)
        self.parseoperands()
    def parseoperands(self):
        match_aluop = r"^\s*(?P<opcode>\w+)\s+(?P<dest>\$\d+)\s*,\s*(?P<imm>-?\w+)\((?P<addr>\$\d+)\)"
        match = re.match(match_aluop, self.line)
        self.throw_parse_error(match is not None)
        self.args = (GPRegister(match.groups()[1]), GPRegister(match.groups()[3]), Immediate(match.groups()[2]))
    def encode(self) -> int:
        opcode = RISCV.Opcode.STORE.value
        funct3 = 0b010
        imm = self.args[2].value & 0xFFF  # Ensure imm is 12-bit (split into imm[11:5] and imm[4:0])
        imm_11_5 = (imm >> 5) & 0x7F  # Imm[11:5]
        imm_4_0 = imm & 0x1F         # Imm[4:0]
        self.bytes = (imm_11_5 << 25) | (self.args[0].num << 20) | (self.args[1].num << 15) | (funct3 << 12) | (imm_4_0 << 7) | opcode


# i type
class AluImm(Op):
    args: tuple[GPRegister, Immediate]
    destination: GPRegister
    
    def __init__(self, l, opcode, filename, line_number):
        super().__init__(l, opcode, filename, line_number)
        self.parseoperands()
    def parseoperands(self):
        match_aluop = r"^\s*(?P<opcode>\w+)\s+(?P<dest>\$\d+)\s*,\s*(?P<a>\$\d+)\s*,\s*(?P<b>-?\w+)"
        match = re.match(match_aluop, self.line)
        self.throw_parse_error(match is not None)
        self.destination = GPRegister(match.groups()[1])
        self.args = (GPRegister(match.groups()[2]), Immediate(match.groups()[3]))
    def encode(self) -> int:
        opcode = int(RISCV.Opcode.ALU.value)
        funct3 = int(RISCV.get_funct3(self.opcode).value)
        imm = self.args[1].value & 0xFFF  # Ensure imm is 12-bit
        self.bytes = (imm << 20) | (self.args[0].num << 15) | (funct3 << 12) | (self.destination.num << 7) | opcode
    
# Branches
class Branch(AluImm):
    def __init__(self, l, opcode, filename, line_number):
        super().__init__(l, opcode, filename, line_number)
    def calculate_branch_offset(self):
        self.args[1].value = self.args[1].value - self.pc
    
# rtype
class Alu(Op):
    
    args: tuple[GPRegister, GPRegister]
    destination: GPRegister
    
    def __init__(self, l, opcode, filename, line_number):
        super().__init__(l, opcode, filename, line_number)
        self.parseoperands()
    def parseoperands(self):
        match_aluop = r"^\s*(?P<opcode>\w+)\s+(?P<dest>\$\d+)\s*,\s*(?P<a>\$\d+)\s*,\s*(?P<b>\$\d+)"
        match = re.match(match_aluop, self.line)
        assert match is not None, f"couldn't parse {self.opcode} at {self.filename}: {self.line_number}"
        self.destination = GPRegister(match.groups()[1])
        self.args = (GPRegister(match.groups()[2]), GPRegister(match.groups()[3]))
    def encode(self) -> int:
        opcode = int(RISCV.Opcode.ALU.value)
        funct3 = int(RISCV.get_funct3(self.opcode).value)
        funct7 = int(RISCV.get_funct7(self.opcode).value)
        self.bytes = (funct7 << 25) | (self.args[0].num << 20) | (self.args[1].num << 15) | (funct3 << 12) | (self.destination.num << 7) | opcode

class Macro(Op):
    def __init__(self, l, opcode, filename, line_number):
        super().__init__(l, opcode, filename, line_number)
        self.macro = True
    
    def expand(self) -> list[Op]:
        raise ValueError("cannot expand abstract macro")

class Push(Macro):
    def __init__(self, l, opcode, filename, line_number):
        super().__init__(l, opcode, filename, line_number)
        self.parseoperands()
    def parseoperands(self):
        match_push = r"^\s*(?P<opcode>\w+)\s+(?P<reg>\$\d+)"
        match = re.match(match_push, self.line)
        self.throw_parse_error(match is not None)
        self.args = GPRegister(match.groups()[1]),
    def expand(self):
        #       addi sp, sp, -4   # Move stack pointer down
        #       sw \reg, 0(sp)    # Store the register at the top of the stack
        addi = AluImm("addi $2, $2, -4", "addi", self.line_number, self.filename)
        
        sw = Store(f"sw ${self.args[0].num}, 0($2)", "sw", self.line_number, self.filename)
        return [addi, sw]
    
class J(Macro):
    def __init__(self, l, opcode, filename, line_number):
        super().__init__(l, opcode, filename, line_number)
        self.parseoperands()
    def parseoperands(self):
        match_jal = r"^\s*(?P<opcode>\w+)\s+(?P<imm>-?\w+)"
        match = re.match(match_jal, self.line)
        self.throw_parse_error(match is not None)
        self.args = Immediate(match.groups()[1]),
    def expand(self):
        jal = Jal(f"jal {self.args[0]}", "jal", self.filename, self.line_number)
        jal.args = (jal.args[0], GPRegister("$0"))
        return [jal]
        
class Jr(Macro):
    def __init__(self, l, opcode, filename, line_number):
        super().__init__(l, opcode, filename, line_number)
        self.parseoperands()
    def parseoperands(self):
        match_jal = r"^\s*(?P<opcode>\w+)\s+(?P<reg>\$\d+)"
        match = re.match(match_jal, self.line)
        self.throw_parse_error(match is not None)
        self.args = GPRegister(match.groups()[1]),
    def expand(self):
        jalr = Jalr(f"jal {self.args[0]}", "jalr", self.filename, self.line_number)
        jalr.args = (jalr.args[0], GPRegister("$0"))
        return []

class Renderer():
    
    filename: str
    code: list[str]
    ops: list[Op]
    symbols: dict[str, Symbol]
    symbol_table: dict[str, int]
    reverse_symbol_table: dict[int, str]
    memory: bytearray
    
    num_gp_regs: int
    num_matrix_regs: int
    
    ops: dict[str, type] = {
        "org": Org,
        "cfw": Cfw,
        "push": Push,
        "halt": Halt,
        
        "lui": Lui,
        "auipc": Auipc,
        
        "jal": Jal,
        "jalr": Jalr,
        "j": J,
        "jr": Jr,
        
        "lw": Load,
        "sw": Store,
        
        "beq": Branch,
        "bne": Branch,
        "blt": Branch,
        "bge": Branch,
        "bltu": Branch,
        "bgeu": Branch,
        
        "addi": AluImm,
        "subi": AluImm,
        "slli": AluImm,
        "slti": AluImm,
        "sltui": AluImm,
        "xori": AluImm,
        "srli": AluImm,
        "srai": AluImm,
        "ori": AluImm,
        "andi": AluImm,
        
        "add": Alu,
        "sub": Alu,
        "sll": Alu,
        "slt": Alu,
        "sltu": Alu,
        "xor": Alu,
        "srl": Alu,
        "sra": Alu,
        "or": Alu,
        "and": Alu
    }
    
    def __init__(self, output_filename, num_gp_regs, num_matrix_regs):
        self.output_filename = output_filename
        self.num_gp_regs = num_gp_regs
        self.num_matrix_regs = num_matrix_regs
        
        self.filename = None
        self.code = []
        self.ops = []
        self.symbols = {}
        self.symbol_table = {}
        self.reverse_symbol_table = {}
        
    def render(self, filename):
        self.filename = filename
        self._readsource()
        self._parseops()
        self._expandmacros()
        self._buildsymboltable()
        self._sortbyaddr()
        self._fillsymbols()
        self._generate_binary()
        self._write_binary()
        # raise ValueError("not implemented")
    
    def write_ops(self, filename):
        print(f"writing ops to: {filename}")
        with open(filename, "w") as f:
            for op in self.ops:
                f.write(op.__str__())
                if op.pc in self.reverse_symbol_table:
                    f.write(f"        // {self.reverse_symbol_table[op.pc]}")
                f.write("\n")
            f.close()
        print("done writing ops.")
        
    def _write_binary(self):
        minsize = max(op.pc for op in self.ops) + 4
        
            
        with open(self.output_filename, "wb") as f:
            f.truncate(minsize)
            f.close()
            
        with open(self.output_filename, "r+b") as f:
            m = mmap.mmap(f.fileno(), 0)
            for op in self.ops:
                print(f"{op.pc}:{op.pc+4} - {hex(op.bytes)}")
                m[op.pc:op.pc+4] = op.bytes.to_bytes(4)
            m.close()
            f.close()
        print(f"wrote binary to {self.output_filename}.")
        
    def _generate_binary(self):
        for op in self.ops: op.encode()

    def _fillsymbols(self):
        for i,op in enumerate(self.ops):
            op.fill_symbols(self.symbol_table)
            if isinstance(op, Branch): op.calculate_branch_offset()
            
    def _sortbyaddr(self):
        self.ops.sort(key=lambda op: op.pc)
        
    def _buildsymboltable(self):
        pc = 0
        _ops = []
        for i,op in enumerate(self.ops):
            if isinstance(op, Symbol):
                op: Symbol = op
                self.symbols[op.symbol] = op
                self.symbol_table[op.symbol] = pc
                self.reverse_symbol_table[pc] = op.symbol
            elif isinstance(op, Org):
                pc = op.args[0].value
                op.pc = pc
            else:
                op.pc = pc
                _ops.append(op)
                pc += 4
        self.ops = _ops
                
    def _expandmacros(self):
        _ops = []
        for op in self.ops:
            if isinstance(op, Symbol) or not op.macro:
                _ops.append(op)
                continue
            for micro in op.expand():
                _ops.append(micro)
        self.ops = _ops
                
    
    def _readsource(self):
        with open(self.filename) as f:
            self.code = f.readlines()
            f.close()
            
    def _parseops(self):
        for i,l in enumerate(self.code):
            # chop off comments
            l = l.split("#")[0]
            
            # try to parse out an op
            op = self._parseop(l, i+1)
            
            # if we couldn't find an opcode or a symbol, continue
            if op is None: continue
            self.ops.append(op)
           
    def _parseop(self, l: str, line_number: int) -> Op|Symbol:
        opcode = re.search(match_opcode, l)
        if opcode is None:
            match = re.match(r"^\s*(?P<name>\w+):\s*$", l)
            if match is not None:
                return Symbol(l, line_number, self.filename)
            else:
                return None
        else: opcode = opcode.groups("opcode")[0]
        assert opcode in Renderer.ops, f"Couldn't parse opcode: {opcode} at {self.filename}: {line_number}"
        
        op: Op = Renderer.ops[opcode](l, opcode, line_number, self.filename)
        return op
        
if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Assemble a file")

    # Add an argument for the filename
    parser.add_argument('filename', type=str, help="The filename of the source assembly")
    parser.add_argument('-o', '--output', type=str, help="The filename of the output binary", default="out.bin")

    # Parse the arguments
    args = parser.parse_args()
    
    print(f"Assembling: {args.filename}")
    
    renderer = Renderer("out.bin", 32, 8)
    renderer.render(args.filename)
    renderer.write_ops("./kernels/out.ops")