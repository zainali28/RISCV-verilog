`timescale 1ns / 1ns

module control_unit(
  input [31:0] inst,
  output reg wb_en,
  output reg pc_sel,
  output reg op1,
  output reg op2,
  output reg [1:0] wb_sel,
  output reg [3:0] alu_sel,
  output reg mem_rw,
  output reg [2:0] imm_sel,
  output reg [1:0] mem_mode
);

  always @(*) begin
    
  case(inst[6:0])
    7'b0110011: begin  //R-type
      case(inst[14:12])  //alu select logic
        3'b000: alu_sel = inst[30] ? 1 : 0;  //ADD=0, SUB=1
        3'b001: alu_sel = 2;  //SLL=2
        3'b010: alu_sel = 3;  //SLT=3
        3'b011: alu_sel = 4;  //SLTU=4
        3'b100: alu_sel = 5;  //XOR=5
        3'b101: alu_sel = inst[30] ? 7 : 6;  //SRL=6, SRA=7
        3'b110: alu_sel = 8;  //OR=8
        3'b111: alu_sel = 9;  //AND=9
      endcase
      
      pc_sel = 0;
      wb_en = 1;
      op1 = 0;
      op2 = 0;
      wb_sel = 1; // use blocking assignment here
      
    end
    7'b0010011: begin  //I-type
      case(inst[14:12])  //alu select, imm gen logic
        3'b000: begin 
            alu_sel = 0;  //ADD=0
            imm_sel = 0;  //I-type
          end
        3'b001: begin 
            alu_sel = 2;  //SLL=2
            imm_sel = 5;  //I-type SLL
          end
        3'b010: begin
            alu_sel = 3;  //SLT=3
            imm_sel = 0;
          end
        3'b011: begin
            alu_sel = 4;  //SLTU=4
            imm_sel = 0;
          end
        3'b100: begin 
            alu_sel = 5;  //XOR=5
            imm_sel = 0;
          end
        3'b101: begin
            alu_sel = (inst[30]) ? (7) : (6);  //SRL=6, SRA=7
            imm_sel = 5;
          end
        3'b110: begin
            alu_sel = 8;  //OR=8
            imm_sel = 0;
          end
        3'b111: begin 
            alu_sel = 9;  //AND=9
            imm_sel = 0;
          end
      endcase
      
    pc_sel = 0;
    wb_en = 1;
    op1 = 0;
    op2 = 1;
    wb_sel = 1; // use blocking assignment here 
    
    end
    
    7'b0000011: begin  //load
      case(inst[14:12])
        3'b000: begin  //load byte
              mem_mode = 0;  //read byte
            end
            
        3'b001: begin  //load half word
              mem_mode = 1;  //read half-word
            end
            
        3'b010: begin  //load word
              mem_mode = 2;  //read word
            end
            
          endcase
        
        alu_sel = 0;  //offset
        pc_sel = 0;
        wb_en = 1;
        op1 = 0;
        op2 = 1;
        wb_sel = 0;
        imm_sel = 0;
        mem_rw = 0;  //read from memory
          
        end
    
    7'b0100011: begin  //S-type
      case(inst[11:7])
        3'b000: begin  //store byte
              mem_mode = 0;  //write byte
            end
            
        3'b001: begin  //store half word
              mem_mode = 1;  //write half-word
            end
            
        3'b010: begin  //store word
              mem_mode = 2;  //write word
            end
            
          endcase
        
        alu_sel = 0;  //offset
        pc_sel = 0;
        wb_en = 0;
        op1 = 0;
        op2 = 1;
        wb_sel = 0;
        imm_sel = 1;  //s-type
        mem_rw = 1;  //read from memory
          
        end
        
          
    endcase
  
  end

endmodule
                 

module data_memory(
  input clk,
  input [1:0] mem_mode,  //byte, half-word, or word addressable
  input [31:0] address,  //address to which either read/write from/to
  input [31:0] data,  //data to be written on address pointed to
  input rw,  //0 for read and 1 for write
  output reg [31:0] out //data output
);

reg [7:0] mem[0:1023];  //1024 locations each of 32 bit


initial begin
mem[0] = 0;
mem[1] = 1;
mem[2] = 2;
mem[3] = 3;
end

always @(posedge clk) begin

  if(!rw) begin  //read for rw = 0
    case(mem_mode)
      2'b00: out <= {{24{1'b0}}, mem[address]};  //load byte
      2'b01: out <= {mem[address+1], mem[address]};  //load half-word
      2'b10: out <= {{{mem[address+3], mem[address+2]}, mem[address+1]}, mem[address]};  //load word
    endcase
      
  end else begin  //write for rw = 1
    case(mem_mode)
      2'b00: mem[address] <= data[7:0];  //write byte
      
      2'b01: begin  //write half-word
        mem[address] <= data[7:0];
        mem[address+1] <= data[15:8];
      end
      
      2'b01: begin  //write word
        mem[address] <= data[7:0];
        mem[address+1] <= data[15:8];
        mem[address] <= data[23:16];
        mem[address+1] <= data[31:24];
      end
      
    endcase
  end
end
  
endmodule

module three_in_mux(
  input [31:0] in1,
  input [31:0] in2,
  input [31:0] in3,
  input [1:0] sel,
  output reg [31:0] out
);

always @(*) begin
  
  case(sel)
    2'b00: out = in1;
    2'b01: out = in2;
    2'b10: out = in3;
    default: out = 0;
  endcase
end

endmodule

module imm_gen(
  input [24:0] inst,
  input [2:0] sel,
  output reg [31:0] imm
);

always @(*) begin

  case(sel)
    3'b000: assign imm = {{20{inst[24]}}, inst[24:13]};  //I-type
    3'b001: assign imm = {{{20{inst[24]}}, inst[24:18]}, inst[4:0]};  //S-type
    3'b010: assign imm = {{{{{{19{inst[24]}}, inst[24]}, inst[0]}, inst[23:18]}, inst[4:1]}, 1'b0};  //B-type    
    3'b011: assign imm = {{12{inst[24]}}, inst[24:5]};  //U-type
    3'b100: assign imm = {{{{{{11{inst[24]}}, inst[24]}, inst[12:5]}, inst[12]}, inst[23:14]}, 1'b0};  //J-type
    3'b101: assign imm = {{27{32'b00000000000000000000000000000000}}, inst[17:13]};  //I-type SLL, SRL, SRA
  endcase
end

endmodule

module branch_comparator(
  input [31:0] rs1,
  input [31:0] rs2,
  input brun,  //branch unit, enables it to branch
  output reg breq,
  output reg brne,
  output reg brlt,
  output reg bge,
  output reg bltu,
  output reg bgeu  
);

  always @(*) begin
  
    assign breq = ($signed(rs1) == $signed(rs2));               // BEQ
    assign brne = ($signed(rs1) != $signed(rs2));               // BNE
    assign brlt = ($signed(rs1) < $signed(rs2));                // BLT
    assign bge = ($signed(rs1) >= $signed(rs2));               // BGE
    assign bltu = ((rs1 < rs2) || (rs1[31] != rs2[31]));  // BLTU
    assign bgeu = ((rs1 >= rs2) || (rs1[31] != rs2[31])); // BGEU
    
  end

//  assign branch = branch && (imm[31] == rs1[31]); // check sign bit of rs1 and imm

endmodule  
    

module alu(
  input [31:0] operand_a,    // first operand
  input [31:0] operand_b,    // second operand
  input [3:0] alu_sel,       // Upper bits of the ALU function code
  output reg [31:0] result       // ALU result
);

  // Combinational logic to implement the ALU operations
  always @(*) begin
    case (alu_sel)
      4'b0000: result = operand_a + operand_b; // ADD
      4'b0001: result = operand_a - operand_b; // SUB
      4'b0010: result = operand_a << operand_b; // SLL
      4'b0011: result = ($signed(operand_a) < $signed(operand_b)) ? 1 : 0;  //SLT using signed to convert a number to its signed 2's complement form
      4'b0100: result = operand_a < operand_b ? 1 : 0; // SLTU
      4'b0101: result = operand_a ^ operand_b; // XOR
      4'b0110: result = operand_a >> operand_b; // SRL
      4'b0111: result = $signed(operand_a) >>> operand_b;  // SRA
      4'b1000: result = operand_a | operand_b; // OR
      4'b1001: result = operand_a & operand_b; // AND
      default: result = 0; // Default case
    endcase
  end

endmodule

module plus_four(
  input [31:0] address, // take input from program counter
  output [31:0] new_address // return the address plus 4
);

assign new_address = address + 4;

endmodule

module two_in_mux(
  input [31:0] in1, // 1st input
  input [31:0] in2, // 2nd input
  input sel, // input selector
  output reg [31:0] out // output
); 
always @(*) begin  
  //forward in2 if sel = 1, else forward in1
  out = sel ? in2 : in1;
end
 
endmodule

module program_counter(
  input clk, // clock input
  input rst, // reset input
  input [31:0] address, // input address
  output reg [31:0] pc // output program counter
);
 

always @(posedge clk or posedge rst) begin
  if (rst) begin
    pc <= 32'h0; // reset to 0
  end
  else begin
    pc <= address; // set PC to input address
  end
end

endmodule

module instruction_memory (
  input [31:0] address, //address from program counter
  output reg [31:0] instruction //output instruction at that address
);

reg [31:0] mem [0:1023]; //1024 locations each of 32 bits

initial begin
  // Load instructions into memory
  //$readmemh("program.hex", mem);
//  mem[0] = 32'b00000000000000001000000010110011;  //add
//  mem[0] = 32'b00000000000100000000000000010011;  //addi
//  mem[0] = 32'b00000000000000000000000000000011;  //lb
  mem[0] = 32'b00000000000100000000000000100011;  //sb
  mem[16] = 32'b00000000000000000000000110000011;  //lb
end


  
  //execute the block whenever any of the input changes
always @(*) begin
  instruction <= mem[address[31:0]]; //because lower 2 bits are always zero
end

endmodule

module regfile(
  input [4:0] addrA,  //address of rs1
  input [4:0] addrB,  //address of rs2
  input [4:0] addrD,  //address of rd
  input [31:0] dataD,  //data write to adress of D
  input wr_en,  //write enable
  input clk,  //clock
  output reg [31:0] dataA,  //data from address of A
  output reg [31:0] dataB  //data from address of B
);

reg [31:0] mem [31:0];  //32 locations each of 32 bit

initial begin
mem[0] = 0;
mem[1] = 3;
end

always @(posedge clk) begin
  if(wr_en) begin
    mem[addrD] <= dataD;
  end
  
  dataA <= mem[addrA];
  dataB <= mem[addrB];

end

endmodule


module tb_riscv;  //test bench

reg clk;  //clk state
reg rst;  //reset state
wire [31:0] pc_p4;  //address wire from pc_plus_four to pc
wire [31:0] pc;  //output of pc, address
wire [31:0] inst;  //instruction read from location pointed to by pc
wire wb_en;
wire pc_sel;
wire op1;
wire op2;
wire [1:0] wb_sel;
wire [3:0] alu_sel;
wire [31:0] pc_mux;
wire [31:0] alu;
wire [31:0] rs1;
wire [31:0] rs2;
wire [31:0] wb;
wire [31:0] result;
wire mem_rw;
wire [31:0] dmem_out;
wire [31:0] imm;
wire [31:0] op1_mux;
wire [31:0] op2_mux;
wire [2:0] imm_sel;
wire [1:0] mem_mode;

instruction_memory imem1(
  .address(pc),
  .instruction(inst)
);

control_unit cu(
  .inst(inst),
  .wb_en(wb_en),
  .pc_sel(pc_sel),
  .op1(op1),
  .op2(op2),
  .wb_sel(wb_sel),
  .alu_sel(alu_sel),
  .mem_rw(mem_rw),
  .imm_sel(imm_sel),
  .mem_mode(mem_mode)
);

program_counter pc1 (
  .clk(clk), //connecting clock pin of module (outside paranthesis) to the wire clk (inside paranthesis)
  .rst(rst),
  .address(pc_mux),
  .pc(pc)
);

two_in_mux m1(
  .in1(pc_p4),
  .in2(alu),
  .sel(pc_sel),
  .out(pc_mux)
);

two_in_mux m2(
  .in1(rs1),
  .in2(pc),
  .sel(op1),
  .out(op1_mux)
);

two_in_mux m3(
  .in1(rs2),
  .in2(imm),
  .sel(op2),
  .out(op2_mux)
);

plus_four p41(
  .address(pc),
  .new_address(pc_p4)
);

regfile rf1(
  .addrA(inst[19:15]),
  .addrB(inst[24:20]),
  .addrD(inst[11:7]),
  .dataD(wb),
  .wr_en(wb_en),
  .clk(clk),
  .dataA(rs1),
  .dataB(rs2)
);

three_in_mux m4(
  .in1(dmem_out),
  .in2(result),
  .in3(pc_p4),
  .sel(wb_sel),
  .out(wb)
);

imm_gen immgen1(
  .inst(inst[31:7]),
  .sel(imm_sel),
  .imm(imm)
);

alu alu1(
  .operand_a(op1_mux),
  .operand_b(op2_mux),
  .alu_sel(alu_sel),
  .result(result)
);

data_memory dmem1(
  .clk(clk),
  .address(result),
  .data(rs2),
  .rw(mem_rw),
  .out(dmem_out),
  .mem_mode(mem_mode)
);

branch_comparator br_cp(
  .rs1(rs1),
  .rs2(rs2),
  .breq(breq),
  .brne(brne),
  .brlt(brlt),
  .bge(bge),
  .bltu(bltu),
  .bgeu(bgeu)
);

initial begin
  clk = 0;
  forever #5 clk = ~clk; // toggle clock every 5ns
end

initial begin
  rst = 1;

  #10 rst = 0; // release reset after 10ns
  

  #100 $finish; // end simulation after 100ns
end

endmodule
