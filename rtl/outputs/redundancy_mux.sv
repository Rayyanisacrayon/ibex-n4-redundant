//simple mux to be used for synthesis of redundancy paths
module redundancy_mux #(
  parameter int WIDTH = 32
) (
  input  logic [WIDTH-1:0]  operand_a,
  input  logic [WIDTH-1:0]  operand_b,

  input  logic              select,

  output logic [WIDTH-1:0]  result
);

    assign result = select ? operand_b : operand_a;


endmodule
