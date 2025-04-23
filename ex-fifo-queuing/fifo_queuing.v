`define FORMAL

module fifo_queuing (
					clk,		// The Synchronous FIFO has 
							// a single clock port for both data-read and data-write operations, 
							// it means it is used for synchronising across two process 
							// when two process are running on same clock
					reset,
					put,		// Write Enable
					get,		// Read Enable
					DataIn,
					empty,
					QFull,
					DataOut
);

parameter DEPTH = 8;			// D1-D8
parameter WIDTH = 16;			// 16-bit Data
parameter POINTER_WIDTH = 3;	// 3-bit Address

input clk;
input reset;
input put;
input get;
input [WIDTH-1:0] DataIn;
output empty;
output QFull;
output [WIDTH-1:0] DataOut;

reg [POINTER_WIDTH:0] wr_ptr;	// Write Pointer
reg [POINTER_WIDTH:0] rd_ptr;	// Read Pointer
reg empty;
reg QFull;
reg [WIDTH-1:0] DataOut;

reg [WIDTH-1:0] static_mem [DEPTH-1:0]; // Static Memory

wire [POINTER_WIDTH-1:0] wr_ptr_int;
wire [POINTER_WIDTH-1:0] rd_ptr_int;
wire [POINTER_WIDTH:0] wr_rd;
wire put_e;
wire get_e;

assign wr_rd = wr_ptr - rd_ptr;
assign put_e = (put && QFull == 1'b0);
assign get_e = (get && empty == 1'b0);
assign wr_ptr_int = wr_ptr[POINTER_WIDTH-1:0];
assign rd_ptr_int = rd_ptr[POINTER_WIDTH-1:0];

always @ (posedge clk)
	begin
		if (!reset)
			begin
				wr_ptr <= 3'b0000;
				rd_ptr <= 3'b0000;
			end 
		else
			begin
				if (put_e)
					begin
						static_mem[wr_ptr_int] <= DataIn;
						wr_ptr <= wr_ptr + 3'b001;
					end
				if (get_e)
					begin
						rd_ptr <= rd_ptr + 3'b001;
					end
			end
	end

always @(rd_ptr_int)
	begin
		DataOut <= static_mem[rd_ptr_int - 3'b001];
	end

always @ (posedge clk) 
	begin
		if (!reset)
			begin
				QFull <= 1'b0;
				empty <= 1'b0;				
			end
		else
			begin
				QFull <= (wr_rd == 4'b1000);
				empty <= (wr_rd == 4'b0000);
			end
	end

`ifdef FORMAL

initial wr_ptr = 4'b0000;
initial rd_ptr = 4'b0000;
initial QFull = 0;

reg f_past_valid;
initial f_past_valid = 1'b0;
always @(posedge clk)
	f_past_valid <= 1'b1;

always @(*)
	if (!f_past_valid)
		assume(!reset);

always @(posedge clk)
	if (!f_past_valid || (!$past(reset))) begin
		assume(!DATAIn);
		assume(!put);
		assume(!get);
	end

always @(*)
 	assume(!(get)||!(put));

always @(posedge clk)
	if (put)
		assume(!$stable(DataIn));


// Properties put here.
// Property 1: G [!QFull => Datain AND PUT]

always @(posedge clk)
	if (f_past_valid && !QFull && ($past(reset))) begin
		assume(DataIn && put);
	end
	

// Property 2: G [QFull => Get]
//
reg [3:0] f_count;
initial f_count = 0;
always @(posedge clk)
	if (!reset||get)
		f_count <= 0;
	else if (put&&!get) begin
		f_count <= f_count + 1'b1;
	end

// always @(posedge clk)
// 	if (f_past_valid && (!$past(reset))&&(f_count == 8)) begin
// 		assume(get);
// 	end
always @(posedge clk)
	if (f_past_valid&&($past(reset))&&QFull) begin
		assume(get);
	end
	

// Property 3: FIFO check;
// property FIFO_check;
// 	int x;
// 	int y;
// 	@(posedge clk)
// 	((PUT && !QFull, x = DataIn) ##[1, $]
// 		(PUT && !QFull, y = DataIn)) |->
// 		##[1,$] ((Get && x == DataOut) ##[1,$]
// 			(Get && y == DataOut));
// endproperty
always @(posedge clk)
	if (f_past_valid && ($past(reset)))
		cover(rd_ptr == 2);


`endif

endmodule
