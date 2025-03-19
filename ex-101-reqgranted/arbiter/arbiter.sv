typedef enum logic[2:0] {
	NORMAL_ARB, // 000
	FORCE0,			// 001
	FORCE1,			// 010
	FORCE2,			// 011	
	FORCE3,			// 100
	ACCESS_OFF, // 101
	ACCESS_ON,	// 110
	RESERVED		// 111
} t_opcode;

module arbiter(
	input logic [3:0] req,
	input t_opcode opcode,
	input logic clk, rst,
	output logic [3:0] gnt,
	output logic op_error
);

	// Internal signals
	logic [3:0] next_gnt;
	logic next_op_error;

	// Sequential logic for state update
	always_ff @(posedge clk or posedge rst) begin
		if (rst) begin
			gnt <= 4'b0000;
			op_error <= 1'b0;
		end else begin
			gnt <= next_gnt;
			op_error <= next_op_error;
		end
	end

	// Combinational logic for next state and output
	always_comb begin
		// Default values
		next_gnt = 4'b0000;
		next_op_error = 1'b0;

		case (opcode)
			NORMAL_ARB: begin
				// Normal arbitration logic (e.g., priority based)
				if (req[0]) next_gnt = 4'b0001;
				else if (req[1]) next_gnt = 4'b0010;
				else if (req[2]) next_gnt = 4'b0100;
				else if (req[3]) next_gnt = 4'b1000;
			end
			FORCE0: next_gnt = 4'b0001;
			FORCE1: next_gnt = 4'b0010;
			FORCE2: next_gnt = 4'b0100;
			FORCE3: next_gnt = 4'b1000;
			ACCESS_OFF: next_gnt = 4'b0000;
			ACCESS_ON: next_gnt = 4'b1111;
			RESERVED: next_op_error = 1'b1; // Reserved opcode, raise error
			default: next_op_error = 1'b1; // Invalid opcode, raise error
		endcase
	end

`ifdef FORMAL
	reg f_valid_clock;
	initial f_valid_clock = 1'b0;
	always @(posedge clk)
		f_valid_clock = 1'b1;

	// Check Grant
	always @(posedge clk)
		assume (rst == 1'b0);
	initial assume (req == 4'b0000);
	initial assume (next_gnt == 4'b0000);

	// always @(posedge clk)
	// 	if (f_valid_clock && !(gnt[0]))
	// 		check_grant: assert(!$past(req[0]));
	//
	
	// Good opcode
	always @(posedge clk) begin
		assume (opcode != RESERVED);
		// assume (opcode == NORMAL_ARB);
	end

	// Cover all at once
	// always @(posedge clk)
	// 	cover_all_at_once: cover (req[0]&&req[1]&&req[2]&&req[3]);

	// gnt_falls
	initial assume(gnt==4'b0000);	
	always @(posedge clk)
		if (f_valid_clock)
			if (!gnt[0] && $past(gnt[0]))
				gnt_falls: assert ($past(req[0], 2));

	// Immediate assertions
	// grant0_ok
	// you never expect a grant to agent 0 when it was not requested
	// always @(posedge clk)
	// 	if (f_valid_clock)
	// 		grant0_ok: assert (!(gnt[0] && !$past(req[0])));

	
	// reg [1:0] num_gnts;
	// always @(*) begin
	// 	// num_gnts = $countbits(gnt, 1'b1);
	// 	num_gnts = $countones(gnt);
	// 	cover (num_gnts == 2'b01);
	// end

	// reg safe_gnts;
	// always @(*) begin
	// 	safe_gnts = $onehot0(gnt);
	// 	assert(safe_gnts);
	// end

	reg [2:0] f_min_wait;
	initial f_min_wait = 0;
	always @(posedge clk)
		if (req[0] && !gnt[0])
			f_min_wait <= 3'b001;
		else if (f_min_wait != 3'b000)
			f_min_wait <= f_min_wait + 1'b1;

	// cover case where agant 0 req gets grants in 1 cycle
	// always @(posedge clk)
	// 	if (gnt[0])
	// 		c1: cover ($past(req[0]));

	// cover case where agent 0 req waits > 5 cycles
	always @(posedge clk)	
		if (gnt[0])
			if (f_min_wait >= 5)
				c2: cover ($past(req[0], 5) && !$past(gnt[0], 5));

	always @(posedge clk)
		if (req[0] && !gnt[0])
			if (f_min_wait >= 1)
				c3: cover (opcode == FORCE1);

`endif
endmodule
