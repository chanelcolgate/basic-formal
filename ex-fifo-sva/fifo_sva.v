module fifo(
	clk, rst,
	in_read_ctrl,		// read request
	in_write_ctrl,	// write request
	in_write_data,	// Data Bus in with 8-bit wide

	out_read_data,	// Data Bus out with 8-bit wide
	out_is_full,		// FIFO is full
	out_is_empty		// FIFO is empty
);

parameter ENTRIES = 4;

localparam [31:0] ENTRIES_LOG2 = $clog2(ENTRIES);

input clk;
input rst;
input in_read_ctrl;
input in_write_ctrl;
input [7:0] in_write_data;

output [7:0] out_read_data;
output out_is_full;
output out_is_empty;

reg [ENTRIES_LOG2-1:0] write_ptr;
reg [ENTRIES_LOG2-1:0] read_ptr;
reg [ENTRIES-1:0] [7:0] fifo_data;
wire [7:0] head;
reg [ENTRIES_LOG2:0] number_of_current_entries;

always @(posedge clk) begin
	if (rst) begin
		write_ptr <= 0;
	end else if (in_write_ctrl) begin
		write_ptr <= write_ptr + 1;
		fifo_data[write_ptr] <= in_write_data;
	end
end

always @(*) begin
	head = fifo_data[read_ptr];
end

always @(posedge clk) begin
	if (rst) begin
		read_ptr <= 0;
	end else if (in_read_ctrl) begin
		read_ptr <= read_ptr + 1;
		fifo_data[read_ptr] <= head;
	end
end

always @(posedge clk) begin
	if (rst) begin
		number_of_current_entries <= 0;
		out_is_empty <= 1;
		out_is_full <= 0;
	end else if (in_read_ctrl & ~in_write_ctrl) begin
		// number_of_current_entries <= number_of_current_entries - 1 && 3'b111;
		number_of_current_entries <= number_of_current_entries - 1;
		out_is_full <= 0;
		out_is_empty <= (number_of_current_entries == 1'b1);
	end else if (~in_read_ctrl & in_write_ctrl) begin
		number_of_current_entries <= number_of_current_entries + 1;
		out_is_empty <= 0;
		out_is_full <= (number_of_current_entries == (ENTRIES-1'b1));
	end
end

`ifdef FORMAL
	initial number_of_current_entries = 0;
	reg f_past_valid;
	initial f_past_valid = 0;
	always @(posedge clk)
		f_past_valid <= 1'b1;

	always @(*)
		if (!f_past_valid)
			assume(rst);

	// Assume: specifies property as assumption for the verification environment
	// fifo_assume_empty: assume property (@(posedge clk) out_is_empty |->
	// ~in_read_ctrl);
	// fifo_assume_full: assume property (@(posedge clk) out_is_full |->
	// ~in_write_ctrl);
	always @(posedge clk)
		if (f_past_valid && (!$past(rst)) && ($past(out_is_empty)))
			fifo_assume_empty: assume(!in_read_ctrl && !$past(in_read_ctrl));

	always @(posedge clk)
		if (f_past_valid && (!$past(rst)) && ($past(out_is_full)))
			fifo_assume_full: assume(!in_write_ctrl && !$past(in_write_ctrl));

	// Coverage: grant asserted
	// fifo_num_entries_6: cover property (number_of_current_entries == 6);
	// fifo_num_entries_5: cover property (number_of_current_entries == 5);
	// fifo_num_entries_4: cover property (number_of_current_entries == 4);
	// fifo_num_entries_3: cover property (number_of_current_entries == 3);
	// fifo_num_entries_2: cover property (number_of_current_entries == 2);
	// fifo_num_entries_1: cover property (number_of_current_entries == 1);
	// fifo_num_entries_0: cover property (number_of_current_entries == 0);
	always @(*) begin
	 	fifo_num_entries_0: cover(number_of_current_entries == 0);
		fifo_num_entries_1: cover(number_of_current_entries == 1);
		fifo_num_entries_2: cover(number_of_current_entries == 2);
		fifo_num_entries_3: cover(number_of_current_entries == 3);
		fifo_num_entries_4: cover(number_of_current_entries == 4);
		fifo_num_entries_5: cover(number_of_current_entries == 5);
		fifo_num_entries_6: cover(number_of_current_entries == 6);
	end

`endif
endmodule
