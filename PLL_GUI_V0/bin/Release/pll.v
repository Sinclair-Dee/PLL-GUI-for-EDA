//#PLL
//#N_m=4
//#M_m=56
//#locked_window_size=0
//#locked_counter=0
//#IRRAD_mode=YES
//#clk0_ali=2
//#clk1_ali=2
//#clk2_ali=2
//#clk3_ali=2
//#clk4_ali=2
`timescale 1 ps / 1 ps
module pll(
	inclk0,
	c0,
	c1,
	c2,
	c3,
	c4,
	e0);

	input	inclk0;
	output	c0;
	output	c1;
	output	c2;
	output	c3;
	output	c4;
	output	e0;
	wire[5:0] wireC;
	wire[3:0] wireE;
	assign c0 = wireC[0];
	assign c1 = wireC[1];
	assign c2 = wireC[2];
	assign c3 = wireC[3];
	assign c4 = wireC[4];
	assign e0 = wireE[0];
	altpll	altpll_component (
				.inclk ({1'h0, inclk0}),
				.pllena (1'b1),
				.pfdena (1'b1),
				.areset (1'b0),
				.clk (wireC),
				.locked (),
				.extclk (wireE),
				.activeclock (),
				.clkbad (),
				.clkena ({6{1'b1}}),
				.clkloss (),
				.clkswitch (1'b0),
				.configupdate (1'b1),
				.enable0 (),
				.enable1 (),
				.extclkena ({4{1'b1}}),
				.fbin (1'b1),
				.fbout (),
				.phasecounterselect ({4{1'b1}}),
				.phasedone (),
				.phasestep (1'b1),
				.phaseupdown (1'b1),
				.scanaclr (1'b0),
				.scanclk (1'b0),
				.scanclkena (1'b1),
				.scandata (1'b0),
				.scandataout (),
				.scandone (),
				.scanread (1'b0),
				.scanwrite (1'b0),
				.sclkout0 (),
				.sclkout1 (),
				.vcooverrange (),
				.vcounderrange ());
	defparam
		altpll_component.clk0_divide_by = 56,
		altpll_component.clk0_duty_cycle = 50,
		altpll_component.clk0_multiply_by = 56,
		altpll_component.clk0_phase_shift = "0",
		altpll_component.clk1_divide_by = 56,
		altpll_component.clk1_duty_cycle = 50,
		altpll_component.clk1_multiply_by = 56,
		altpll_component.clk1_phase_shift = "0",
		altpll_component.clk2_divide_by = 56,
		altpll_component.clk2_duty_cycle = 50,
		altpll_component.clk2_multiply_by = 56,
		altpll_component.clk2_phase_shift = "0",
		altpll_component.compensate_clock = "CLK3",
		altpll_component.clk3_divide_by = 56,
		altpll_component.clk3_duty_cycle = 50,
		altpll_component.clk3_multiply_by = 56,
		altpll_component.clk3_phase_shift = "0",
		altpll_component.clk4_divide_by = 56,
		altpll_component.clk4_duty_cycle = 50,
		altpll_component.clk4_multiply_by = 56,
		altpll_component.clk4_phase_shift = "0",
		altpll_component.extclk0_divide_by = 56,
		altpll_component.extclk0_duty_cycle = 50,
		altpll_component.extclk0_multiply_by = 56,
		altpll_component.extclk0_phase_shift = "0",
		altpll_component.clk5_divide_by = 224,
		altpll_component.clk5_duty_cycle = 50,
		altpll_component.clk5_multiply_by = 56,
		altpll_component.clk5_phase_shift = "0",
		altpll_component.inclk0_input_frequency = 20000,
		altpll_component.operation_mode = "NORMAL",
		altpll_component.port_pllena = "PORT_UNUSED",
		altpll_component.port_pfdena = "PORT_UNUSED",
		altpll_component.port_areset = "PORT_UNUSED",
		altpll_component.port_locked = "PORT_UNUSED",
		altpll_component.port_clk0 = "PORT_USED",
		altpll_component.port_clk1 = "PORT_USED",
		altpll_component.port_clk2 = "PORT_USED",
		altpll_component.port_clk3 = "PORT_USED",
		altpll_component.port_clk4 = "PORT_USED",
		altpll_component.port_clk5 = "PORT_USED",
		altpll_component.port_extclk0 = "PORT_USED",
		altpll_component.intended_device_family = "Stratix",
		altpll_component.lpm_type = "altpll",
		altpll_component.pll_type = "Enhanced",
		altpll_component.port_activeclock = "PORT_UNUSED",
		altpll_component.port_clkbad0 = "PORT_UNUSED",
		altpll_component.port_clkbad1 = "PORT_UNUSED",
		altpll_component.port_clkloss = "PORT_UNUSED",
		altpll_component.port_clkswitch = "PORT_UNUSED",
		altpll_component.port_fbin = "PORT_UNUSED",
		altpll_component.port_inclk0 = "PORT_USED",
		altpll_component.port_inclk1 = "PORT_UNUSED",
		altpll_component.port_phasecounterselect = "PORT_UNUSED",
		altpll_component.port_phasedone = "PORT_UNUSED",
		altpll_component.port_phasestep = "PORT_UNUSED",
		altpll_component.port_phaseupdown = "PORT_UNUSED",
		altpll_component.port_scanaclr = "PORT_UNUSED",
		altpll_component.port_scanclk = "PORT_UNUSED",
		altpll_component.port_scanclkena = "PORT_UNUSED",
		altpll_component.port_scandata = "PORT_UNUSED",
		altpll_component.port_scandataout = "PORT_UNUSED",
		altpll_component.port_scandone = "PORT_UNUSED",
		altpll_component.port_scanread = "PORT_UNUSED",
		altpll_component.port_scanwrite = "PORT_UNUSED",
		altpll_component.port_clkena0 = "PORT_UNUSED",
		altpll_component.port_clkena1 = "PORT_UNUSED",
		altpll_component.port_clkena2 = "PORT_UNUSED",
		altpll_component.port_clkena3 = "PORT_UNUSED",
		altpll_component.port_clkena4 = "PORT_UNUSED",
		altpll_component.port_clkena5 = "PORT_UNUSED",
		altpll_component.port_extclk1 = "PORT_UNUSED",
		altpll_component.port_extclk2 = "PORT_UNUSED",
		altpll_component.port_extclk3 = "PORT_UNUSED",
		altpll_component.valid_lock_multiplier = 1;
endmodule
