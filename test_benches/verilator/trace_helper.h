

#pragma once

#if TRACE_WITH_FST

#define TRACE_FORMAT "fst"

#include <verilated_fst_c.h>

#define VERILATOR_TRACER_T VerilatedFstC

#else

#define TRACE_FORMAT "vcd"

#include <verilated_vcd_c.h>

#define VERILATOR_TRACER_T VerilatedVcdC

#endif