/*
 * Copyright © 2019 Eric Matthews,  Lesley Shannon
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * Initial code developed under the supervision of Dr. Lesley Shannon,
 * Reconfigurable Computing Lab, Simon Fraser University.
 *
 * Author(s):
 *             Eric Matthews <ematthew@sfu.ca>
 */

#ifndef CVA5Tracer_H
#define CVA5Tracer_H
#include <cstdlib>
#include <iostream>
#include <iterator>
#include <termios.h>
#include "verilated.h"
#include "verilated_vcd_c.h"
#include "Vcva5_sim.h"
#include "SimMem.h"
#include "AXI_DDR_simulation/axi_ddr_sim.h"

// ADDI NOPS: 
// addi zero, zero, [X] mask & pattern to find all magic nops
#define MAGIC_NOP_PATTERN 0x00000013U
#define MAGIC_NOP_MASK    0x000FFFFFU
#define MAGIC_NOP_NUMBER(x) ((x >> 20) & 0xFFF)

// addi zero, zero, 0x10
#define MAGIC_TRACE_ENABLE 0x10
// addi zero, zero, 0x11
#define MAGIC_TRACE_DISABLE 0x11
// addi zero, zero, 0x12
#define MAGIC_TICKS_RESET 0x12

// addi zero, zero, 0xC
#define MAGIC_STAT_COLLECTION_START 0xC
// addi zero, zero, 0xD
#define MAGIC_STAT_COLLECTION_END 0xD
// addi zero, zero, 0xE
#define MAGIC_STAT_COLLECTION_RESUME 0xE

// addi zero, zero, 0x1
#define MAGIC_USER_APP_START 0x1
// addi zero, zero, 0xF
#define MAGIC_USER_APP_EXIT_ERROR 0xF
// addi zero, zero, 0xA
#define MAGIC_USER_APP_EXIT_SUCCESS 0xA

#define INFINITE_LOOP_INSN 0x0000006FU

#define COMPLIANCE_SIG_PHASE_NOP 0x00B00013U

template <typename T, int N>
constexpr int arraySize(T(&)[N]) { return N; }

static const char * const eventNames[] = {
    "early_branch_correction",
    "operand_stall",
    "unit_stall",
    "no_id_stall",
    "no_instruction_stall",
    "other_stall",
    "instruction_issued_dec",
    "branch_operand_stall",
    "alu_operand_stall",
    "ls_operand_stall",
    "div_operand_stall",
    "alu_op",
    "branch_or_jump_op",
    "load_op",
    "store_op",
    "mul_op",
    "div_op",
    "misc_op",
    "branch_correct",
    "branch_misspredict",
    "return_correct",
    "return_misspredict",
    "load_conflict_delay",
    "rs1_forwarding_needed",
    "rs2_forwarding_needed",
    "rs1_and_rs2_forwarding_needed",
    "instr_inv_stall"
};
static const int numEvents = arraySize(eventNames);

//Testbench with CVA5 trace outputs on toplevel
class CVA5Tracer {
public:
  CVA5Tracer();
  CVA5Tracer(std::ifstream& programFile);
  CVA5Tracer(std::ifstream& scratchFile, std::ifstream& ramFile);
  ~CVA5Tracer();

  bool check_if_instruction_retired(uint32_t instruction);
  /**
   * Uses the fact, that all-0 is invalid instruction in RV. So 0 means no match, otherwise the first match is returned!
   * 
   */
  uint32_t check_if_instruction_retired(uint32_t pattern, uint32_t mask);
  bool has_terminated();
  bool has_stalled();
  bool store_queue_empty();
  void print_stats();
  void reset_stats();
  void reset();
  void tick();

  void set_log_file(std::ofstream* logFile);
  void set_pc_file(std::ofstream* pcFile);
  void start_tracer(const char *trace_file);

  void set_terminate_on_user_exit(bool terminate);

  uint64_t get_cycle_count();
  uint64_t get_ticks();

  int get_user_app_response();

  void set_uart_file(int uartFile);
  void reset_uart();

  //DDR Simulation
  Vcva5_sim *tb;
  axi_ddr_sim * axi_ddr;
  SimMem *mem;
private:
#if VM_TRACE == 1
		VerilatedVcdC	*verilatorWaveformTracer;
#endif
  std::ofstream* logFile;
  std::ofstream* pcFile;
  bool logPC = false;

  int uartFile;
  bool hasUartFile = false;
  bool uartReadPending = false;
  int reset_length = 64;
  int stall_limit = 2000;
  int stall_count = 0;
  /**
   * counts time-intervals of simulation. Needed for VCD. Needs to be strictly monotone.
   */
  uint64_t cycle_count = 0;
  /**
   * counts actual clock-cycles for the application. Can be reset be Hint-NOP
   */
  uint64_t ticks = 0;
  uint64_t event_counters[numEvents];

  bool terminated = false;
  bool terminating = false;
  bool stalling = false;
  bool collect_stats = false;
  bool trace_active = true;
  /**
   * basically a C exit code.
   * -100 indicates no state received from simulator
   * -10 indicates: received user_app begin
   * 0 indicates: received user_app exit+success
   * 0xF indicates: received user_app exit+error
   */
  int userAppResponse = -100;

  bool terminateOnUserExit = false;

  void update_stats();
  void update_UART();
  void update_memory();

  void checkForStalls();
  void checkForTerminationAndMagicNops();

  uint32_t instruction_r;
  uint32_t data_out_r;

};
#endif
