###############################################################
VERILATOR_DIR=$(CVA5_DIR)/test_benches/verilator

# Sources for verilator
CVA5_HW_SRCS = $(addprefix $(CVA5_DIR)/, $(shell cat $(CVA5_DIR)/tools/compile_order))
CVA5_SIM_SRCS = $(addprefix $(VERILATOR_DIR)/, CVA5Tracer.cc SimMem.cc cva5_sim.cc AXI_DDR_simulation/axi_ddr_sim.cc AXI_DDR_simulation/ddr_page.cc BaseMemoryFragmentLoader.cpp MemoryFragmentLoader.cpp)
CVA5_INCLUDED_SIM_SRCS = $(addprefix $(VERILATOR_DIR)/, cva5_sim.cc AXI_DDR_simulation/ddr_page.cc SimMem.cc)


#Tracing: Set to True or False
TRACE_ENABLE?=False

#Used for DDR-Sim to read init-file to correct offset (since the file itself does not include this address)
DDR_START_ADDR ?= 0x40000000

#Simulation Binary Name
CVA5_SIM_DIR?=$(VERILATOR_DIR)/build
CVA5_SIM?=$(CVA5_SIM_DIR)/cva5-sim

#AXI DDR Parameters
DDR_SIZE_GB = 1
PAGE_SIZE_KB = 2
MAX_READ_REQ = 8
MAX_WRITE_REQ = $(MAX_READ_REQ)
MIN_RD_DELAY = 1
MAX_RD_DELAY = 1
MIN_WR_DELAY = 1
MAX_WR_DELAY = 1
DELAY_SEED = 867583
LMEM_START_ADDR = 0x80000000
######################################################################
ddr_size_def = DDR_SIZE=\(long\)$(DDR_SIZE_GB)*\(long\)1073741824
page_size_def = PAGE_SIZE=\($(PAGE_SIZE_KB)*1024\)
max_inflight_read_requests = MAX_INFLIGHT_RD_REQ=$(MAX_READ_REQ)
max_inflight_write_requests = MAX_INFLIGHT_WR_REQ=$(MAX_WRITE_REQ)
mix_delay_read = MIN_DELAY_RD=$(MIN_RD_DELAY)
max_delay_read = MAX_DELAY_RD=$(MAX_RD_DELAY)
min_delay_write = MIN_DELAY_WR=$(MIN_WR_DELAY)
max_delay_write = MAX_DELAY_WR=$(MAX_WR_DELAY)
delay_seed = DELAY_SEED=$(DELAY_SEED)

ddr_start_addr = DDR_START_ADDR=$(DDR_START_ADDR)

CFLAGS = -g0 -O3 -std=c++14 -march=native -D$(ddr_size_def) -D$(page_size_def) -D$(max_inflight_read_requests) -D$(max_inflight_write_requests)\
	-D$(mix_delay_read) -D$(max_delay_read) -D$(min_delay_write) -D$(max_delay_write) -D$(delay_seed) -D$(ddr_start_addr) -DLMEM_START_ADDR=$(LMEM_START_ADDR) -I$(VERILATOR_DIR)/AXI_DDR_simulation

#Verilator
################################################################################
VERILATOR_LINT_IGNORE= -Wno-LITENDIAN -Wno-SYMRSVDWORD

# C++ Code can detect Verilator-intrinsic VM_TRACE == 1, set by --trace option, instead of an additional one that depends on --trace (because of needed data types only existing then)
ifeq ($(TRACE_ENABLE), True)
	VERILATOR_CFLAGS =  --trace --trace-structs --CFLAGS "$(CFLAGS)"
else
	VERILATOR_CFLAGS =   --CFLAGS  "$(CFLAGS)"
endif

VERILATOR_LINT_IGNORE= -Wno-LITENDIAN -Wno-SYMRSVDWORD

#(to-do)
#ifeq ($(LOAD_DDR_FROM_FILE), True)
#	VERILATOR_CFLAGS :=  $(VERILATOR_CFLAGS) -D LOAD_DDR_FROM_FILE"
#endif

##################################################################################

#cva5_sim included as linter requires top-level to have no interfaces
.PHONY: lint
lint: 
	verilator -cc $(CVA5_HW_SRCS) \
	$(VERILATOR_DIR)/cva5_sim.sv \
	--top-module cva5_sim \
	--lint-only

.PHONY: lint-full
lint-full:
	verilator -cc $(CVA5_HW_SRCS) \
	$(VERILATOR_DIR)/cva5_sim.sv \
	--top-module cva5_sim \
	--lint-only -Wall

#Build CVA5 Sim
$(CVA5_SIM): $(CVA5_HW_SRCS) $(CVA5_SIM_SRCS)
	mkdir -p $(CVA5_SIM_DIR)
	verilator --cc --exe --Mdir $(CVA5_SIM_DIR) -DENABLE_SIMULATION_ASSERTIONS --assert \
		-o cva5-sim \
		--build -j 8 \
		$(VERILATOR_LINT_IGNORE) $(VERILATOR_CFLAGS) \
		$(CVA5_SIM_SRCS) \
		$(CVA5_HW_SRCS) $(VERILATOR_DIR)/cva5_sim.sv --top-module cva5_sim

.PHONY: cva5-sim
cva5-sim: $(CVA5_SIM)

.PHONY: clean-cva5-sim
clean-cva5-sim:
	rm -rf $(CVA5_SIM_DIR)

