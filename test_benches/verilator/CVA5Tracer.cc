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

#include <iostream>
#include <termios.h>
#include "CVA5Tracer.h"

bool CVA5Tracer::check_if_instruction_retired(uint32_t instruction) {
    return check_if_instruction_retired(instruction, 0xFFFFFFFFU) != 0;
}

uint32_t CVA5Tracer::check_if_instruction_retired(uint32_t pattern, uint32_t mask) {
    for (int i =0; i < tb->NUM_RETIRE_PORTS; i++) {
        if (tb->retire_ports_valid[i]) {
            uint32_t insn = tb->retire_ports_instruction[i];
            if ((insn & mask) == pattern) {
                return insn;
            }
        }
    }
    return 0;
}

void CVA5Tracer::force_terminate() {
    terminated = true;
}

bool CVA5Tracer::has_terminated() {
    return terminated;
}


bool CVA5Tracer::has_stalled() {
	return stalling;
}

bool CVA5Tracer::store_queue_empty() {
    return tb->store_queue_empty;
}

void CVA5Tracer::reset_stats() {
    for (int i=0; i < numEvents; i++)
         event_counters[i] = 0;
}


void CVA5Tracer::update_stats() {
    if (collect_stats) {
        for (int i=0; i < numEvents; i++)
            event_counters[i] += tb->cva5_events[i];
    }
}


void CVA5Tracer::print_stats() {
	std::cout << "   CVA5 trace stats\n";
	std::cout << "--------------------------------------------------------------\n";
    for (int i=0; i < numEvents; i++)
       std::cout << "    " << eventNames[i] << ":" << event_counters[i] << std::endl;

    std::cout << "    user_application_ticks:" << ticks << std::endl;
	std::cout << "--------------------------------------------------------------\n\n";
}



void CVA5Tracer::reset() {
    terminated = false;
    terminating = false;
    stalling = false;
    stall_count = 0;
    userAppResponse = -100;
    this->lastContTickCount = ticks;
    this->lastContMeasurementTime = chrono::system_clock::now();

    tb->clk = 0;
    tb->rst = 1;
    for (int i=0; i <reset_length; i++){
        tick();
    }

    tb->rst = 0;
    reset_stats();
	this->reset_uart();
    std::cout << "DONE System reset \n" << std::flush;
}

void CVA5Tracer::set_log_file(std::ofstream* logFile) {
    this->logFile = logFile;
}
void CVA5Tracer::set_pc_file(std::ofstream* pcFile) {
    this->pcFile = pcFile;
    logPC = true;
}

void CVA5Tracer::set_uart_file(int uFile) {
	this->uartFile = uFile;
	this->hasUartFile = true;
}

void CVA5Tracer::reset_uart() {
	if (this->hasUartFile) {
		struct termios uartOptions;
		tcgetattr(this->uartFile, &uartOptions);

		// Baud rate (read/write)
		cfsetspeed(&uartOptions, 115200);

		// Timeout Settings
		uartOptions.c_cc[VMIN] = 1;
		uartOptions.c_cc[VTIME] = 0;

		// choosing Raw input
        uartOptions.c_iflag &= ~(IGNBRK | BRKINT | ICRNL | INLCR | PARMRK | INPCK | ISTRIP | IXON);

        // no line processing
        uartOptions.c_lflag &= ~(ECHO | ECHONL | ICANON | IEXTEN | ISIG);

		// choosing Raw output
		uartOptions.c_oflag &= ~OPOST;

		// Turn off character processing
	    uartOptions.c_cflag &= ~(CSIZE | PARENB);
	    uartOptions.c_cflag |= (CS8 | CLOCAL | CREAD);
		// enabling Software flow control
		//uartOptions.c_cflag |= (CLOCAL | CREAD); // enable receiver
		tcsetattr(this->uartFile, TCSAFLUSH, &uartOptions); // Flush input/output buffer and apply changes
	}
    tb->read_uart0 = 0;
	tb->uart0_read_byte = 0;
#ifdef HAS_2ND_UART
    tb->read_uart1 = 0;
	tb->uart1_read_byte = 0;
#endif
    uart0ReadPending = false;
    uart1ReadPending = false;
}

// If we have 2 UART ports, then use the 2nd one for bootloader / automated stuff, the primary one remains stdout
#ifdef HAS_2ND_UART
#define REDIRECTABLE_UART_WRITE_EN tb->write_uart1
#define REDIRECTABLE_UART_WRITE_DATA tb->uart1_write_byte
#define REDIRECTABLE_UART_READ_DATA tb->uart1_read_byte
#define REDIRECTABLE_UART_READ_VALID tb->read_uart1
#define REDIRECTABLE_UART_READ_ACK tb->read_uart1_ack
#define REDIRECTABLE_UART_READ_PENDING uart1ReadPending
#else
#define REDIRECTABLE_UART_WRITE_EN tb->write_uart0
#define REDIRECTABLE_UART_WRITE_DATA tb->uart0_write_byte
#define REDIRECTABLE_UART_READ_DATA tb->uart0_read_byte
#define REDIRECTABLE_UART_READ_VALID tb->read_uart0
#define REDIRECTABLE_UART_READ_ACK tb->read_uart0_ack
#define REDIRECTABLE_UART_READ_PENDING uart0ReadPending
#endif


void CVA5Tracer::update_UART() {
	if (tb->write_uart0) {
		std::cout <<  tb->uart0_write_byte << std::flush;
        if (logFile) {
		    *logFile << tb->uart0_write_byte;
        }
	}

    char c;
#ifdef NOPE
    if (read(fileno(stdin), &c, 1) == 1) {
        tb->read_uart0 = c;
        tb->uart0_read_byte = 1;
        uart0ReadPending = true;
    }

    if(uart0ReadPending && tb->read_uart0_ack) {
        uart0ReadPending = false;
        tb->read_uart0 = 0;
        tb->uart0_read_byte = 0;
    }
#endif

	if (this->hasUartFile) {
		// write handling (testbench to tty)
		if (REDIRECTABLE_UART_WRITE_EN) {
			int len = write(this->uartFile, &REDIRECTABLE_UART_WRITE_DATA, 1);
			(void) len;
		}

		// clean up old read if needed
		if(REDIRECTABLE_UART_READ_PENDING && REDIRECTABLE_UART_READ_ACK) {
			REDIRECTABLE_UART_READ_PENDING = false;
			REDIRECTABLE_UART_READ_VALID = 0;
            REDIRECTABLE_UART_READ_DATA = 0;
		}

		// read handling (check tty for next character, and send to testbench)
		if(!REDIRECTABLE_UART_READ_PENDING) {
			if(read(this->uartFile, &c, 1) == 1) {
				REDIRECTABLE_UART_READ_DATA = c;
				REDIRECTABLE_UART_READ_VALID = 1;
				REDIRECTABLE_UART_READ_PENDING = true;
			}
		}
	}
}


void CVA5Tracer::update_memory() {
    tb->instruction_bram_data_out = instruction_r;
    if (tb->instruction_bram_en)
        instruction_r = mem->read(tb->instruction_bram_addr);

    tb->data_bram_data_out = data_out_r;
    if (tb->data_bram_en) {
        data_out_r = mem->read(tb->data_bram_addr);
        mem->write(tb->data_bram_addr, tb->data_bram_data_in, tb->data_bram_be);
    }
}


void CVA5Tracer::tick() {
    cycle_count++;

    tb->clk = 1;
    tb->eval();

    #if VM_TRACE == 1
    if (verilatorWaveformTracer && trace_active) {
        verilatorWaveformTracer->dump(vluint32_t(cycle_count));
    }
    #endif
    cycle_count++;
    ticks++;

    tb->clk = 0;
    tb->eval();
    #if VM_TRACE == 1
    if (verilatorWaveformTracer && trace_active) {
        verilatorWaveformTracer->dump(vluint32_t(cycle_count));
    }
    #endif

    tb->clk = 1;
    tb->eval();
    axi_ddr->step();
    update_stats();
    update_UART();
    update_memory();


    checkForTerminationAndMagicNops();

    checkForStalls();


    if (logPC) {
        for (int i =0; i < tb->NUM_RETIRE_PORTS; i++) {
            if (tb->retire_ports_valid[i]) {
                *pcFile << std::hex << tb->retire_ports_pc[i] << std::endl;
            }
        }
    }

    if (continousPerfReporting) {
        handlePerfReporting();
    }

}

void CVA5Tracer::handlePerfReporting() {
    auto now = chrono::system_clock::now();

    auto msSince = static_cast<long>(chrono::duration_cast<chrono::milliseconds>(now - this->lastContMeasurementTime).count());
    if (msSince > 10000) {

        auto cyclesSince = ticks - lastContTickCount;

        float perf = (static_cast<float>(cyclesSince) / msSince) * 1000;

        cout << "#Sim Perf: " << perf << " cyc/s at tick " << ticks << endl;

        this->lastContMeasurementTime = now;
        this->lastContTickCount = ticks;
    }
}

void CVA5Tracer::set_stall_limit(int stallLimit) {
    if (stallLimit < 0) {
        std::cerr << "Invalid stallLimit " << stallLimit << ", sticking with previous " << stall_limit << std::endl;
        return;
    }
    this->stall_limit = stallLimit;
}

void CVA5Tracer::checkForStalls() {
    if (!tb->instruction_issued) {
        if (stall_count > stall_limit && stall_limit != 0) {
            stalling = true;
            stall_count = 0;
            std::cout << "\n\nError!!!!\n";
            std::cout << "Stall of " << stall_limit << " cycles detected at " << cycle_count << std::endl << std::endl;
		} else {
			stall_count++;
		}
	} else {
        stall_count = 0;
    }
}

void CVA5Tracer::set_terminate_on_user_exit(bool terminate) {
    terminateOnUserExit = terminate;
}


void CVA5Tracer::checkForTerminationAndMagicNops() {
    if (terminating && tb->store_queue_empty) { // await empty store queue, so that memory reflects arch-state
        terminated = true;
    }

    for (int i =0; i < tb->NUM_RETIRE_PORTS; i++) {
        if (tb->retire_ports_valid[i]) {
            uint32_t insn = tb->retire_ports_instruction[i];

            if (insn == INFINITE_LOOP_INSN) {

                terminating = true;
            } else if ((insn & MAGIC_NOP_MASK) == MAGIC_NOP_PATTERN) {
                uint32_t magicNumber = MAGIC_NOP_NUMBER(insn);

                if (magicNumber == MAGIC_TRACE_ENABLE) {
                    #if VM_TRACE == 1
                    if (verilatorWaveformTracer) {
                        std::cerr << "Starting "<< TRACE_FORMAT << " trace at " << cycle_count << std::endl;
                        trace_active = true;
                    }
                    #else
                    std::cerr << "Ignoring TRACE_ENABLE command, tracing was not configured" << std::endl;
                    #endif
                } else if (magicNumber == MAGIC_TRACE_DISABLE) {
                    #if VM_TRACE == 1
                    if (verilatorWaveformTracer) {
                        std::cerr << "Stopping " << TRACE_FORMAT << " trace at " << cycle_count << std::endl;
                        trace_active = false;
                    }
                    #else
                    std::cerr << "Ignoring TRACE_DISABLE command, tracing was not configured" << std::endl;
                    #endif
                } else if (magicNumber == MAGIC_TICKS_RESET) {
                    ticks = 0;
                } else if (magicNumber == MAGIC_STAT_COLLECTION_START) {
                    std::cerr << "Starting stat collection at " << cycle_count << std::endl;
                    reset_stats();
                    collect_stats = true;
                } else if (magicNumber == MAGIC_STAT_COLLECTION_RESUME) {
                    std::cerr << "Resuming stat collection at " << cycle_count << std::endl;
                    collect_stats = true;
                } else if (magicNumber == MAGIC_STAT_COLLECTION_END) {
                    std::cerr << "Stopping stat collection at " << cycle_count << std::endl;
                    collect_stats = false;
                } else if (magicNumber == MAGIC_USER_APP_START) {
                    userAppResponse = -10;
                } else if (magicNumber == MAGIC_USER_APP_EXIT_SUCCESS) {
                    userAppResponse = 0;
                    if (terminateOnUserExit) {
                        std::cerr << "\n\nUser App Exited\n\n";
                        terminating = true;
                    }
                } else if (magicNumber == MAGIC_USER_APP_EXIT_ERROR) {
                    std::cerr << "\n\nUser App Error!!!!\n\n";
                    userAppResponse = 0xF;
                    if (terminateOnUserExit) {
                        terminating = true;
                    }
                }
            }
        }
    }
}

int CVA5Tracer::get_user_app_response() {
    return userAppResponse;
}


void CVA5Tracer::start_tracer(const char *trace_file) {
	#if VM_TRACE == 1
    Verilated::traceEverOn(true);
    verilatorWaveformTracer = new VERILATOR_TRACER_T;
    tb->trace(verilatorWaveformTracer, 99);
    verilatorWaveformTracer->open(trace_file);
    trace_active = true;
	#else
    cout << "Trace support was not compiled, ignoring!" << endl;
    #endif
}



uint64_t CVA5Tracer::get_cycle_count() {
    return cycle_count;
}

uint64_t CVA5Tracer::get_ticks() {
    return ticks;
}

void CVA5Tracer::set_continousPerfReporting(bool reporting) {
    continousPerfReporting = reporting;
}

CVA5Tracer::CVA5Tracer(const char* const* const eventNames, const int numEvents, const int scratchMemSizeKB) : eventNames(eventNames), numEvents(numEvents) {
    tb = new Vcva5_sim;

    axi_ddr = new axi_ddr_sim(tb);

    mem = new SimMem(scratchMemSizeKB);

    instruction_r = 0; // illegal op, should actually not be relevant
    data_out_r = 0;

    event_counters = new uint64_t[numEvents];
}

void CVA5Tracer::loadMemoriesFromFile(ifstream& programFile) {
    axi_ddr = new axi_ddr_sim(programFile, DDR_START_ADDR, tb);
        
    programFile.clear();
    programFile.seekg(0, ios::beg);
    mem = new SimMem(programFile, 128);
}

void CVA5Tracer::loadMemoriesFromFiles(ifstream& scratchFile, ifstream& ramFile) {
    axi_ddr = new axi_ddr_sim(ramFile, DDR_START_ADDR, tb);

	scratchFile.clear();
	scratchFile.seekg(0, ios::beg);
	mem = new SimMem(scratchFile, 128);
}

CVA5Tracer::CVA5Tracer(std::ifstream& programFile) : CVA5Tracer() {
    loadMemoriesFromFile(programFile);
}


CVA5Tracer::CVA5Tracer(std::ifstream& scratchFile, std::ifstream& ramFile) : CVA5Tracer() {
	loadMemoriesFromFiles(scratchFile, ramFile);
}

CVA5Tracer::~CVA5Tracer() {
	#if VM_TRACE == 1
    if (verilatorWaveformTracer) {
		verilatorWaveformTracer->flush();
		verilatorWaveformTracer->close();
        delete verilatorWaveformTracer;
        verilatorWaveformTracer = nullptr;
    }
	#endif
    
    delete[] event_counters;
	delete mem;
	delete tb;
}
