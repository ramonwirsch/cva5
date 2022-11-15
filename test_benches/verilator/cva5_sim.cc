#include <cstdlib>
#include <iostream>
#include <fstream>
#include <fcntl.h>
#include <getopt.h>
#include "verilated.h"
#include "verilated_vcd_c.h"
#include "Vcva5_sim.h"
#include "CVA5Tracer.h"
#include "cmdArgs.h"
#include "buildCva5Tracer.h"
#include "MemoryFragmentLoader.h"

using namespace std;

CVA5Tracer *cva5Tracer;

//For time index on assertions
double sc_time_stamp() {
	return cva5Tracer->get_cycle_count();
}

int openPort(char *port) {
	int fd = open(port, O_RDWR | O_NOCTTY | O_NDELAY | O_NONBLOCK);
	return fd;
}

int main(int argc, char **argv) {
	ofstream logFile, sigFile, pcFile;
	int uartFile = 0;
	struct cmdline_options opts;

	// Initialize Verilators variables
	Verilated::commandArgs(argc, argv);
	handleArguments(argc, argv, &opts);
	
	if (opts.hwInitMode == Combined) {
		
	} else if (opts.hwInitMode == Seperate) {
		
	}

	cva5Tracer = buildCva5Tracer(&opts);

	if (opts.hwInitMode == Combined) {
		ifstream hwFile;
		hwFile.open(opts.scratchInitFile);

		cout << "Same firmware file is used for both memories: " << opts.scratchInitFile << endl;
		if (!hwFile.is_open()) {
			cout << "Failed to open hwinit File: " << opts.scratchInitFile << endl;
			exit(EXIT_FAILURE);
		}

    	cva5Tracer->loadMemoriesFromFile(hwFile);

		hwFile.close();
	} else if (opts.hwInitMode == Seperate) {
		ifstream scratchFile, ramFile;
		scratchFile.open(opts.scratchInitFile);
		ramFile.open(opts.ramInitFile);

		cout << "Seperate firmware files are used for the memories! Scratch:" << opts.scratchInitFile << " and RAM:" << opts.ramInitFile << endl;
		if (!scratchFile.is_open()) {
			cout << "Failed to open Scratch File: " << opts.scratchInitFile << endl;
			exit(EXIT_FAILURE);
		}
		if (!ramFile.is_open()) {
			cout << "Failed to open RAM File: " << opts.ramInitFile << endl;
			exit(EXIT_FAILURE);
		}

		cva5Tracer->loadMemoriesFromFiles(scratchFile, ramFile);

		scratchFile.close();
		ramFile.close();
	} else if (opts.hwInitMode == MemIdx) {
		cout << "Loading MemoryIdx: " << opts.memIdxFile << endl;
		MemoryFragmentLoader* loader = new MemoryFragmentLoader(cva5Tracer->mem, LMEM_START_ADDR, cva5Tracer->axi_ddr, DDR_START_ADDR, DDR_START_ADDR + DDR_SIZE);
		loader->load(opts.memIdxFile);
		delete loader;
	}

	if (opts.logFile) {
		logFile.open(opts.logFile);
		if (!logFile.is_open()) {
    		cout << "Failed to open logfile: " << opts.logFile << endl;
    		exit(EXIT_FAILURE);
    	} else {
			cva5Tracer->set_log_file(&logFile);
		}
	}
	if (opts.signatureFile) {
		sigFile.open(opts.signatureFile);
		if (!sigFile.is_open()) {
    		cout << "Failed to open sigFile: " << opts.signatureFile << endl;
    		exit(EXIT_FAILURE);
    	}
	}

    if (opts.pcFile) {
        pcFile.open(opts.pcFile);

		if (pcFile.is_open()) {
        	cva5Tracer->set_pc_file(&pcFile);
    	} else {
			cout << "Failed to open pcFile: " << opts.pcFile << endl;
			exit(EXIT_FAILURE);
		}
    }

    if (opts.uartFile) {
		cout << "Found parameter for Uart-File, will try to open the serial interface for UART: " << opts.uartFile << ".\n";
		uartFile = openPort(opts.uartFile);
		if (uartFile > 0) {
			cva5Tracer->set_uart_file(uartFile);
		} else {
			cout << "Failed to open Uart File: " << opts.uartFile << endl;
			exit(EXIT_FAILURE);
		}
	}

	if (opts.traceFile) {
		cva5Tracer->start_tracer(opts.traceFile);
	}

	if (opts.terminateOnUserExit) {
		cva5Tracer->set_terminate_on_user_exit(true);
		cout << "Will terminate simulation on first User App Exit!" << endl;
	}

	if (opts.stallLimit >= 0) { // leave default value for negative values or when not set
		cva5Tracer->set_stall_limit(opts.stallLimit);
	}

	cva5Tracer->reset();
	cout << "--------------------------------------------------------------\n";
	cout << "   Starting Simulation";
	if (opts.logFile && logFile.is_open()) {
		cout << ", logging to " << opts.logFile;
	}
	cout << "\n";
	cout << "--------------------------------------------------------------\n";
	cout << flush;

	// Tick the clock until we are done
    bool sig_phase_complete = false;
	do {
	    cva5Tracer->tick();
        //Compliance Tests Signature Printing Phase
        sig_phase_complete |= cva5Tracer->check_if_instruction_retired(COMPLIANCE_SIG_PHASE_NOP);
        if (sig_phase_complete && cva5Tracer->store_queue_empty()) {
            std::cout << "\n--------------------------------------------------------------\n";
            std::cout << "                   Signature\n";
            std::cout << "--------------------------------------------------------------\n";
            cva5Tracer->set_log_file(&sigFile);
        }
	} while (!(cva5Tracer->has_stalled() || cva5Tracer->has_terminated()));

	cout << "\n--------------------------------------------------------------\n";
	cout << "   Simulation Completed  " << cva5Tracer->get_cycle_count() << " cycles.\n";
    cva5Tracer->print_stats();

	int exitCode = cva5Tracer->get_user_app_response();

	switch (exitCode) {
		case 0: break;
		case -10: 
			cout << "User App started but never finished!" << endl;
			break;
		case 0xF: 
			cout << "User App finished with error!" << endl;
			break;
		case -100:
			cout << "No User App ran!" << endl;
			break;
		default:
			cout << "User App Exit Code: " << exitCode << endl;
	}

	if (opts.logFile) {
		logFile.close();
	}
	if (opts.signatureFile) {
		sigFile.close();
	}
    pcFile.close();

	delete cva5Tracer;

	exit(exitCode);
}
