#include <cstdlib>
#include <iostream>
#include <fstream>
#include <fcntl.h>
#include <getopt.h>
#include "verilated.h"
#include "verilated_vcd_c.h"
#include "Vcva5_sim.h"
#include "CVA5Tracer.h"
#include "MemoryFragmentLoader.h"

CVA5Tracer *cva5Tracer;

//For time index on assertions
double sc_time_stamp() {
	return cva5Tracer->get_cycle_count();
}

int openPort(char *port) {
	int fd = open(port, O_RDWR | O_NOCTTY | O_NDELAY | O_NONBLOCK);
	return fd;
}

typedef enum {
	None,
	Combined,
	Seperate,
	MemIdx
} firmwareLoadingMode_t;

struct cmdline_options {
	char *logFile;
	char *signatureFile;
	char *ramInitFile;
	char *scratchInitFile;
	char *memIdxFile;
	char *traceFile;
	char *uartFile;
	char *pcFile;
	firmwareLoadingMode_t hwInitMode;
};

void PrintHelp () {
	std::cout <<
		"parameters with '*' are mandatory!\n"
		"--log          set a logfile\n"
		"--sig          set a signature logfile for Signature Printing phase\n"
		"--trace        set a file for trace output\n"
		"               * The firmware can be set in two ways: either together for Scratch- and RAM-Section together, or via seperate files\n"
		"--hwInit       set firmware in Scratch- and RAM-Section\n"
		"--ramInit      set firmware for RAM-Section only\n"
		"--scratchInit  set firmware for Scratch-Section only\n"
		"--memIdx		use memoryIdx file format, which can initialize all of memory"
		"\n"
		"--uart         set a UART device for the serial console to connect to\n"
		"--help         print this help and exit\n";
}

void ExitWithArgumentError(const char *text) {
	cout << text << "\n";
	PrintHelp();
	exit(EXIT_FAILURE);
}

void HandleArguments(int argc, char **argv, struct cmdline_options *opts) {
	const option long_opt[] = {
			{"log", required_argument, nullptr, 'l'},
			{"sig", required_argument, nullptr, 's'},
			{"hwInit", required_argument, nullptr, 'f'},
			{"trace", required_argument, nullptr, 't'},
			{"uart", required_argument, nullptr, 'u'},
			{"ramInit", required_argument, nullptr, 'r'},
			{"scratchInit", required_argument, nullptr, 'i'},
			{"pcFile", required_argument, nullptr, 'p'},
			{"memIdx", required_argument, nullptr, 'm'},
			{nullptr, no_argument, nullptr, 0}
	};
	firmwareLoadingMode_t loadingMode = None;

	// force nullpointers to for later testing
	opts->logFile = nullptr;
	opts->signatureFile = nullptr;
	opts->ramInitFile = nullptr;
	opts->scratchInitFile = nullptr;
	opts->memIdxFile = nullptr;
	opts->traceFile = nullptr;
	opts->uartFile = nullptr;
	opts->pcFile = nullptr;


	while(true) {
		int opt = getopt_long(argc, argv, "l:s:f:t:u:r:i:p:m", long_opt, nullptr);

		if (opt == -1) {
			break;
		}

		switch(opt) {
			case 'l':
				opts->logFile = optarg;
				break;

			case 's':
				opts->signatureFile = optarg;
				break;

			case 'f':
				if (loadingMode == None || loadingMode == Combined) {
					opts->ramInitFile = optarg;
					opts->scratchInitFile = optarg;
					loadingMode = Combined;
				} else {
					ExitWithArgumentError("use either hwInit for the firmware or ramInit and scratchInit!");
				}
				break;

			case 't':
				opts->traceFile = optarg;
				break;

			case 'u':
				opts->uartFile = optarg;
				break;

			case 'r':
				if (loadingMode == None || loadingMode == Seperate) {
					opts->ramInitFile = optarg;
					loadingMode = Seperate;
				} else {
					ExitWithArgumentError("use either hwInit for the firmware or ramInit and scratchInit!");
				}
				break;

			case 'i':
				if (loadingMode == None || loadingMode == Seperate) {
					opts->scratchInitFile = optarg;
					loadingMode = Seperate;
				} else {
					ExitWithArgumentError("use either hwInit for the firmware or ramInit and scratchInit!");
				}
				break;
			case 'p':
				opts->pcFile = optarg;
				break;
			case 'm':
				if (loadingMode == None) {
					opts->memIdxFile = optarg;
					loadingMode = MemIdx;
				} else {
					ExitWithArgumentError("use either the old --[xx]init options or memIdx");
				}
				break;
			default:
				cout << "unknown argument: " << opt << " ... stop!\n";
				PrintHelp();
				exit(EXIT_FAILURE);
		}
	}
	// make sure that both init files are set!
	if (loadingMode == None) {
		ExitWithArgumentError("use either memIdx, hwInit or ramInit & scratchInit to initialize memories!");
	}

	// set mode to struct
	opts->hwInitMode = loadingMode;
}


using namespace std;

int main(int argc, char **argv) {
	ofstream logFile, sigFile, pcFile;
	ifstream scratchFile, ramFile;
	int uartFile = 0;
	struct cmdline_options opts;

	// Initialize Verilators variables
	Verilated::commandArgs(argc, argv);
	HandleArguments(argc, argv, &opts);


	scratchFile.open(opts.scratchInitFile);
	ramFile.open(opts.ramInitFile);
	
	if (opts.hwInitMode == Combined) {
		cout << "Same firmware file is used for both memories: " << opts.scratchInitFile << endl;
		if (!scratchFile.is_open()) {
			cout << "Failed to open hwinit File: " << opts.scratchInitFile << endl;
			exit(EXIT_FAILURE);
		}
	} else if (opts.hwInitMode == Seperate) {
		cout << "Seperate firmware files are used for the memories! Scratch:" << opts.scratchInitFile << " and RAM:" << opts.ramInitFile << endl;
		if (!scratchFile.is_open()) {
			cout << "Failed to open Scratch File: " << opts.scratchInitFile << endl;
			exit(EXIT_FAILURE);
		}
		if (!ramFile.is_open()) {
			cout << "Failed to open RAM File: " << opts.ramInitFile << endl;
			exit(EXIT_FAILURE);
		}
	}

	// Create an instance of our module under test
	if (opts.hwInitMode == Combined) {
    	cva5Tracer = new CVA5Tracer(scratchFile);
	} else if (opts.hwInitMode == Seperate) {
		cva5Tracer = new CVA5Tracer(scratchFile,ramFile);
	} else if (opts.hwInitMode == MemIdx) {
		cva5Tracer = new CVA5Tracer();
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
	while(!(cva5Tracer->has_stalled() || cva5Tracer->has_terminated())) {
	    cva5Tracer->tick();
        //Compliance Tests Signature Printing Phase
        sig_phase_complete |= cva5Tracer->check_if_instruction_retired(COMPLIANCE_SIG_PHASE_NOP);
        if (sig_phase_complete && cva5Tracer->store_queue_empty()) {
            std::cout << "\n--------------------------------------------------------------\n";
            std::cout << "                   Signature\n";
            std::cout << "--------------------------------------------------------------\n";
            cva5Tracer->set_log_file(&sigFile);
        }
	}

	cout << "\n--------------------------------------------------------------\n";
	cout << "   Simulation Completed  " << cva5Tracer->get_cycle_count() << " cycles.\n";
    cva5Tracer->print_stats();

	if (opts.logFile) {
		logFile.close();
	}
	if (opts.signatureFile) {
		sigFile.close();
	}
    scratchFile.close();
    pcFile.close();

	delete cva5Tracer;

	exit(EXIT_SUCCESS);
}
