
#include "cmdArgs.h"

#include <iostream>
#include <sstream>
#include <getopt.h>
#include "trace_helper.h"

using namespace std;



void printHelp () {
	std::cout <<
		"parameters with '*' are mandatory!\n"
		"--log          set a logfile\n"
		"--sig          set a signature logfile for Signature Printing phase\n"
        "--pcFile       output PC / excecuted instructions to a log file\n"
		"--trace        set a file for trace output ("
		TRACE_FORMAT
		"-format)\n"
		"               * The firmware can be set in two ways: either together for Scratch- and RAM-Section together, or via seperate files\n"
		"--hwInit       set firmware in Scratch- and RAM-Section\n"
		"--ramInit      set firmware for RAM-Section only\n"
		"--scratchInit  set firmware for Scratch-Section only\n"
		"--memIdx		use memoryIdx file format, which can initialize all of memory"
		"\n"
		"--uart         set a UART device for the serial console to connect to\n"
		"--terminateOnUserExit      stops similuation as soon as one of the USER_APP_EXIT MAGIC NOPS is executed. Otherwise simulation will run until crash or infinite loop\n"
		"--stallLimit	set the amount of ticks without CVA5 issuing any instruction that is considered a stall. 0 disables this completely\n"
		"--help         print this help and exit\n";
}

void exitWithArgumentError(const char *text) {
	cout << text << "\n";
	printHelp();
	exit(EXIT_FAILURE);
}

void handleArguments(int argc, char **argv, struct cmdline_options *opts) {
	const option long_opt[] = { // if option is present, return 'char' from getopt_long
			{"log", required_argument, nullptr, 'l'},
			{"sig", required_argument, nullptr, 's'},
			{"hwInit", required_argument, nullptr, 'f'},
			{"trace", required_argument, nullptr, 't'},
			{"uart", required_argument, nullptr, 'u'},
			{"ramInit", required_argument, nullptr, 'r'},
			{"scratchInit", required_argument, nullptr, 'i'},
			{"pcFile", required_argument, nullptr, 'p'},
			{"memIdx", required_argument, nullptr, 'm'},
			{"terminateOnUserExit", no_argument, &opts->terminateOnUserExit, 1}, // overwrite pointer with 1 if option is given
			{"stallLimit", required_argument, nullptr, 'S'},
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
	opts->terminateOnUserExit = 0;
	opts->stallLimit = -1;


	while(true) {
		int opt = getopt_long(argc, argv, "l:t:u:m:", long_opt, nullptr); // string is [short-option-char][:], where : indicates that the short option requires an argument. Chars should match above chars to use the same code

		if (opt == -1) {
			break;
		}

		switch(opt) {
			case 0: // flag option, nothing to do here
				break;
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
					exitWithArgumentError("use either hwInit for the firmware or ramInit and scratchInit!");
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
					exitWithArgumentError("use either hwInit for the firmware or ramInit and scratchInit!");
				}
				break;

			case 'i':
				if (loadingMode == None || loadingMode == Seperate) {
					opts->scratchInitFile = optarg;
					loadingMode = Seperate;
				} else {
					exitWithArgumentError("use either hwInit for the firmware or ramInit and scratchInit!");
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
					exitWithArgumentError("use either the old --[xx]init options or memIdx");
				}
				break;
			case 'S':
				{
					stringstream ss(optarg);
					ss >> opts->stallLimit;
					if (ss.fail()) {
						cout << "Invalid value for stallLimit: " << optarg << "!" << endl;
						printHelp();
						exit(EXIT_FAILURE);
					}
				}
				break;
			default:
				cout << "unknown argument: " << opt << " ... stop!\n";
				printHelp();
				exit(EXIT_FAILURE);
		}
	}
	// make sure that both init files are set!
	if (loadingMode == None) {
		exitWithArgumentError("use either memIdx, hwInit or ramInit & scratchInit to initialize memories!");
	}

	// set mode to struct
	opts->hwInitMode = loadingMode;
}