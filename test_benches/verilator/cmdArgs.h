#pragma once

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
	int terminateOnUserExit;
	int stallLimit;
};

void printHelp();

void exitWithArgumentError(const char *text);

void handleArguments(int argc, char **argv, struct cmdline_options *opts);

//TODO wrap in a extensible class!