
#include "MemoryFragmentLoader.h"
#include <iostream>
#include <fstream>
#include <cstdlib>
#include <filesystem>
#include <utility>

using namespace std;

BaseMemoryFragmentLoader::BaseMemoryFragmentLoader() = default;
BaseMemoryFragmentLoader::~BaseMemoryFragmentLoader() = default;

//#define DEBUG_OUTPUT


void BaseMemoryFragmentLoader::load(const char *infoFile) {
    // open information file
    ifstream infoStream;
    infoStream.open(infoFile);

    if (!infoStream.is_open()) {
        cout << "Memory fragments information file failed to open: " << infoFile << endl;
        exit(EXIT_FAILURE);
    }

    bool validFragment = false;

    int fragIdx = 0;

    do {
        bool fail = false;

        string startAddrLine;

        fail |= !getline(infoStream, startAddrLine);

        uint64_t startAddr;
        if (!fail) {
            try {
                startAddr = stoul(startAddrLine, nullptr, 16);
            } catch (std::exception const& ex) {
                cout << "Fragment " << fragIdx << ": startAddr invalid '" << startAddrLine << "'" << endl;
                fail = true;
                startAddr = -1;
            }
        } else {
            startAddr = -1;
        }

        string sizeLine;

        fail |= !getline(infoStream, sizeLine);

        uint64_t size;
        if (!fail) {
            try {
                size = stoul(sizeLine, nullptr, 16);
            } catch (std::exception const& ex) {
                cout << "Fragment " << fragIdx << ": size invalid '" << sizeLine << "'" << endl;
                fail = true;
                size = -1;
            }
        } else {
            size = -1;
        }

        string initFile;

        fail |= !getline(infoStream, initFile);

        string initOffsetLine;

        fail |= !getline(infoStream, initOffsetLine);

        uint64_t initOffset;
        if (!fail) {
            try {
                initOffset = stoul(initOffsetLine, nullptr, 16);
            } catch (std::exception const& ex) {
                cout << "Fragment " << fragIdx << ": initOffset invalid '" << initOffsetLine << "'" << endl;
                fail = true;
                initOffset = -1;
            }    
        } else {
            initOffset = -1;
        }

        string refFile;

        fail |= !getline(infoStream, refFile);

        string refOffsetLine;

        fail |= !getline(infoStream, refOffsetLine);

        uint64_t refOffset;
        if (!fail && !refOffsetLine.empty()) {
            try {
                refOffset = stoul(refOffsetLine, nullptr, 16);
            } catch (std::exception const& ex) {
                cout << "Fragment " << fragIdx << ": refOffset invalid '" << refOffsetLine << "'" << endl;
                fail = true;
                refOffset = -1;
            }  
        } else {
            refOffset = -1;
        }



        if (initFile.empty()) {
            cout << "Loaded " << fragments.size() << " fragments!" << endl;
            validFragment = false;
        } else {
            auto basePath = absolute(filesystem::path(infoFile)).parent_path();
            auto initPath = basePath / initFile;

            optional<filesystem::path> refPath;
            if (!refFile.empty()) {
                refPath = optional(basePath / refFile);
            } else {
                refPath = nullopt;
            }

            if (filesystem::exists(initPath) && (!refPath.has_value() || filesystem::exists(refPath.value())) && startAddr >= 0 && size > 0) {
                validFragment = true;

                MemoryFragment frag(startAddr, size, initPath, initOffset, refPath, refOffset);

                loadFragment(frag);
            } else {
                cout << "Invalid Fragment Info: init: " << initPath << ", ref: ";
                if (refPath.has_value()) {
                    cout << *refPath;
                } else {
                    cout << "[None]";
                }
                cout << ", startAddr: "
                     << startAddrLine << ", size: " << sizeLine << ", initOffs: " << initOffsetLine
                     << ", refOffset: " << refOffsetLine << endl;
                exit(EXIT_FAILURE);
                validFragment = false;
            }
        }

        fragIdx++;
    } while (validFragment);
}

void BaseMemoryFragmentLoader::loadFragment(MemoryFragment &frag) {

    fragments.push_back(frag);

    if (frag.startAddr % 4 != 0 || frag.size % 4 != 0) {
        cout << "WARNING: Fragment is not multiple of word / word-aligned: 0x" << hex << frag.startAddr << "+.." << dec << frag.size << endl;
    }

    cout << "Loading MemoryFrag " << frag.initPath << ": starting at 0x" << hex << frag.initFileOffset << ", " << dec << frag.size << " bytes" << endl;

    if (frag.initPath == "/dev/null") { // filling with 0
        auto endAddr = frag.startAddr + frag.size;
        for (uint64_t addr = frag.startAddr; addr < endAddr; addr += 4) {
            writeWord(static_cast<uint32_t>(addr), 0);
        }

    } else {

        ifstream initStream(frag.initPath, ios::binary);
        initStream.seekg(frag.initFileOffset);

        auto endAddr = frag.startAddr + frag.size;
        for (uint64_t addr = frag.startAddr; addr < endAddr; addr += 4) {
            unsigned char data[4];
            initStream.read(reinterpret_cast<char *>(&data[0]), 4);

            if (initStream.fail()) {
                cout << "initStream " << frag.initPath << " failed at memAddr 0x" << hex << addr << ", streamOffset " << initStream.tellg() << " with state " << initStream.rdstate() << dec << endl;
                throw std::invalid_argument("initStream failed");
            }

            uint32_t word = (data[3] << 24) | (data[2] << 16) | (data[1] << 8) | data[0];

#ifdef DEBUG_OUTPUT
            cout << "Writing " << hex << "0x" << addr << ": 0x" << word << dec << endl;
#endif

            writeWord(static_cast<uint32_t>(addr), word);
        }
    }
}

bool BaseMemoryFragmentLoader::diffWithReference() {

    bool passed = true;

    for (auto frag: fragments) {
        passed &= diffFragmentWithReference(frag);
    }

    return passed;
}

bool BaseMemoryFragmentLoader::diffFragmentWithReference(MemoryFragment &frag) {
    if (frag.refPath.has_value()) {
        auto refPath = frag.refPath.value();

        cout << "Checking Fragment 0x" << hex << frag.startAddr << " ..+ 0x" << frag.size << " against reference!" << dec << endl;

//        cout << "Loading RefMemoryFrag " << refPath << ": starting at 0x" << hex << frag.refFileOffset << ", " << dec << frag.size << " bytes" << endl;

        ifstream refStream(refPath, ios::binary);
        refStream.seekg(frag.refFileOffset);


        if (refStream.fail()) {
            cout << "failed to seek refStream " << refPath << " to 0x" << hex << frag.refFileOffset << " with " << refStream.rdstate() << dec << endl;
            return false;
        }

        bool matching = true;

        auto endAddr = frag.startAddr + frag.size;
        for (uint64_t addr = frag.startAddr; addr < endAddr; addr += 4) {
            unsigned char data[4];
            refStream.read(reinterpret_cast<char *>(&data[0]), 4);

            if (refStream.fail()) {
                cout << "refStream " << refPath << " failed at memAddr 0x" << hex << addr << ", streamOffset " << refStream.tellg() << " with state " << refStream.rdstate() << dec << endl;
                return false;
            }

            uint32_t refWord = (data[3] << 24) | (data[2] << 16) | (data[1] << 8) | data[0];
#ifdef DEBUG_OUTPUT
            cout << "Reading " << hex << "0x" << addr << ": 0x" << refWord << dec << endl;
#endif

            uint32_t actualWord = readWord(static_cast<uint32_t>(addr));

            if (actualWord != refWord) {
                cerr << " At 0x" << hex << addr << ": Expected: 0x" << refWord << ", but found: 0x" << actualWord << dec << " !" << endl;
                matching = false;
            } else {
#ifdef DEBUG_OUTPUT
                cout << " At 0x" << hex << addr << ": Expected: 0x" << refWord << ", but found: 0x" << actualWord << dec << " !" << endl;
#endif
            }
        }

        if (matching) {
            cout << "  Matches reference!" << endl;
            return true;
        } else {
            return false;
        }
    } else {
        return true;
    }
}
