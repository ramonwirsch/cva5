
#include "MemoryFragmentLoader.h"

#include <iostream>

using namespace std;

MemoryFragmentLoader::MemoryFragmentLoader(SimMem* memory, uint32_t localMemBaseAddr, axi_ddr_sim* ddr, uint32_t ddrBaseAddr, uint32_t ddrEndExclAddr)
    : memory(memory), localMemBaseAddr(localMemBaseAddr), ddr(ddr), ddrBaseAddr(ddrBaseAddr), ddrEndExclAddr(ddrEndExclAddr) {

    localMemEndExclAddr = localMemBaseAddr + memory->getMemSizeInBytes();
}

MemoryFragmentLoader::~MemoryFragmentLoader() = default;

TargetMemory MemoryFragmentLoader::decodeAddress(uint32_t addr) {
    if (addr >= localMemBaseAddr && addr < localMemEndExclAddr) {
        return TargetMemLocal;
    } else if (addr >= ddrBaseAddr && addr < ddrEndExclAddr) {
        return TargetMemDDR;
    } else {
        return TargetMemInvalid;
    }
}

void MemoryFragmentLoader::writeWord(uint32_t addr, uint32_t data) {
    TargetMemory t = decodeAddress(addr);

    switch (t) {
        case TargetMemLocal:
            memory->writeWord(addr/4, data);
            break;
        case TargetMemDDR:
            ddr->set_data(addr, data, 0xFFFFFFFF);
            break;
        default:
            cout << "Address 0x" << hex << addr << " does not belong into either local (0x" << localMemBaseAddr << " until 0x" << localMemEndExclAddr <<") or ddr (0x" << ddrBaseAddr << " until 0x" << ddrEndExclAddr << ")! Ignoring..." << dec << endl;
    }
    
}

uint32_t MemoryFragmentLoader::readWord(uint32_t addr) {
    TargetMemory t = decodeAddress(addr);

    switch (t) {
        case TargetMemLocal:
            return memory->read(addr/4);
            break;
        case TargetMemDDR:
            return ddr->get_data(addr);
            break;
        default:
            cout << "Address 0x" << hex << addr << " does not belong into either local (0x" << localMemBaseAddr << " until 0x" << localMemEndExclAddr <<") or ddr (0x" << ddrBaseAddr << " until 0x" << ddrEndExclAddr << ")! Using 0" << dec << endl;
            return 0;
    }
}