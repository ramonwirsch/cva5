#pragma once

#include "BaseMemoryFragmentLoader.h"
#include "SimMem.h"
#include "AXI_DDR_simulation/axi_ddr_sim.h"

enum TargetMemory {
    TargetMemLocal, TargetMemDDR, TargetMemInvalid
};

class MemoryFragmentLoader : public BaseMemoryFragmentLoader {
public:
    MemoryFragmentLoader(SimMem* memory, uint32_t localMemBaseAddr, axi_ddr_sim* ddr, uint32_t ddrBaseAddr, uint32_t ddrEndExclAddr);
    ~MemoryFragmentLoader();

protected:
    virtual void writeWord(uint32_t addr, uint32_t data);
    virtual uint32_t readWord(uint32_t addr);

private:
    uint32_t localMemBaseAddr;
    uint32_t localMemEndExclAddr;
    uint32_t ddrBaseAddr;
    uint32_t ddrEndExclAddr;

    SimMem * memory;
    axi_ddr_sim * ddr;

    TargetMemory decodeAddress(uint32_t addr);
};