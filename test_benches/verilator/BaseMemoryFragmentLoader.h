
#pragma once

#include <functional>
#include <list>
#include <filesystem>
#include <optional>

struct MemoryFragment {
    uint64_t startAddr;
    uint64_t size;
    std::filesystem::path initPath;
    uint64_t initFileOffset;
    std::optional<std::filesystem::path> refPath;
    uint64_t refFileOffset;

    MemoryFragment(uint64_t startAddr, uint64_t size, std::filesystem::path initPath, uint64_t initFileOffset,
                   std::optional<std::filesystem::path> refPath, uint64_t refFileOffset)
            : startAddr(startAddr), size(size), initPath(initPath), initFileOffset(initFileOffset), refPath(refPath), refFileOffset(refFileOffset) {};
};

class BaseMemoryFragmentLoader {
public:
    BaseMemoryFragmentLoader();
    ~BaseMemoryFragmentLoader();

    void load(const char * infoFile);

    bool diffWithReference();
protected:
    virtual void writeWord(uint32_t addr, uint32_t data) = 0;
    virtual uint32_t readWord(uint32_t addr) = 0;
private:
    std::list<MemoryFragment> fragments;

    void loadFragment(MemoryFragment &frag);

    bool diffFragmentWithReference(MemoryFragment &frag);
};