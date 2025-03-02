#include <vector>
#include <cstdint>
#include <fstream>
#include <string>
#include <iostream>
#include <iomanip>  // Added for std::setw and std::setfill
#include "svdpi.h"

std::vector<uint32_t> memory;

extern "C" {

    
    void mem_init() {
        std::ifstream file("meminit.hex");
        if (!file.is_open()) {
            std::cerr << "Error: Could not open meminit.hex" << std::endl;
            memory.clear();
            return;
        }
        std::string line;
        while (std::getline(file, line)) {
            uint32_t value = std::stoul(line, nullptr, 16);
            memory.push_back(value);
        }
        file.close();
        std::cout << "Memory initialized with " << memory.size() << " words" << std::endl;
    }

    // Read from memory: address is input, data is output
    void mem_read(const svBitVecVal* address, svBitVecVal* data) {
        uint32_t addr = *address;
        if (addr < memory.size()) {
            *data = memory[addr];
        } else {
            *data = 0;  // Uninitialized addresses return 0
        }
    }

    // Write to memory: both address and data are inputs
    void mem_write(const svBitVecVal* address, const svBitVecVal* data) {
        uint32_t addr = *address;
        uint32_t d = *data;
        if (addr >= memory.size()) {
            memory.resize(addr + 1, 0);  // Resize to addr+1, new elements initialized to 0
        }
        memory[addr] = d;  // Write the data
    }

    void mem_save() {
        std::ofstream file("meminit.hex");
        if (!file.is_open()) {
            std::cerr << "Error: Could not open meminit.hex for writing" << std::endl;
            return;
        }
        for (const auto& val : memory) {
            file << std::hex << std::setw(8) << std::setfill('0') << val << std::endl;
        }
        file.close();
    }
}