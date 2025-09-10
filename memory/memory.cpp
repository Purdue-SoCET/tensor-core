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

    bool mem_read(const svBitVecVal* address, svBitVecVal* data) {
        uint32_t addr = *address;
        if (addr % 4 != 0) {
            std::cerr << "Error: Unaligned memory read at address " << addr << std::endl;
            *data = 0;
            return false;
        }
        uint32_t index = addr / 4;
        if (index < memory.size()) {
            *data = memory[index];
            return true;
        } else {
            *data = 0;  // Uninitialized addresses return 0
            return false;
        }
        return false;
    }


    void mem_write(const svBitVecVal* address, const svBitVecVal* data) {
        uint32_t addr = *address;
        if (addr % 4 != 0) {
            std::cerr << "Error: Unaligned memory write at address " << addr << std::endl;
            return;
        }
        uint32_t index = addr / 4;
        uint32_t d = *data;
        if (index >= memory.size()) {
            memory.resize(index + 1, 0);  // Resize to index+1, new elements initialized to 0
        }
        memory[index] = d;  // Write the data
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