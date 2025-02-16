#include "dram_sim.h"
#include "util.h"
#include <fstream>
#include <yaml-cpp/yaml.h>
#include <svdpi.h>

DISABLE_WARNING_PUSH
DISABLE_WARNING_UNUSED_PARAMETER
DISABLE_WARNING_MISSING_FIELD_INITIALIZERS
#include <base/base.h>
#include <base/request.h>
#include <base/config.h>
#include <frontend/frontend.h>
#include <memory_system/memory_system.h>
DISABLE_WARNING_POP

using namespace vortex;

class DramSim::Impl {
private:
    Ramulator::IFrontEnd* ramulator_frontend_;
    Ramulator::IMemorySystem* ramulator_memorysystem_;
    std::unordered_map<uint64_t, uint64_t> memory_data_; 
    std::unordered_set<uint64_t> pending_requests_;

public:
    Impl(const std::string& config_file) {
        YAML::Node dram_config = YAML::LoadFile(config_file);
        
        
        ramulator_frontend_ = Ramulator::Factory::create_frontend(dram_config);
        ramulator_memorysystem_ = Ramulator::Factory::create_memory_system(dram_config);
        ramulator_frontend_->connect_memory_system(ramulator_memorysystem_);
        ramulator_memorysystem_->connect_frontend(ramulator_frontend_);
    }

    ~Impl() {
        std::ofstream nullstream("ramulator_ddr5.stats.log");
        auto original_buf = std::cout.rdbuf();
        std::cout.rdbuf(nullstream.rdbuf());
        ramulator_frontend_->finalize();
        ramulator_memorysystem_->finalize();
        std::cout.rdbuf(original_buf);
    }

    void reset() {
        memory_data_.clear();
        pending_requests_.clear();
    }

    void tick() {
        ramulator_memorysystem_->tick();
    }

    bool send_request(bool is_write, uint64_t addr, int source_id, ResponseCallback response_cb, void* arg) {
        if (is_write) {
            memory_data_[addr] = *(reinterpret_cast<uint64_t*>(arg));
            response_cb(arg);
            return true;
        }
        
        pending_requests_.insert(addr);
        return ramulator_frontend_->receive_external_requests(
            Ramulator::Request::Type::Read, addr, source_id,
            [this, callback_ = std::move(response_cb), addr, arg](Ramulator::Request& /*dram_req*/) {
                if (memory_data_.find(addr) != memory_data_.end()) {
                    *(reinterpret_cast<uint64_t*>(arg)) = memory_data_[addr];
                } else {
                    *(reinterpret_cast<uint64_t*>(arg)) = 0; 
                }
                pending_requests_.erase(addr);
                callback_(arg);
            }
        );
    }

    bool is_request_done(uint64_t addr) {
        return pending_requests_.find(addr) == pending_requests_.end();
    }

    uint64_t get_memory_data(uint64_t addr) {
        return memory_data_.find(addr) != memory_data_.end() ? memory_data_[addr] : 0;
    }
};

///////////////////////////////////////////////////////////////////////////////

DramSim::DramSim()
    : impl_(new Impl("ddr5-config.yaml"))
{}

DramSim::~DramSim() {
    delete impl_;
}

void DramSim::reset() {
    impl_->reset();
}

void DramSim::tick() {
    impl_->tick();
}

bool DramSim::send_request(bool is_write, uint64_t addr, int source_id, ResponseCallback callback, void* arg) {
    return impl_->send_request(is_write, addr, source_id, callback, arg);
}


extern "C" {
    static DramSim* dpi_dram_sim = nullptr;
    static uint64_t last_data = 0;
    
    void dpi_init_ramulator() {
        if (!dpi_dram_sim) {
            dpi_dram_sim = new DramSim();
        }
    }
    
    void dpi_send_memory_request(long long addr, int is_write, long long data) {
        if (dpi_dram_sim) {
            dpi_dram_sim->send_request(is_write, addr, 0, [](void* arg) {
                last_data = *(reinterpret_cast<uint64_t*>(arg));
            }, &data);
        }
    }
    
    int dpi_is_request_done(long long addr) {
        return dpi_dram_sim ? dpi_dram_sim->impl_->is_request_done(addr) : 0;
    }
    
    long long dpi_get_memory_data(long long addr) {
        return dpi_dram_sim ? dpi_dram_sim->impl_->get_memory_data(addr) : 0;
    }
    
    void dpi_tick_ramulator() {
        if (dpi_dram_sim) {
            dpi_dram_sim->tick();
        }
    }
}