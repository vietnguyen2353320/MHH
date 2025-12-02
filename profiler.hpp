// profiler.hpp
#ifndef PROFILER_HPP
#define PROFILER_HPP

#include <chrono>
#include <iostream>
#include <string>

#ifdef _WIN32
#include <windows.h>
#include <psapi.h>
#else
#include <sys/resource.h>
#endif

class Stopwatch {
private:
    std::chrono::time_point<std::chrono::high_resolution_clock> start_time;
    bool running = false;
    
public:
    void start() {
        start_time = std::chrono::high_resolution_clock::now();
        running = true;
    }
    
    void stop() {
        running = false;
    }
    
    double ms() const {
        if (running) {
            auto end = std::chrono::high_resolution_clock::now();
            return std::chrono::duration_cast<std::chrono::microseconds>(end - start_time).count() / 1000.0;
        }
        return 0.0;
    }
};

static void print_mem_now(const std::string& label) {
#ifdef _WIN32
    PROCESS_MEMORY_COUNTERS pmc;
    if (GetProcessMemoryInfo(GetCurrentProcess(), &pmc, sizeof(pmc))) {
        std::cout << "[mem ] " << label << " WorkingSet: " 
                  << (pmc.WorkingSetSize / 1024) << " KB, Peak: " 
                  << (pmc.PeakWorkingSetSize / 1024) << " KB\n";
    }
#else
    struct rusage usage;
    if (getrusage(RUSAGE_SELF, &usage) == 0) {
        std::cout << "[mem ] " << label << " RSS: " 
                  << (usage.ru_maxrss) << " KB\n";
    }
#endif
}

#endif