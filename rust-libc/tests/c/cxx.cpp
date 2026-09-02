// C++ against the host's libstdc++.a: exceptions, static constructors and
// destructors, thread_local, containers, iostreams, std::thread.
#include <algorithm>
#include <chrono>
#include <cstdio>
#include <iostream>
#include <map>
#include <memory>
#include <mutex>
#include <sstream>
#include <stdexcept>
#include <string>
#include <thread>
#include <vector>

struct Ctor {
    int v;
    Ctor() : v(42) {}
    ~Ctor() { std::puts("dtor ran"); }
} global;

thread_local int tl = 7;

int main() {
    std::vector<std::string> v = {"pear", "apple", "fig"};
    std::sort(v.begin(), v.end());
    std::map<std::string, int> m;
    for (auto &s : v) m[s] = (int)s.size();
    try {
        throw std::runtime_error("boom");
    } catch (const std::exception &e) {
        std::printf("caught %s\n", e.what());
    }
    auto p = std::make_unique<int>(global.v + tl);
    std::printf("%s %s %s %d %d\n", v[0].c_str(), v[1].c_str(), v[2].c_str(), m["apple"], *p);

    std::ostringstream os;
    os << "value=" << 42 << " pi=" << 3.5 << std::hex << " " << 255;
    std::cout << os.str() << std::endl;
    std::istringstream is("12 34");
    int a = 0, b = 0;
    is >> a >> b;
    std::cout << "sum " << (a + b) << std::endl;

    std::mutex mu;
    int counter = 0;
    std::vector<std::thread> threads;
    for (int i = 0; i < 4; i++)
        threads.emplace_back([&] {
            for (int j = 0; j < 1000; j++) {
                std::lock_guard<std::mutex> g(mu);
                counter++;
            }
            tl++;
        });
    for (auto &t : threads) t.join();
    std::cout << "counter " << counter << " tl " << tl << std::endl;
    std::this_thread::sleep_for(std::chrono::milliseconds(1));
    return 0;
}
