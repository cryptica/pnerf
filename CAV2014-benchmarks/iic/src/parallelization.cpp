#include "wsts.h"
#include "parallelization.h"
#include <unistd.h>
#include <signal.h>
#include <sys/types.h>
#include <stdlib.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <sys/wait.h>

extern bool forward_search_zero_one_omega_done;
extern bool forward_search_zero_one_omega_result;
extern bool forward_search_done;

void sigusr1_handler(int) {
    forward_search_zero_one_omega_result = true;
    forward_search_zero_one_omega_done = true;
}

void sigusr2_handler(int) {
    forward_search_zero_one_omega_result = false;
    forward_search_zero_one_omega_done = true;
}

void sigchld_handler(int) {
    forward_search_done = true;
    wait(NULL);
}

void set_limits() {
    // 8 MB of memory
    struct rlimit lim;
    lim.rlim_cur = 8 * (1UL << 20);
    lim.rlim_max = lim.rlim_cur;
    setrlimit(RLIMIT_AS, &lim);
    std::cerr << "Limit for AS: " << lim.rlim_cur <<std::endl;
}

void spawn_zero_one_omega(const ic3_data& d) {
    pid_t child = fork();
    signal(SIGUSR1, sigusr1_handler);
    signal(SIGUSR2, sigusr2_handler);
    signal(SIGCHLD, sigchld_handler);
    if (child == -1) {
	std::cerr << "fork failed" <<std::endl;
	exit(1);
    } else if (child == 0) {
	set_limits();
	ic3_check_zero_one_omega(d);
	if (forward_search_zero_one_omega_done) {
	    std::cerr << "01w successful" <<std::endl;
	    int signal = forward_search_zero_one_omega_result ? 
		SIGUSR1 : SIGUSR2;
	    kill(getppid(), signal);
	}
	exit(0);
    }
}
