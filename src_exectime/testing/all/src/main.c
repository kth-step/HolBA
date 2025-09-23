#include <stdint.h>
#include <stdarg.h>
#include "lib/printf.h"
#include "config.h"

#if __has_include("experiment/binpatch.h")
#include "experiment/binpatch.h"
#endif


#ifdef RUN_CACHE
void run_cache_experiment();
void reset_cache_experiment();
#endif

#ifdef RUN_TIME
void run_time_experiment();
#endif

void experiment_complete_marker() {
  // infinite echo loop
  printf_echoloop();
}

void benchmark_run();
#include "io.h"

int main()
{
#ifdef __BENCHMARK_MODE
	io_init();
	out_info("");
	out_info("--------------------------------");
	out_info("io ready!");
	out_info("benchmark start");

	while(1) {
		benchmark_run();
	}
#endif

#if __has_include("experiment/binpatch.h")
  patch_binary();
#endif

#ifdef RUN_CACHE
  reset_cache_experiment();
#endif

  printf_init();

  printf("Init complete.\n");

#ifdef RUN_CACHE
  run_cache_experiment();
#elif defined RUN_TIME
  run_time_experiment();
#endif

  printf("Experiment complete.\n");

  experiment_complete_marker();

  return 0;
}

void main_core1()
{
}

void main_core2()
{
}

void main_core3()
{
}

