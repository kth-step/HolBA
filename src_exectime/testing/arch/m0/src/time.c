#include "config.h"
#include "lib/printf.h"
#include <stdint.h>

#include "experiment/exp_time_runner.h"

#ifdef RUN_TIME

void run_time_experiment(void)
{
#ifdef RUN_2EXPS
    uint32_t t1 = time_run(1);
    uint32_t t2 = time_run(2);

    if (t1 == t2) { printf("RESULT: EQUAL\n"); }
    else { printf("RESULT: UNEQUAL\n"); }
#elif defined RUN_1EXPS
    uint32_t t = time_run(1);
    printf("T = %d\n", t);
#else
    #error "no experiment type selected"
#endif

}

#endif // RUN_TIME
