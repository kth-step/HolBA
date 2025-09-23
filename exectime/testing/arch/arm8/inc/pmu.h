#ifndef _PMU_H
#define _PMU_H

#define ARMV8_PMCR_MASK          0x3f
#define ARMV8_PMCR_E             (1 << 0) /*  Enable all counters */
#define ARMV8_PMCR_P             (1 << 1) /*  Reset all counters */

#define ARMV8_PMUSERENR_EN_EL0   (1 << 0) /*  EL0 access enable */
#define ARMV8_PMUSERENR_DIS_EL0  (0 << 0) /*  EL0 access disbale */
#define ARMV8_PMUSERENR_ER       (1 << 3) /*  Event counter read enable */

#define ARMV8_PMEVTYPER_EVTCOUNT_MASK  0x3ff
#define ARMV8_PMSELR_COUNTER_MASK      0x1f


#define ARMV8_PMCNTENSET_EL0_ENABLE  (1 << 1) /* *< Enable Perf count reg */
#define ARMV8_PMCNTENSET_EL0_DISABLE (1 << 1)


void enable_pmu(unsigned int counter, unsigned int evtCount);
unsigned int read_pmu(unsigned int counter);
void disable_pmu(unsigned int counter);

#endif
