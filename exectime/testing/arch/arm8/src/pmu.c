#include "pmu.h"

static unsigned int armv8pmu_pmcr_read(void)
{
	unsigned long long val=0;
	asm volatile("mrs %0, pmcr_el0" : "=r" (val));
	asm volatile("isb");
	return (unsigned int)val;
}

static void armv8pmu_pmcr_write(unsigned int val)
{
	val &= ARMV8_PMCR_MASK;
	asm volatile("isb");
	asm volatile("msr pmcr_el0, %0" : : "r" ((unsigned long long)val));
}

static void disable_cpu_counters()
{
	/*  Program PMU and disable all counters */
	armv8pmu_pmcr_write(armv8pmu_pmcr_read() |~ARMV8_PMCR_E);
	/*  disable user-mode access to counters. */
	asm volatile("msr pmuserenr_el0, %0" : : "r"(ARMV8_PMUSERENR_DIS_EL0));
}

void enable_pmu(unsigned int counter, unsigned int evtCount)
{
	counter  &= ARMV8_PMSELR_COUNTER_MASK;
	evtCount &= ARMV8_PMEVTYPER_EVTCOUNT_MASK;
	#define USER_EVENTS	(1 << 31)

	/*  Enable user-mode access to counters. */
	asm volatile("msr pmuserenr_el0, %0" : : "r"((unsigned long long)ARMV8_PMUSERENR_EN_EL0|ARMV8_PMUSERENR_ER));
	
	unsigned long long val=0;
	asm volatile("mrs %0, pmcntenset_el0" : "=r" (val));
	asm volatile("isb");
	/* Performance Monitors Count Enable Set */
	asm volatile("msr pmcntenset_el0, %0" : : "r" ((unsigned long long)(val | (1 << counter))));
	//asm volatile("msr pmcntenset_el0, %0" : : "r" (1 << counter));



	/* Select counter */
	asm volatile("msr pmselr_el0, %0" : : "r" (counter));
	asm volatile("isb");
	asm volatile("msr pmxevtyper_el0, %0" : : "r" (evtCount));

	/* Initialize: E bits. and Reset: P bits. */
	armv8pmu_pmcr_write(armv8pmu_pmcr_read() | ARMV8_PMCR_E | ARMV8_PMCR_P);
	asm volatile("isb");
}


void disable_pmu(unsigned int counter)
{
	counter  &= ARMV8_PMSELR_COUNTER_MASK;
	asm volatile("msr pmcntenclr_el0, %0" : : "r" (1 << counter));
}

unsigned int read_pmu(unsigned int counter)
{
	unsigned long long val=0;
	counter  &= ARMV8_PMSELR_COUNTER_MASK;
    /* Select counter */
	asm volatile("msr pmselr_el0, %0" : : "r" (counter));
	asm volatile("isb");
	asm volatile("mrs %0, pmxevcntr_el0" : "=r" (val)); 
	printf("Value of counter is %d \n", val);
	// Disable all counters
	disable_cpu_counters();

	return val;
}
