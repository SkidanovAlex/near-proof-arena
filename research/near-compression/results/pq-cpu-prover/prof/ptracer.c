#include <sys/prctl.h>
__attribute__((constructor)) static void init(void){ prctl(PR_SET_PTRACER, PR_SET_PTRACER_ANY, 0,0,0); }
