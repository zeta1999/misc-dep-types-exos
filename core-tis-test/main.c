#define CoreUse(x) (void)(x)
#include <stdlib.h>
#include <stdbool.h>
#include <stdio.h>
#include <string.h>

#ifdef TIS
//#error "tis"
// BOOM
#endif

/*@
requires c > 0;
terminates c>0;
assigns \nothing;
*/
void f (int c) { while(!c) { CoreUse(c); } return;}

int main(int argc, char **argv) {
	CoreUse(argc);
	CoreUse(argv);

	bool ok = true;

	// ok means SUCCESS = retval => 0
	return !(ok == true);
}
