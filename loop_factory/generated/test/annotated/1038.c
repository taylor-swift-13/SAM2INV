int main1(){
  int d, j, x, ud, xxh;
  d=157;
  j=d;
  x=d;
  ud=j;
  xxh=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d == 157;
  loop invariant 0 <= j;
  loop invariant j <= 157;
  loop assigns j;
*/
for (; j-1>=0; j -= 1) {
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d - 3*x == -314;
  loop invariant xxh == 3;
  loop invariant d >= 157;
  loop assigns ud, d, x;
*/
while (1) {
      if (!(x<xxh)) {
          break;
      }
      ud = xxh-x;
      d += xxh;
      x = x + 1;
  }
}