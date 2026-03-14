int main1(){
  int h5, jch, l9n, px, lt;
  h5=1*3;
  jch=h5;
  l9n=jch;
  px=h5;
  lt=1+2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 3*jch + 2*l9n == 15;
  loop invariant px == h5;
  loop invariant lt == 1 + 2;
  loop invariant (l9n - jch) % 10 == 0;
  loop invariant l9n >= jch;
  loop invariant jch <= h5;
  loop invariant jch >= 0;
  loop assigns l9n, jch;
*/
while (1) {
      if (!(jch-4>=0)) {
          break;
      }
      l9n = l9n+px+lt;
      jch -= 4;
  }
}