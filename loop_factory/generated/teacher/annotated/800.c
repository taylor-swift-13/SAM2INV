int main1(int a,int b){
  int n, f, v;

  n=(b%33)+13;
  f=0;
  v=3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == 0;
  loop invariant n == (b % 33) + 13;
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant (v == 0) || (v == 3);
  loop invariant v % 3 == 0;
  loop invariant v >= 0;
  loop invariant v == 0 || v == 3;
  loop invariant f % 4 == 0;
  loop invariant 0 <= v;
  loop invariant v <= 3;
  loop invariant n == ((\at(b, Pre) % 33) + 13);
  loop assigns v;
*/
while (1) {
      v = v+3;
      if ((f%4)==0) {
          v = v-v;
      }
  }

}
