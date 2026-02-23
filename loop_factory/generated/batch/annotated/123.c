int main1(int m){
  int b, v, a, w;

  b=53;
  v=b;
  a=v;
  w=v;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 4*a + v == 5*b;
  loop invariant a + w == 2*b;
  loop invariant 0 <= v;
  loop invariant v <= b;
  loop invariant m == \at(m, Pre);
  loop invariant v % 4 == 1;
  loop invariant a >= 53;
  loop invariant w <= 53;
  loop invariant v <= 53;
  loop invariant b == 53;
  loop invariant a <= 66;
  loop assigns a, v, w;
*/
while (v>3) {
      a = a+1;
      w = w-1;
      v = v-4;
  }

}
