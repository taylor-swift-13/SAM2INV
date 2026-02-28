int main1(int a,int n){
  int h, i, s, w;

  h=a+13;
  i=0;
  s=2;
  w=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (s - w == 0 || s - w == 7) && w <= s;
  loop invariant h == a + 13;
  loop invariant n == \at(n, Pre);
  loop invariant w <= s;
  loop invariant (s - w == 0) || (s - w == 7);
  loop invariant s >= 2;
  loop invariant a == \at(a, Pre);
  loop invariant s % 7 == 2;
  loop invariant (s - w) % 7 == 0;
  loop invariant ((s - 2) % 7 == 0);
  loop assigns w, s;
*/
while (1) {
      w = s;
      s = s+3;
      s = s+4;
  }

}
