int main1(int a,int n){
  int h, i, s, w;

  h=a+13;
  i=0;
  s=2;
  w=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == \at(n, Pre);
  loop invariant s >= 2;
  loop invariant w >= 2;
  loop invariant h == a + 13;
  loop invariant a == \at(a, Pre);
  loop invariant h == \at(a, Pre) + 13;
  loop invariant (s == 2) || (s % 4 == 0);
  loop invariant w % 2 == 0;
  loop invariant s % 2 == 0;
  loop assigns s, w;
*/
while (1) {
      s = s*4+4;
      w = w*s+4;
      s = s*4+4;
  }

}
