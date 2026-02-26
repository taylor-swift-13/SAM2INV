int main1(int a,int m){
  int n, x, v, i;

  n=72;
  x=n;
  v=m;
  i=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant n == 72;
  loop invariant 0 <= x <= 72;
  loop invariant i == a + 4*(72 - x);
  loop invariant v == m + 3*(72 - x);
  loop invariant i + 4*x == a + 288;
  loop invariant v + 3*x == m + 216;
  loop invariant 0 <= x;
  loop invariant x <= 72;
  loop invariant i == \at(a, Pre) + 4*(72 - x);
  loop invariant v == \at(m, Pre) + 3*(72 - x);
  loop invariant x >= 0;
  loop assigns v, i, x;
*/
while (x>=1) {
      v = v+3;
      i = i+4;
      x = x-1;
  }

}
