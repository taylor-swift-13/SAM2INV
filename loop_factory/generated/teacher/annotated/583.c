int main1(int a,int m){
  int n, x, v, i;

  n=72;
  x=0;
  v=a;
  i=-6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == 72;
  loop invariant x <= n;
  loop invariant x % 4 == 0;

  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant 0 <= x;
  loop invariant i == 2*v - (2*a + 6);
  loop invariant i == 2*v - 2*a - 6;
  loop invariant x >= 0;
  loop invariant i - 2*v == -6 - 2*a;
  loop assigns v, i, x;
*/
while (x<n) {
      v = v*2;
      i = i+v;
      x = x+4;
  }

}
