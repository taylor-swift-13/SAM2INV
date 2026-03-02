int main1(int k,int q){
  int n, x, e, y;

  n=40;
  x=0;
  e=0;
  y=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == 2*y;
  loop invariant 0 <= e && e <= n && k == \at(k, Pre) && q == \at(q, Pre);
  loop invariant y % 2 == 0;
  loop invariant e >= 0;
  loop invariant k == \at(k, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant e <= n + 3;
  loop invariant e % 4 == 0;
  loop invariant 0 <= e && e <= n;
  loop invariant y >= 0;
  loop invariant 0 <= e && e % 4 == 0 && 0 <= y && e <= n + 3;
  loop invariant k == \at(k, Pre) && q == \at(q, Pre);
  loop invariant 2*y == e && e >= 0 && y >= 0;
  loop invariant 2*y == e;
  loop invariant e == 2*y && 0 <= e && e <= n + 3;
  loop invariant e == 2*y && e >= 0;
  loop invariant e <= n + 3 && k == \at(k, Pre) && q == \at(q, Pre);
  loop assigns e, y;
*/
while (e<n) {
      y = y+2;
      e = e+1;
      e = e+3;
  }

}
