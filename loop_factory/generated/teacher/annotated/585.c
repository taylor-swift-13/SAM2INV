int main1(int n,int p){
  int a, e, v;

  a=(p%12)+6;
  e=0;
  v=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == \at(p, Pre);
  loop invariant v >= p;
  loop invariant a == (\at(p, Pre) % 12) + 6;
  loop invariant n == \at(n, Pre);
  loop invariant a == (p % 12) + 6;
  loop invariant a == p % 12 + 6;
  loop assigns v;
*/
while (1) {
      v = v+3;
      v = v*v+v;
  }

}
