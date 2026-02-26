int main1(int a,int n){
  int y, i, c, v;

  y=n;
  i=0;
  c=6;
  v=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v >= 0;
  loop invariant c >= 2*v + 6;
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant 8*c == v*v + 16*v + 48;
  loop invariant y == \at(n, Pre);
  loop invariant v % 8 == 0;
  loop invariant 8*(c - 6) == v*(v + 16);
  loop invariant y == n;
  loop invariant c == (v*v)/8 + 2*v + 6;
  loop assigns c, v;
*/
while (1) {
      c = c+8;
      v = v+8;
      c = c+v+v;
  }

}
