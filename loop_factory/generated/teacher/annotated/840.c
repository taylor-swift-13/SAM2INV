int main1(int a,int m,int p){
  int r, e, v, y, q, w;

  r=31;
  e=2;
  v=e;
  y=-3;
  q=8;
  w=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v - y >= 1;
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant r == 31;
  loop invariant v >= 2;
  loop invariant y == v - 1 || (y == -3 && v == 2);
  loop invariant y < v;
  loop invariant y >= -3;
  loop invariant y <= v - 1;
  loop assigns y, v;
*/
while (1) {
      y = v;
      v = v+1;
  }

}
