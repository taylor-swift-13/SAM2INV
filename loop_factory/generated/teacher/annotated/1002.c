int main1(int a,int q){
  int l, u, j, v;

  l=(q%32)+9;
  u=0;
  j=3;
  v=6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j - 2*v*u == 3;
  loop invariant u >= 0;
  loop invariant v == 6;
  loop invariant q == \at(q,Pre);
  loop invariant a == \at(a,Pre);
  loop invariant l == (\at(q,Pre) % 32) + 9;
  loop invariant j - 2*v*u == 3 && u >= 0 && v == 6;
  loop invariant q == \at(q, Pre) && a == \at(a, Pre) && l == (\at(q, Pre)%32) + 9;
  loop invariant j == 3 + 2*v*u;
  loop invariant l == ((\at(q, Pre) % 32) + 9);
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant j == 3 + 2*v*u && u >= 0 && v == 6;
  loop invariant a == \at(a,Pre) && q == \at(q,Pre) && l == (\at(q,Pre) % 32) + 9;
  loop invariant l == (q % 32) + 9;
  loop invariant u >= 0 && v == 6 && l == (q%32) + 9;
  loop invariant l == (q%32)+9;
  loop invariant l == (\at(q, Pre) % 32) + 9;
  loop assigns j, u;
*/
while (1) {
      j = j+v+v;
      u = u+1;
  }

}
