int main1(int a,int q){
  int l, u, j, v;

  l=(q%32)+9;
  u=0;
  j=3;
  v=6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j >= 3 && l == (q % 32) + 9;
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant l == (q % 32) + 9;
  loop invariant j >= 3;
  loop invariant u >= 0;
  loop invariant l == (\at(q,Pre) % 32) + 9;
  loop invariant a == \at(a,Pre);
  loop invariant q == \at(q,Pre);
  loop invariant j >= u;
  loop invariant j >= 2*u + 3;
  loop invariant u <= j;
  loop invariant l == ((\at(q,Pre) % 32) + 9);
  loop invariant q == \at(q,Pre) && j >= 3 && u >= 0;
  loop invariant l == (q % 32) + 9 && a == \at(a, Pre) && q == \at(q, Pre) && j >= 0;

  loop invariant l == (\at(q, Pre) % 32) + 9;
  loop invariant j > 0;
  loop assigns j, u;
*/
while (1) {
      j = j*j+j;
      u = u+1;
  }

}
