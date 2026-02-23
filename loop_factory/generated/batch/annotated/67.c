int main1(int m,int q){
  int e, u, j, v, f;

  e=(m%12)+16;
  u=0;
  j=-8;
  v=m;
  f=e;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == (m % 12) + 16;
  loop invariant v == m;
  loop invariant f == e;
  loop invariant j == -8 + u*(v+f);
  loop invariant 0 <= u && u <= e;
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant v == \at(m, Pre);
  loop invariant (0 <= u) && (u <= e);
  loop assigns j, u;
*/
while (u<e) {
      j = j+v+f;
      u = u+1;
  }

}
