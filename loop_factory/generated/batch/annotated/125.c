int main1(int p){
  int m, u, j, b;

  m=35;
  u=0;
  j=p;
  b=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j + b == 2 * \at(p, Pre);
  loop invariant u == 3 * (j - \at(p, Pre));
  loop invariant u >= 0;
  loop invariant u <= m;
  loop invariant p == \at(p, Pre);
  loop invariant m == 35;
  loop invariant u == 3*(j - p);
  loop invariant u == 3*(p - b);
  loop invariant j + b == 2*p;
  loop invariant 3*(j - p) == u;

  loop invariant b + j == 2 * p;
  loop invariant j >= p;
  loop invariant b <= p;
  loop assigns j, b, u;
*/
while (u<=m-3) {
      j = j+1;
      b = b-1;
      u = u+3;
  }

}
