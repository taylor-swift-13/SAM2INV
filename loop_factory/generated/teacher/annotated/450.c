int main1(int m,int p){
  int b, u, x, n;

  b=19;
  u=0;
  x=5;
  n=u;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == 0;

  loop invariant u >= 0;
  loop invariant m == \at(m,Pre);
  loop invariant p == \at(p,Pre);
  loop invariant u % 5 == 0;
  loop invariant 0 <= u;
  loop invariant u <= b;
  loop invariant b == 19;
  loop invariant (b == 19);
  loop invariant (m == \at(m, Pre));
  loop invariant (p == \at(p, Pre));
  loop invariant (n == 0);

  loop assigns n, u;
*/
while (u<=b-5) {
      n = n+n;
      u = u+5;
  }

}
