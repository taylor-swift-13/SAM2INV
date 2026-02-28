int main1(int m,int p){
  int a, j, u, r;

  a=m;
  j=0;
  u=a;
  r=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == m;
  loop invariant (u - a) % 3 == 0;
  loop invariant ((r == p) && (u == m)) || (r == u - 3);
  loop invariant u >= a;
  loop invariant p == \at(p, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant u >= m;
  loop invariant (u - m) % 3 == 0;
  loop assigns r, u;
*/
while (1) {
      r = u;
      u = u+3;
  }

}
