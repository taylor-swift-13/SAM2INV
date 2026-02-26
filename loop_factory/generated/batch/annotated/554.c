int main1(int m,int p){
  int a, j, u, r;

  a=m;
  j=0;
  u=a;
  r=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u == a + 2*j*r;
  loop invariant a == \at(m, Pre);
  loop invariant r == \at(p, Pre);
  loop invariant j >= 0;
  loop invariant r == p;
  loop invariant u == m + 2*r*j;
  loop invariant a == m;
  loop invariant u == \at(m, Pre) + 2 * \at(p, Pre) * j;
  loop invariant (j >= 0);
  loop invariant (a == \at(m, Pre));
  loop invariant (m == \at(m, Pre));
  loop invariant (p == \at(p, Pre));
  loop invariant (r == \at(p, Pre));
  loop invariant u == a + 2 * r * j;
  loop assigns u, j;
*/
while (1) {
      u = u+r+r;
      j = j+1;
  }

}
