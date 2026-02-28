int main1(int b,int n){
  int h, a, p, u;

  h=33;
  a=0;
  p=-2;
  u=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p <= h;
  loop invariant p >= -2;
  loop invariant u == -p - 2;
  loop invariant h == 33;
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant u == -(p + 2);
  loop invariant -2 <= p;
  loop invariant -2 <= p <= h;
  loop assigns p, u;
*/
while (p<h) {
      if (p<h) {
          p = p+1;
      }
      u = u+u;
      u = u+p;
  }

}
