int main1(int p,int q){
  int h, d, n, c;

  h=48;
  d=0;
  n=d;
  c=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == 4*d;
  loop invariant c == 2*d*(d+1) + 4;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant d <= h;
  loop invariant c == 2*d*d + 2*d + 4;
  loop invariant d >= 0;
  loop invariant (d <= h);
  loop invariant (n == 4*d);
  loop invariant (c == 2*d*d + 2*d + 4);
  loop invariant (p == \at(p, Pre));
  loop invariant (q == \at(q, Pre));
  loop assigns d, n, c;
*/
while (1) {
      if (d>=h) {
          break;
      }
      n = n+3;
      d = d+1;
      n = n+1;
      c = c+n;
  }

}
