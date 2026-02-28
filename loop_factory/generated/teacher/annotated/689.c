int main1(int a,int k,int m,int q){
  int p, j, d, s, c, v, x;

  p=q+14;
  j=0;
  d=j;
  s=5;
  c=p;
  v=a;
  x=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == q + 14 + 2*(v - a);
  loop invariant s == 5 + (v - a)*(q + 14) + (v - a)*((v - a) - 1);
  loop invariant d == (v - a)*5 + (q + 14)*((v - a)*((v - a) - 1))/2 + ((v - a)*((v - a) - 1)*((v - a) - 2))/3 + 4*(v - a);
  loop invariant v >= a;
  loop invariant p == q + 14;
  loop invariant c == p + 2*(v - a);
  loop invariant s == 5 + p*(v - a) + (v - a)*(v - a - 1);
  loop invariant 6*d == 54*(v - a) + 3*p*(v - a)*(v - a - 1) + 2*(v - a)*(v - a - 1)*(v - a - 2);

  loop invariant c - 2*v == p - 2*a;
  loop invariant a == \at(a, Pre);

  loop invariant c - p == 2*(v - a);
  loop invariant s == (v - a)*(v - a) + (p - 1)*(v - a) + 5;

  loop assigns d, s, c, v;
*/
while (1) {
      if (v>p) {
          break;
      }
      d = d+s;
      s = s+c;
      c = c+2;
      v = v+1;
      d = d+4;
  }

}
