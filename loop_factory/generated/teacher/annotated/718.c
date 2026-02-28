int main1(int b,int m,int p,int q){
  int t, i, x, a, y, r, v, l;

  t=55;
  i=0;
  x=q;
  a=p;
  y=-8;
  r=p;
  v=3;
  l=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i >= 0 && i <= t && (i % 3) == 0 && x == q + i/3 && a == p + (i/3)*q + (i/3)*((i/3) + 1)/2;
  loop invariant i >= 0 && i <= t;
  loop invariant i <= t;
  loop invariant i % 3 == 0;
  loop invariant x - i/3 == \at(q, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant x == q + i/3;
  loop invariant a == p + (i/3)*q + ((i/3) * ((i/3) + 1)) / 2;
  loop invariant (p >= b+4) ==> (r == p);
  loop invariant a == p + (i/3)*q + ((i/3)*((i/3)+1))/2;
  loop invariant i == 3*(x - q);
  loop invariant x >= q;
  loop invariant i >= 0;
  loop invariant r >= p;
  loop assigns x, a, i, r;
*/
while (i<=t-3) {
      x = x+1;
      a = a+x;
      if (p<b+4) {
          r = r+i;
      }
      i = i+3;
  }

}
