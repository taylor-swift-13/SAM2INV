int main1(int a,int b,int n,int q){
  int l, x, i, g, d, c;

  l=(b%39)+16;
  x=0;
  i=5;
  g=a;
  d=-5;
  c=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i >= 5;
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant l == (\at(b, Pre) % 39) + 16;
  loop invariant (g == \at(a, Pre)) || (g == d);
  loop invariant g <= a;
  loop invariant q == \at(q, Pre);
  loop invariant (g == a) || (g == d);
  loop invariant (i >= 5) && (d == -5) && (g == a || g == d);
  loop invariant l == (b % 39) + 16;
  loop invariant d == -5;
  loop invariant g == a || g == -5;
  loop assigns i, g;
*/
while (1) {
      i = i+3;
      if (d<=g) {
          g = d;
      }
      i = i*2;
  }

}
