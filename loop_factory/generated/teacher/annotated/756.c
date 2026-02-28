int main1(int b,int m,int n,int p){
  int l, a, v, y, k, i, d, x;

  l=50;
  a=5;
  v=0;
  y=1;
  k=6;
  i=0;
  d=n;
  x=-6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i <= l+1;
  loop invariant k == 6 + 4*i;
  loop invariant y == 2*i*i + 4*i + 1;
  loop invariant v == i*(i+1)*(2*i+1)/3;
  loop invariant (b == \at(b, Pre) && m == \at(m, Pre) && n == \at(n, Pre) && p == \at(p, Pre));
  loop invariant l == 50;
  loop invariant i >= 0;
  loop invariant v == ((i-1)*i*(2*i-1))/3 + 2*i*(i-1) + 2*i;
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant 0 <= i <= l+1;
  loop invariant v == 2*i*i + ((i-1)*i*(2*i-1))/3;
  loop invariant 0 <= i;
  loop invariant v == i*(2*i + 1)*(i + 1) / 3;
  loop assigns i, v, y, k;
*/
while (i<=l) {
      i = i+1;
      v = v+y;
      y = y+k;
      k = k+4;
      v = v+1;
  }

}
