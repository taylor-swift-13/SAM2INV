int main1(int b,int k,int p,int q){
  int g, j, r, a, v, i, x, l;

  g=61;
  j=g;
  r=0;
  a=1;
  v=6;
  i=0;
  x=b;
  l=g;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == i*i + 5*i + 1;
  loop invariant v == 6 + 2*i;
  loop invariant r == i*(i*i + 6*i - 4)/3;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant i <= g+1;
  loop invariant 0 <= i <= g + 1;
  loop invariant r == (i*i*i + 6*i*i - 4*i) / 3;
  loop invariant r == ((i-1)*i*(2*i-1))/6 + (5*(i-1)*i)/2 + i;
  loop assigns i, r, a, v;
*/
while (i<=g) {
      i = i+1;
      r = r+a;
      a = a+v;
      v = v+2;
  }

}
