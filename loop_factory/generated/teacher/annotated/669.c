int main1(int m,int n){
  int l, k, e, c, v, i;

  l=67;
  k=4;
  e=0;
  c=1;
  v=6;
  i=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= i;
  loop invariant i <= l + 1;
  loop invariant v == 6 + 2*i;
  loop invariant c == i*i + 5*i + 1;
  loop invariant e*3 == i*(i*i + 6*i - 4);
  loop invariant e == (i*(i*i + 6*i - 4)) / 3;
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant i >= 0;
  loop invariant e == i*(i-1)*(2*i-1)/6 + 5*i*(i-1)/2 + i;
  loop invariant c == 1 + 6*i + i*(i - 1);
  loop invariant e == (i*i*i + 6*i*i - 4*i) / 3;
  loop assigns i, e, c, v;
*/
while (i<=l) {
      i = i+1;
      e = e+c;
      c = c+v;
      v = v+2;
  }

}
