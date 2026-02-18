int main1(int b,int k,int m,int p){
  int l, i, v, c, g;

  l=49;
  i=0;
  v=k;
  c=3;
  g=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == k + i;
    loop invariant c == 3 + i*(k+4) + i*(i-1)/2;
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant k == \at(k, Pre);
    loop invariant c == 3 + i*(k + 3) + i*(i + 1)/2;
    loop invariant l == 49;
    loop invariant c == 3 + i*(k + 4) + i*(i - 1)/2;
    loop invariant b == \at(b, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant 0 <= i <= l;
    loop assigns v, c, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v+1;
      c = c+v;
      c = c+3;
      i = i+1;
  }

}