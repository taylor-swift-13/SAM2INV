int main1(int m,int n,int p){
  int l, i, v, k, h, x;

  l=26;
  i=0;
  v=2;
  k=l;
  h=n;
  x=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant v == i + 2;
    loop invariant x == m + i * p;
    loop invariant k == l + (i * (i + 5)) / 2;
    loop assigns v, k, x, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v+1;
      k = k+v;
      x = x+p;
      i = i+1;
  }

}