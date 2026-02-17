int main1(int a,int n,int q){
  int l, i, v, s, m, f;

  l=43;
  i=l;
  v=q;
  s=1;
  m=i;
  f=q;

  
  /*@

    loop invariant v == q + (l - i) * l - ((l - i) * (l - i - 1)) / 2;

    loop invariant i >= 0;

    loop invariant i <= l;

    loop invariant s == 1;

    loop assigns v, i, s;

    loop variant i;

  */
  while (i>0) {
      v = v+i;
      s = s*s;
      i = i-1;
  }

}