int main1(int b,int m,int p){
  int l, i, v, o, w, r, q, s, g;

  l=43;
  i=l;
  v=i;
  o=2;
  w=-3;
  r=p;
  q=1;
  s=m;
  g=m;

  
  /*@

    loop invariant i >= 0;

    loop invariant i <= l;

    loop invariant v == l + (l - i)*l - ((l - i)*(l - i - 1))/2;

    loop invariant l == 43;

    loop assigns v, i;

    loop variant i;

  */
  while (i>0) {
      v = v+i;
      i = i-1;
  }

}