int main1(int b,int n,int p){
  int l, i, v, o, t, a, w, k, r, d;

  l=79;
  i=l;
  v=i;
  o=p;
  t=i;
  a=-2;
  w=b;
  k=-2;
  r=p;
  d=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v + o == i + p;
    loop invariant v >= i;
    loop invariant o <= p;
    loop invariant i >= 0;
    loop assigns v, o;
  */
  while (i>0) {
      v = v+1;
      o = o-1;
  }

}