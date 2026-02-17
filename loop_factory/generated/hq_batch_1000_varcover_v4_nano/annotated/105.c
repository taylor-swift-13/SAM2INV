int main1(int a,int b,int m){
  int l, i, v, f, w;

  l=75;
  i=l;
  v=0;
  f=m;
  w=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == (l - i) * (f + w + 1);
    loop invariant i <= l;
    loop invariant i >= 0;
    loop assigns v, i;
    loop variant i;
  */
  while (i>0) {
      v = v+f+w;
      v = v+1;
      i = i-1;
  }

}