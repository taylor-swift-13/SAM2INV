int main1(int b,int k,int p){
  int l, i, v, h, r, e, u, n, j, c;

  l=44;
  i=0;
  v=l;
  h=3;
  r=-6;
  e=p;
  u=i;
  n=0;
  j=p;
  c=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == l + (i*(i-1))/2;
    loop invariant 0 <= i <= l;
    loop assigns v, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v+i;
      i = i+1;
  }

}