int main1(int k,int p,int q){
  int l, i, v, n, y, r;

  l=34;
  i=0;
  v=l;
  n=l;
  y=p;
  r=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == l;
    loop invariant r == p + 2*i;
    loop invariant y == p + i*v;
    loop invariant n == l + i*p + (i*(i-1)/2)*(v+1);
    loop invariant i <= l;
    loop invariant i >= 0;
    loop assigns n, y, r, i;
  */
  while (i<l) {
      n = n+y;
      y = y+v;
      n = n+i;
      r = r+2;
      i = i+1;
  }

}