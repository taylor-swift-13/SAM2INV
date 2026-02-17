int main1(int b,int k,int q){
  int l, i, v, y, h, s, d, z;

  l=72;
  i=0;
  v=i;
  y=l;
  h=q;
  s=l;
  d=i;
  z=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i <= l;
    loop invariant h == q + i;
    loop invariant y == l + i*q + i*(i-1)/2;
    loop assigns i, h, y;
  */
  while (i<l) {
      y = y+h;
      h = h+v;
      h = h+1;
      i = i+1;
  }

}