int main1(int b,int p,int q){
  int l, i, v, z, f, w, y;

  l=60;
  i=0;
  v=2;
  z=i;
  f=q;
  w=-6;
  y=3;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant v == i + 2;
    loop invariant z == 2*i + i*(i+1)/2;
    loop assigns v, z, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v+1;
      z = z+v;
      i = i+1;
  }

}