int main1(int a,int k,int q){
  int l, i, v, h;

  l=63;
  i=0;
  v=i;
  h=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 63;
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant h == -i;
    loop invariant 2*v == -(i*(i-1));
    loop assigns i, v, h;
  */
  while (i<l) {
      v = v+1;
      h = h-1;
      v = v+h;
      i = i+1;
  }

}