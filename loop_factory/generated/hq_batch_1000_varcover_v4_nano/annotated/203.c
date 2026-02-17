int main1(int a,int m,int p){
  int l, i, v, f;

  l=62;
  i=0;
  v=i;
  f=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant v == 0;
    loop invariant l == 62;
    loop invariant f % 2 == 0;
    loop invariant f >= 0;
    loop assigns i, f;
  */
  while (i<l) {
      f = f+f;
      f = f+v;
      i = i+1;
  }

}