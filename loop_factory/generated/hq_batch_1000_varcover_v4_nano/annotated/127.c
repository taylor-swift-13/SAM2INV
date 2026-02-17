int main1(int a,int k,int q){
  int l, i, v, p, w, g;

  l=35;
  i=l;
  v=1;
  p=a;
  w=i;
  g=-6;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant ((v + 2) % 3) == 0;
    loop invariant v >= 1;
    loop assigns v, i;
  */
  while (i>0) {
      v = v*3+4;
      i = i/2;
  }

}