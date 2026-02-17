int main1(int a,int k,int m){
  int l, i, v, u, o, j;

  l=38;
  i=l;
  v=-5;
  u=i;
  o=i;
  j=3;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i > 0;
    loop invariant v >= -5;
    loop invariant u >= i;
    loop invariant o >= i;
    loop invariant (i % 3 == 1) ==> (u == i) && (o == i);
    loop invariant (i % 3 != 1) ==> (v == -5);
    loop assigns v, u, o;
  */
  while (i>0) {
      if (i%3==1) {
          v = v+1;
      }
      else {
          u = u+1;
      }
      if (i%3==2) {
          o = o+1;
      }
      else {
      }
  }

}