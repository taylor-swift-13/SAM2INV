int main1(int b,int m,int q){
  int l, i, v, d, n, r;

  l=75;
  i=l;
  v=q;
  d=i;
  n=m;
  r=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
   loop invariant i <= l;
   loop invariant i >= 0;
   loop invariant v * q >= 0;
   loop invariant v >= 0 <==> q >= 0;
   loop assigns v, i;
 */
while (i>0) {
      v = v*3;
      i = i/2;
  }

}