int main1(int n,int p,int q){
  int l, i, v, a, c, k, j;

  l=35;
  i=l;
  v=0;
  a=-6;
  c=q;
  k=-3;
  j=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
   loop invariant l == 35;
   loop invariant i <= l;
   loop invariant i >= 0;
   loop invariant v == 0;
   loop invariant n == \at(n, Pre);
   loop assigns v, i;
   loop variant i;
 */
while (i>0) {
      v = v*3;
      i = i-1;
  }

}