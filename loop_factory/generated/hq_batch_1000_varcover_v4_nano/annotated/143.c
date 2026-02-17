int main1(int a,int k,int n){
  int l, i, v, q, m;

  l=9;
  i=l;
  v=n;
  q=2;
  m=6;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
   loop invariant i <= l;
   loop invariant i >= 0;
   loop invariant v == n + 2*(l - i);
   loop invariant q == 2 + (l - i)*(n + l + 1) + ((l - i)*(l - i - 1))/2;
   loop invariant m == 6;
   loop assigns v, q, m, i;
   loop variant i;
 */
while (i>0) {
      v = v+1;
      q = q+v;
      q = q+i;
      if (i+6<=l+l) {
          v = v+1;
      }
      else {
          m = m+1;
      }
      i = i-1;
  }

}