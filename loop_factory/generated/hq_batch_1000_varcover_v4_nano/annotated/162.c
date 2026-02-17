int main1(int a,int k,int m){
  int l, i, v, b;

  l=17;
  i=0;
  v=4;
  b=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
   loop invariant v == 4 + 5*i;
   loop invariant b == k + 12*i + (5*i*(i-1))/2;
   loop invariant 0 <= i && i <= l;
   loop invariant l == 17;
   loop assigns v, b, i;
 */
while (i<l) {
      v = v+4;
      b = b+4;
      b = b+v;
      v = v+1;
      i = i+1;
  }

}