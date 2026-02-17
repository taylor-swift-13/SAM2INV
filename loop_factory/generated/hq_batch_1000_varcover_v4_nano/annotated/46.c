int main1(int b,int k,int m){
  int l, i, v, w, q, a, r;

  l=(k%7)+18;
  i=0;
  v=b;
  w=i;
  q=k;
  a=k;
  r=5;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
   loop invariant w == 0;
   loop invariant i % 2 == 0;
   loop invariant 0 <= i;
   loop invariant i <= l + 1;
   loop invariant v == \at(b,Pre) + (i/2) * w;
   loop assigns v, i;
   loop variant l - i;
 */
 while (i<l) {
       v = v+w;
       i = i+2;
   }

}