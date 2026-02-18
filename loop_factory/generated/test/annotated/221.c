int main1(int a,int q){
  int l, i, v, j;

  l=51;
  i=0;
  v=i;
  j=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
   loop invariant l == 51;
   loop invariant i >= 0;
   loop invariant i <= l;
   loop invariant v >= 0;
   loop invariant a == \at(a, Pre);
   loop invariant q == \at(q, Pre);
   loop invariant v % 5 == 0;
   loop invariant 0 <= i;
   loop invariant v >= 5*i;
   loop invariant (i == 0) <==> (v == 0);
   loop assigns v, i;
 */
while (i<l) {
      v = v*4+5;
      i = i+1;
  }

}