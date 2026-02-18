int main1(int b,int k,int m,int q){
  int l, i, v;

  l=77;
  i=0;
  v=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
   loop invariant 0 <= i <= l;
   loop invariant l == 77;
   loop invariant b == \at(b, Pre);
   loop invariant k == \at(k, Pre);
   loop invariant m == \at(m, Pre);
   loop invariant q == \at(q, Pre);

   loop invariant (i == 0) ==> (v == k);

   loop assigns i, v;
   loop variant l - i;
 */
while (i<l) {
      v = v*2;
      v = v+v;
      if (i+6<=i+l) {
          v = v%9;
      }
      i = i+1;
  }

}