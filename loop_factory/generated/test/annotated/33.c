int main1(int a,int b,int k,int q){
  int l, i, v;

  l=65;
  i=0;
  v=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
   loop invariant 0 <= i <= l;
   loop invariant l == 65;
   loop invariant v == 0 || v - i == q;
   loop invariant (q >= 61) ==> (v == q + i);
   loop invariant 0 <= i && i <= l;

   loop invariant a == \at(a, Pre);
   loop invariant b == \at(b, Pre);
   loop invariant k == \at(k, Pre);
   loop invariant q == \at(q, Pre);
   loop invariant 0 <= i;
   loop invariant i <= l;
   loop assigns v, i;
   loop variant l - i;
 */
while (i<l) {
      v = v+1;
      if (v+3<l) {
          v = v-v;
      }
      i = i+1;
  }

}