int main1(int a,int b,int k,int p){
  int l, i, v;

  l=a+24;
  i=0;
  v=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@

   loop invariant 0 <= i;
   loop invariant v == l;
   loop invariant l == a + 24;
   loop invariant a == \at(a, Pre);
   loop invariant i >= 0;
   loop invariant b == \at(b, Pre);
   loop invariant k == \at(k, Pre);
   loop invariant p == \at(p, Pre);
   loop invariant i <= l || l < 0;
   loop invariant a == \at(a, Pre) && b == \at(b, Pre) && k == \at(k, Pre) && p == \at(p, Pre);
   loop assigns i, v;
   loop variant l - i;
 */
while (i<l) {
      if (v+6<l) {
          v = v+1;
      }
      i = i+1;
  }

}