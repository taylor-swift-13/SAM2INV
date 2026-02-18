int main1(int a,int b,int m,int q){
  int l, i, v, d;

  l=q;
  i=0;
  v=-2;
  d=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
   loop invariant d <= 0;
   loop invariant v <= -2;
   loop invariant d + v <= -2;
   loop invariant 0 <= i;
   loop invariant l == \at(q, Pre);
   loop invariant i >= 0;
   loop invariant i <= l || l < 0;
   loop invariant d >= v;
   loop invariant l == q;

   loop invariant q == \at(q, Pre);
   loop invariant a == \at(a, Pre);
   loop invariant b == \at(b, Pre);
   loop invariant m == \at(m, Pre);
   loop invariant d % 2 == 0;
   loop invariant v % 2 == 0;
   loop assigns d, v, i;
   loop variant l - i;
 */
while (i<l) {
      d = d+d;
      d = d+v;
      v = v+2;
      v = v+d;
      i = i+1;
  }

}