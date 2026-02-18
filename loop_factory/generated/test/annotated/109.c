int main1(int a,int b,int m,int q){
  int l, i, v, y;

  l=17;
  i=0;
  v=-8;
  y=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
   loop invariant i <= l;
   loop invariant 0 <= i;
   loop invariant (i == 0) ==> (v == -8);
   loop invariant (i > 0) ==> (v >= 0 && v <= 2);
   loop invariant a == \at(a, Pre) && b == \at(b, Pre) && m == \at(m, Pre) && q == \at(q, Pre);
   loop invariant l == 17;
   loop invariant a == \at(a, Pre);
   loop invariant b == \at(b, Pre);
   loop invariant m == \at(m, Pre);
   loop invariant q == \at(q, Pre);
   loop invariant (v == -8) || (v == 0) || (v == 2);
   loop invariant i >= 0;
   loop assigns i, v;
 */
while (i<l) {
      v = v*v+v;
      v = v%3;
      i = i+1;
  }

}