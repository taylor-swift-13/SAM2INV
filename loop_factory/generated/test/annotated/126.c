int main1(int a,int b,int m,int p){
  int l, i, v;

  l=54;
  i=l;
  v=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
   loop invariant l == 54;
   loop invariant i <= l;
   loop invariant i >= 0;
   loop invariant (i == l) ==> (v == 54);
   loop invariant a == \at(a, Pre) && b == \at(b, Pre) && m == \at(m, Pre) && p == \at(p, Pre);
   loop invariant a == \at(a, Pre);
   loop invariant b == \at(b, Pre);
   loop invariant m == \at(m, Pre);
   loop invariant p == \at(p, Pre);
   loop invariant 0 <= i;
   loop invariant v >= 0;
   loop invariant v <= i;
   loop invariant (i >= 0 && i <= l);
   loop invariant (a == \at(a, Pre) && b == \at(b, Pre) && m == \at(m, Pre) && p == \at(p, Pre));
   loop assigns v, i;
 */
while (i>0) {
      if (i+5<=l+l) {
          v = v-v;
      }
      else {
          v = v+1;
      }
      i = i-1;
  }

}