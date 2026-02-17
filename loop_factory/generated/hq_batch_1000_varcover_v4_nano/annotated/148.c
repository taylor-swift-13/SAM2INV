int main1(int b,int p,int q){
  int l, i, v;

  l=58;
  i=0;
  v=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
   loop invariant 0 <= i && i <= l;
   loop invariant l <= v && v <= 2*l;
   loop invariant (i == 0) ==> (v == l);
   loop invariant (i > 0) ==> (v == 2*l);
   loop invariant l == 58;
   loop invariant b == \at(b, Pre) && p == \at(p, Pre) && q == \at(q, Pre);
   loop assigns v, i;
   loop variant l - i;
 */
while (i<l) {
      if (v<l+2) {
          v = v+v;
      }
      i = i+1;
  }

}