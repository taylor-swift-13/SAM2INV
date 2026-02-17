int main1(int m,int n,int p){
  int l, i, v, a, r;

  l=62;
  i=0;
  v=3;
  a=-5;
  r=-8;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
   loop invariant l == 62;
   loop invariant 0 <= i && i <= l;
   loop invariant v == 3 + i;
   loop invariant a == -5;
   loop invariant r == -8 + 2*i;
   loop invariant m == \at(m, Pre);
   loop invariant n == \at(n, Pre);
   loop invariant p == \at(p, Pre);
   loop assigns i, v, a, r;
   loop variant l - i;
 */
while (i<l) {
      v = v+1;
      a = a-1;
      r = r+2;
      if (i+3<=i+l) {
          a = a+1;
      }
      i = i+1;
  }

}