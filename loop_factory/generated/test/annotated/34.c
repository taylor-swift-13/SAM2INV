int main1(int a,int b,int m,int p){
  int l, i, v, r;

  l=30;
  i=0;
  v=-8;
  r=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
   loop invariant i == 4*v + 32;
   loop invariant l == 30;
   loop invariant i >= 0;
   loop invariant a == \at(a, Pre);
   loop invariant b == \at(b, Pre);
   loop invariant m == \at(m, Pre);
   loop invariant p == \at(p, Pre);
   loop invariant i - 4*v == 32;

   loop invariant 4*(v + 8) == i;
   loop invariant i % 4 == 0;
   loop invariant 0 <= i && i <= l + 3;
   loop invariant a == \at(a, Pre) && b == \at(b, Pre) && m == \at(m, Pre) && p == \at(p, Pre);
   loop invariant i == 4*(v + 8);
   loop invariant -8 <= v <= 0;
   loop invariant 0 <= i;
   loop assigns i, v;
   loop variant l - i;
 */
while (i<l) {
      v = v+1;
      i = i+4;
  }

}