int main1(int b,int k,int m,int p){
  int a, r, v, h;

  a=p+13;
  r=1;
  v=k;
  h=-2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(p, Pre) + 13;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant h == -2 || h == 3;
  loop invariant v <= \at(k, Pre) + 4 || v <= a + 2;
  loop invariant a == p + 13;

  loop invariant (k == \at(k, Pre)) && (m == \at(m, Pre)) && (p == \at(p, Pre)) && (b == \at(b, Pre)) && ((h == -2) || (h == 3));


  loop assigns v, h;
*/
while (1) {
      if (v+2<=a) {
          v = v+2;
      }
      else {
          v = a;
      }
      v = v+1;
      h = h-1;
      v = v+1;
      h = h+v;
      h = v-h;
  }

}
