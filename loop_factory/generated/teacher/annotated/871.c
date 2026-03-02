int main1(int a,int n){
  int m, h, v;

  m=17;
  h=0;
  v=h;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre) && h == 0 && m == 17;
  loop invariant n == \at(n, Pre) && v >= 0 && h + 7 <= h + m;
  loop invariant a == \at(a, Pre) && n == \at(n, Pre) && m == 17;
  loop invariant h <= m - 1 && v >= 0 && v <= (v+3)*(v+4);
  loop invariant h == 0;
  loop invariant m == 17;
  loop invariant v >= 0;

  loop invariant h <= m - 1;
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant h <= m;

  loop assigns v;
*/
while (h+1<=m) {
      v = v+3;
      if (h+7<=h+m) {
          v = v*v+v;
      }
  }

}
