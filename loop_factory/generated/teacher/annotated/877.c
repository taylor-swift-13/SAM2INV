int main1(int m,int n){
  int j, b, v;

  j=m+3;
  b=0;
  v=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == 0 && j == \at(m, Pre) + 3 && m == \at(m, Pre) && n == \at(n, Pre);
  loop invariant v >= -4 && v <= 0;
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant j == \at(m, Pre) + 3;
  loop invariant b == 0;
  loop invariant (v % 2) == 0;
  loop invariant j == m + 3;
  loop invariant -4 <= v <= 0;
  loop invariant v == 0 || v == -4;
  loop invariant v % 2 == 0;
  loop invariant j == \at(m, Pre) + 3 && b == 0 && (b % 7) == 0;
  loop invariant (v == 0 || v == -4) && m == \at(m, Pre) && n == \at(n, Pre);
  loop invariant v >= -4;
  loop invariant v % 4 == 0;
  loop invariant j == \at(m, Pre) + 3 && m == \at(m, Pre) && n == \at(n, Pre) && b % 7 == 0;
  loop invariant m == \at(m, Pre) && n == \at(n, Pre);
  loop assigns v;
*/
while (1) {
      v = v+2;
      v = v+v;
      if ((b%7)==0) {
          v = v-v;
      }
  }

}
