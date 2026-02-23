int main1(int m,int n){
  int b, f, v;

  b=m+16;
  f=0;
  v=-1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(m, Pre) + 16;
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);

  loop invariant v == -1 || v == 0;
  loop invariant -1 <= v <= 0;
  loop invariant 0 <= f;
  loop invariant b == m + 16;
  loop invariant f >= 0 && (v == -1 || v == 0);
  loop invariant f <= b || b < 0;
  loop invariant (v == -1) || (v == 0);
  loop invariant f >= 0;

  loop assigns f, v;
*/
while (f+1<=b) {
      if (v+2<b) {
          v = v-v;
      }
      f = f+1;
  }

}
