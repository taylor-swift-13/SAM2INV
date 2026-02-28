int main1(int a,int b){
  int j, u, v, g;

  j=(b%10)+18;
  u=0;
  v=0;
  g=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant j == (b % 10) + 18;
  loop invariant v <= j;
  loop invariant (v <= j/2) ==> g == 3*v;
  loop invariant (v > j/2) ==> g == 3*(2*(j/2) - v);
  loop invariant 0 <= v;
  loop invariant 0 <= v <= j;
  loop invariant g % 3 == 0;
  loop invariant (v <= j - v) ==> (g <= 3*v);
  loop invariant (v <= j - v) ==> (g >= -3*v);
  loop invariant (v > j - v) ==> (g <= 3*(j - v));

  loop invariant g % 3 == 0 && -3*v <= g && g <= 3*v && (v < j/2) ==> g == 3*v && (v >= j/2) ==> g == 3*(j/2) - 3*(v - j/2);
  loop assigns g, v;
*/
while (v<j) {
      if (v<j/2) {
          g = g+3;
      }
      else {
          g = g-3;
      }
      v = v+1;
  }

}
