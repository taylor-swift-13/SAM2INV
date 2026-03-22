int main1(){
  int by, tb, t, j5;
  by=(1%28)+8;
  tb=(1%22)+5;
  t=0;
  j5=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= tb <= 6 &&
                   0 <= by &&
                   0 <= t &&
                   0 <= j5;
  loop invariant by % 9 == 0;
  loop invariant t <= by;
  loop invariant tb >= 0;
  loop invariant tb <= 6;
  loop invariant by > 0;
  loop invariant t >= 0;
  loop invariant j5 >= 0;
  loop assigns by, tb, t, j5;
*/
while (tb!=0) {
      if (tb%2==1) {
          t = t + by;
          tb -= 1;
      }
      tb = tb/2;
      by = 2*by;
      j5 += tb;
  }
}