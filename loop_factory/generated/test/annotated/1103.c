int main1(int w){
  int i8, t50, t, g8, a, ijh0, df;
  i8=w;
  t50=0;
  t=0;
  g8=0;
  a=0;
  ijh0=0;
  df=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w == \at(w, Pre) * (t + 1);
  loop invariant df + ijh0 + a + g8 == t;
  loop invariant w == \at(w, Pre) + t * i8;
  loop invariant 0 <= df;
  loop invariant 0 <= ijh0;
  loop invariant 0 <= a;
  loop invariant 0 <= g8;
  loop assigns df, ijh0, a, g8, w, t;
*/
while (1) {
      if (!(t<i8)) {
          break;
      }
      if (t%10==0) {
          df++;
      }
      else {
          if (t%5==0) {
              ijh0 = ijh0 + 1;
          }
          else {
              if (t%7==0) {
                  a++;
              }
              else {
                  g8 = g8 + 1;
              }
          }
      }
      w = w + i8;
      t += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t50 >= 0;
  loop invariant t >= 0;
  loop assigns w, t50, t;
*/
for (; t-4>=0; t -= 4) {
      w = w + w;
      w = w + t50;
      t50++;
  }
}