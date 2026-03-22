int main1(int a,int f){
  int c, lcl0, u9, fn, s, vw;
  c=26;
  lcl0=0;
  u9=0;
  fn=0;
  s=0;
  vw=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= lcl0 <= c;
  loop invariant f >= \at(f,Pre);
  loop invariant vw == lcl0 - ((lcl0 + 6) / 7);
  loop invariant 0 <= fn;
  loop invariant 0 <= u9;
  loop invariant fn <= lcl0/42 + 1;
  loop invariant s == ((lcl0 + 34) / 35);
  loop invariant u9 == ((lcl0 + 6) / 7) - ((lcl0 + 34) / 35) - ((lcl0 + 41) / 42) + ((lcl0 + 209) / 210);
  loop assigns lcl0, f, vw, s, fn, u9;
*/
while (lcl0<=c-1) {
      if (!(!(lcl0%7==0))) {
          if (lcl0%5==0) {
              s++;
          }
          else {
              if (lcl0%6==0) {
                  fn += 1;
              }
              else {
                  u9 = u9 + 1;
              }
          }
      }
      else {
          vw = vw + 1;
      }
      lcl0 = lcl0 + 1;
      f = f + vw;
  }
}