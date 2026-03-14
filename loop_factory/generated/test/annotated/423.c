int main1(int w,int p){
  int qg, s, xc, tt;
  qg=w+25;
  s=0;
  xc=s;
  tt=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xc == s;
  loop invariant tt == -s;
  loop invariant qg == \at(w, Pre) + 25;
  loop invariant w == qg - 25 + (s * (s - 1)) / 2;
  loop invariant 0 <= s;
  loop invariant p == \at(p, Pre);
  loop assigns tt, xc, w, s;
*/
while (1) {
      tt -= 1;
      xc = xc + 1;
      w = w + s;
      s++;
      if (s>=qg) {
          break;
      }
  }
}