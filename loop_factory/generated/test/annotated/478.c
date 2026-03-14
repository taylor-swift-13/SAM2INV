int main1(int w,int c){
  int qyc, ln, bl7, li, mm;
  qyc=c*4;
  ln=0;
  bl7=0;
  li=0;
  mm=qyc;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qyc == c*4;
  loop invariant ln == 0;
  loop invariant bl7 % 4 == 0;
  loop invariant li <= bl7;
  loop invariant li >= bl7 - 4;
  loop invariant w == \at(w, Pre) + (bl7/4) * qyc;
  loop assigns w, bl7, li;
*/
while (bl7<=qyc-1) {
      li = bl7;
      w = w+qyc-ln;
      bl7 += 4;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mm == qyc;
  loop invariant qyc == 4*c;
  loop invariant li <= bl7 + 7;
  loop assigns w, ln, li;
*/
while (bl7+8<=li) {
      w += 2;
      ln = ln+mm*bl7;
      li = (bl7+8)-1;
  }
}