int main1(int s){
  int a2kq, nc, gs, ine, j5, sqed;
  a2kq=s+10;
  nc=a2kq;
  gs=0;
  ine=0;
  j5=nc;
  sqed=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ine;
  loop invariant gs == ine * s;
  loop invariant a2kq == \at(s, Pre) + 10;
  loop invariant a2kq == s + 10;
  loop assigns gs, ine, j5;
*/
while (1) {
      if (!(ine<a2kq)) {
          break;
      }
      gs = gs + s;
      ine++;
      j5 += gs;
      j5 = j5*j5+j5;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant sqed == 0;
  loop invariant sqed >= 0;
  loop assigns a2kq, j5, sqed, s;
*/
while (a2kq<=gs-1) {
      a2kq++;
      j5 = j5 + s;
      sqed = sqed*2;
      s = s+gs-nc;
  }
}