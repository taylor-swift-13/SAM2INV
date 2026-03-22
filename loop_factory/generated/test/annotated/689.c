int main1(int u,int g){
  int jd4, s, nc, x3, qnz, u4, ybn;
  jd4=56;
  s=jd4;
  nc=7;
  x3=7;
  qnz=0;
  u4=7;
  ybn=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ybn;
  loop invariant s <= jd4;
  loop invariant s - ybn == jd4;
  loop invariant s - ybn == 56;
  loop invariant 0 <= nc <= u4;
  loop invariant qnz >= 0;
  loop invariant x3 >= 7;
  loop assigns nc, qnz, x3, ybn, s;
*/
while (s<jd4) {
      if (!(!(s%3==0))) {
          if (nc>0) {
              nc = nc - 1;
              qnz = qnz + 1;
          }
      }
      else {
          if (nc<u4) {
              nc += 1;
              x3 = x3 + 1;
          }
      }
      ybn += 1;
      s++;
  }
}