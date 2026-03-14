int main1(int c){
  int si, hl36, jd, wv, w;
  si=c;
  hl36=0;
  jd=hl36;
  wv=c;
  w=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (hl36 == 0) || (hl36 == si);
  loop invariant (w == 5) || (w == c + 1);
  loop invariant (jd == 0) || (jd == 4);
  loop invariant jd + wv == c;
  loop invariant si == \at(c, Pre);
  loop invariant (hl36 == 0) ==> (jd == 0 && wv == c && w == 5 && si == c);
  loop assigns w, wv, jd, hl36;
*/
while (hl36<si) {
      wv -= 4;
      jd += 4;
      w = w + wv;
      hl36 = si;
  }
}