int main1(){
  int fr, nolv, ulaw, xn;
  fr=77;
  nolv=0;
  ulaw=1;
  xn=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((ulaw == 1 && xn == 0) ||
                    (ulaw == 2 && xn == 1) ||
                    (ulaw == 4 && xn == 2) ||
                    (ulaw == 8 && xn == 3) ||
                    (ulaw == 16 && xn == 4) ||
                    (ulaw == 32 && xn == 5) ||
                    (ulaw == 64 && xn == 6) ||
                    (ulaw == 128 && xn == 7));
  loop invariant nolv == 0;
  loop invariant ulaw >= 1;
  loop invariant ulaw <= 2*fr - 2;
  loop invariant xn >= 0;
  loop invariant fr == 77;
  loop assigns ulaw, xn;
*/
while (ulaw<fr) {
      ulaw = 2*ulaw;
      xn += 1;
      xn = (nolv)+(xn);
  }
}