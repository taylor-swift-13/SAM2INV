int main1(){
  int mvg, yc, x3, lni5;
  mvg=1-2;
  yc=0;
  x3=-2;
  lni5=yc;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mvg == -1;
  loop invariant (yc == 0) ==> (lni5 == 0);
  loop invariant ((lni5 == 0) || (lni5 == -2) || (lni5 == 2));
  loop invariant (yc >= 0);
  loop invariant ((yc == 0 && lni5 == 0) ||
                    (yc == 1 && lni5 == -2) ||
                    (yc >= 2 && lni5 == 2));
  loop invariant x3 == -2;
  loop assigns lni5, yc;
*/
while (1) {
      lni5 = lni5*lni5+x3;
      yc++;
      if (yc>=mvg) {
          break;
      }
  }
}