int main1(){
  int hlkf, mya, wvo4, nk, ji, yf, w80, q, t54;
  hlkf=64;
  mya=0;
  wvo4=0;
  nk=0;
  ji=0;
  yf=0;
  w80=0;
  q=0;
  t54=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= mya <= hlkf;
  loop invariant wvo4 + nk + ji + yf + w80 == mya;
  loop invariant q == wvo4 + 2*nk + 3*ji + 4*yf + 5*w80;
  loop invariant 0 <= t54 <= 5*mya;
  loop invariant 0 <= wvo4 <= mya;
  loop invariant 0 <= nk <= mya;
  loop invariant 0 <= ji <= mya;
  loop invariant 0 <= yf <= mya;
  loop invariant 0 <= w80 <= mya;
  loop assigns wvo4, q, nk, ji, yf, w80, t54, mya;
*/
while (mya<=hlkf-1) {
      if (mya%10==0) {
          wvo4++;
          q += 1;
      }
      else {
          if (mya%8==0) {
              nk++;
              q += 2;
          }
          else {
              if (mya%6==0) {
                  ji++;
                  q = q + 3;
              }
              else {
                  if (mya%2==0) {
                      yf++;
                      q += 4;
                  }
                  else {
                      if (1) {
                          w80++;
                          q = q + 5;
                      }
                  }
              }
          }
      }
      mya = mya + 1;
      t54 = t54+mya%6;
  }
}