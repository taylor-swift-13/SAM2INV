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
