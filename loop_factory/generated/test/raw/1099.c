int main1(){
  int ui, qvc3, v4, e11, c5, zd6, hj, rwa;

  ui=(1%30)+5;
  qvc3=0;
  v4=0;
  e11=0;
  c5=0;
  zd6=0;
  hj=0;
  rwa=qvc3;

  while (v4<=ui-1) {
      if (v4%7==0) {
          hj = hj + 1;
      }
      else {
          if (v4%9==0) {
              zd6 = zd6 + 1;
          }
          else {
              if (v4%5==0) {
                  c5 += 1;
              }
              else {
                  e11++;
              }
          }
      }
      v4 += 1;
      rwa += ui;
  }

  while (rwa<e11) {
      hj += rwa;
      rwa = rwa + 1;
      v4 += rwa;
  }

}
