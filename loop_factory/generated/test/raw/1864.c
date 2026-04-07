int main1(int w){
  int jd, d2, cj5p, o4, ats, ut, cu4, i2jy, oi, ce;

  jd=(w%21)+5;
  d2=0;
  cj5p=0;
  o4=1;
  ats=0;
  ut=jd;
  cu4=d2;
  i2jy=-3;
  oi=d2;
  ce=0;

  while (cj5p>=0&&cj5p<3) {
      if (!(!(cj5p==0&&o4>=jd))) {
          cj5p = 3;
      }
      else {
          if (cj5p==1&&ats<o4) {
              ut = ut+o4-ats;
              ats++;
          }
          else {
              if (cj5p==1&&ats>=o4) {
                  cj5p = 2;
              }
              else {
                  if (cj5p==2) {
                      o4++;
                      cj5p = 0;
                  }
              }
          }
      }
      i2jy += cj5p;
      cu4 += 2;
      oi += ats;
      w = w+(d2%2);
      ce += ats;
      cu4++;
  }

}
