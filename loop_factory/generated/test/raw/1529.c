int main1(){
  int l, v3, sn3, s8r, vl, qy, xj, fi, e;

  l=1+4;
  v3=l;
  sn3=0;
  s8r=1;
  vl=0;
  qy=6;
  xj=6;
  fi=3;
  e=l;

  while (sn3>=0&&sn3<3) {
      if (!(!(sn3==0&&s8r>=l))) {
          sn3 = 3;
      }
      else {
          if (sn3==1&&vl<s8r) {
              qy = qy+s8r-vl;
              vl++;
          }
          else {
              if (sn3==1&&vl>=s8r) {
                  sn3 = 2;
              }
              else {
                  if (sn3==2) {
                      s8r = s8r + 1;
                      sn3 = 0;
                  }
              }
          }
      }
      xj = xj + 3;
      fi = fi+(v3%2);
      e += 2;
  }

}
