int main1(){
  int mye, rwh, kv83, zd, eb, m5pb, dh, g0r, hrp, ig;

  mye=57;
  rwh=0;
  kv83=0;
  zd=1;
  eb=0;
  m5pb=rwh;
  dh=rwh;
  g0r=mye;
  hrp=20;
  ig=-6;

  while (kv83>=0&&kv83<3) {
      if (!(!(kv83==0&&zd>=mye))) {
          kv83 = 3;
      }
      else {
          if (kv83==1&&eb<zd) {
              m5pb = m5pb+zd-eb;
              eb++;
          }
          else {
              if (kv83==1&&eb>=zd) {
                  kv83 = 2;
              }
              else {
                  if (kv83==2) {
                      zd = zd + 1;
                      kv83 = 0;
                  }
              }
          }
      }
      g0r += hrp;
      ig = ig + rwh;
      g0r += 4;
      hrp += dh;
      g0r++;
  }

}
