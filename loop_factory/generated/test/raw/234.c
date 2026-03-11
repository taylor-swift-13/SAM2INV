int main1(){
  int y65, ljz, ya, d, tx, nn;

  y65=1-7;
  ljz=0;
  ya=0;
  d=0;
  tx=ljz;
  nn=12;

  while (d<y65) {
      ya += 1;
      d++;
      nn += ya;
      tx = tx*2;
  }

  while (ya<=ljz-1) {
      tx += 1;
      ya += 1;
      y65 = y65+(tx%9);
      d = d*2;
  }

}
