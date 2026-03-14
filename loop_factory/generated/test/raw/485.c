int main1(int h,int b){
  int qk, ebc, vgz, y, qp;

  qk=h+14;
  ebc=0;
  vgz=0;
  y=(h%28)+10;
  qp=6;

  while (y>vgz) {
      y = y - vgz;
      vgz++;
      qp = qp + 3;
      b = b+qk-ebc;
      h += 1;
  }

  while (y>vgz) {
      y = y - vgz;
      vgz++;
      h = h+(y%6);
      b = b+(y%7);
  }

}
