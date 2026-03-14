int main1(){
  int yl, sq, usn, fbl, vey;

  yl=15;
  sq=0;
  usn=0;
  fbl=0;
  vey=sq;

  while (usn<yl) {
      fbl += usn;
      usn = usn + 1;
      vey += fbl;
      if (vey+3<yl) {
          vey++;
      }
  }

}
