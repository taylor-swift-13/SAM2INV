int main1(){
  int yl, sq, usn, fbl, vey;
  yl=15;
  sq=0;
  usn=0;
  fbl=0;
  vey=sq;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= usn <= yl;
  loop invariant fbl == usn * (usn - 1) / 2;
  loop invariant vey >= 0;
  loop assigns fbl, usn, vey;
*/
while (usn<yl) {
      fbl += usn;
      usn = usn + 1;
      vey += fbl;
      if (vey+3<yl) {
          vey++;
      }
  }
}