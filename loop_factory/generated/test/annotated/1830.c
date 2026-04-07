int main1(){
  int uxu, wzeb, yp5, czzf, kq, qlx;
  uxu=1-2;
  wzeb=3;
  yp5=0;
  czzf=-2;
  kq=wzeb;
  qlx=uxu;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yp5 >= 0;
  loop invariant kq >= 3;
  loop invariant qlx >= -1;
  loop invariant czzf - yp5 == -2;
  loop invariant czzf <= uxu;
  loop assigns czzf, yp5, kq, qlx;
*/
while (czzf<uxu) {
      yp5++;
      czzf++;
      kq = kq+(yp5%6);
      qlx = qlx+(yp5%3);
  }
}