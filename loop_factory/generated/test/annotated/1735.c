int main1(){
  int q, yh, m5, a65, ur;
  q=(1%28)+18;
  yh=-6;
  m5=1;
  a65=0;
  ur=yh;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((a65 == 0 && m5 == 1) ||
                    (a65 == 1 && m5 == 2) ||
                    (a65 == 2 && m5 == 4) ||
                    (a65 == 3 && m5 == 8) ||
                    (a65 == 4 && m5 == 16) ||
                    (a65 == 5 && m5 == 32));
  loop invariant (0 <= a65 && a65 <= 5);
  loop invariant q == 19;
  loop invariant ((a65 == 0)  ==> (ur == -6))  &&
                 ((a65 == 1)  ==> (ur == -9))  &&
                 ((a65 == 2)  ==> (ur == -14)) &&
                 ((a65 == 3)  ==> (ur == -23)) &&
                 ((a65 == 4)  ==> (ur == -40)) &&
                 ((a65 == 5)  ==> (ur == -73));
  loop assigns m5, a65, ur;
*/
while (1) {
      if (!(m5<q)) {
          break;
      }
      m5 = 2*m5;
      a65 = (1)+(a65);
      ur = ur*2+(a65%7)+2;
  }
}