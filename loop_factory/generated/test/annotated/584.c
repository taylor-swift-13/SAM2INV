int main1(){
  int eyv, iq, tb, su8, zmg;
  eyv=1;
  iq=3;
  tb=0;
  su8=eyv;
  zmg=-3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant su8 == eyv + iq * tb;
  loop invariant su8 == 1 + iq * tb;
  loop invariant zmg <= tb;
  loop invariant 0 <= tb;
  loop invariant tb <= eyv;
  loop assigns tb, zmg, su8;
*/
while (tb<eyv) {
      tb++;
      if (!(!(tb<=zmg))) {
          zmg = tb;
      }
      su8 += iq;
  }
}