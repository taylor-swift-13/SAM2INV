int main1(){
  int ea, x4d, am, tb1k, efc, xo;
  ea=44;
  x4d=0;
  am=x4d;
  tb1k=x4d;
  efc=ea;
  xo=(1%6)+2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant efc == ea;
  loop invariant tb1k == 0;
  loop invariant xo >= 3;
  loop invariant am >= 0;
  loop assigns tb1k, am, xo, efc;
*/
while (efc<ea) {
      tb1k = tb1k*xo;
      am = am*xo+1;
      xo += am;
      efc = ea;
  }
}